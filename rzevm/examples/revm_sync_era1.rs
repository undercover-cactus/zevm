//! The revm counterpart to `sync_era1.rs`: reads the same `.era1` files
//! (`data/era1/`, populated by `make download-era1`) and replays them
//! through revm natively (no FFI) instead of zevm. Same era1 parsing and
//! reward bookkeeping, so the only real difference is which EVM executes
//! the transactions. Timed the same way, so the two `done: ... in Xms`
//! lines are directly comparable.
//!
//! Also splits that total into `decode` (Snappy + RLP + ECDSA sender
//! recovery) and `execute` (`transact_commit` plus reward bookkeeping),
//! the same split `examples/sync_era1.zig` reports, to compare *EVM
//! execution* speed alone rather than total wall time.
//!
//! Duplicates `sync_era1.rs`'s era1-parsing helpers rather than sharing
//! them, matching this project's convention of self-contained examples.
//!
//! Value affordability: revm's default balance check rejects a transaction
//! unless the sender can afford `value` *and* gas together up front; real
//! Ethereum's inclusion rule only requires gas to be covered (see geth's
//! `buyGas`). `value` affordability is checked separately at execution
//! time and just reverts rather than invalidating the transaction. revm's
//! `disable_balance_check` escape hatch is the wrong tool here: it's built
//! for `eth_call` simulation and overcorrects by topping up the sender's
//! balance (caught via an account-count mismatch against zevm; see
//! `sync.rs`'s identical fix). The per-transaction loop below applies the
//! real gas-only rule directly instead.

use revm::{
    context::{CfgEnv, Context, TxEnv},
    database::{CacheDB, EmptyDB},
    primitives::{hardfork::SpecId, Address, Bytes, TxKind, B256, U256},
    state::AccountInfo,
    Database, ExecuteCommitEvm, MainBuilder, MainContext,
};
use secp256k1::ecdsa::{RecoverableSignature, RecoveryId};
use sha3::{Digest, Keccak256};
use snap::read::FrameDecoder;
use std::fs;
use std::io::Read;
use std::path::PathBuf;
use std::time::{Duration, Instant};

const BLOCKS_PER_FILE: u64 = 8192;

// 5 ETH, in wei: the flat pre-Byzantium block reward.
const BLOCK_REWARD: u128 = 5_000_000_000_000_000_000;

fn parse_address(hex: &str) -> Address {
    Address::from_slice(&hex::decode(hex.trim_start_matches("0x")).unwrap())
}

fn parse_hex_u256(hex: &str) -> U256 {
    let digits = hex.trim_start_matches("0x");
    if digits.is_empty() {
        U256::ZERO
    } else {
        U256::from_str_radix(digits, 16).unwrap()
    }
}

/// Concatenates `r`/`s` into the 64-byte compact form `secp256k1` expects,
/// left-padding each to 32 bytes (RLP strips leading zero bytes, so
/// they're not necessarily already that length).
fn compact_signature(r: &[u8], s: &[u8]) -> [u8; 64] {
    let mut sig = [0u8; 64];
    sig[32 - r.len()..32].copy_from_slice(r);
    sig[64 - s.len()..64].copy_from_slice(s);
    sig
}

struct DecodedTx {
    from: Address,
    nonce: u64,
    gas_price: u128,
    gas_limit: u64,
    kind: TxKind,
    value: U256,
    data: Bytes,
}

/// Parses one legacy transaction from its RLP encoding, deriving `from` via
/// ECDSA signature recovery. Every transaction in this block range
/// predates EIP-2718 typed transactions.
fn parse_transaction(payload: &[u8]) -> DecodedTx {
    let transaction = rlp::Rlp::new(payload);
    assert!(
        transaction.is_list(),
        "expected a legacy (list-encoded) transaction"
    );

    let nonce: u64 = transaction.at(0).unwrap().as_val().unwrap();
    let gas_price: Vec<u8> = transaction.at(1).unwrap().as_val().unwrap();
    let gas_limit: u64 = transaction.at(2).unwrap().as_val().unwrap();
    let to: Vec<u8> = transaction.at(3).unwrap().as_val().unwrap();
    let value: Vec<u8> = transaction.at(4).unwrap().as_val().unwrap();
    let data: Vec<u8> = transaction.at(5).unwrap().as_val().unwrap();
    let v: u64 = transaction.at(6).unwrap().as_val().unwrap();
    let r: Vec<u8> = transaction.at(7).unwrap().as_val().unwrap();
    let s: Vec<u8> = transaction.at(8).unwrap().as_val().unwrap();

    // Reconstruct the signed message: the first 6 fields, re-wrapped as
    // their own RLP list, plus chain_id/0/0 for EIP-155 transactions
    // (v > 28), which shouldn't occur here but is kept for correctness.
    let mut rlps = rlp::RlpStream::new();
    rlps.begin_unbounded_list();
    for n in 0..=5 {
        rlps.append_raw(transaction.at(n).unwrap().as_raw(), 1);
    }
    if v > 28 {
        let chain_id = (v - 35) / 2;
        rlps.append(&chain_id);
        rlps.append(&0_u8);
        rlps.append(&0_u8);
    }
    rlps.finalize_unbounded_list();

    let mut hasher = Keccak256::new();
    hasher.update(rlps.as_raw());
    let digest = hasher.finalize();

    let msg = secp256k1::Message::from_digest_slice(&digest).unwrap();
    let recid = match v {
        0 | 1 | 2 | 3 => RecoveryId::from_i32(v as i32).unwrap(),
        27 => RecoveryId::from_i32(0).unwrap(),
        28 => RecoveryId::from_i32(1).unwrap(),
        _ => RecoveryId::from_i32(((v - 35) % 2) as i32).unwrap(),
    };
    let sig = RecoverableSignature::from_compact(&compact_signature(&r, &s), recid).unwrap();
    let pubkey = sig.recover(&msg).unwrap();
    let mut hasher = Keccak256::new();
    hasher.update(&pubkey.serialize_uncompressed()[1..]);
    let from_hash = hasher.finalize();
    let from = Address::from_slice(&from_hash[12..]);

    let kind = if to.is_empty() {
        TxKind::Create
    } else {
        TxKind::Call(Address::from_slice(&to))
    };

    DecodedTx {
        from,
        nonce,
        gas_price: U256::from_be_slice(&gas_price).to::<u128>(),
        gas_limit,
        kind,
        value: U256::from_be_slice(&value),
        data: Bytes::from(data),
    }
}

/// The fields block execution actually needs out of a block header.
/// Frontier-era headers RLP-encode as a 15-field list; everything except
/// coinbase/difficulty/number/gasLimit/timestamp is decoded and discarded.
struct DecodedHeader {
    number: u64,
    miner: Address,
    timestamp: u64,
    gas_limit: u64,
    difficulty: U256,
}

fn decode_header(header: &rlp::Rlp) -> DecodedHeader {
    let miner: Vec<u8> = header.at(2).unwrap().as_val().unwrap();
    let difficulty: Vec<u8> = header.at(7).unwrap().as_val().unwrap();
    let number: u64 = header.at(8).unwrap().as_val().unwrap();
    let gas_limit: u64 = header.at(9).unwrap().as_val().unwrap();
    let timestamp: u64 = header.at(11).unwrap().as_val().unwrap();

    DecodedHeader {
        number,
        miner: Address::from_slice(&miner),
        timestamp,
        gas_limit,
        difficulty: U256::from_be_slice(&difficulty),
    }
}

struct DecodedUncle {
    number: u64,
    miner: Address,
}

/// An uncle is encoded as a full header (not the abbreviated
/// `{number, miner}` JSON-RPC gives us); only coinbase/number matter here.
fn decode_uncle(uncle: &rlp::Rlp) -> DecodedUncle {
    let miner: Vec<u8> = uncle.at(2).unwrap().as_val().unwrap();
    let number: u64 = uncle.at(8).unwrap().as_val().unwrap();
    DecodedUncle {
        number,
        miner: Address::from_slice(&miner),
    }
}

mod record_type {
    pub const VERSION: [u8; 2] = [0x65, 0x32]; // "e2"
    pub const COMPRESSED_HEADER: [u8; 2] = [0x03, 0x00];
    pub const COMPRESSED_BODY: [u8; 2] = [0x04, 0x00];
    pub const COMPRESSED_RECEIPTS: [u8; 2] = [0x05, 0x00];
}

/// One e2store record: an 8-byte header (2-byte type, 4-byte little-endian
/// length, 2 reserved bytes) followed by `length` bytes of data.
struct Record<'a> {
    kind: [u8; 2],
    data: &'a [u8],
}

fn read_records(bytes: &[u8]) -> Vec<Record<'_>> {
    let mut records = Vec::new();
    let mut pos = 0;
    while pos + 8 <= bytes.len() {
        let kind = [bytes[pos], bytes[pos + 1]];
        let length = u32::from_le_bytes(bytes[pos + 2..pos + 6].try_into().unwrap()) as usize;
        let data = &bytes[pos + 8..pos + 8 + length];
        records.push(Record { kind, data });
        pos += 8 + length;
    }
    records
}

fn snappy_decompress(compressed: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    FrameDecoder::new(compressed)
        .read_to_end(&mut out)
        .expect("snappy decompress");
    out
}

fn era1_files() -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = fs::read_dir("../data/era1")
        .expect("read data/era1: run `make download-era1` first")
        .map(|entry| entry.expect("dir entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "era1"))
        .collect();
    files.sort();
    files
}

fn main() {
    let mut db = CacheDB::<EmptyDB>::default();

    let genesis_text =
        fs::read_to_string("../examples/data/mainnet_genesis.json").expect("read genesis");
    let genesis: serde_json::Value = serde_json::from_str(&genesis_text).expect("parse genesis");
    let alloc = genesis["alloc"].as_object().expect("alloc object");
    for (addr_hex, info) in alloc {
        let address = parse_address(addr_hex);
        let balance = parse_hex_u256(info["balance"].as_str().expect("balance"));
        db.insert_account_info(address, AccountInfo::from_balance(balance));
    }
    println!("loaded {} genesis accounts", alloc.len());

    let mut ctx = Context::mainnet().with_db(db);
    // `with_spec` (deprecated) only sets the opcode-level spec flag, not
    // the separate `gas_params` table intrinsic-gas validation reads,
    // leaving CREATE transactions charged modern surcharges even under
    // "Frontier". `with_spec_and_mainnet_gas_params` sets both together.
    ctx.cfg = CfgEnv::new().with_spec_and_mainnet_gas_params(SpecId::FRONTIER);
    let mut evm = ctx.build_mainnet();

    let files = era1_files();
    println!("found {} era1 files", files.len());

    // Started here, after genesis is loaded, so this measures block
    // processing only, matching sync_era1.rs's methodology.
    let start = Instant::now();

    let mut blocks_processed: u64 = 0;
    let mut transactions_processed: u64 = 0;

    let mut decode_duration = Duration::ZERO;
    let mut execute_duration = Duration::ZERO;

    for (i, path) in files.iter().enumerate() {
        let raw = fs::read(path).expect("read era1 file");
        let records = read_records(&raw);

        let mut iter = records.iter();
        let version = iter.next().expect("version record");
        assert_eq!(
            version.kind,
            record_type::VERSION,
            "expected e2store version record first"
        );

        let mut blocks_in_file = 0u64;
        let mut transactions_in_file = 0u64;
        loop {
            let Some(header_record) = iter.next() else {
                break;
            };
            if header_record.kind != record_type::COMPRESSED_HEADER {
                // AccumulatorRoot + BlockIndex trailer: end of this file's blocks.
                break;
            }
            let body_record = iter.next().expect("body record");
            let receipts_record = iter.next().expect("receipts record");
            let _total_difficulty = iter.next().expect("total difficulty record");
            assert_eq!(body_record.kind, record_type::COMPRESSED_BODY);
            assert_eq!(receipts_record.kind, record_type::COMPRESSED_RECEIPTS);

            let decode_t0 = Instant::now();
            let header_rlp = snappy_decompress(header_record.data);
            let body_rlp = snappy_decompress(body_record.data);

            let header = decode_header(&rlp::Rlp::new(&header_rlp));

            // Body = [transactions, uncles].
            let body_item = rlp::Rlp::new(&body_rlp);
            let transactions_rlp = body_item.at(0).unwrap();
            let uncles_rlp = body_item.at(1).unwrap();
            decode_duration += decode_t0.elapsed();

            let execute_t0 = Instant::now();
            evm.ctx.block.number = U256::from(header.number);
            evm.ctx.block.beneficiary = header.miner;
            evm.ctx.block.timestamp = U256::from(header.timestamp);
            evm.ctx.block.gas_limit = header.gas_limit;
            evm.ctx.block.difficulty = header.difficulty;
            execute_duration += execute_t0.elapsed();

            for n in 0..transactions_rlp.item_count().unwrap() {
                let decode_t0 = Instant::now();
                let tx_item = transactions_rlp.at(n).unwrap();
                let tx = parse_transaction(tx_item.as_raw());

                let from = tx.from;
                let value = tx.value;
                let gas_limit = tx.gas_limit;
                let gas_price = U256::from(tx.gas_price);
                let tx_env = TxEnv::builder()
                    .caller(tx.from)
                    .kind(tx.kind)
                    .value(tx.value)
                    .gas_limit(tx.gas_limit)
                    .gas_price(tx.gas_price)
                    .nonce(tx.nonce)
                    .data(tx.data)
                    .build()
                    .unwrap();
                decode_duration += decode_t0.elapsed();

                let execute_t0 = Instant::now();
                // Real Ethereum's inclusion rule only requires `gas_limit *
                // gas_price` to be affordable, not that plus `value`
                // together; `value` affordability is checked separately at
                // execution time and just reverts rather than invalidating
                // the transaction. revm's own balance check requires both
                // together, and its `disable_balance_check` escape hatch
                // overcorrects by topping up the sender's balance, meant
                // for `eth_call` simulation, not faithful replay (see
                // `sync.rs`'s identical fix). Applying the real rule
                // directly here instead.
                let gas_params = &evm.ctx.cfg.gas_params;
                let intrinsic = gas_params.initial_tx_gas_for_tx(&tx_env, None).initial_total_gas();
                let max_fee_for_gas = U256::from(gas_limit) * gas_price;
                let sender_info = evm
                    .ctx
                    .journaled_state
                    .database
                    .basic(from)
                    .unwrap()
                    .unwrap_or_default();
                if sender_info.balance < max_fee_for_gas {
                    panic!(
                        "block {}: sender {from} can't even afford gas ({} < {max_fee_for_gas}): replayed state has diverged from real chain",
                        header.number, sender_info.balance
                    );
                }
                if sender_info.balance >= max_fee_for_gas + value {
                    evm.transact_commit(tx_env).unwrap_or_else(|e| {
                        panic!(
                            "transact_commit failed for block {}: {:?}",
                            header.number, e
                        )
                    });
                } else {
                    // Soft-revert: charge only the intrinsic gas fee, move
                    // no value, run no code.
                    let fee = U256::from(intrinsic) * gas_price;
                    let mut sender = sender_info;
                    sender.balance -= fee;
                    sender.nonce += 1;
                    evm.ctx
                        .journaled_state
                        .database
                        .insert_account_info(from, sender);

                    let mut coinbase_info = evm
                        .ctx
                        .journaled_state
                        .database
                        .basic(header.miner)
                        .unwrap()
                        .unwrap_or_default();
                    coinbase_info.balance += fee;
                    evm.ctx
                        .journaled_state
                        .database
                        .insert_account_info(header.miner, coinbase_info);
                }
                execute_duration += execute_t0.elapsed();
            }
            transactions_in_file += transactions_rlp.item_count().unwrap() as u64;

            let decode_t0 = Instant::now();
            let uncles: Vec<DecodedUncle> = (0..uncles_rlp.item_count().unwrap())
                .map(|n| decode_uncle(&uncles_rlp.at(n).unwrap()))
                .collect();
            decode_duration += decode_t0.elapsed();

            let execute_t0 = Instant::now();
            // Block + uncle rewards: revm only executes transactions, it
            // doesn't know about mining rewards.
            let mut miner_reward = U256::from(BLOCK_REWARD);
            for uncle in &uncles {
                let distance = header.number - uncle.number;
                let uncle_reward =
                    U256::from(BLOCK_REWARD) * U256::from(8 - distance) / U256::from(8u64);
                let mut uncle_miner_info = evm
                    .ctx
                    .journaled_state
                    .database
                    .basic(uncle.miner)
                    .unwrap()
                    .unwrap_or_default();
                uncle_miner_info.balance += uncle_reward;
                evm.ctx
                    .journaled_state
                    .database
                    .insert_account_info(uncle.miner, uncle_miner_info);
                miner_reward += U256::from(BLOCK_REWARD) / U256::from(32u64); // "nephew" bonus
            }
            let mut miner_info = evm
                .ctx
                .journaled_state
                .database
                .basic(header.miner)
                .unwrap()
                .unwrap_or_default();
            miner_info.balance += miner_reward;
            evm.ctx
                .journaled_state
                .database
                .insert_account_info(header.miner, miner_info);
            execute_duration += execute_t0.elapsed();

            // Makes this block's hash available to BLOCKHASH for any later
            // block within revm's own 256-block lookback window. revm's
            // `blockhash` opcode enforces that distance check itself, so
            // there's no need to cap how much history stays cached here
            // (unlike `sync_era1.rs`'s manual `recent_hashes` rotation).
            let this_hash: [u8; 32] = Keccak256::digest(&header_rlp).into();
            evm.ctx
                .journaled_state
                .database
                .cache
                .block_hashes
                .insert(U256::from(header.number), B256::from(this_hash));

            blocks_in_file += 1;
        }
        blocks_processed += blocks_in_file;
        transactions_processed += transactions_in_file;

        println!(
            "[{}/{}] {}: {blocks_in_file} blocks, {transactions_in_file} transactions processed",
            i + 1,
            files.len(),
            path.file_name().unwrap().to_string_lossy(),
        );
    }

    let accounts_touched = evm.ctx.journaled_state.database.cache.accounts.len();
    println!(
        "done: {blocks_processed} blocks, {transactions_processed} transactions, {accounts_touched} accounts touched in {:.2}ms (expected ~{} blocks)",
        start.elapsed().as_secs_f64() * 1000.0,
        files.len() as u64 * BLOCKS_PER_FILE
    );
    println!(
        "  decode (snappy+RLP+ecrecover): {:.2}ms",
        decode_duration.as_secs_f64() * 1000.0
    );
    println!(
        "  execute (transact_commit+rewards): {:.2}ms",
        execute_duration.as_secs_f64() * 1000.0
    );
}
