//! Reads `.era1` files (`data/era1/`, populated by `make download-era1`),
//! Portal Network's archival format for pre-merge mainnet history, and
//! replays them through zevm via FFI: e2store container unwrap, then
//! Snappy-framed decompression, then RLP-decodes each block's header,
//! transactions (deriving `from` via ECDSA signature recovery), and
//! uncles, feeding all of it to `zevm_evm_process_block`, the same FFI
//! surface `rzevm/src/main.rs` drives from JSON.
//!
//! era1's record layout (empirically verified against a real downloaded
//! file): a `Version` record, then per block, four records in order,
//! `CompressedHeader`, `CompressedBody`, `CompressedReceipts`,
//! `TotalDifficulty` (the latter stored raw, not Snappy-compressed),
//! repeated for all 8192 blocks, followed by a trailing `AccumulatorRoot`
//! and `BlockIndex`.
//!
//! Transaction parsing and signature recovery mirror
//! https://github.com/cyber-coop/eth-prototype/blob/main/src/message.rs's
//! `parse_transaction`, keeping only its legacy-transaction branch: every
//! transaction in this block range predates EIP-2718 typed transactions.

use std::ffi::c_void;
use std::fs;
use std::io::Read;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use secp256k1::ecdsa::{RecoverableSignature, RecoveryId};
use sha3::{Digest, Keccak256};
use snap::read::FrameDecoder;

const BLOCKS_PER_FILE: u64 = 8192;

/// A C-compatible mirror of `Block.Entry`, matching `rzevm/src/main.rs`'s
/// definition (duplicated rather than shared, self-contained by convention).
#[repr(C)]
struct CTransaction {
    from: [u8; 20],
    nonce: u64,
    gas_price: [u8; 32],
    gas_limit: u64,
    has_to: bool,
    to: [u8; 20],
    value: [u8; 32],
    data_ptr: *const u8,
    data_len: usize,
    v: u64,
    r: [u8; 32],
    s: [u8; 32],
}

#[repr(C)]
struct CUncle {
    number: u64,
    miner: [u8; 20],
}

unsafe extern "C" {
    fn zevm_state_create() -> *mut c_void;
    fn zevm_state_destroy(handle: *mut c_void);
    fn zevm_state_set_balance(
        handle: *mut c_void,
        address: *const [u8; 20],
        balance: *const [u8; 32],
    ) -> i32;
    fn zevm_state_get_balance(
        handle: *mut c_void,
        address: *const [u8; 20],
        out_balance: *mut [u8; 32],
    );
    fn zevm_state_accounts_count(handle: *mut c_void) -> usize;
    fn zevm_evm_create(state_handle: *mut c_void) -> *mut c_void;
    fn zevm_evm_destroy(handle: *mut c_void);
    fn zevm_evm_process_block(
        evm_handle: *mut c_void,
        number: u64,
        miner: *const [u8; 20],
        timestamp: u64,
        gas_limit: u64,
        difficulty: *const [u8; 32],
        transactions_ptr: *const CTransaction,
        transactions_len: usize,
        uncles_ptr: *const CUncle,
        uncles_len: usize,
        recent_hashes_ptr: *const [u8; 32],
        recent_hashes_len: usize,
    ) -> i32;
}

fn parse_address(hex: &str) -> [u8; 20] {
    hex::decode(hex.trim_start_matches("0x"))
        .unwrap()
        .try_into()
        .unwrap()
}

fn parse_hex_u256(hex: &str) -> [u8; 32] {
    let digits = hex.trim_start_matches("0x");
    let mut out = [0u8; 32];
    if digits.is_empty() {
        return out;
    }
    let padded = if digits.len() % 2 == 0 {
        digits.to_string()
    } else {
        format!("0{digits}")
    };
    let bytes = hex::decode(&padded).unwrap();
    out[32 - bytes.len()..].copy_from_slice(&bytes);
    out
}

fn to_u256(bytes: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[32 - bytes.len()..].copy_from_slice(bytes);
    out
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

/// Parses one legacy transaction from its RLP encoding, deriving `from`
/// via ECDSA signature recovery. Returns the decoded calldata alongside
/// the `CTransaction`, since `data_ptr` borrows from it; the caller must
/// keep it alive at least as long as the `CTransaction`.
fn parse_transaction(payload: &[u8]) -> (CTransaction, Vec<u8>) {
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
    let mut from = [0u8; 20];
    from.copy_from_slice(&from_hash[12..]);

    let has_to = !to.is_empty();
    let mut to_bytes = [0u8; 20];
    if has_to {
        to_bytes.copy_from_slice(&to);
    }

    let ctransaction = CTransaction {
        from,
        nonce,
        gas_price: to_u256(&gas_price),
        gas_limit,
        has_to,
        to: to_bytes,
        value: to_u256(&value),
        data_ptr: data.as_ptr(),
        data_len: data.len(),
        v,
        r: to_u256(&r),
        s: to_u256(&s),
    };
    (ctransaction, data)
}

/// The fields `Evm.processBlock` actually needs out of a block header.
/// Frontier-era headers RLP-encode as a 15-field list; everything except
/// coinbase/difficulty/number/gasLimit/timestamp is decoded and discarded.
struct DecodedHeader {
    number: u64,
    miner: [u8; 20],
    timestamp: u64,
    gas_limit: u64,
    difficulty: [u8; 32],
}

fn decode_header(header: &rlp::Rlp) -> DecodedHeader {
    let miner: Vec<u8> = header.at(2).unwrap().as_val().unwrap();
    let difficulty: Vec<u8> = header.at(7).unwrap().as_val().unwrap();
    let number: u64 = header.at(8).unwrap().as_val().unwrap();
    let gas_limit: u64 = header.at(9).unwrap().as_val().unwrap();
    let timestamp: u64 = header.at(11).unwrap().as_val().unwrap();

    let mut miner_bytes = [0u8; 20];
    miner_bytes.copy_from_slice(&miner);

    DecodedHeader {
        number,
        miner: miner_bytes,
        timestamp,
        gas_limit,
        difficulty: to_u256(&difficulty),
    }
}

/// An uncle is encoded as a full header (not the abbreviated
/// `{number, miner}` JSON-RPC gives us); only coinbase/number matter here.
fn decode_uncle(uncle: &rlp::Rlp) -> CUncle {
    let miner: Vec<u8> = uncle.at(2).unwrap().as_val().unwrap();
    let number: u64 = uncle.at(8).unwrap().as_val().unwrap();
    let mut miner_bytes = [0u8; 20];
    miner_bytes.copy_from_slice(&miner);
    CUncle {
        number,
        miner: miner_bytes,
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
    let state = unsafe { zevm_state_create() };
    assert!(!state.is_null(), "zevm_state_create failed");

    let genesis_text =
        fs::read_to_string("../examples/data/mainnet_genesis.json").expect("read genesis");
    let genesis: serde_json::Value = serde_json::from_str(&genesis_text).expect("parse genesis");
    let alloc = genesis["alloc"].as_object().expect("alloc object");
    for (addr_hex, info) in alloc {
        let address = parse_address(addr_hex);
        let balance = parse_hex_u256(info["balance"].as_str().expect("balance"));
        let status = unsafe { zevm_state_set_balance(state, &address, &balance) };
        assert_eq!(status, 0, "zevm_state_set_balance failed");
    }
    println!("loaded {} genesis accounts", alloc.len());

    let evm = unsafe { zevm_evm_create(state) };
    assert!(!evm.is_null(), "zevm_evm_create failed");

    let files = era1_files();
    println!("found {} era1 files", files.len());

    // Started here, after genesis is loaded, so this measures block
    // processing only, matching examples/sync.zig and the other rzevm
    // benchmarks' methodology.
    let start = Instant::now();

    let mut blocks_processed: u64 = 0;
    let mut transactions_processed: u64 = 0;
    let mut decode_duration = Duration::ZERO;
    let mut execute_duration = Duration::ZERO;

    // BLOCKHASH's lookup window, most recent first (index 0 is the
    // previous block's hash), capped at the 256 blocks real Ethereum keeps.
    // Persists across files: just "the last 256 blocks processed so far."
    let mut recent_hashes: Vec<[u8; 32]> = Vec::with_capacity(256);

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

            // Decoded calldata has to outlive the `CTransaction`s that
            // point into it (and the FFI call below).
            let mut calldata_bufs = Vec::new();
            let mut transactions = Vec::new();
            for n in 0..transactions_rlp.item_count().unwrap() {
                let tx_item = transactions_rlp.at(n).unwrap();
                let (ctransaction, calldata) = parse_transaction(tx_item.as_raw());
                transactions.push(ctransaction);
                calldata_bufs.push(calldata);
            }
            transactions_in_file += transactions.len() as u64;

            let uncles: Vec<CUncle> = (0..uncles_rlp.item_count().unwrap())
                .map(|n| decode_uncle(&uncles_rlp.at(n).unwrap()))
                .collect();

            decode_duration += decode_t0.elapsed();

            let execute_t0 = Instant::now();
            let status = unsafe {
                zevm_evm_process_block(
                    evm,
                    header.number,
                    &header.miner,
                    header.timestamp,
                    header.gas_limit,
                    &header.difficulty,
                    transactions.as_ptr(),
                    transactions.len(),
                    uncles.as_ptr(),
                    uncles.len(),
                    recent_hashes.as_ptr(),
                    recent_hashes.len(),
                )
            };
            execute_duration += execute_t0.elapsed();

            // This block's own hash becomes available for BLOCKHASH lookups
            // starting with the *next* block, pushed after the call so
            // `recent_hashes` here only ever covers strictly earlier blocks.
            let this_hash: [u8; 32] = Keccak256::digest(&header_rlp).into();
            recent_hashes.insert(0, this_hash);
            recent_hashes.truncate(256);

            if status != 0 {
                eprintln!("block {} failed (status {status})", header.number);
                for tx in &transactions {
                    eprintln!(
                        "  from={} nonce={} to={} has_to={} value={} gas_price={} gas_limit={} v={}",
                        hex::encode(tx.from),
                        tx.nonce,
                        hex::encode(tx.to),
                        tx.has_to,
                        hex::encode(tx.value),
                        hex::encode(tx.gas_price),
                        tx.gas_limit,
                        tx.v,
                    );
                    let mut balance = [0u8; 32];
                    unsafe { zevm_state_get_balance(state, &tx.from, &mut balance) };
                    eprintln!("    simulated from-balance = {}", hex::encode(balance));
                }
                panic!("zevm_evm_process_block failed for block {}", header.number);
            }

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

    let accounts_touched = unsafe { zevm_state_accounts_count(state) };
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
        "  execute (zevm_evm_process_block via FFI): {:.2}ms",
        execute_duration.as_secs_f64() * 1000.0
    );

    unsafe {
        zevm_evm_destroy(evm);
        zevm_state_destroy(state);
    }
}
