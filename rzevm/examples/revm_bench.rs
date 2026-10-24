//! Head-to-head with zevm: revm executing the same era1 blocks, from the same
//! starting state, on the same machine.
//!
//! The starting state is a zevm snapshot file (the very file zevm's
//! `sync_era1 --resume-from` reads), served to revm by `SnapshotDb`: read-only,
//! mmap'd, accounts found through an address -> offset index and slots by
//! binary search, exactly as zevm's own `State.Base` reads it. revm's
//! `CacheDB` layers every write on top. Every block's gas is checked against
//! its header, so a timing only counts if revm executed the block correctly.
//!
//!     cargo run --release --example revm_bench -- <snapshot> [files]
//!
//! Prints the same `execute`/`decode` split zevm does. Compare `execute`.

use revm::{
    context::{CfgEnv, Context, TxEnv},
    context_interface::transaction::{AccessList, AccessListItem},
    database::CacheDB,
    primitives::{hardfork::SpecId, Address, Bytes, TxKind, B256, KECCAK_EMPTY, U256},
    state::{AccountInfo, Bytecode},
    DatabaseRef, ExecuteCommitEvm, MainBuilder, MainContext,
};
use rustc_hash::FxHashMap;
use secp256k1::ecdsa::{RecoverableSignature, RecoveryId};
use sha3::{Digest, Keccak256};
use snap::read::FrameDecoder;
use std::convert::Infallible;
use std::fs;
use std::io::Read;
use std::os::fd::AsRawFd;
use std::path::PathBuf;
use std::time::{Duration, Instant};

const BLOCKS_PER_FILE: u64 = 8192;
const BLOCK_REWARD: u128 = 2_000_000_000_000_000_000; // EIP-1234, through the Merge

// The three libc calls needed to map a snapshot, declared directly rather
// than pulling in a crate for them.
unsafe extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut u8;
    fn madvise(addr: *mut u8, len: usize, advice: i32) -> i32;
}
const PROT_READ: i32 = 1;
const MAP_PRIVATE: i32 = 2;
const MADV_NORMAL: i32 = 0;
const MADV_SEQUENTIAL: i32 = 2;

/// A zevm snapshot as a revm database. Layout (see `State.writeSnapshot`):
/// block u64, count u64, then per account address (20, big-endian), balance
/// (32, little-endian), nonce (8), code length (4) and code, slot count (8)
/// and that many (slot, value) pairs of 32 little-endian bytes each, sorted by
/// slot; then the recent block hashes, most recent first.
struct SnapshotDb {
    bytes: &'static [u8],
    index: FxHashMap<Address, usize>,
    block: u64,
    hashes: Vec<B256>,
}

fn u256_le(b: &[u8]) -> U256 {
    U256::from_le_slice(b)
}

impl SnapshotDb {
    fn open(path: &str) -> Self {
        let file = fs::File::open(path).expect("open snapshot");
        let len = file.metadata().unwrap().len() as usize;
        let ptr = unsafe { mmap(std::ptr::null_mut(), len, PROT_READ, MAP_PRIVATE, file.as_raw_fd(), 0) };
        assert!(ptr as isize != -1, "mmap failed");
        // Same advice as zevm: sequential while indexing, default afterwards.
        unsafe { madvise(ptr, len, MADV_SEQUENTIAL) };
        let bytes: &'static [u8] = unsafe { std::slice::from_raw_parts(ptr, len) };

        let block = u64::from_le_bytes(bytes[0..8].try_into().unwrap());
        let count = u64::from_le_bytes(bytes[8..16].try_into().unwrap()) as usize;
        let mut index = FxHashMap::with_capacity_and_hasher(count, Default::default());
        let mut pos = 16;
        for _ in 0..count {
            index.insert(Address::from_slice(&bytes[pos..pos + 20]), pos);
            let code_len = u32::from_le_bytes(bytes[pos + 60..pos + 64].try_into().unwrap()) as usize;
            let slots = u64::from_le_bytes(bytes[pos + 64 + code_len..pos + 72 + code_len].try_into().unwrap()) as usize;
            pos += 72 + code_len + slots * 64;
        }
        let n = u64::from_le_bytes(bytes[pos..pos + 8].try_into().unwrap()) as usize;
        pos += 8;
        let hashes = (0..n)
            .map(|k| B256::from(u256_le(&bytes[pos + k * 32..pos + k * 32 + 32]).to_be_bytes::<32>()))
            .collect();
        unsafe { madvise(ptr, len, MADV_NORMAL) };
        SnapshotDb { bytes, index, block, hashes }
    }

    /// (balance, nonce, code, slot region) of the record at `pos`.
    fn record(&self, pos: usize) -> (U256, u64, &[u8], &[u8]) {
        let b = self.bytes;
        let balance = u256_le(&b[pos + 20..pos + 52]);
        let nonce = u64::from_le_bytes(b[pos + 52..pos + 60].try_into().unwrap());
        let code_len = u32::from_le_bytes(b[pos + 60..pos + 64].try_into().unwrap()) as usize;
        let code = &b[pos + 64..pos + 64 + code_len];
        let n = u64::from_le_bytes(b[pos + 64 + code_len..pos + 72 + code_len].try_into().unwrap()) as usize;
        let slots = &b[pos + 72 + code_len..pos + 72 + code_len + n * 64];
        (balance, nonce, code, slots)
    }
}

impl DatabaseRef for SnapshotDb {
    type Error = Infallible;

    fn basic_ref(&self, address: Address) -> Result<Option<AccountInfo>, Infallible> {
        let Some(&pos) = self.index.get(&address) else { return Ok(None) };
        let (balance, nonce, code, _) = self.record(pos);
        if code.is_empty() {
            return Ok(Some(AccountInfo::new(balance, nonce, KECCAK_EMPTY, Bytecode::default())));
        }
        let hash = B256::from_slice(&Keccak256::digest(code));
        Ok(Some(AccountInfo::new(balance, nonce, hash, Bytecode::new_raw(Bytes::copy_from_slice(code)))))
    }

    fn code_by_hash_ref(&self, _hash: B256) -> Result<Bytecode, Infallible> {
        // `basic_ref` always hands the code over with the account.
        unreachable!("code_by_hash_ref: code is always supplied by basic_ref")
    }

    fn storage_ref(&self, address: Address, index: U256) -> Result<U256, Infallible> {
        let Some(&pos) = self.index.get(&address) else { return Ok(U256::ZERO) };
        let (_, _, _, slots) = self.record(pos);
        let (mut low, mut high) = (0usize, slots.len() / 64);
        while low < high {
            let mid = low + (high - low) / 2;
            let key = u256_le(&slots[mid * 64..mid * 64 + 32]);
            if key == index {
                return Ok(u256_le(&slots[mid * 64 + 32..mid * 64 + 64]));
            }
            if key < index { low = mid + 1 } else { high = mid }
        }
        Ok(U256::ZERO)
    }

    fn block_hash_ref(&self, number: u64) -> Result<B256, Infallible> {
        if number <= self.block && ((self.block - number) as usize) < self.hashes.len() {
            return Ok(self.hashes[(self.block - number) as usize]);
        }
        Ok(B256::ZERO)
    }
}

/// Arrow and Gray Glacier only moved the difficulty bomb, so revm has no
/// separate spec for them: London rules run all the way to the Merge.
fn spec_at(number: u64) -> SpecId {
    if number >= 12_965_000 { SpecId::LONDON }
    else if number >= 12_244_000 { SpecId::BERLIN }
    else { panic!("revm_bench covers Berlin onward") }
}

fn be_u128(b: &[u8]) -> u128 {
    let mut buf = [0u8; 16];
    buf[16 - b.len()..].copy_from_slice(b);
    u128::from_be_bytes(buf)
}

fn recover(hash: &[u8; 32], r: &[u8], s: &[u8], recid: u8) -> Address {
    let mut compact = [0u8; 64];
    compact[32 - r.len()..32].copy_from_slice(r);
    compact[64 - s.len()..].copy_from_slice(s);
    let sig = RecoverableSignature::from_compact(&compact, RecoveryId::from_i32(recid as i32).unwrap()).unwrap();
    let msg = secp256k1::Message::from_digest_slice(hash).unwrap();
    let pubkey = sig.recover(&msg).unwrap().serialize_uncompressed();
    Address::from_slice(&Keccak256::digest(&pubkey[1..])[12..])
}

fn kind_of(to: &[u8]) -> TxKind {
    if to.is_empty() { TxKind::Create } else { TxKind::Call(Address::from_slice(to)) }
}

/// Legacy, EIP-2930 and EIP-1559 transactions, as `TxEnv` with the sender
/// recovered.
fn parse_transaction(item: &rlp::Rlp) -> TxEnv {
    if item.is_list() {
        let f = |n: usize| item.at(n).unwrap();
        let v: u64 = f(6).as_val().unwrap();
        let mut s = rlp::RlpStream::new();
        let chain_id = if v >= 35 { Some((v - 35) / 2) } else { None };
        s.begin_list(if chain_id.is_some() { 9 } else { 6 });
        for n in 0..6 { s.append_raw(f(n).as_raw(), 1); }
        if let Some(id) = chain_id { s.append(&id); s.append(&0u8); s.append(&0u8); }
        let hash: [u8; 32] = Keccak256::digest(s.out()).into();
        let recid = if v >= 35 { ((v - 35) % 2) as u8 } else { (v - 27) as u8 };
        let from = recover(&hash, f(7).data().unwrap(), f(8).data().unwrap(), recid);
        return TxEnv::builder()
            .tx_type(Some(0))
            .caller(from)
            .nonce(f(0).as_val().unwrap())
            .gas_price(be_u128(f(1).data().unwrap()))
            .gas_limit(f(2).as_val().unwrap())
            .kind(kind_of(f(3).data().unwrap()))
            .value(U256::from_be_slice(f(4).data().unwrap()))
            .data(Bytes::copy_from_slice(f(5).data().unwrap()))
            .chain_id(chain_id)
            .build()
            .unwrap();
    }
    // A typed transaction: `type || rlp(fields)`. EIP-1559 splits EIP-2930's
    // gas_price into tip and fee caps, so everything after it is one later.
    let raw = item.data().unwrap();
    let tx_type = raw[0];
    let fields = rlp::Rlp::new(&raw[1..]);
    let f = |n: usize| fields.at(n).unwrap();
    let signed = match tx_type { 1 => 8, 2 => 9, t => panic!("unsupported tx type {t}") };
    let mut s = rlp::RlpStream::new();
    s.begin_list(signed);
    for n in 0..signed { s.append_raw(f(n).as_raw(), 1); }
    let mut preimage = vec![tx_type];
    preimage.extend_from_slice(&s.out());
    let hash: [u8; 32] = Keccak256::digest(&preimage).into();
    let recid: u8 = f(signed).as_val().unwrap();
    let from = recover(&hash, f(signed + 1).data().unwrap(), f(signed + 2).data().unwrap(), recid);
    let shift = if tx_type == 2 { 1 } else { 0 };
    let access_list = AccessList(
        f(7 + shift)
            .iter()
            .map(|e| AccessListItem {
                address: Address::from_slice(e.at(0).unwrap().data().unwrap()),
                storage_keys: e.at(1).unwrap().iter().map(|k| B256::from_slice(k.data().unwrap())).collect(),
            })
            .collect(),
    );
    TxEnv::builder()
        .tx_type(Some(tx_type))
        .caller(from)
        .chain_id(Some(f(0).as_val().unwrap()))
        .nonce(f(1).as_val().unwrap())
        .gas_priority_fee(if tx_type == 2 { Some(be_u128(f(2).data().unwrap())) } else { None })
        .gas_price(be_u128(f(2 + shift).data().unwrap()))
        .gas_limit(f(3 + shift).as_val().unwrap())
        .kind(kind_of(f(4 + shift).data().unwrap()))
        .value(U256::from_be_slice(f(5 + shift).data().unwrap()))
        .data(Bytes::copy_from_slice(f(6 + shift).data().unwrap()))
        .access_list(access_list)
        .build()
        .unwrap()
}

fn snappy(compressed: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    FrameDecoder::new(compressed).read_to_end(&mut out).expect("snappy");
    out
}

fn era1_files() -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = fs::read_dir("../data/era1")
        .expect("read data/era1")
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "era1"))
        .collect();
    files.sort();
    files
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = args.get(1).expect("usage: revm_bench <snapshot> [files]");
    let file_count: usize = args.get(2).map(|s| s.parse().unwrap()).unwrap_or(2);

    let t0 = Instant::now();
    let db = SnapshotDb::open(path);
    println!("loaded snapshot at block {} ({} accounts) in {:.2}ms", db.block, db.index.len(), t0.elapsed().as_secs_f64() * 1000.0);
    let first_block = db.block + 1;
    assert_eq!(first_block % BLOCKS_PER_FILE, 0, "snapshot must end on a file boundary");

    let mut spec = spec_at(first_block);
    let mut ctx = Context::mainnet().with_db(CacheDB::new(db));
    ctx.cfg = CfgEnv::new().with_spec_and_mainnet_gas_params(spec);
    let mut evm = ctx.build_mainnet();

    let files = era1_files();
    let first_file = (first_block / BLOCKS_PER_FILE) as usize;
    let mut decode = Duration::ZERO;
    let mut execute = Duration::ZERO;
    let mut total_gas: u64 = 0;

    for path in &files[first_file..first_file + file_count] {
        let raw = fs::read(path).expect("read era1");
        let mut pos = 0;
        let mut records = Vec::new();
        while pos + 8 <= raw.len() {
            let kind = [raw[pos], raw[pos + 1]];
            let len = u32::from_le_bytes(raw[pos + 2..pos + 6].try_into().unwrap()) as usize;
            records.push((kind, &raw[pos + 8..pos + 8 + len]));
            pos += 8 + len;
        }
        let (mut blocks, mut txs) = (0u64, 0u64);
        let mut r = 1; // skip the version record
        while r + 3 < records.len() && records[r].0 == [0x03, 0x00] {
            let d0 = Instant::now();
            let header_rlp = snappy(records[r].1);
            let body_rlp = snappy(records[r + 1].1);
            r += 4;
            let header = rlp::Rlp::new(&header_rlp);
            let h = |n: usize| header.at(n).unwrap();
            let number: u64 = h(8).as_val().unwrap();
            let miner = Address::from_slice(h(2).data().unwrap());
            let gas_used: u64 = h(10).as_val().unwrap();
            let base_fee: u64 = if header.item_count().unwrap() > 15 { h(15).as_val().unwrap() } else { 0 };
            let body = rlp::Rlp::new(&body_rlp);
            let tx_envs: Vec<TxEnv> = body.at(0).unwrap().iter().map(|t| parse_transaction(&t)).collect();
            let uncles: Vec<(u64, Address)> = body.at(1).unwrap().iter()
                .map(|u| (u.at(8).unwrap().as_val().unwrap(), Address::from_slice(u.at(2).unwrap().data().unwrap())))
                .collect();
            decode += d0.elapsed();

            let e0 = Instant::now();
            // revm bakes gas tables in at build time, so each fork change
            // needs a rebuilt Evm, not just a new cfg.
            if spec_at(number) != spec {
                spec = spec_at(number);
                let mut ctx = evm.ctx;
                ctx.cfg = CfgEnv::new().with_spec_and_mainnet_gas_params(spec);
                evm = ctx.build_mainnet();
            }
            evm.ctx.block.number = U256::from(number);
            evm.ctx.block.beneficiary = miner;
            evm.ctx.block.timestamp = U256::from(h(11).as_val::<u64>().unwrap());
            evm.ctx.block.gas_limit = h(9).as_val().unwrap();
            evm.ctx.block.difficulty = U256::from_be_slice(h(7).data().unwrap());
            evm.ctx.block.basefee = base_fee;
            let mut block_gas = 0u64;
            for tx in tx_envs {
                let result = evm.transact_commit(tx).unwrap_or_else(|e| panic!("block {number}: {e:?}"));
                block_gas += result.tx_gas_used();
            }
            // Block and uncle rewards: revm only executes transactions.
            let reward = U256::from(BLOCK_REWARD);
            let db = &mut evm.ctx.journaled_state.database;
            let mut miner_reward = reward;
            for (uncle_number, uncle_miner) in &uncles {
                let mut info = db.basic_ref(*uncle_miner).unwrap().unwrap_or_default();
                info.balance += reward * U256::from(8 - (number - uncle_number)) / U256::from(8u64);
                db.insert_account_info(*uncle_miner, info);
                miner_reward += reward / U256::from(32u64);
            }
            let mut info = db.basic_ref(miner).unwrap().unwrap_or_default();
            info.balance += miner_reward;
            db.insert_account_info(miner, info);
            let this_hash: [u8; 32] = Keccak256::digest(&header_rlp).into();
            db.cache.block_hashes.insert(U256::from(number), B256::from(this_hash));
            execute += e0.elapsed();

            assert_eq!(block_gas, gas_used, "BLOCK GAS MISMATCH at block {number}");
            total_gas += block_gas;
            txs += body.at(0).unwrap().item_count().unwrap() as u64;
            blocks += 1;
        }
        println!("{}: {blocks} blocks, {txs} transactions, gas matched every block", path.file_name().unwrap().to_string_lossy());
    }
    println!("  decode (snappy+RLP+ecrecover): {:.2}ms", decode.as_secs_f64() * 1000.0);
    println!("  execute (transact_commit+rewards): {:.2}ms", execute.as_secs_f64() * 1000.0);
    println!("  gas executed: {total_gas} ({:.1} Mgas/s of execute time)", total_gas as f64 / execute.as_secs_f64() / 1e6);
}
