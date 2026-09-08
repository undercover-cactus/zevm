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

// Block reward in wei: 5 ETH pre-Byzantium, cut to 3 ETH by EIP-649.
const BLOCK_REWARD_PRE_BYZANTIUM: u128 = 5_000_000_000_000_000_000;
const BLOCK_REWARD_BYZANTIUM: u128 = 3_000_000_000_000_000_000;

fn block_reward(is_byzantium: bool) -> u128 {
    if is_byzantium {
        BLOCK_REWARD_BYZANTIUM
    } else {
        BLOCK_REWARD_PRE_BYZANTIUM
    }
}

fn parse_address(hex: &str) -> Address {
    Address::from_slice(&hex::decode(hex.trim_start_matches("0x")).unwrap())
}

// The DAO fork (block 1,920,000) wasn't an EVM/gas rule change, just a
// one-time irregular state transition hardcoded into every client: move
// all ether out of The DAO and its children into a recovery contract.
// revm has no built-in notion of this, so without applying it here too,
// revm's simulation would diverge from real chain state starting exactly
// at that block. Mirrors `DaoFork.zig`'s address list exactly.
const DAO_RECOVERY: &str = "0xbf4ed7b27f1d666546e30d74d50d173d20bca754";
const DAO_ACCOUNTS: &[&str] = &[
    "0xd4fe7bc31cedb7bfb8a345f31e668033056b2728",
    "0xb3fb0e5aba0e20e5c49d252dfd30e102b171a425",
    "0x2c19c7f9ae8b751e37aeb2d93a699722395ae18f",
    "0xecd135fa4f61a655311e86238c92adcd779555d2",
    "0x1975bd06d486162d5dc297798dfc41edd5d160a7",
    "0xa3acf3a1e16b1d7c315e23510fdd7847b48234f6",
    "0x319f70bab6845585f412ec7724b744fec6095c85",
    "0x06706dd3f2c9abf0a21ddcc6941d9b86f0596936",
    "0x5c8536898fbb74fc7445814902fd08422eac56d0",
    "0x6966ab0d485353095148a2155858910e0965b6f9",
    "0x779543a0491a837ca36ce8c635d6154e3c4911a6",
    "0x2a5ed960395e2a49b1c758cef4aa15213cfd874c",
    "0x5c6e67ccd5849c0d29219c4f95f1a7a93b3f5dc5",
    "0x9c50426be05db97f5d64fc54bf89eff947f0a321",
    "0x200450f06520bdd6c527622a273333384d870efb",
    "0xbe8539bfe837b67d1282b2b1d61c3f723966f049",
    "0x6b0c4d41ba9ab8d8cfb5d379c69a612f2ced8ecb",
    "0xf1385fb24aad0cd7432824085e42aff90886fef5",
    "0xd1ac8b1ef1b69ff51d1d401a476e7e612414f091",
    "0x8163e7fb499e90f8544ea62bbf80d21cd26d9efd",
    "0x51e0ddd9998364a2eb38588679f0d2c42653e4a6",
    "0x627a0a960c079c21c34f7612d5d230e01b4ad4c7",
    "0xf0b1aa0eb660754448a7937c022e30aa692fe0c5",
    "0x24c4d950dfd4dd1902bbed3508144a54542bba94",
    "0x9f27daea7aca0aa0446220b98d028715e3bc803d",
    "0xa5dc5acd6a7968a4554d89d65e59b7fd3bff0f90",
    "0xd9aef3a1e38a39c16b31d1ace71bca8ef58d315b",
    "0x63ed5a272de2f6d968408b4acb9024f4cc208ebf",
    "0x6f6704e5a10332af6672e50b3d9754dc460dfa4d",
    "0x77ca7b50b6cd7e2f3fa008e24ab793fd56cb15f6",
    "0x492ea3bb0f3315521c31f273e565b868fc090f17",
    "0x0ff30d6de14a8224aa97b78aea5388d1c51c1f00",
    "0x9ea779f907f0b315b364b0cfc39a0fde5b02a416",
    "0xceaeb481747ca6c540a000c1f3641f8cef161fa7",
    "0xcc34673c6c40e791051898567a1222daf90be287",
    "0x579a80d909f346fbfb1189493f521d7f48d52238",
    "0xe308bd1ac5fda103967359b2712dd89deffb7973",
    "0x4cb31628079fb14e4bc3cd5e30c2f7489b00960c",
    "0xac1ecab32727358dba8962a0f3b261731aad9723",
    "0x4fd6ace747f06ece9c49699c7cabc62d02211f75",
    "0x440c59b325d2997a134c2c7c60a8c61611212bad",
    "0x4486a3d68fac6967006d7a517b889fd3f98c102b",
    "0x9c15b54878ba618f494b38f0ae7443db6af648ba",
    "0x27b137a85656544b1ccb5a0f2e561a5703c6a68f",
    "0x21c7fdb9ed8d291d79ffd82eb2c4356ec0d81241",
    "0x23b75c2f6791eef49c69684db4c6c1f93bf49a50",
    "0x1ca6abd14d30affe533b24d7a21bff4c2d5e1f3b",
    "0xb9637156d330c0d605a791f1c31ba5890582fe1c",
    "0x6131c42fa982e56929107413a9d526fd99405560",
    "0x1591fc0f688c81fbeb17f5426a162a7024d430c2",
    "0x542a9515200d14b68e934e9830d91645a980dd7a",
    "0xc4bbd073882dd2add2424cf47d35213405b01324",
    "0x782495b7b3355efb2833d56ecb34dc22ad7dfcc4",
    "0x58b95c9a9d5d26825e70a82b6adb139d3fd829eb",
    "0x3ba4d81db016dc2890c81f3acec2454bff5aada5",
    "0xb52042c8ca3f8aa246fa79c3feaa3d959347c0ab",
    "0xe4ae1efdfc53b73893af49113d8694a057b9c0d1",
    "0x3c02a7bc0391e86d91b7d144e61c2c01a25a79c5",
    "0x0737a6b837f97f46ebade41b9bc3e1c509c85c53",
    "0x97f43a37f595ab5dd318fb46e7a155eae057317a",
    "0x52c5317c848ba20c7504cb2c8052abd1fde29d03",
    "0x4863226780fe7c0356454236d3b1c8792785748d",
    "0x5d2b2e6fcbe3b11d26b525e085ff818dae332479",
    "0x5f9f3392e9f62f63b8eac0beb55541fc8627f42c",
    "0x057b56736d32b86616a10f619859c6cd6f59092a",
    "0x9aa008f65de0b923a2a4f02012ad034a5e2e2192",
    "0x304a554a310c7e546dfe434669c62820b7d83490",
    "0x914d1b8b43e92723e64fd0a06f5bdb8dd9b10c79",
    "0x4deb0033bb26bc534b197e61d19e0733e5679784",
    "0x07f5c1e1bc2c93e0402f23341973a0e043f7bf8a",
    "0x35a051a0010aba705c9008d7a7eff6fb88f6ea7b",
    "0x4fa802324e929786dbda3b8820dc7834e9134a2a",
    "0x9da397b9e80755301a3b32173283a91c0ef6c87e",
    "0x8d9edb3054ce5c5774a420ac37ebae0ac02343c6",
    "0x0101f3be8ebb4bbd39a2e3b9a3639d4259832fd9",
    "0x5dc28b15dffed94048d73806ce4b7a4612a1d48f",
    "0xbcf899e6c7d9d5a215ab1e3444c86806fa854c76",
    "0x12e626b0eebfe86a56d633b9864e389b45dcb260",
    "0xa2f1ccba9395d7fcb155bba8bc92db9bafaeade7",
    "0xec8e57756626fdc07c63ad2eafbd28d08e7b0ca5",
    "0xd164b088bd9108b60d0ca3751da4bceb207b0782",
    "0x6231b6d0d5e77fe001c2a460bd9584fee60d409b",
    "0x1cba23d343a983e9b5cfd19496b9a9701ada385f",
    "0xa82f360a8d3455c5c41366975bde739c37bfeb8a",
    "0x9fcd2deaff372a39cc679d5c5e4de7bafb0b1339",
    "0x005f5cee7a43331d5a3d3eec71305925a62f34b6",
    "0x0e0da70933f4c7849fc0d203f5d1d43b9ae4532d",
    "0xd131637d5275fd1a68a3200f4ad25c71a2a9522e",
    "0xbc07118b9ac290e4622f5e77a0853539789effbe",
    "0x47e7aa56d6bdf3f36be34619660de61275420af8",
    "0xacd87e28b0c9d1254e868b81cba4cc20d9a32225",
    "0xadf80daec7ba8dcf15392f1ac611fff65d94f880",
    "0x5524c55fb03cf21f549444ccbecb664d0acad706",
    "0x40b803a9abce16f50f36a77ba41180eb90023925",
    "0xfe24cdd8648121a43a7c86d289be4dd2951ed49f",
    "0x17802f43a0137c506ba92291391a8a8f207f487d",
    "0x253488078a4edf4d6f42f113d1e62836a942cf1a",
    "0x86af3e9626fce1957c82e88cbf04ddf3a2ed7915",
    "0xb136707642a4ea12fb4bae820f03d2562ebff487",
    "0xdbe9b615a3ae8709af8b93336ce9b477e4ac0940",
    "0xf14c14075d6c4ed84b86798af0956deef67365b5",
    "0xca544e5c4687d109611d0f8f928b53a25af72448",
    "0xaeeb8ff27288bdabc0fa5ebb731b6f409507516c",
    "0xcbb9d3703e651b0d496cdefb8b92c25aeb2171f7",
    "0x6d87578288b6cb5549d5076a207456a1f6a63dc0",
    "0xb2c6f0dfbb716ac562e2d85d6cb2f8d5ee87603e",
    "0xaccc230e8a6e5be9160b8cdf2864dd2a001c28b6",
    "0x2b3455ec7fedf16e646268bf88846bd7a2319bb2",
    "0x4613f3bca5c44ea06337a9e439fbc6d42e501d0a",
    "0xd343b217de44030afaa275f54d31a9317c7f441e",
    "0x84ef4b2357079cd7a7c69fd7a37cd0609a679106",
    "0xda2fef9e4a3230988ff17df2165440f37e8b1708",
    "0xf4c64518ea10f995918a454158c6b61407ea345c",
    "0x7602b46df5390e432ef1c307d4f2c9ff6d65cc97",
    "0xbb9bc244d798123fde783fcc1c72d3bb8c189413",
    "0x807640a13483f8ac783c557fcdf27be11ea4ac7a",
];

fn apply_dao_fork(db: &mut CacheDB<EmptyDB>) {
    let recovery = parse_address(DAO_RECOVERY);
    let mut total = U256::ZERO;
    for addr_hex in DAO_ACCOUNTS {
        let addr = parse_address(addr_hex);
        let mut info = db.basic(addr).unwrap().unwrap_or_default();
        if info.balance.is_zero() {
            continue;
        }
        total += info.balance;
        info.balance = U256::ZERO;
        db.insert_account_info(addr, info);
    }
    let mut recovery_info = db.basic(recovery).unwrap().unwrap_or_default();
    recovery_info.balance += total;
    db.insert_account_info(recovery, recovery_info);
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

    // Homestead activates at block 1,150,000 (matches `Fork.zig`'s
    // boundary). Switched once, not per-block, to avoid rebuilding
    // `CfgEnv` on every iteration.
    let mut is_homestead = false;
    let mut is_tangerine = false;
    let mut is_spurious_dragon = false;
    let mut is_byzantium = false;

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
            if !is_homestead && header.number >= 1_150_000 {
                // `build_mainnet()` bakes the opcode dispatch/gas-cost
                // tables (`EthInstructions`/`EthPrecompiles`) into `Evm` at
                // construction time from whatever spec is active then;
                // later mutating `evm.ctx.cfg` alone updates only the
                // *dynamic* spec checks (e.g. EIP-150's 63/64 forwarding
                // rule), not those baked-in per-opcode costs (e.g. SLOAD).
                // Rebuilding the whole `Evm` on every fork transition is
                // required to pick up repriced opcodes.
                let mut ctx = evm.ctx;
                ctx.cfg = CfgEnv::new().with_spec_and_mainnet_gas_params(SpecId::HOMESTEAD);
                evm = ctx.build_mainnet();
                is_homestead = true;
            }
            if header.number == 1_920_000 {
                apply_dao_fork(&mut evm.ctx.journaled_state.database);
            }
            if !is_tangerine && header.number >= 2_463_000 {
                let mut ctx = evm.ctx;
                ctx.cfg = CfgEnv::new().with_spec_and_mainnet_gas_params(SpecId::TANGERINE);
                evm = ctx.build_mainnet();
                is_tangerine = true;
            }
            if !is_spurious_dragon && header.number >= 2_675_000 {
                let mut ctx = evm.ctx;
                ctx.cfg = CfgEnv::new().with_spec_and_mainnet_gas_params(SpecId::SPURIOUS_DRAGON);
                evm = ctx.build_mainnet();
                is_spurious_dragon = true;
            }
            if !is_byzantium && header.number >= 4_370_000 {
                let mut ctx = evm.ctx;
                ctx.cfg = CfgEnv::new().with_spec_and_mainnet_gas_params(SpecId::BYZANTIUM);
                evm = ctx.build_mainnet();
                is_byzantium = true;
            }
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
            let reward = U256::from(block_reward(is_byzantium));
            let mut miner_reward = reward;
            for uncle in &uncles {
                let distance = header.number - uncle.number;
                let uncle_reward = reward * U256::from(8 - distance) / U256::from(8u64);
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
                miner_reward += reward / U256::from(32u64); // "nephew" bonus
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
