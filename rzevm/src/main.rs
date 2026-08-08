//! Replays real mainnet genesis + blocks 0..46299 through zevm itself, via
//! FFI into the compiled `libzevm.a`: the same workload
//! `examples/sync.zig`/`rzevm/examples/sync.rs` run, but driven from a Rust
//! host process. The proof of concept for embedding zevm in a Rust node.
//!
//! Each transaction/uncle is parsed here into a C-compatible struct and
//! passed by value across the boundary, rather than as raw JSON text: an
//! earlier version parsed each block's raw JSON inside zevm, but
//! `std.json.Value`'s dynamic tree parsing done 46,300 times cost far more
//! than parsing the whole file once.

use std::ffi::c_void;
use std::fs;
use std::time::Instant;

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

fn parse_u256(hex: &str) -> [u8; 32] {
    let digits = hex.trim_start_matches("0x");
    let mut out = [0u8; 32];
    if digits.is_empty() {
        return out;
    }
    // hex::decode needs an even number of digits.
    let padded = if digits.len() % 2 == 0 {
        digits.to_string()
    } else {
        format!("0{digits}")
    };
    let bytes = hex::decode(&padded).unwrap();
    out[32 - bytes.len()..].copy_from_slice(&bytes); // right-align, big-endian
    out
}

fn parse_u64(hex: &str) -> u64 {
    u64::from_str_radix(hex.trim_start_matches("0x"), 16).unwrap()
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
        let balance = parse_u256(info["balance"].as_str().expect("balance"));
        let status = unsafe { zevm_state_set_balance(state, &address, &balance) };
        assert_eq!(status, 0, "zevm_state_set_balance failed");
    }
    println!("loaded {} genesis accounts", alloc.len());

    let evm = unsafe { zevm_evm_create(state) };
    assert!(!evm.is_null(), "zevm_evm_create failed");

    let blocks_text = fs::read_to_string("../examples/data/mainnet_blocks_0_46299.json")
        .expect("read blocks");
    let blocks: serde_json::Value = serde_json::from_str(&blocks_text).expect("parse blocks");

    // Started here, after loading/parsing, so this measures EVM processing
    // time only, matching examples/sync.zig and rzevm/examples/sync.rs.
    let start = Instant::now();

    for block in blocks.as_array().expect("blocks array") {
        let number = parse_u64(block["number"].as_str().expect("number"));
        let miner = parse_address(block["miner"].as_str().expect("miner"));
        let timestamp = parse_u64(block["timestamp"].as_str().expect("timestamp"));
        let gas_limit = parse_u64(block["gasLimit"].as_str().expect("gasLimit"));
        let difficulty = parse_u256(block["difficulty"].as_str().expect("difficulty"));

        let txs = block["transactions"].as_array().expect("transactions array");

        // Decoded calldata has to outlive the `CTransaction`s that point
        // into it (and the FFI call below), so it's collected into its own
        // Vec rather than inline in the `map` that builds `transactions`.
        let calldata: Vec<Vec<u8>> = txs
            .iter()
            .map(|tx| {
                let input_hex = tx["input"].as_str().expect("input");
                hex::decode(input_hex.trim_start_matches("0x")).unwrap()
            })
            .collect();

        let transactions: Vec<CTransaction> = txs
            .iter()
            .zip(calldata.iter())
            .map(|(tx, data)| {
                let to = tx["to"].as_str();
                CTransaction {
                    from: parse_address(tx["from"].as_str().expect("from")),
                    nonce: parse_u64(tx["nonce"].as_str().expect("nonce")),
                    gas_price: parse_u256(tx["gasPrice"].as_str().expect("gasPrice")),
                    gas_limit: parse_u64(tx["gas"].as_str().expect("gas")),
                    has_to: to.is_some(),
                    to: to.map(parse_address).unwrap_or([0u8; 20]),
                    value: parse_u256(tx["value"].as_str().expect("value")),
                    data_ptr: data.as_ptr(),
                    data_len: data.len(),
                    v: parse_u64(tx["v"].as_str().expect("v")),
                    r: parse_u256(tx["r"].as_str().expect("r")),
                    s: parse_u256(tx["s"].as_str().expect("s")),
                }
            })
            .collect();

        // Uncles fetched but not yet enriched are still a raw hash string
        // rather than a {hash, number, miner} object; skip those, matching
        // sync.zig/sync.rs.
        let uncles: Vec<CUncle> = block["uncles"]
            .as_array()
            .expect("uncles array")
            .iter()
            .filter_map(|u| u.as_object())
            .map(|uncle| CUncle {
                number: parse_u64(uncle["number"].as_str().expect("uncle number")),
                miner: parse_address(uncle["miner"].as_str().expect("uncle miner")),
            })
            .collect();

        // This benchmark's JSON snapshot doesn't carry block hashes, so
        // BLOCKHASH reads as unavailable (0) throughout. `sync_era1.rs`
        // has real hashes (from era1 header RLP) and passes them through.
        let status = unsafe {
            zevm_evm_process_block(
                evm,
                number,
                &miner,
                timestamp,
                gas_limit,
                &difficulty,
                transactions.as_ptr(),
                transactions.len(),
                uncles.as_ptr(),
                uncles.len(),
                std::ptr::null(),
                0,
            )
        };
        assert_eq!(status, 0, "zevm_evm_process_block failed for block {number}");

        if !txs.is_empty() || number % 5000 == 0 {
            println!("processed block {number} ({} txs)", txs.len());
        }
    }

    let accounts_touched = unsafe { zevm_state_accounts_count(state) };
    println!(
        "done: {accounts_touched} accounts touched in {:.2}ms",
        start.elapsed().as_secs_f64() * 1000.0
    );

    unsafe {
        zevm_evm_destroy(evm);
        zevm_state_destroy(state);
    }
}
