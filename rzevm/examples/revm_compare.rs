//! Cross-checks a single historical mainnet transaction against revm,
//! fetching whatever account/storage/code state it needs lazily over
//! JSON-RPC. Useful whenever zevm's `gas_used` for some historical
//! transaction doesn't match the real receipt: if revm (fed the same real
//! historical state) agrees with the real receipt, its EIP-3155 step trace
//! pinpoints exactly which opcode zevm prices differently. Note revm's own
//! `SpecId::FRONTIER` isn't bug-free either (it was found to charge
//! EIP-160's `exp_byte` (50) instead of Frontier's original 10), so check
//! for known revm quirks before assuming a mismatch means zevm is wrong.
//!
//! Edit `block_number`/`tx_hash` below to point at whatever transaction
//! needs checking. Not part of the normal build; a standalone diagnostic,
//! run with `cargo run --release --example revm_compare`.

use revm::{
    context::{BlockEnv, CfgEnv, Context, TxEnv},
    database::CacheDB,
    primitives::{hardfork::SpecId, Address, Bytes, TxKind, B256, U256},
    state::{AccountInfo, Bytecode},
    DatabaseRef, InspectEvm, MainBuilder, MainContext,
};
use revm::context_interface::result::ResultAndState;
use revm::inspector::inspectors::TracerEip3155;
use revm::ExecuteCommitEvm;
use std::process::Command;

const RPC_URL: &str = "https://eth.drpc.org";

fn rpc_call(method: &str, params: serde_json::Value) -> serde_json::Value {
    let body = serde_json::json!({"jsonrpc": "2.0", "method": method, "params": params, "id": 1});
    for attempt in 0..20 {
        let output = Command::new("curl")
            .args([
                "-s",
                RPC_URL,
                "-X",
                "POST",
                "-H",
                "Content-Type: application/json",
                "--data",
                &body.to_string(),
            ])
            .output()
            .expect("curl failed to run");
        let parsed: Option<serde_json::Value> = serde_json::from_slice(&output.stdout).ok();
        match parsed {
            Some(p) if p.get("error").is_none() => return p["result"].clone(),
            Some(p) => eprintln!("RPC error calling {method} (attempt {attempt}): {:?}", p.get("error")),
            None => eprintln!("invalid JSON from RPC calling {method} (attempt {attempt})"),
        }
        std::thread::sleep(std::time::Duration::from_millis(2000 + attempt * 500));
    }
    panic!("RPC call to {method} failed after retries");
}

fn hex_to_u256(s: &str) -> U256 {
    U256::from_str_radix(s.trim_start_matches("0x"), 16).unwrap_or(U256::ZERO)
}

fn hex_to_u64(s: &str) -> u64 {
    u64::from_str_radix(s.trim_start_matches("0x"), 16).unwrap_or(0)
}

/// Fetches whatever `basic`/`code_by_hash`/`storage`/`block_hash` needs,
/// one JSON-RPC call at a time, at a fixed block height.
struct RpcDb {
    block_hex: String,
}

impl DatabaseRef for RpcDb {
    type Error = std::convert::Infallible;

    fn basic_ref(&self, address: Address) -> Result<Option<AccountInfo>, Self::Error> {
        let addr_hex = format!("0x{}", hex::encode(address));
        let balance = hex_to_u256(
            rpc_call(
                "eth_getBalance",
                serde_json::json!([addr_hex, self.block_hex]),
            )
            .as_str()
            .unwrap(),
        );
        let nonce = hex_to_u64(
            rpc_call(
                "eth_getTransactionCount",
                serde_json::json!([addr_hex, self.block_hex]),
            )
            .as_str()
            .unwrap(),
        );
        let code_hex = rpc_call("eth_getCode", serde_json::json!([addr_hex, self.block_hex]))
            .as_str()
            .unwrap()
            .to_string();
        let code_bytes = hex::decode(code_hex.trim_start_matches("0x")).unwrap();
        let code = Bytecode::new_raw(Bytes::from(code_bytes));
        let code_hash = code.hash_slow();
        Ok(Some(AccountInfo {
            balance,
            nonce,
            code_hash,
            account_id: None,
            code: Some(code),
        }))
    }

    fn code_by_hash_ref(&self, _code_hash: B256) -> Result<Bytecode, Self::Error> {
        // `basic_ref` always embeds `code` directly, so revm's journal
        // should never need to fall back to this.
        unreachable!("code_by_hash_ref should not be called: basic_ref always embeds code")
    }

    fn storage_ref(&self, address: Address, index: U256) -> Result<U256, Self::Error> {
        let addr_hex = format!("0x{}", hex::encode(address));
        let slot_hex = format!("0x{index:x}");
        let value = rpc_call(
            "eth_getStorageAt",
            serde_json::json!([addr_hex, slot_hex, self.block_hex]),
        );
        Ok(hex_to_u256(value.as_str().unwrap()))
    }

    fn block_hash_ref(&self, number: u64) -> Result<B256, Self::Error> {
        let hash_hex = rpc_call(
            "eth_getBlockByNumber",
            serde_json::json!([format!("0x{number:x}"), false]),
        )["hash"]
            .as_str()
            .unwrap()
            .to_string();
        Ok(B256::from_slice(&hex::decode(hash_hex.trim_start_matches("0x")).unwrap()))
    }
}

fn build_tx_env(tx_hash: &str, fetch_receipt: bool) -> (u64, TxEnv, u64) {
    let real_gas_used = if fetch_receipt {
        hex_to_u64(
            rpc_call("eth_getTransactionReceipt", serde_json::json!([tx_hash]))["gasUsed"]
                .as_str()
                .unwrap(),
        )
    } else {
        0
    };
    let tx_json = rpc_call("eth_getTransactionByHash", serde_json::json!([tx_hash]));
    let block_number = hex_to_u64(tx_json["blockNumber"].as_str().unwrap());

    let from = Address::from_slice(
        &hex::decode(tx_json["from"].as_str().unwrap().trim_start_matches("0x")).unwrap(),
    );
    let kind = match tx_json["to"].as_str() {
        Some(to_hex) => TxKind::Call(Address::from_slice(
            &hex::decode(to_hex.trim_start_matches("0x")).unwrap(),
        )),
        None => TxKind::Create,
    };
    let value = hex_to_u256(tx_json["value"].as_str().unwrap());
    let gas_limit = hex_to_u64(tx_json["gas"].as_str().unwrap());
    let gas_price = hex_to_u256(tx_json["gasPrice"].as_str().unwrap());
    let nonce = hex_to_u64(tx_json["nonce"].as_str().unwrap());
    let input = tx_json["input"].as_str().unwrap();
    let data = Bytes::from(hex::decode(input.trim_start_matches("0x")).unwrap());

    let tx_env = TxEnv::builder()
        .caller(from)
        .kind(kind)
        .value(value)
        .gas_limit(gas_limit)
        .gas_price(gas_price.to::<u128>())
        .nonce(nonce)
        .data(data)
        .build()
        .unwrap();

    (block_number, tx_env, real_gas_used)
}

fn block_env(block_number: u64) -> BlockEnv {
    let block_hex = format!("0x{block_number:x}");
    let header = rpc_call("eth_getBlockByNumber", serde_json::json!([block_hex, false]));
    BlockEnv {
        number: U256::from(block_number),
        beneficiary: Address::from_slice(
            &hex::decode(header["miner"].as_str().unwrap().trim_start_matches("0x")).unwrap(),
        ),
        timestamp: U256::from(hex_to_u64(header["timestamp"].as_str().unwrap())),
        gas_limit: hex_to_u64(header["gasLimit"].as_str().unwrap()),
        difficulty: hex_to_u256(header["difficulty"].as_str().unwrap()),
        basefee: 0,
        ..Default::default()
    }
}

fn main() {
    // A sequence of real historical transactions to replay in order
    // against one shared, RPC-backed state, tracing only the last one.
    // Used to chase a divergence that only shows up after several
    // transactions accumulate state (e.g. a contract's own "last action"
    // storage growing wrong): state is fetched once, as of the block
    // *before* the first transaction here, then each transaction's
    // effects carry into the next via `transact_commit`.
    // Block 6,463,949, nonce 567 from 0x1bb5835f...b2eee, selector
    // 0x349cdcac on 0xdd9fd6b6...16f3c: succeeds on real chain using
    // 248446 gas, but zevm computes 255967 — 7521 over. The state this
    // leaves behind then sends the *next* transaction (same contract,
    // same selector, nonce 568) down a completely different path: 25473
    // real gas vs zevm's 213491, which is what finally surfaces as an
    // InsufficientBalance at block 6,464,014.
    // Block 6,436,825: both transactions into 0xdd9fd6b6...16f3c fail on
    // real chain consuming their FULL gas limit (an exceptional halt, not
    // a revert). zevm instead lets the second one through, crediting the
    // contract's slot 5 with 7.7e12 (a tenth of the tx's 7.7e13 value)
    // that real chain rolls back — the first corruption of that contract's
    // state, which surfaces ~27K blocks later as an InsufficientBalance.
    let tx_hashes = ["0x9751be08e65ce89c69bd029ac63fbc4d4e9175bbfc6c8a40b652ca5842cab04a"];

    let last_idx = tx_hashes.len() - 1;
    let entries: Vec<(u64, TxEnv, u64)> = tx_hashes
        .iter()
        .enumerate()
        .map(|(i, h)| build_tx_env(h, i == last_idx))
        .collect();
    let first_block = entries[0].0;

    let query_block_hex = format!("0x{:x}", first_block - 1);
    let db = CacheDB::new(RpcDb {
        block_hex: query_block_hex,
    });

    let mut ctx = Context::mainnet().with_db(db);
    // `with_spec` (deprecated) only sets the opcode-level spec flag, not
    // the separate `gas_params` table intrinsic-gas validation reads,
    // leaving CREATE transactions charged modern surcharges even under
    // "Frontier". `with_spec_and_mainnet_gas_params` sets both together.
    ctx.cfg = CfgEnv::new().with_spec_and_mainnet_gas_params(SpecId::PETERSBURG);

    let mut entries = entries;
    let (last_block, last_tx_env, last_real_gas_used) = entries.pop().unwrap();

    let shared_block_env = block_env(first_block); // every entry here is from the same block
    let mut evm = ctx.build_mainnet();
    evm.ctx.block = shared_block_env.clone();
    for (i, (_, tx_env, real_gas_used)) in entries.into_iter().enumerate() {
        let result = match evm.transact_commit(tx_env) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("tx[{i}]: FAILED to apply: {e:?} (continuing)");
                continue;
            }
        };
        eprintln!(
            "tx[{i}]: tx_gas_used={} real={real_gas_used} success={}",
            result.tx_gas_used(),
            result.is_success()
        );
    }

    evm.ctx.block = shared_block_env;
    let _ = last_block;
    let mut traced = evm.with_inspector(TracerEip3155::new_stdout());
    let ResultAndState { result, .. } = traced
        .inspect_tx(last_tx_env)
        .expect("revm execution failed");
    eprintln!("\n=== revm result (final tx) ===");
    eprintln!("gas_used (tx_gas_used): {}", result.tx_gas_used());
    eprintln!("real receipt gasUsed:   {last_real_gas_used}");
    eprintln!("success: {}", result.is_success());
}
