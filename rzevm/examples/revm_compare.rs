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
use std::process::Command;

const RPC_URL: &str = "https://eth.drpc.org";

fn rpc_call(method: &str, params: serde_json::Value) -> serde_json::Value {
    let body = serde_json::json!({"jsonrpc": "2.0", "method": method, "params": params, "id": 1});
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
    let parsed: serde_json::Value =
        serde_json::from_slice(&output.stdout).expect("invalid JSON from RPC");
    if let Some(err) = parsed.get("error") {
        panic!("RPC error calling {method}: {err}");
    }
    parsed["result"].clone()
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

fn main() {
    // Edit these two to point at whatever transaction needs checking.
    let block_number: u64 = 508226;
    let block_hex = format!("0x{block_number:x}");
    let tx_hash = "0x34f1644c0d55d4664a3b45d741da884553cde157dc3280991f2c373ad1f4f104";

    let real_gas_used = hex_to_u64(
        rpc_call(
            "eth_getTransactionReceipt",
            serde_json::json!([tx_hash]),
        )["gasUsed"]
            .as_str()
            .unwrap(),
    );

    let tx_json = rpc_call(
        "eth_getTransactionByHash",
        serde_json::json!([tx_hash]),
    );
    let header = rpc_call(
        "eth_getBlockByNumber",
        serde_json::json!([block_hex.clone(), false]),
    );

    let from = Address::from_slice(
        &hex::decode(tx_json["from"].as_str().unwrap().trim_start_matches("0x")).unwrap(),
    );
    let to = Address::from_slice(
        &hex::decode(tx_json["to"].as_str().unwrap().trim_start_matches("0x")).unwrap(),
    );
    let value = hex_to_u256(tx_json["value"].as_str().unwrap());
    let gas_limit = hex_to_u64(tx_json["gas"].as_str().unwrap());
    let gas_price = hex_to_u256(tx_json["gasPrice"].as_str().unwrap());
    let nonce = hex_to_u64(tx_json["nonce"].as_str().unwrap());
    let input = tx_json["input"].as_str().unwrap();
    let data = Bytes::from(hex::decode(input.trim_start_matches("0x")).unwrap());

    println!("from={from} to={to} value={value} gas_limit={gas_limit} gas_price={gas_price} nonce={nonce}");

    // Query state as of the block *before* this one: the state this
    // transaction actually executed against.
    let query_block_hex = format!("0x{:x}", block_number - 1);
    let db = CacheDB::new(RpcDb {
        block_hex: query_block_hex,
    });

    let mut ctx = Context::mainnet().with_db(db);
    // `with_spec` (deprecated) only sets the opcode-level spec flag, not
    // the separate `gas_params` table intrinsic-gas validation reads,
    // leaving CREATE transactions charged modern surcharges even under
    // "Frontier". `with_spec_and_mainnet_gas_params` sets both together.
    ctx.cfg = CfgEnv::new().with_spec_and_mainnet_gas_params(SpecId::FRONTIER);
    ctx.block = BlockEnv {
        number: U256::from(block_number),
        beneficiary: Address::from_slice(
            &hex::decode(header["miner"].as_str().unwrap().trim_start_matches("0x")).unwrap(),
        ),
        timestamp: U256::from(hex_to_u64(header["timestamp"].as_str().unwrap())),
        gas_limit: hex_to_u64(header["gasLimit"].as_str().unwrap()),
        difficulty: hex_to_u256(header["difficulty"].as_str().unwrap()),
        basefee: 0,
        ..Default::default()
    };

    let tx_env = TxEnv::builder()
        .caller(from)
        .kind(TxKind::Call(to))
        .value(value)
        .gas_limit(gas_limit)
        .gas_price(gas_price.to::<u128>())
        .nonce(nonce)
        .data(data)
        .build()
        .unwrap();

    let mut evm = ctx.build_mainnet_with_inspector(TracerEip3155::new_stdout());
    let ResultAndState { result, .. } = evm.inspect_tx(tx_env).expect("revm execution failed");

    eprintln!("\n=== revm result ===");
    eprintln!("gas_used (tx_gas_used): {}", result.tx_gas_used());
    eprintln!("real receipt gasUsed:   {real_gas_used}");
    eprintln!("success: {}", result.is_success());
}
