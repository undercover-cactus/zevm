//! Replays real mainnet genesis + blocks 0..46299 through revm, the same
//! workload `examples/sync.zig` runs through zevm, for comparing the two.
//! No FFI here: revm running natively in Rust, a separate process from the
//! Zig side, timed externally.

use revm::{
    context::{CfgEnv, Context, TxEnv},
    database::{CacheDB, EmptyDB},
    primitives::{hardfork::SpecId, Address, Bytes, TxKind, U256},
    state::AccountInfo,
    Database, ExecuteCommitEvm, MainBuilder, MainContext,
};
use std::fs;
use std::time::Instant;

fn parse_address(hex: &str) -> Address {
    let bytes = hex::decode(hex.trim_start_matches("0x")).unwrap();
    Address::from_slice(&bytes)
}

fn parse_u256(hex: &str) -> U256 {
    let digits = hex.trim_start_matches("0x");
    if digits.is_empty() {
        U256::ZERO
    } else {
        U256::from_str_radix(digits, 16).unwrap()
    }
}

fn parse_u64(hex: &str) -> u64 {
    u64::from_str_radix(hex.trim_start_matches("0x"), 16).unwrap()
}

// 5 ETH, in wei: the flat pre-Byzantium block reward, same simplification
// examples/sync.zig makes (see Evm.zig's block_reward / Fork guard).
const BLOCK_REWARD: u128 = 5_000_000_000_000_000_000;

fn main() {
    let mut db = CacheDB::<EmptyDB>::default();

    let genesis_text =
        fs::read_to_string("../examples/data/mainnet_genesis.json").expect("read genesis");
    let genesis: serde_json::Value = serde_json::from_str(&genesis_text).expect("parse genesis");
    let alloc = genesis["alloc"].as_object().expect("alloc object");
    for (addr_hex, info) in alloc {
        let address = parse_address(addr_hex);
        let balance = parse_u256(info["balance"].as_str().expect("balance"));
        db.insert_account_info(address, AccountInfo::from_balance(balance));
    }
    println!("loaded {} genesis accounts", alloc.len());

    let mut ctx = Context::mainnet().with_db(db);
    // Without this, revm defaults to its latest mainnet spec (Berlin+), not
    // genuine Frontier. `with_spec` alone (deprecated) only sets the
    // opcode-level spec flag, not the separate `gas_params` table intrinsic-
    // gas validation reads; `with_spec_and_mainnet_gas_params` sets both
    // (see `revm_sync_era1.rs`'s identical fix for the CREATE-tx bug that caused).
    ctx.cfg = CfgEnv::new().with_spec_and_mainnet_gas_params(SpecId::FRONTIER);
    let mut evm = ctx.build_mainnet();

    let blocks_text = fs::read_to_string("../examples/data/mainnet_blocks_0_46299.json")
        .expect("read blocks");
    let blocks: serde_json::Value = serde_json::from_str(&blocks_text).expect("parse blocks");

    // Started here, after loading/parsing, so this measures EVM processing
    // time only, matching examples/sync.zig's methodology.
    let start = Instant::now();

    for block in blocks.as_array().expect("blocks array") {
        let number = parse_u64(block["number"].as_str().expect("number"));
        let miner = parse_address(block["miner"].as_str().expect("miner"));

        // Mirrors Evm.zig's processBlock, which sets these on its
        // Interpreter.BlockContext before running the block's transactions.
        evm.ctx.block.number = U256::from(number);
        evm.ctx.block.beneficiary = miner;
        evm.ctx.block.timestamp =
            U256::from(parse_u64(block["timestamp"].as_str().expect("timestamp")));
        evm.ctx.block.gas_limit = parse_u64(block["gasLimit"].as_str().expect("gasLimit"));
        evm.ctx.block.difficulty = parse_u256(block["difficulty"].as_str().expect("difficulty"));

        let txs = block["transactions"].as_array().expect("transactions array");

        for tx in txs {
            let from = parse_address(tx["from"].as_str().expect("from"));
            let to = tx["to"].as_str().map(parse_address);
            let value = parse_u256(tx["value"].as_str().expect("value"));
            let gas_limit = parse_u64(tx["gas"].as_str().expect("gas"));
            let gas_price = parse_u256(tx["gasPrice"].as_str().expect("gasPrice"));
            let nonce = parse_u64(tx["nonce"].as_str().expect("nonce"));
            let input_hex = tx["input"].as_str().expect("input");
            let data = Bytes::from(hex::decode(input_hex.trim_start_matches("0x")).unwrap());

            let kind = match to {
                Some(addr) => TxKind::Call(addr),
                None => TxKind::Create,
            };

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

            // Real Ethereum's inclusion rule only requires `gas_limit *
            // gas_price` to be affordable, not that plus `value` together;
            // `value` affordability is checked separately at execution
            // time and just reverts rather than invalidating the
            // transaction. revm's own balance check requires both
            // together, and its `disable_balance_check` escape hatch
            // overcorrects by topping up the sender's balance, meant for
            // `eth_call` simulation, not faithful replay. Applying the
            // real rule directly here instead.
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
                    "block {number}: sender {from} can't even afford gas ({} < {max_fee_for_gas}): replayed state has diverged from real chain",
                    sender_info.balance
                );
            }
            if sender_info.balance >= max_fee_for_gas + value {
                evm.transact_commit(tx_env).expect("transact_commit");
            } else {
                // Soft-revert: charge only the intrinsic gas fee, move no
                // value, run no code, matching Evm.zig's `call`/`create`
                // for this same case.
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
                    .basic(miner)
                    .unwrap()
                    .unwrap_or_default();
                coinbase_info.balance += fee;
                evm.ctx
                    .journaled_state
                    .database
                    .insert_account_info(miner, coinbase_info);
            }
        }

        // Block + uncle rewards: revm only executes transactions, same as
        // zevm's Interpreter/Evm split. Mirrors Evm.zig's processBlock.
        let mut miner_reward = U256::from(BLOCK_REWARD);
        for uncle_json in block["uncles"].as_array().expect("uncles array") {
            // Uncles fetched but not yet enriched are still a raw hash
            // string rather than a {hash, number, miner} object; skip
            // those, matching examples/sync.zig.
            let Some(uncle) = uncle_json.as_object() else {
                continue;
            };
            let uncle_number = parse_u64(uncle["number"].as_str().expect("uncle number"));
            let uncle_miner = parse_address(uncle["miner"].as_str().expect("uncle miner"));
            let distance = number - uncle_number;
            let uncle_reward =
                U256::from(BLOCK_REWARD) * U256::from(8 - distance) / U256::from(8u64);

            let mut uncle_miner_info = evm
                .ctx
                .journaled_state
                .database
                .basic(uncle_miner)
                .unwrap()
                .unwrap_or_default();
            uncle_miner_info.balance += uncle_reward;
            evm.ctx
                .journaled_state
                .database
                .insert_account_info(uncle_miner, uncle_miner_info);

            miner_reward += U256::from(BLOCK_REWARD) / U256::from(32u64); // "nephew" bonus
        }

        let mut miner_info = evm
            .ctx
            .journaled_state
            .database
            .basic(miner)
            .unwrap()
            .unwrap_or_default();
        miner_info.balance += miner_reward;
        evm.ctx
            .journaled_state
            .database
            .insert_account_info(miner, miner_info);

        if !txs.is_empty() || number % 5000 == 0 {
            println!("processed block {number} ({} txs)", txs.len());
        }
    }

    let accounts_touched = evm.ctx.journaled_state.database.cache.accounts.len();
    println!(
        "done: {accounts_touched} accounts touched in {:.2}ms",
        start.elapsed().as_secs_f64() * 1000.0
    );
}
