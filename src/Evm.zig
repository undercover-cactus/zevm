//! Executes a decoded `Transaction` against a `State`.
//!
//! Frontier through Prague are implemented (Muir, Arrow and Gray Glacier
//! only delayed the difficulty bomb and change nothing this executes).
//! `processBlock` panics on any block from a later fork (see `Fork`) instead
//! of silently applying stale rules.
//!
//! Constantinople and Petersburg share a block on mainnet (7,280,000):
//! Constantinople's EIP-1283 SSTORE repricing was withdrawn by Petersburg
//! before either ever ran, so no block on this chain uses it and it is
//! deliberately not implemented. `SSTORE` keeps Byzantium's pricing.

const std = @import("std");
const Address = @import("Address.zig").Address;
const Hash = @import("Hash.zig").Hash;
const State = @import("State.zig");
const Interpreter = @import("Interpreter.zig");
const Transaction = @import("Transaction.zig").Transaction;
const AccessListEntry = @import("Transaction.zig").AccessListEntry;
const Block = @import("Block.zig").Block;
const Fork = @import("Fork.zig").Fork;
const DaoFork = @import("DaoFork.zig");
const gas = @import("gas.zig");
const Precompiles = @import("Precompiles.zig");
const Rlp = @import("Rlp.zig");
const Authorization = @import("Transaction.zig").Authorization;
const keccak256 = @import("Hash.zig").keccak256;

allocator: std.mem.Allocator,
state: *State,
/// The block currently being processed. Set automatically by
/// `processBlock`; set it directly if calling `executeTransaction` on its
/// own and the code reads block-context opcodes.
block: Interpreter.BlockContext = .{},
/// The transaction currently executing, set by `executeTransaction` itself.
tx: Interpreter.TxContext = .{},
/// Total gas used by the last `processBlock`'s transactions. A real block
/// header commits to this, so comparing the two catches any gas divergence
/// at the exact block it happens, at full replay speed and without building
/// a state trie.
block_gas_used: u64 = 0,

const Evm = @This();

/// EIP-4788 (Cancun): the contract that keeps recent beacon block roots,
/// and the address its once-per-block update is sent from.
const beacon_roots_address: Address = 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02;
const system_address: Address = 0xfffffffffffffffffffffffffffffffffffffffe;
/// Gas given to a system call. It does not count toward the block's gas.
const system_call_gas: u64 = 30_000_000;
/// EIP-2935 (Prague): the contract that keeps recent block hashes.
const history_storage_address: Address = 0x0000F90827F1C53a10cb7A02335B175320002935;
/// EIP-7002 and EIP-7251 (Prague): the queues of withdrawal and
/// consolidation requests that validators submit from the execution layer,
/// drained by a system call after each block's transactions.
const withdrawal_request_address: Address = 0x00000961Ef480Eb55e80D19ad83579A64c007002;
const consolidation_request_address: Address = 0x0000BBdDc7CE488642fb579F8B00f3a590007251;

/// Miner reward for a block with no uncles: Frontier's flat 5 ETH, cut to
/// 3 ETH by EIP-649 at Byzantium and again to 2 ETH by EIP-1234 at
/// Constantinople. Both EIPs also delayed the difficulty bomb, which is a
/// mining-difficulty concern and not something this executes.
fn blockReward(fork: Fork) u256 {
    if (fork.atLeast(.constantinople)) return 2_000_000_000_000_000_000;
    if (fork.atLeast(.byzantium)) return 3_000_000_000_000_000_000;
    return 5_000_000_000_000_000_000;
}

pub const Result = struct {
    status: Interpreter.Status,
    /// A plain call's output, or a contract creation's deployed code.
    /// Caller-owned; free with the same allocator passed to `Evm`.
    return_data: []const u8,
    /// Set for contract-creation transactions, even if deployment failed.
    created_address: ?Address = null,
    /// Gas actually spent: `gas_limit` in full on `.out_of_gas` (all of it
    /// is forfeit), otherwise `gas_limit` minus what the interpreter had left.
    gas_used: u64 = 0,
};

// DEBUG: era1-replay divergence hunt scaffolding. Emits an EIP-3155 step
// trace for exactly one transaction of the live replay (real state, no
// seeding), for diffing against revm's trace of the same transaction.
// Gated by an explicit boolean, never by the address values alone.
const debug_trace_tx_enabled = false;
const debug_trace_tx_block: u64 = 7_753_545;
const debug_trace_tx_from: Address = 0x151e7f516f1f2002e9fbfaacebe87c4bd346941e;
const debug_tx_summary_enabled = false;

pub fn executeTransaction(self: *Evm, tx: Transaction, from: Address) !Result {
    // DEBUG: resets Interpreter's step-count safety valve (see its doc
    // comment) so it measures *this* transaction's total, not a running
    // total across the whole replay.
    if (Interpreter.counts_steps) Interpreter.debug_total_step_count = 0;

    const tracing = debug_trace_tx_enabled and self.block.number == debug_trace_tx_block and from == debug_trace_tx_from;
    if (tracing) Interpreter.step_trace_enabled = true;
    defer if (tracing) {
        Interpreter.step_trace_enabled = false;
    };
    // DEBUG: one line per transaction of the target block (gas used and
    // status), to diff against the real receipts and find which
    // transaction's execution diverges without tracing all of them.
    const summarizing = debug_tx_summary_enabled and self.block.number == debug_trace_tx_block;

    // A nonce mismatch means we fed transactions out of order, not that the
    // transaction itself is invalid. Worth panicking on immediately.
    const current_nonce = self.state.get(from).nonce;
    if (tx.nonce != current_nonce) {
        std.debug.panic(
            "nonce mismatch for {x}: transaction has {d}, state has {d}",
            .{ from, tx.nonce, current_nonce },
        );
    }

    // EIP-155, from Spurious Dragon on: a `v` of 27/28 predates chain-id
    // replay protection and is always accepted; `v >= 35` encodes a chain
    // id (`(v - 35) / 2`) that must match this network's. A `v` too
    // malformed to have produced `from` in the first place (recovered
    // externally, before this function runs) can't reach here, so unlike
    // real Ethereum's `chain_id()` there's no separate "bad v" rejection.
    if (self.block.fork.atLeast(.spurious_dragon) and tx.v >= 35) {
        const tx_chain_id: u256 = (tx.v - 35) / 2;
        if (tx_chain_id != self.block.chain_id) return error.WrongChainId;
    }
    // A typed transaction (EIP-2718) states its chain id outright.
    if (tx.chain_id) |tx_chain_id| {
        if (tx_chain_id != self.block.chain_id) return error.WrongChainId;
    }

    // Real Ethereum reserves the full potential fee up front and refunds
    // what's unused after execution. The sender must be able to cover the
    // `value` it is sending *as well as* that fee: execution-specs'
    // `process_transaction` asserts `balance >= gas_fee + value`, and a
    // block carrying a transaction that fails it is invalid. This is a
    // different rule from a *nested* `CALL`/`CREATE` that can't afford its
    // value, which fails gracefully (pushes 0) rather than voiding
    // anything — checking only `gas_fee` here let zevm accept transactions
    // real chain rejects, charging gas and silently dropping the transfer.
    // Failing this check on a replayed transaction means our balance has
    // already drifted from real chain state.
    //
    // EIP-1559 (London) splits the fee into a base fee, which is burned, and
    // a priority fee, which goes to the miner. A fee-market transaction
    // offers a maximum total (`gas_price`) and a maximum tip
    // (`max_priority_fee`) and pays `base_fee + min(tip, max - base_fee)`;
    // every other type pays its `gas_price` outright, which must at least
    // cover the base fee. The balance check below is still against the
    // *maximum*, as execution-specs' `check_transaction` does it.
    const base_fee: u256 = if (self.block.fork.atLeast(.london)) self.block.base_fee else 0;
    var effective_gas_price = tx.gas_price;
    if (tx.max_priority_fee) |tip| {
        if (tx.gas_price < tip) return error.PriorityFeeAboveMaxFee;
        if (tx.gas_price < base_fee) return error.MaxFeeBelowBaseFee;
        effective_gas_price = base_fee + @min(tip, tx.gas_price - base_fee);
    } else if (tx.gas_price < base_fee) return error.GasPriceBelowBaseFee;

    // EIP-4844 (Cancun): a blob transaction also buys blob gas, at the
    // block's blob base fee, which it must be willing to pay. All of that
    // fee is burned and none is refunded, so it is charged in full up front
    // and checked against the transaction's maximum like the gas fee is.
    const blob_gas = @as(u256, tx.blob_versioned_hashes.len) * gas.blob_gas_per_blob;
    var max_blob_fee: u256 = 0;
    if (tx.max_fee_per_blob_gas) |max_fee_per_blob_gas| {
        if (max_fee_per_blob_gas < self.block.blob_base_fee) return error.BlobFeeBelowBaseFee;
        max_blob_fee = blob_gas * max_fee_per_blob_gas;
    }

    // EIP-7623 (Prague): the gas limit must cover the calldata floor, which
    // the gas used is raised to after execution.
    const calldata_floor: u64 = if (self.block.fork.atLeast(.prague)) gas.calldataFloorCost(tx.data) else 0;
    if (tx.gas_limit < calldata_floor) return error.GasLimitBelowCalldataFloor;

    const gas_fee = @as(u256, tx.gas_limit) * tx.gas_price;
    const upfront_cost = gas_fee + tx.value + max_blob_fee;
    const balance_before = self.state.getBalance(from);
    if (upfront_cost > balance_before) {
        // Fatal path: this aborts the whole replay, so the detail is worth
        // printing unconditionally rather than hiding behind a flag.
        std.debug.print(
            "DEBUG InsufficientBalance: block={d} from={x} nonce={d} gas_limit={d} gas_price={d} value={d} gas_fee={d} upfront_cost={d} balance_before={d} short_by={d}\n",
            .{ self.block.number, from, tx.nonce, tx.gas_limit, tx.gas_price, tx.value, gas_fee, upfront_cost, balance_before, upfront_cost - balance_before },
        );
        return error.InsufficientBalance;
    }
    // Only the fee is debited here; `value` moves separately, through the
    // transfer inside the call/create this transaction turns into.
    try self.state.setBalance(from, balance_before - @as(u256, tx.gas_limit) * effective_gas_price - blob_gas * self.block.blob_base_fee);

    // A transaction's nonce always advances, whether it succeeds, reverts,
    // or fails outright.
    try self.state.setNonce(from, current_nonce + 1);

    // GASPRICE reports what is actually being paid per gas.
    self.tx = .{ .origin = from, .gas_price = effective_gas_price, .blob_hashes = tx.blob_versioned_hashes };

    // EIP-2929/2930 (Berlin): the sender, every precompile and everything in
    // the access list start warm. The target (or the address being created)
    // is warmed inside `call`/`create`, which know it. None of this is ever
    // reverted: it all precedes the checkpoint either of them takes.
    if (self.block.fork.atLeast(.berlin)) {
        _ = try self.state.warmAddress(from);
        // Cancun added the point evaluation precompile at 0x0a, Prague the
        // BLS12-381 ones at 0x0b to 0x11.
        const last_precompile: Address = if (self.block.fork.atLeast(.prague)) 0x11 else if (self.block.fork.atLeast(.cancun)) 0x0a else 0x09;
        var precompile: Address = 1;
        while (precompile <= last_precompile) : (precompile += 1) _ = try self.state.warmAddress(precompile);
        for (tx.access_list) |entry| {
            _ = try self.state.warmAddress(entry.address);
            for (entry.storage_keys) |key| _ = try self.state.warmSlot(entry.address, key);
        }
        // EIP-3651 (Shanghai): so does the block's coinbase.
        if (self.block.fork.atLeast(.shanghai)) _ = try self.state.warmAddress(self.block.coinbase);
    }
    const access_list_cost = gas.accessListCost(tx.access_list);

    var result = if (tx.to) |to| call: {
        // EIP-7702 (Prague): every authorization costs intrinsic gas, valid
        // or not, and the valid ones are applied now, after the sender's
        // nonce moved and before the call's checkpoint.
        const authorization_cost = gas.per_empty_account_7702 * @as(u64, tx.authorization_list.len);
        const authorization_refund = try self.applyAuthorizations(tx.authorization_list);
        break :call try self.call(tx.value, tx.data, access_list_cost + authorization_cost, authorization_refund, tx.gas_limit, from, to);
    } else try self.create(tx.nonce, tx.value, tx.data, access_list_cost, tx.gas_limit, from);
    result.gas_used = @max(result.gas_used, calldata_floor);

    // Refund unused gas, then pay the miner, via `creditBalance` (unjournaled,
    // like block rewards): a transaction's gas fee is never undone by a revert.
    const unused = @as(u256, tx.gas_limit - result.gas_used) * effective_gas_price;
    if (unused != 0) try self.state.creditBalance(from, unused);
    // Only the priority fee reaches the miner; the base fee part of what the
    // sender paid is credited to no one, which is what burns it.
    const priority_fee = effective_gas_price - base_fee;
    if (result.gas_used != 0 and priority_fee != 0) {
        try self.state.creditBalance(self.block.coinbase, @as(u256, result.gas_used) * priority_fee);
    }

    // Any `SELFDESTRUCT` that survived to here (a reverted one never
    // reaches `pending_destructions` in the first place) is now permanent:
    // erase those accounts from state entirely, same as real Ethereum does
    // at the end of a transaction.
    self.state.finalizeTransaction();

    if (summarizing) {
        std.debug.print("DEBUG txsum from={x} to={?x} nonce={d} gas_used={d} status={s}\n", .{ from, tx.to, tx.nonce, result.gas_used, @tagName(result.status) });
    }

    return result;
}

/// Runs every transaction in `block`, then credits block and uncle rewards.
/// Per-transaction `Result`s aren't surfaced; call `executeTransaction`
/// directly if you need them.
pub fn processBlock(self: *Evm, block: Block) !void {
    State.debug_block_number = block.number;
    const fork = Fork.at(block.number);
    // Muir Glacier delayed the difficulty bomb and changed nothing this
    // executes, so Istanbul's rules carry through it unchanged.
    if (fork.atLeast(.osaka)) {
        std.debug.panic(
            "block {d} is past Prague (fork: {s}): this Evm only implements up to Prague's rules",
            .{ block.number, @tagName(fork) },
        );
    }

    // The DAO fork wasn't an EVM/gas rule change: at exactly this block, an
    // irregular state transition hardcoded into every client moves all
    // ether out of The DAO (and its children) before any of the block's
    // own transactions run.
    if (block.number == 1_920_000) try DaoFork.apply(self.state);

    self.block = .{
        .number = block.number,
        .timestamp = block.timestamp,
        .coinbase = block.miner,
        .gas_limit = block.gas_limit,
        .difficulty = block.difficulty,
        .base_fee = block.base_fee,
        .chain_id = block.chain_id,
        .recent_hashes = block.recent_hashes,
        .fork = fork,
        .blob_base_fee = if (fork.atLeast(.cancun)) gas.blobBaseFee(block.excess_blob_gas, fork) else 0,
    };

    // EIP-4788 (Cancun) and EIP-2935 (Prague): before any transaction, the
    // parent beacon block root and the parent block hash are stored.
    if (fork.atLeast(.cancun)) _ = try self.systemCall(beacon_roots_address, block.parent_beacon_block_root);
    if (fork.atLeast(.prague)) _ = try self.systemCall(history_storage_address, block.parent_hash);

    self.block_gas_used = 0;
    for (block.transactions) |entry| {
        const result = try self.executeTransaction(entry.tx, entry.from);
        self.block_gas_used += result.gas_used;
        self.allocator.free(result.return_data);
    }

    // EIP-3675 (the Merge): proof of stake pays validators on the beacon
    // chain, so execution blocks carry no block or uncle rewards. From
    // Shanghai on (EIP-4895), what validators withdraw from the beacon chain
    // is credited here instead, in gwei, using no gas and outside any
    // transaction. A zero amount credits nothing and creates no account
    // (reth skips it the same way).
    if (fork.atLeast(.merge)) {
        for (block.withdrawals) |withdrawal| {
            if (withdrawal.amount != 0) try self.state.creditBalance(withdrawal.address, @as(u256, withdrawal.amount) * 1_000_000_000);
        }
        // EIP-7002 and EIP-7251 (Prague): then the request queues are
        // drained. What they return goes into the header's requests hash,
        // which this does not check, but draining changes their storage.
        // Unlike the calls above these must succeed, or the block is invalid.
        if (fork.atLeast(.prague)) {
            if (!try self.systemCall(withdrawal_request_address, null)) return error.SystemCallFailed;
            if (!try self.systemCall(consolidation_request_address, null)) return error.SystemCallFailed;
        }
        self.state.debugDumpBlockAccounts();
        return;
    }

    // A whole block is never rolled back once processed, so rewards credit
    // directly rather than through `setBalance`'s journaled bookkeeping.
    const reward = blockReward(fork);
    var miner_reward = reward;
    for (block.uncles) |uncle| {
        const distance = block.number - uncle.number;
        const uncle_reward = reward * (8 - distance) / 8;
        try self.state.creditBalance(uncle.miner, uncle_reward);
        miner_reward += reward / 32; // "nephew" bonus for including it
    }
    try self.state.creditBalance(block.miner, miner_reward);
    self.state.debugDumpBlockAccounts();
}

/// A system call (EIP-4788 onwards): the system address calls `target`
/// with `word` as calldata, or none if it is null. No sender account, no
/// fee, no value, and its gas counts toward nothing. Whether it ran to a
/// stop; a contract that has not been deployed yet counts as failing.
fn systemCall(self: *Evm, target: Address, word: ?Hash) !bool {
    const code = self.state.getCode(target);
    if (code.len == 0) return false;
    var calldata: [32]u8 = undefined;
    if (word) |w| std.mem.writeInt(u256, &calldata, w, .big);
    self.tx = .{ .origin = system_address, .gas_price = self.block.base_fee };

    const cp = self.state.checkpoint();
    var interp = try Interpreter.initCall(self.allocator, code, system_call_gas, .{
        .address = target,
        .caller = system_address,
        .value = 0,
        .calldata = if (word != null) &calldata else &.{},
        .tx = self.tx,
        .state = self.state,
        .block = self.block,
        .jumpdest = try self.state.getJumpdest(target),
    });
    defer interp.deinit();
    try interp.run();
    const ok = interp.status == .stopped;
    if (!ok) self.state.revertTo(cp);
    self.state.finalizeTransaction();
    return ok;
}

/// EIP-7702 (Prague): applies a set-code transaction's authorizations in
/// order. One that fails a check is skipped, and a later one from the same
/// authority overrides an earlier one. Returns the gas refunded for
/// authorities that already existed, which applies even if the call then
/// fails.
fn applyAuthorizations(self: *Evm, authorizations: []const Authorization) !u64 {
    var refund: u64 = 0;
    for (authorizations) |auth| {
        if (auth.chain_id != 0 and auth.chain_id != self.block.chain_id) continue;
        if (auth.nonce == std.math.maxInt(u64)) continue;
        const authority = try recoverAuthority(self.allocator, auth) orelse continue;
        _ = try self.state.warmAddress(authority);
        const code = self.state.getCode(authority);
        if (code.len != 0 and Interpreter.delegatedAddress(code) == null) continue;
        if (self.state.get(authority).nonce != auth.nonce) continue;
        if (self.state.exists(authority)) refund += gas.per_empty_account_7702 - gas.per_auth_base_7702;
        if (auth.address == 0) {
            try self.state.setDelegation(authority, &.{});
        } else {
            var indicator: [23]u8 = undefined;
            indicator[0..3].* = .{ 0xef, 0x01, 0x00 };
            std.mem.writeInt(u160, indicator[3..23], auth.address, .big);
            try self.state.setDelegation(authority, &indicator);
        }
        try self.state.setNonce(authority, auth.nonce + 1);
    }
    return refund;
}

/// The account that signed `auth`, or null for a signature that does not
/// recover or whose `s` is in the upper half of the curve order (EIP-2).
fn recoverAuthority(allocator: std.mem.Allocator, auth: Authorization) !?Address {
    const half_curve_order: u256 = 0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0;
    if (auth.y_parity > 1 or auth.s > half_curve_order) return null;

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var address_bytes: [20]u8 = undefined;
    std.mem.writeInt(u160, &address_bytes, auth.address, .big);
    const payload = try Rlp.encodeList(a, &.{
        try Rlp.encodeInt(a, auth.chain_id),
        try Rlp.encodeBytes(a, &address_bytes),
        try Rlp.encodeInt(a, auth.nonce),
    });
    const preimage = try a.alloc(u8, payload.len + 1);
    preimage[0] = 0x05;
    @memcpy(preimage[1..], payload);

    var hash: [32]u8 = undefined;
    std.mem.writeInt(u256, &hash, keccak256(preimage), .big);
    var r: [32]u8 = undefined;
    std.mem.writeInt(u256, &r, auth.r, .big);
    var s: [32]u8 = undefined;
    std.mem.writeInt(u256, &s, auth.s, .big);
    const recovered = Precompiles.ecrecover(hash, 27 + auth.y_parity, r, s) orelse return null;
    return std.mem.readInt(u160, &recovered, .big);
}

/// `extra_intrinsic` is what the access list and any EIP-7702
/// authorizations add to the intrinsic cost, and `authorization_refund` the
/// refund those authorizations earned.
fn call(self: *Evm, value: u256, data: []const u8, extra_intrinsic: u64, authorization_refund: u64, gas_limit: u64, from: Address, to: Address) !Result {
    if (self.block.fork.atLeast(.berlin)) _ = try self.state.warmAddress(to);
    const cp = self.state.checkpoint();

    // The intrinsic cost is paid before any code runs; real Ethereum
    // forfeits the whole limit if gas_limit can't cover it.
    const intrinsic = gas.intrinsicCost(data, self.block.fork) + extra_intrinsic;
    if (gas_limit < intrinsic) {
        self.state.revertTo(cp);
        return .{
            .status = .out_of_gas,
            .return_data = try self.allocator.alloc(u8, 0),
            .gas_used = gas_limit,
        };
    }

    // Insufficient balance for `value` alone doesn't abort the block: the
    // gas fee is already reserved, so this fails like an immediate REVERT,
    // paying only the intrinsic cost. Always calls `transfer`, even for
    // value == 0, since it still has to touch `to` (see its own doc comment).
    const execution_gas_limit = gas_limit - intrinsic;
    if (!try self.state.transfer(from, to, value)) {
        if (value > 1_000_000_000_000_000_000_000) {
            std.debug.print(
                "DEBUG large reverted transfer: block={d} from={x} to={x} value={d} sender_balance={d}\n",
                .{ self.block.number, from, to, value, self.state.getBalance(from) },
            );
        }
        self.state.revertTo(cp);
        return .{
            .status = .reverted,
            .return_data = try self.allocator.alloc(u8, 0),
            .gas_used = gasUsed(.reverted, execution_gas_limit, 0, authorization_refund, execution_gas_limit, intrinsic, self.block.fork),
        };
    }

    // A transaction can target a precompile directly, same as `Interpreter.call`.
    if (try Precompiles.call(self.allocator, to, data, execution_gas_limit, self.block.fork)) |result| {
        const status: Interpreter.Status = if (result.success) .stopped else .out_of_gas;
        // EIP-161, from Spurious Dragon on: mark `to` touched regardless
        // of outcome — journaled, so the revert below (if any)
        // automatically discards it, same as `Interpreter.call`.
        if (self.block.fork.atLeast(.spurious_dragon)) try self.state.markTouchedIfEmpty(to);
        if (status != .stopped) self.state.revertTo(cp);
        return .{
            .status = status,
            .return_data = result.output,
            .gas_used = gasUsed(status, result.gas_remaining, 0, authorization_refund, execution_gas_limit, intrinsic, self.block.fork),
        };
    }

    // EIP-7702 (Prague): a delegated destination runs the code its
    // indicator points at, which starts warm.
    var code_address = to;
    var code = self.state.getCode(to);
    if (self.block.fork.atLeast(.prague)) {
        if (Interpreter.delegatedAddress(code)) |delegate| {
            _ = try self.state.warmAddress(delegate);
            code_address = delegate;
            code = self.state.getCode(delegate);
        }
    }

    // A call to an address with no code is an immediate, trivial success.
    // Skipping straight to that result avoids constructing a full
    // `Interpreter` (its 1024-word `Stack` alone measures ~4.4us to
    // build/teardown, from stack-probing a frame that size) for a call
    // that would just hit `.stopped` anyway.
    if (code.len == 0) {
        // Always a trivial success, so no revert to worry about here.
        if (self.block.fork.atLeast(.spurious_dragon)) try self.state.markTouchedIfEmpty(to);
        return .{
            .status = .stopped,
            .return_data = try self.allocator.alloc(u8, 0),
            .gas_used = gasUsed(.stopped, execution_gas_limit, 0, authorization_refund, execution_gas_limit, intrinsic, self.block.fork),
        };
    }

    var interp = try Interpreter.initCall(self.allocator, code, execution_gas_limit, .{
        .address = to,
        .caller = from,
        .value = value,
        .calldata = data,
        .tx = self.tx,
        .state = self.state,
        .block = self.block,
        .jumpdest = try self.state.getJumpdest(code_address),
    });
    defer interp.deinit();
    try interp.run();

    if (self.block.fork.atLeast(.spurious_dragon)) try self.state.markTouchedIfEmpty(to);
    if (interp.status != .stopped) self.state.revertTo(cp);

    return .{
        .status = interp.status,
        .return_data = try self.allocator.dupe(u8, interp.return_data),
        .gas_used = gasUsed(interp.status, interp.gas_remaining, interp.refund, authorization_refund, execution_gas_limit, intrinsic, self.block.fork),
    };
}

/// The gas actually charged: `intrinsic` plus what the interpreter spent,
/// minus any refund. The refund cap applies to the total including
/// intrinsic (matching real Ethereum, so padding calldata can't dodge it).
/// Exceptional halts (`.out_of_gas`, `.invalid_opcode`, `.invalid_jump`,
/// `.stack_overflow`, `.stack_underflow`) spend the entire limit;
/// `.reverted` only spends what actually ran. The execution's own `refund`
/// only counts on `.stopped`, while `authorization_refund` (EIP-7702) was
/// earned before execution began and counts whatever happens.
fn gasUsed(status: Interpreter.Status, gas_remaining: u64, refund: i64, authorization_refund: u64, execution_gas_limit: u64, intrinsic: u64, fork: Fork) u64 {
    const spent = switch (status) {
        .out_of_gas, .invalid_opcode, .invalid_jump, .stack_overflow, .stack_underflow => execution_gas_limit + intrinsic,
        else => intrinsic + (execution_gas_limit - gas_remaining),
    };
    // A negative counter means more refund was taken back than granted,
    // which refunds nothing rather than charging extra.
    const total_refund = @as(i64, @intCast(authorization_refund)) + (if (status == .stopped) refund else 0);
    if (total_refund <= 0) return spent;
    const denominator = if (fork.atLeast(.london)) gas.max_refund_denominator_3529 else gas.max_refund_denominator;
    return spent - @min(@as(u64, @intCast(total_refund)), spent / denominator);
}

fn create(self: *Evm, nonce: u64, value: u256, data: []const u8, access_list_cost: u64, gas_limit: u64, from: Address) !Result {
    // EIP-3860 (Shanghai): a creation transaction carrying more init code
    // than this is invalid, so no real block contains one.
    if (self.block.fork.atLeast(.shanghai) and data.len > Interpreter.max_initcode_size) return error.InitcodeTooLarge;
    const new_address = try Interpreter.createAddress(self.allocator, from, nonce);
    if (self.block.fork.atLeast(.berlin)) _ = try self.state.warmAddress(new_address);

    // EIP-684, the transaction-level half of the rule `Interpreter.createOp`
    // enforces for the opcodes (execution-specs checks it in
    // `process_message_call`, before the creation even begins): an address
    // that already holds code or a nonzero nonce cannot be created at, and
    // the attempt forfeits the whole gas limit. A creation transaction
    // derives its address from the sender's nonce, so reaching this needs a
    // genuine collision rather than a chosen salt, but the rule is the same.
    if (self.state.get(new_address).nonce != 0 or self.state.getCode(new_address).len != 0) {
        return .{
            .status = .out_of_gas,
            .return_data = try self.allocator.alloc(u8, 0),
            .created_address = new_address,
            .gas_used = gas_limit,
        };
    }

    const cp = self.state.checkpoint();
    if (self.block.fork.atLeast(.cancun)) try self.state.markCreated(new_address);

    // EIP-161, from Spurious Dragon on: a freshly created contract's own
    // nonce starts at 1, not 0 (mirrors `Interpreter.createOp`'s nested
    // `CREATE`/`CREATE2`).
    if (self.block.fork.atLeast(.spurious_dragon)) try self.state.setNonce(new_address, 1);

    // EIP-2 (Homestead): a top-level contract-creation transaction pays an
    // extra `create_base` surcharge on top of the usual intrinsic cost.
    // Nested `CREATE`/`CREATE2` (`Interpreter.createOp`) are unaffected.
    var intrinsic = gas.intrinsicCost(data, self.block.fork) + access_list_cost;
    if (self.block.fork != .frontier) intrinsic += gas.create_base;
    // EIP-3860 (Shanghai): init code also pays per word.
    if (self.block.fork.atLeast(.shanghai)) intrinsic += gas.initcode_word * ((data.len + 31) / 32);
    if (gas_limit < intrinsic) {
        self.state.revertTo(cp);
        return .{
            .status = .out_of_gas,
            .return_data = try self.allocator.alloc(u8, 0),
            .created_address = new_address,
            .gas_used = gas_limit,
        };
    }

    // See the equivalent branch in `call`: insufficient balance for `value`
    // fails just this transaction, not the whole block.
    if (value != 0 and !try self.state.transfer(from, new_address, value)) {
        self.state.revertTo(cp);
        return .{
            .status = .reverted,
            .return_data = try self.allocator.alloc(u8, 0),
            .created_address = new_address,
            .gas_used = intrinsic,
        };
    }

    // Materialise the new contract before its init code runs, matching
    // execution-specs' `process_message`. Pre-Spurious-Dragon there's no
    // nonce to set and a zero-value creation moves nothing, so without this
    // the address exists nowhere while its constructor executes — and a
    // constructor that `SELFDESTRUCT`s then registers no destruction at all
    // (`destroyAccount` no-ops on an account that isn't there), leaving
    // `setCode` below to create it permanently. Real chain deletes such a
    // contract at transaction end; zevm was keeping it forever.
    try self.state.touch(new_address);

    var interp = try Interpreter.initCall(self.allocator, data, gas_limit - intrinsic, .{
        .address = new_address,
        .caller = from,
        .value = value,
        .tx = self.tx,
        .state = self.state,
        .block = self.block,
    });
    defer interp.deinit();
    try interp.run();

    // EIP-170, from Spurious Dragon on: deployed code over this size is an
    // exceptional halt (forfeits all remaining gas), not a graceful stop.
    // No limit at all before this fork. Mirrors `Interpreter.createOp`.
    const oversized = self.block.fork.atLeast(.spurious_dragon) and interp.return_data.len > Interpreter.max_code_size;
    // EIP-3541 (London), mirroring `Interpreter.createOp`.
    const ef_prefixed = self.block.fork.atLeast(.london) and interp.return_data.len > 0 and interp.return_data[0] == 0xef;
    const rejected = oversized or ef_prefixed;

    // Mirrors `Interpreter.createOp`: a successful init code run still has
    // to afford storing its returned code, at `code_deposit_byte` gas/byte.
    var success = interp.status == .stopped and !rejected;
    var status: Interpreter.Status = if (rejected) .out_of_gas else interp.status;
    var deployed_code: []const u8 = interp.return_data;
    if (success) {
        const deposit_cost = gas.code_deposit_byte * @as(u64, interp.return_data.len);
        if (interp.gas_remaining < deposit_cost) {
            if (self.block.fork == .frontier) {
                // Real Frontier: an unaffordable deposit just skips storing
                // code; the creation still succeeds and gas_remaining is
                // left exactly as-is. Homestead (EIP-2) made this a hard,
                // gas-forfeiting failure instead.
                deployed_code = &.{};
            } else {
                success = false;
                status = .out_of_gas;
            }
        } else {
            interp.gas_remaining -= deposit_cost;
        }
    }
    if (success) {
        try self.state.setCode(new_address, deployed_code);
    } else {
        self.state.revertTo(cp);
    }

    return .{
        .status = status,
        .return_data = try self.allocator.dupe(u8, interp.return_data),
        .created_address = new_address,
        .gas_used = gasUsed(status, interp.gas_remaining, interp.refund, 0, gas_limit - intrinsic, intrinsic, self.block.fork),
    };
}

fn testTx() Transaction {
    return .{
        .nonce = 0,
        .gas_price = 0,
        .gas_limit = 1_000_000,
        .to = null,
        .value = 0,
        .data = &.{},
        .v = 0,
        .r = 0,
        .s = 0,
    };
}

test "a plain value-transfer call moves balance and produces no output" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 1000);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    var tx = testTx();
    tx.to = 0xdd;
    tx.value = 100;

    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);

    try std.testing.expectEqual(Interpreter.Status.stopped, result.status);
    try std.testing.expectEqual(@as(u256, 900), state.getBalance(0x1));
    try std.testing.expectEqual(@as(u256, 100), state.getBalance(0xdd));
    try std.testing.expectEqual(@as(u64, 1), state.get(0x1).nonce);
}

test "a zero-value call still touches (creates) a not-yet-existing recipient" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 1000);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    var tx = testTx();
    tx.to = 0xdd;
    tx.value = 0;

    try std.testing.expect(!state.exists(0xdd));
    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);

    try std.testing.expectEqual(Interpreter.Status.stopped, result.status);
    try std.testing.expect(state.exists(0xdd));
    try std.testing.expectEqual(@as(u256, 0), state.getBalance(0xdd));
}

test "from Spurious Dragon on, a zero-value call to a not-yet-existing recipient leaves no trace behind (EIP-161)" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 1000);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = .spurious_dragon } };
    var tx = testTx();
    tx.to = 0xdd;
    tx.value = 0;

    try std.testing.expect(!state.exists(0xdd));
    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);

    // Contrast with the pre-161 test above: the exact same call, but this
    // time `finalizeTransaction`'s EIP-161 sweep deletes the touched,
    // still-empty account before the transaction is done, instead of
    // leaving a permanent zero-balance shell behind.
    try std.testing.expectEqual(Interpreter.Status.stopped, result.status);
    try std.testing.expect(!state.exists(0xdd));
}

test "a call into a contract runs its code and returns its output" {
    // returns CALLVALUE as a 32-byte word.
    const OpCode = @import("OpCode.zig").OpCode;
    const code = [_]u8{
        @intFromEnum(OpCode.CALLVALUE),
        @intFromEnum(OpCode.PUSH1),
        0,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1),
        32,
        @intFromEnum(OpCode.PUSH1),
        0,
        @intFromEnum(OpCode.RETURN),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 1000);
    try state.setCode(0xcc, &code);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    var tx = testTx();
    tx.to = 0xcc;
    tx.value = 42;

    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);

    try std.testing.expectEqual(Interpreter.Status.stopped, result.status);
    try std.testing.expectEqual(@as(u256, 42), std.mem.readInt(u256, result.return_data[0..32], .big));
}

test "a contract-creation transaction deploys the init code's returned bytes" {
    // init code: pushes 3 bytes of "runtime code" as a right-aligned 32-byte
    // word, stores it at memory[0..32], then RETURNs just those 3 bytes.
    const OpCode = @import("OpCode.zig").OpCode;
    const init_code = [_]u8{
        @intFromEnum(OpCode.PUSH3), 0x60,                       0x2a,                        0x00,
        @intFromEnum(OpCode.PUSH1), 0,                          @intFromEnum(OpCode.MSTORE), @intFromEnum(OpCode.PUSH1),
        3,                          @intFromEnum(OpCode.PUSH1), 29,                          @intFromEnum(OpCode.RETURN),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 1000);
    try state.setNonce(0x1, 5);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    var tx = testTx();
    tx.nonce = 5;
    tx.data = &init_code;

    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);

    try std.testing.expectEqual(Interpreter.Status.stopped, result.status);
    const created = result.created_address.?;
    try std.testing.expectEqualSlices(u8, &.{ 0x60, 0x2a, 0x00 }, state.getCode(created));
    try std.testing.expectEqual(@as(u64, 6), state.get(0x1).nonce);
}

test "a freshly created contract's own nonce is 1 from Spurious Dragon on, 0 before (EIP-161)" {
    const OpCode = @import("OpCode.zig").OpCode;
    const init_code = [_]u8{
        @intFromEnum(OpCode.PUSH3), 0x60,                       0x2a,                        0x00,
        @intFromEnum(OpCode.PUSH1), 0,                          @intFromEnum(OpCode.MSTORE), @intFromEnum(OpCode.PUSH1),
        3,                          @intFromEnum(OpCode.PUSH1), 29,                          @intFromEnum(OpCode.RETURN),
    };

    var pre_state = State.init(std.testing.allocator);
    defer pre_state.deinit();
    try pre_state.setBalance(0x1, 1000);
    var pre_evm = Evm{ .allocator = std.testing.allocator, .state = &pre_state };
    var pre_tx = testTx();
    pre_tx.data = &init_code;
    const pre_result = try pre_evm.executeTransaction(pre_tx, 0x1);
    defer std.testing.allocator.free(pre_result.return_data);
    try std.testing.expectEqual(@as(u64, 0), pre_state.get(pre_result.created_address.?).nonce);

    var sd_state = State.init(std.testing.allocator);
    defer sd_state.deinit();
    try sd_state.setBalance(0x1, 1000);
    var sd_evm = Evm{ .allocator = std.testing.allocator, .state = &sd_state, .block = .{ .fork = .spurious_dragon } };
    var sd_tx = testTx();
    sd_tx.data = &init_code;
    const sd_result = try sd_evm.executeTransaction(sd_tx, 0x1);
    defer std.testing.allocator.free(sd_result.return_data);
    try std.testing.expectEqual(@as(u64, 1), sd_state.get(sd_result.created_address.?).nonce);
}

test "a Homestead contract-creation transaction's intrinsic gas includes the create surcharge" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 1000);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = .homestead } };
    var tx = testTx();
    tx.gas_limit = 52_999; // one short of 21,000 (tx_base) + 32,000 (create_base)

    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);
    try std.testing.expectEqual(Interpreter.Status.out_of_gas, result.status);
}

test "a Homestead contract-creation transaction succeeds once gas covers the create surcharge" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 1000);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = .homestead } };
    var tx = testTx();
    tx.gas_limit = 53_000; // exactly 21,000 + 32,000

    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);
    try std.testing.expectEqual(Interpreter.Status.stopped, result.status);
    try std.testing.expectEqual(@as(u64, 53_000), result.gas_used);
}

test "CREATE transaction with insufficient deposit gas still succeeds on Frontier, with no code stored" {
    const OpCode = @import("OpCode.zig").OpCode;
    // init code: returns 5000 bytes (all zero), whose code-deposit cost
    // (200 gas/byte = 1,000,000 gas) is far beyond what's provided.
    const init_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.PUSH2), 0x13, 0x87, // offset = 4999
        @intFromEnum(OpCode.MSTORE8),
        @intFromEnum(OpCode.PUSH2), 0x13, 0x88, // size = 5000
        @intFromEnum(OpCode.PUSH1), 0, // offset = 0
        @intFromEnum(OpCode.RETURN),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 1000);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = .frontier } };
    var tx = testTx();
    tx.data = &init_code;
    tx.gas_limit = 21_000 + 5_000; // enough to run init code, nowhere near the 1,000,000 deposit

    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);
    try std.testing.expectEqual(Interpreter.Status.stopped, result.status);
    const created = result.created_address.?;
    try std.testing.expect(state.exists(created));
    try std.testing.expectEqualSlices(u8, &.{}, state.getCode(created));
}

test "CREATE transaction with insufficient deposit gas fails entirely on Homestead" {
    const OpCode = @import("OpCode.zig").OpCode;
    const init_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.PUSH2), 0x13, 0x87, // offset = 4999
        @intFromEnum(OpCode.MSTORE8),
        @intFromEnum(OpCode.PUSH2), 0x13, 0x88, // size = 5000
        @intFromEnum(OpCode.PUSH1), 0, // offset = 0
        @intFromEnum(OpCode.RETURN),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 1000);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = .homestead } };
    var tx = testTx();
    tx.data = &init_code;
    tx.gas_limit = 53_000 + 5_000;

    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);
    try std.testing.expectEqual(Interpreter.Status.out_of_gas, result.status);
    const created = result.created_address.?;
    try std.testing.expect(!state.exists(created));
}

test "top-level CREATE transaction rejects code over max_code_size from Spurious Dragon on, not before" {
    const OpCode = @import("OpCode.zig").OpCode;
    // Returns 24577 bytes (max_code_size + 1) read straight out of
    // never-written (so all-zero) memory.
    const init_code = [_]u8{
        @intFromEnum(OpCode.PUSH2), 0x60, 0x01, // size = 24577
        @intFromEnum(OpCode.PUSH1), 0, // offset = 0
        @intFromEnum(OpCode.RETURN),
    };

    // Pre-Spurious-Dragon: no limit at all, the oversized code is stored.
    var tw_state = State.init(std.testing.allocator);
    defer tw_state.deinit();
    try tw_state.setBalance(0x1, 1000);
    var tw_evm = Evm{ .allocator = std.testing.allocator, .state = &tw_state, .block = .{ .fork = .tangerine_whistle } };
    var tw_tx = testTx();
    tw_tx.data = &init_code;
    tw_tx.gas_limit = 10_000_000;
    const tw_result = try tw_evm.executeTransaction(tw_tx, 0x1);
    defer std.testing.allocator.free(tw_result.return_data);
    try std.testing.expectEqual(Interpreter.Status.stopped, tw_result.status);
    try std.testing.expectEqual(@as(usize, 24577), tw_state.getCode(tw_result.created_address.?).len);

    // From Spurious Dragon on: an exceptional halt, nothing stored.
    var sd_state = State.init(std.testing.allocator);
    defer sd_state.deinit();
    try sd_state.setBalance(0x1, 1000);
    var sd_evm = Evm{ .allocator = std.testing.allocator, .state = &sd_state, .block = .{ .fork = .spurious_dragon } };
    var sd_tx = testTx();
    sd_tx.data = &init_code;
    sd_tx.gas_limit = 10_000_000;
    const sd_result = try sd_evm.executeTransaction(sd_tx, 0x1);
    defer std.testing.allocator.free(sd_result.return_data);
    try std.testing.expectEqual(Interpreter.Status.out_of_gas, sd_result.status);
    try std.testing.expect(!sd_state.exists(sd_result.created_address.?));
}

test "a reverted call rolls back its balance transfer and reports .reverted" {
    const OpCode = @import("OpCode.zig").OpCode;
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1),  0,
        @intFromEnum(OpCode.PUSH1),  0,
        @intFromEnum(OpCode.REVERT),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 1000);
    try state.setCode(0xdd, &code);

    // REVERT is Byzantium-only (EIP-140).
    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = .byzantium } };
    var tx = testTx();
    tx.to = 0xdd;
    tx.value = 100;

    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);

    try std.testing.expectEqual(Interpreter.Status.reverted, result.status);
    try std.testing.expectEqual(@as(u256, 1000), state.getBalance(0x1));
    try std.testing.expectEqual(@as(u256, 0), state.getBalance(0xdd));
    // the nonce bump is not part of the reverted call itself, so it stands.
    try std.testing.expectEqual(@as(u64, 1), state.get(0x1).nonce);
}

test "gas is charged to the sender and credited to the block's coinbase" {
    const OpCode = @import("OpCode.zig").OpCode;
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1),  0,
        @intFromEnum(OpCode.PUSH1),  0,
        @intFromEnum(OpCode.RETURN),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 10_000_000);
    try state.setCode(0xdd, &code);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .coinbase = 0xcc } };
    var tx = testTx();
    tx.to = 0xdd;
    tx.gas_price = 10;

    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);

    try std.testing.expectEqual(Interpreter.Status.stopped, result.status);
    try std.testing.expect(result.gas_used > 0);
    const fee_paid = 10_000_000 - state.getBalance(0x1);
    try std.testing.expectEqual(@as(u256, result.gas_used) * 10, fee_paid);
    try std.testing.expectEqual(fee_paid, state.getBalance(0xcc));
}

test "gas is charged even when the call reverts" {
    const OpCode = @import("OpCode.zig").OpCode;
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1),  0,
        @intFromEnum(OpCode.PUSH1),  0,
        @intFromEnum(OpCode.REVERT),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 10_000_000);
    try state.setCode(0xdd, &code);

    // REVERT is Byzantium-only (EIP-140).
    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .coinbase = 0xcc, .fork = .byzantium } };
    var tx = testTx();
    tx.to = 0xdd;
    tx.gas_price = 10;

    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);

    try std.testing.expectEqual(Interpreter.Status.reverted, result.status);
    try std.testing.expect(result.gas_used > 0);
    const fee_paid = 10_000_000 - state.getBalance(0x1);
    try std.testing.expectEqual(@as(u256, result.gas_used) * 10, fee_paid);
    try std.testing.expectEqual(fee_paid, state.getBalance(0xcc));
}

test "a later transaction's CALL to a self-destructed address pays the new-account surcharge again" {
    const OpCode = @import("OpCode.zig").OpCode;
    const selfdestruct_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xbb,
        @intFromEnum(OpCode.SELFDESTRUCT),
    };
    // caller: CALL(gas=10000, addr=0xdd, value=0, argsOffset=0, argsSize=0, retOffset=0, retSize=0)
    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // retSize
        @intFromEnum(OpCode.PUSH1), 0, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH1), 0, // argsOffset
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.PUSH1), 0xdd, // address
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10, // gas
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.STOP),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xdd, &selfdestruct_code);
    try state.setCode(0xee, &caller_code);
    try state.setBalance(0x1, 10_000_000);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    var destroy_tx = testTx();
    destroy_tx.nonce = 0;
    destroy_tx.to = 0xdd;
    const destroy_result = try evm.executeTransaction(destroy_tx, 0x1);
    std.testing.allocator.free(destroy_result.return_data);
    try std.testing.expect(!state.exists(0xdd));

    var call_tx = testTx();
    call_tx.nonce = 1;
    call_tx.to = 0xee;
    const call_result = try evm.executeTransaction(call_tx, 0x1);
    defer std.testing.allocator.free(call_result.return_data);

    // Baseline: the same caller contract, but targeting an address that was
    // never touched at all, so it pays the surcharge exactly once (from the
    // caller's own CALL, not from any prior destruction).
    var baseline_state = State.init(std.testing.allocator);
    defer baseline_state.deinit();
    try baseline_state.setCode(0xee, &caller_code);
    try baseline_state.setBalance(0x1, 10_000_000);
    var baseline_evm = Evm{ .allocator = std.testing.allocator, .state = &baseline_state };
    var baseline_tx = testTx();
    baseline_tx.to = 0xee;
    const baseline_result = try baseline_evm.executeTransaction(baseline_tx, 0x1);
    defer std.testing.allocator.free(baseline_result.return_data);

    try std.testing.expectEqual(Interpreter.Status.stopped, call_result.status);
    try std.testing.expectEqual(baseline_result.gas_used, call_result.gas_used);
}

test "clearing a storage slot earns a refund that reduces gas_used, when not capped" {
    const OpCode = @import("OpCode.zig").OpCode;
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1),  0,
        @intFromEnum(OpCode.PUSH1),  1,
        @intFromEnum(OpCode.SSTORE), @intFromEnum(OpCode.STOP),
    };
    // Padding calldata with nonzero bytes inflates the intrinsic cost well
    // past 30,000, so the refund (15,000) comfortably clears the "half of
    // gas used" cap and applies in full.
    const padding = [_]u8{1} ** 200;

    var cleared = State.init(std.testing.allocator);
    defer cleared.deinit();
    try cleared.setBalance(0x1, 10_000_000);
    try cleared.setCode(0xdd, &code);
    try cleared.setStorage(0xdd, 1, 99);
    var evm_cleared = Evm{ .allocator = std.testing.allocator, .state = &cleared };
    var tx = testTx();
    tx.to = 0xdd;
    tx.data = &padding;
    const cleared_result = try evm_cleared.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(cleared_result.return_data);

    var baseline = State.init(std.testing.allocator);
    defer baseline.deinit();
    try baseline.setBalance(0x1, 10_000_000);
    try baseline.setCode(0xdd, &code);
    var evm_baseline = Evm{ .allocator = std.testing.allocator, .state = &baseline };
    const baseline_result = try evm_baseline.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(baseline_result.return_data);

    try std.testing.expectEqual(Interpreter.Status.stopped, cleared_result.status);
    try std.testing.expectEqual(
        baseline_result.gas_used - gas.sstore_clear_refund,
        cleared_result.gas_used,
    );
}

test "the refund is capped at half of gas used" {
    const OpCode = @import("OpCode.zig").OpCode;
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1),  0,
        @intFromEnum(OpCode.PUSH1),  1,
        @intFromEnum(OpCode.SSTORE), @intFromEnum(OpCode.STOP),
    };

    // No padding this time: intrinsic + opcode cost here is far under
    // 30,000, so the flat 15,000 refund would exceed half of it. The cap
    // must clip it rather than applying it in full.
    var cleared = State.init(std.testing.allocator);
    defer cleared.deinit();
    try cleared.setBalance(0x1, 1_000_000);
    try cleared.setCode(0xdd, &code);
    try cleared.setStorage(0xdd, 1, 99);
    var evm_cleared = Evm{ .allocator = std.testing.allocator, .state = &cleared };
    var tx = testTx();
    tx.to = 0xdd;
    const cleared_result = try evm_cleared.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(cleared_result.return_data);

    var baseline = State.init(std.testing.allocator);
    defer baseline.deinit();
    try baseline.setBalance(0x1, 1_000_000);
    try baseline.setCode(0xdd, &code);
    var evm_baseline = Evm{ .allocator = std.testing.allocator, .state = &baseline };
    const baseline_result = try evm_baseline.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(baseline_result.return_data);

    const spent = baseline_result.gas_used;
    const refund_applied = spent - cleared_result.gas_used;
    try std.testing.expect(refund_applied < gas.sstore_clear_refund); // capped, not the full 15,000
    try std.testing.expect(refund_applied <= spent / gas.max_refund_denominator);
}

test "out-of-gas forfeits the entire gas limit, not just what was nominally spent" {
    const OpCode = @import("OpCode.zig").OpCode;
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1),  0,
        @intFromEnum(OpCode.PUSH1),  0,
        @intFromEnum(OpCode.RETURN),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 1_000_000);
    try state.setCode(0xdd, &code);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .coinbase = 0xcc } };
    var tx = testTx();
    tx.to = 0xdd;
    tx.gas_price = 10;
    tx.gas_limit = 1; // not enough for even the first PUSH1

    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);

    try std.testing.expectEqual(Interpreter.Status.out_of_gas, result.status);
    try std.testing.expectEqual(@as(u64, 1), result.gas_used);
    try std.testing.expectEqual(@as(u256, 1_000_000 - 10), state.getBalance(0x1));
    try std.testing.expectEqual(@as(u256, 10), state.getBalance(0xcc));
}

test "insufficient balance for gas fails the transaction after execution completes" {
    const OpCode = @import("OpCode.zig").OpCode;
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1),  0,
        @intFromEnum(OpCode.PUSH1),  0,
        @intFromEnum(OpCode.RETURN),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 5); // enough for value (0) but not gas
    try state.setCode(0xdd, &code);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .coinbase = 0xcc } };
    var tx = testTx();
    tx.to = 0xdd;
    tx.gas_price = 1_000_000;

    try std.testing.expectError(error.InsufficientBalance, evm.executeTransaction(tx, 0x1));
}

test "a sender that can afford the gas fee but not the value it sends is rejected" {
    // execution-specs' `process_transaction` asserts
    // `balance >= gas_fee + value`, so a block carrying this transaction is
    // invalid. Checking the fee alone let it through, charging gas and
    // silently dropping the transfer — which is how a real mainnet
    // divergence at block 6,831,202 stayed invisible until it surfaced
    // 32 blocks later as someone else's missing balance.
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    // Covers the 21000-wei fee with room to spare, but not fee plus value.
    try state.setBalance(0x1, 21_100);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .coinbase = 0xcc } };
    var tx = testTx();
    tx.to = 0xdd;
    tx.gas_limit = 21_000; // exactly the intrinsic cost of a plain transfer
    tx.gas_price = 1;
    tx.value = 200;

    try std.testing.expectError(error.InsufficientBalance, evm.executeTransaction(tx, 0x1));
    // Rejected outright: no gas debited, no nonce burned, nothing credited.
    try std.testing.expectEqual(@as(u256, 21_100), state.getBalance(0x1));
    try std.testing.expectEqual(@as(u64, 0), state.get(0x1).nonce);
    try std.testing.expectEqual(@as(u256, 0), state.getBalance(0xdd));
}

test "a sender holding exactly the gas fee plus the value it sends is accepted" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 21_200); // exactly 21000 fee + 200 value

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .coinbase = 0xcc } };
    var tx = testTx();
    tx.to = 0xdd;
    tx.gas_limit = 21_000; // exactly the intrinsic cost of a plain transfer
    tx.gas_price = 1;
    tx.value = 200;

    const result = try evm.executeTransaction(tx, 0x1);
    try std.testing.expect(result.status == .stopped);
    try std.testing.expectEqual(@as(u256, 200), state.getBalance(0xdd));
}

test "from Spurious Dragon on, an EIP-155 transaction signed for the wrong chain id is rejected" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 1000);

    // block.chain_id defaults to 1 (mainnet); v = 35 + chain_id*2 + {0,1},
    // so v = 43 encodes chain_id = 4, not 1.
    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = .spurious_dragon } };
    var tx = testTx();
    tx.to = 0xdd;
    tx.v = 43;

    try std.testing.expectError(error.WrongChainId, evm.executeTransaction(tx, 0x1));
}

test "from Spurious Dragon on, a legacy v (27/28) transaction is always accepted regardless of chain id" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 1000);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = .spurious_dragon } };
    var tx = testTx();
    tx.to = 0xdd;
    tx.v = 27;

    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);
    try std.testing.expectEqual(Interpreter.Status.stopped, result.status);
}

test "before Spurious Dragon, a wrong-chain-id v isn't rejected: the check doesn't exist yet" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 1000);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = .tangerine_whistle } };
    var tx = testTx();
    tx.to = 0xdd;
    tx.v = 43; // would encode chain_id = 4, mismatched with the default chain_id = 1

    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);
    try std.testing.expectEqual(Interpreter.Status.stopped, result.status);
}

test "a sender short on value alone is rejected even when the gas is free" {
    // Previously this reverted gracefully "so it fails just that
    // transaction, not the whole block". That leniency was wrong:
    // execution-specs' `process_transaction` requires
    // `balance >= gas_fee + value` and treats a block carrying such a
    // transaction as invalid. A zero gas price makes the fee vanish, so
    // `value` alone decides it.
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 10);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    var tx = testTx();
    tx.to = 0xdd;
    tx.value = 100;

    try std.testing.expectError(error.InsufficientBalance, evm.executeTransaction(tx, 0x1));
    // Rejected before anything is applied: the nonce does not advance.
    try std.testing.expectEqual(@as(u256, 10), state.getBalance(0x1));
    try std.testing.expectEqual(@as(u64, 0), state.get(0x1).nonce);
}

test "a contract whose constructor self-destructs leaves no account behind" {
    // Mainnet block 1,527,679 creates a contract whose init code ends in
    // CALLER SELFDESTRUCT, so it destroys itself before ever deploying. Real
    // chain erases it at transaction end and it exists at no block, ever.
    // With a zero endowment and no EIP-161 nonce to set, nothing materialised
    // the address before its constructor ran, so `destroyAccount` — which
    // no-ops on an account that isn't there — registered nothing, and the
    // `setCode` that follows a successful creation then made it permanent.
    const OpCode = @import("OpCode.zig").OpCode;
    const init_code = [_]u8{
        @intFromEnum(OpCode.CALLER),
        @intFromEnum(OpCode.SELFDESTRUCT),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 1_000_000);

    var evm = Evm{
        .allocator = std.testing.allocator,
        .state = &state,
        .block = .{ .coinbase = 0xcc, .fork = .homestead },
    };
    var tx = testTx();
    tx.to = null;
    tx.value = 0;
    tx.data = &init_code;

    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);

    const created = result.created_address.?;
    try std.testing.expect(!state.exists(created));
}

test "a reverting creation takes a nested CREATE2's deployed code with it, even to a pre-funded address" {
    // Mainnet block 7,306,818, tx 26: a creation's init code CREATE2s a
    // contract at an address someone had already sent ether to, that nested
    // creation succeeds and deploys code, then the outer init code REVERTs.
    // Real chain leaves the pre-funded address exactly as it was. zevm
    // restored its balance and storage through the journal but, with
    // `setCode` unjournaled, left the deployed code in place. A fresh
    // address would have hidden this: its `.created` entry makes the revert
    // delete the whole account. Only a pre-existing target exposes it.
    const OpCode = @import("OpCode.zig").OpCode;

    // Nested init code: deploy one byte of runtime code (STOP).
    const inner_init = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0x00,
        @intFromEnum(OpCode.PUSH1), 0x00,
        @intFromEnum(OpCode.MSTORE8),
        @intFromEnum(OpCode.PUSH1), 0x01,
        @intFromEnum(OpCode.PUSH1), 0x00,
        @intFromEnum(OpCode.RETURN),
    };
    const salt: u256 = 7;

    // Outer init code: put inner_init in memory, CREATE2 it, then REVERT.
    var outer: std.ArrayList(u8) = .empty;
    defer outer.deinit(std.testing.allocator);
    var word: [32]u8 = [_]u8{0} ** 32;
    @memcpy(word[32 - inner_init.len ..], &inner_init);
    try outer.append(std.testing.allocator, @intFromEnum(OpCode.PUSH32));
    try outer.appendSlice(std.testing.allocator, &word);
    try outer.appendSlice(std.testing.allocator, &.{
        @intFromEnum(OpCode.PUSH1), 0x00,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1), @intCast(salt),
        @intFromEnum(OpCode.PUSH1), @intCast(inner_init.len),
        @intFromEnum(OpCode.PUSH1), @intCast(32 - inner_init.len),
        @intFromEnum(OpCode.PUSH1), 0x00,
        @intFromEnum(OpCode.CREATE2),
        @intFromEnum(OpCode.POP),
        @intFromEnum(OpCode.PUSH1), 0x00,
        @intFromEnum(OpCode.PUSH1), 0x00,
        @intFromEnum(OpCode.REVERT),
    });

    const sender: Address = 0x1;
    const outer_address = try Interpreter.createAddress(std.testing.allocator, sender, 0);
    const target = Interpreter.create2Address(outer_address, salt, &inner_init);

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(sender, 10_000_000);
    try state.setBalance(target, 5_000_000_000_000_000); // pre-funded, like mainnet

    var evm = Evm{
        .allocator = std.testing.allocator,
        .state = &state,
        .block = .{ .coinbase = 0xcc, .fork = .constantinople },
    };
    var tx = testTx();
    tx.to = null;
    tx.data = outer.items;

    const result = try evm.executeTransaction(tx, sender);
    defer std.testing.allocator.free(result.return_data);
    try std.testing.expectEqual(Interpreter.Status.reverted, result.status);

    // The target is exactly as it was before: funded, uncoded, nonce 0.
    try std.testing.expect(state.exists(target));
    try std.testing.expectEqual(@as(usize, 0), state.getCode(target).len);
    try std.testing.expectEqual(@as(u256, 5_000_000_000_000_000), state.getBalance(target));
    try std.testing.expectEqual(@as(u64, 0), state.get(target).nonce);
    // And the reverted creation itself left nothing behind.
    try std.testing.expect(!state.exists(outer_address));
}

test "CREATE2 to an address that already has code forfeits all its gas" {
    // EIP-684: the creation fails "as if the first byte in the init code
    // were an invalid opcode", so the init code never runs and every bit of
    // gas handed to the creation is gone. Not the graceful push-0-and-refund
    // of the endowment and depth checks. Mainnet block 7,753,545 does this
    // deliberately: zevm ran the init code real chain had refused and came
    // out 333,570 gas light on the block.
    const OpCode = @import("OpCode.zig").OpCode;

    // Init code that would deploy one byte of runtime code, if it ever ran.
    const inner_init = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0x00,
        @intFromEnum(OpCode.PUSH1), 0x00,
        @intFromEnum(OpCode.MSTORE8),
        @intFromEnum(OpCode.PUSH1), 0x01,
        @intFromEnum(OpCode.PUSH1), 0x00,
        @intFromEnum(OpCode.RETURN),
    };
    const salt: u256 = 7;

    var outer: std.ArrayList(u8) = .empty;
    defer outer.deinit(std.testing.allocator);
    var word: [32]u8 = [_]u8{0} ** 32;
    @memcpy(word[32 - inner_init.len ..], &inner_init);
    try outer.append(std.testing.allocator, @intFromEnum(OpCode.PUSH32));
    try outer.appendSlice(std.testing.allocator, &word);
    try outer.appendSlice(std.testing.allocator, &.{
        @intFromEnum(OpCode.PUSH1), 0x00,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1), @intCast(salt),
        @intFromEnum(OpCode.PUSH1), @intCast(inner_init.len),
        @intFromEnum(OpCode.PUSH1), @intCast(32 - inner_init.len),
        @intFromEnum(OpCode.PUSH1), 0x00,
        @intFromEnum(OpCode.CREATE2),
        @intFromEnum(OpCode.STOP),
    });

    const caller: Address = 0xaa;
    const target = Interpreter.create2Address(caller, salt, &inner_init);

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(caller, outer.items);
    // The target is already occupied: this is the collision.
    try state.setCode(target, &.{@intFromEnum(OpCode.STOP)});

    var interp = try Interpreter.initCall(std.testing.allocator, outer.items, 1_000_000, .{
        .address = caller,
        .state = &state,
        .block = .{ .fork = .constantinople },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Interpreter.Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
    // Everything forwarded is forfeit, so only the 1/64th reservation is
    // left. A graceful failure would have refunded nearly all of it.
    try std.testing.expect(interp.gas_remaining < 20_000);
    // The occupied account is untouched.
    try std.testing.expectEqual(@as(usize, 1), state.getCode(target).len);
}

test "a CREATE2 collision still consumes the creator's nonce" {
    const OpCode = @import("OpCode.zig").OpCode;
    const inner_init = [_]u8{@intFromEnum(OpCode.STOP)};
    const salt: u256 = 3;
    const caller: Address = 0xaa;
    const target = Interpreter.create2Address(caller, salt, &inner_init);

    var code: std.ArrayList(u8) = .empty;
    defer code.deinit(std.testing.allocator);
    var word: [32]u8 = [_]u8{0} ** 32;
    word[31] = @intFromEnum(OpCode.STOP);
    try code.append(std.testing.allocator, @intFromEnum(OpCode.PUSH32));
    try code.appendSlice(std.testing.allocator, &word);
    try code.appendSlice(std.testing.allocator, &.{
        @intFromEnum(OpCode.PUSH1), 0x00,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1), @intCast(salt),
        @intFromEnum(OpCode.PUSH1), 0x01,
        @intFromEnum(OpCode.PUSH1), 0x1f,
        @intFromEnum(OpCode.PUSH1), 0x00,
        @intFromEnum(OpCode.CREATE2),
        @intFromEnum(OpCode.STOP),
    });

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(caller, code.items);
    try state.setNonce(caller, 5);
    try state.setCode(target, &.{@intFromEnum(OpCode.STOP)});

    var interp = try Interpreter.initCall(std.testing.allocator, code.items, 1_000_000, .{
        .address = caller,
        .state = &state,
        .block = .{ .fork = .constantinople },
    });
    defer interp.deinit();
    try interp.run();

    // The increment happens before the collision check and is outside
    // anything a revert undoes, same as every other failed creation.
    try std.testing.expectEqual(@as(u64, 6), state.get(caller).nonce);
}

test "processBlock with no transactions credits the flat block reward" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    try evm.processBlock(.{ .number = 10, .miner = 0xaa, .transactions = &.{} });

    try std.testing.expectEqual(@as(u256, 5_000_000_000_000_000_000), state.getBalance(0xaa));
}

test "processBlock credits no block reward from the Merge on (EIP-3675)" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    try evm.processBlock(.{ .number = 15_537_393, .miner = 0xaa, .transactions = &.{} });
    try std.testing.expectEqual(@as(u256, 2_000_000_000_000_000_000), state.getBalance(0xaa));
    try evm.processBlock(.{ .number = 15_537_394, .miner = 0xbb, .transactions = &.{} });
    try std.testing.expectEqual(@as(u256, 0), state.getBalance(0xbb));
}

test "processBlock credits the reduced 3 ETH block reward from Byzantium on" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    try evm.processBlock(.{ .number = 4_370_000, .miner = 0xaa, .transactions = &.{} });

    try std.testing.expectEqual(@as(u256, 3_000_000_000_000_000_000), state.getBalance(0xaa));
}

test "processBlock credits the reduced 2 ETH block reward from Constantinople on" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    // EIP-1234 cut the reward again at Constantinople (mainnet 7,280,000).
    try evm.processBlock(.{ .number = 7_280_000, .miner = 0xaa, .transactions = &.{} });

    try std.testing.expectEqual(@as(u256, 2_000_000_000_000_000_000), state.getBalance(0xaa));
}

test "processBlock still pays 3 ETH on the last block before Constantinople" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    try evm.processBlock(.{ .number = 7_279_999, .miner = 0xaa, .transactions = &.{} });

    try std.testing.expectEqual(@as(u256, 3_000_000_000_000_000_000), state.getBalance(0xaa));
}

test "processBlock credits Constantinople's uncle rewards and nephew bonus off the reduced 2 ETH reward" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    try evm.processBlock(.{
        .number = 7_280_000,
        .miner = 0xaa,
        .transactions = &.{},
        .uncles = &.{.{ .number = 7_279_998, .miner = 0xbb }},
    });

    // Uncle two blocks back: 2 ETH * (8 - 2) / 8.
    try std.testing.expectEqual(@as(u256, 1_500_000_000_000_000_000), state.getBalance(0xbb));
    // Miner: 2 ETH plus a 2/32 nephew bonus for including it.
    try std.testing.expectEqual(
        @as(u256, 2_000_000_000_000_000_000 + 2_000_000_000_000_000_000 / 32),
        state.getBalance(0xaa),
    );
}

test "processBlock credits Byzantium's uncle rewards and nephew bonus off the reduced 3 ETH reward" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    try evm.processBlock(.{
        .number = 4_370_000,
        .miner = 0xaa,
        .transactions = &.{},
        .uncles = &.{.{ .number = 4_369_998, .miner = 0xbb }}, // distance = 2
    });

    // uncle: 3 ETH * (8 - 2) / 8 = 2.25 ETH
    try std.testing.expectEqual(@as(u256, 2_250_000_000_000_000_000), state.getBalance(0xbb));
    // miner: 3 ETH + 3 ETH/32 nephew bonus = 3.09375 ETH
    try std.testing.expectEqual(@as(u256, 3_093_750_000_000_000_000), state.getBalance(0xaa));
}

test "processBlock applies the DAO fork's irregular state transition at exactly block 1,920,000" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(DaoFork.accounts[0], 4200);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    try evm.processBlock(.{ .number = 1_920_000, .miner = 0xaa, .transactions = &.{} });

    try std.testing.expectEqual(@as(u256, 0), state.getBalance(DaoFork.accounts[0]));
    try std.testing.expectEqual(@as(u256, 4200), state.getBalance(DaoFork.recovery));
}

test "the DAO fork's state transition doesn't apply to any other block" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(DaoFork.accounts[0], 4200);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    try evm.processBlock(.{ .number = 1_919_999, .miner = 0xaa, .transactions = &.{} });

    try std.testing.expectEqual(@as(u256, 4200), state.getBalance(DaoFork.accounts[0]));
    try std.testing.expectEqual(@as(u256, 0), state.getBalance(DaoFork.recovery));
}

test "processBlock runs its transactions before crediting the reward" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 1000);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    var tx = testTx();
    tx.to = 0xdd;
    tx.value = 100;

    try evm.processBlock(.{
        .number = 10,
        .miner = 0xaa,
        .transactions = &.{.{ .tx = tx, .from = 0x1 }},
    });

    try std.testing.expectEqual(@as(u256, 900), state.getBalance(0x1));
    try std.testing.expectEqual(@as(u256, 100), state.getBalance(0xdd));
    try std.testing.expectEqual(@as(u256, 5_000_000_000_000_000_000), state.getBalance(0xaa));
}

test "processBlock credits uncle rewards and the nephew bonus" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    try evm.processBlock(.{
        .number = 10,
        .miner = 0xaa,
        .transactions = &.{},
        .uncles = &.{.{ .number = 8, .miner = 0xbb }}, // distance = 2
    });

    // uncle: 5 ETH * (8 - 2) / 8 = 3.75 ETH
    try std.testing.expectEqual(@as(u256, 3_750_000_000_000_000_000), state.getBalance(0xbb));
    // miner: 5 ETH + 5 ETH/32 nephew bonus = 5.15625 ETH
    try std.testing.expectEqual(@as(u256, 5_156_250_000_000_000_000), state.getBalance(0xaa));
}

test "processBlock credits its reward without journaling it" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    const cp = state.checkpoint();
    try evm.processBlock(.{ .number = 10, .miner = 0xaa, .transactions = &.{} });

    try std.testing.expectEqual(@as(u256, 5_000_000_000_000_000_000), state.getBalance(0xaa));
    try std.testing.expectEqual(cp, state.checkpoint()); // journal untouched
}

test "processBlock exposes its block context to the transactions it runs" {
    // callee stores NUMBER in slot 0, since processBlock discards return_data.
    const OpCode = @import("OpCode.zig").OpCode;
    const code = [_]u8{
        @intFromEnum(OpCode.NUMBER),
        @intFromEnum(OpCode.PUSH1),
        0,
        @intFromEnum(OpCode.SSTORE),
        @intFromEnum(OpCode.STOP),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xdd, &code);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    var tx = testTx();
    tx.to = 0xdd;

    try evm.processBlock(.{
        .number = 46147,
        .miner = 0xaa,
        .transactions = &.{.{ .tx = tx, .from = 0x1 }},
    });

    try std.testing.expectEqual(@as(u256, 46147), state.getStorage(0xdd, 0));
}

test "EIP-2930: an access list costs intrinsic gas and makes its entries start warm" {
    // 0xdd's code: PUSH1 1, SLOAD, POP, STOP.
    const code = [_]u8{ 0x60, 0x01, 0x54, 0x50, 0x00 };
    const keys = [_]u256{1};
    const list = [_]AccessListEntry{.{ .address = 0xdd, .storage_keys = &keys }};

    for ([_]bool{ false, true }) |with_list| {
        var state = State.init(std.testing.allocator);
        defer state.deinit();
        try state.setBalance(0x1, 1000);
        try state.setCode(0xdd, &code);
        state.finalizeTransaction();

        var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
        evm.block.fork = .berlin;
        var tx = testTx();
        tx.to = 0xdd;
        if (with_list) tx.access_list = &list;

        const result = try evm.executeTransaction(tx, 0x1);
        defer std.testing.allocator.free(result.return_data);
        try std.testing.expectEqual(Interpreter.Status.stopped, result.status);

        // PUSH1 + POP either way; the SLOAD is cold (2100) without the list
        // and warm (100) with it, which costs 2400 + 1900 up front.
        const expected: u64 = if (with_list) 21000 + 2400 + 1900 + 3 + 100 + 2 else 21000 + 3 + 2100 + 2;
        try std.testing.expectEqual(expected, result.gas_used);
    }
}

test "EIP-1559: the base fee is burned, only the priority fee reaches the miner" {
    // (max_fee, tip) -> what is actually paid per gas, with a base fee of 10.
    const cases = [_]struct { max_fee: u256, tip: u256, paid: u256 }{
        .{ .max_fee = 100, .tip = 3, .paid = 13 }, // tip fits under the cap
        .{ .max_fee = 12, .tip = 5, .paid = 12 }, // cap leaves room for only 2 of the tip
    };
    for (cases) |c| {
        var state = State.init(std.testing.allocator);
        defer state.deinit();
        const funds: u256 = 21000 * c.max_fee;
        try state.setBalance(0x1, funds);

        var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
        evm.block.fork = .london;
        evm.block.base_fee = 10;
        evm.block.coinbase = 0xc0;
        var tx = testTx();
        tx.to = 0xdd;
        tx.gas_limit = 21000;
        tx.gas_price = c.max_fee;
        tx.max_priority_fee = c.tip;

        const result = try evm.executeTransaction(tx, 0x1);
        defer std.testing.allocator.free(result.return_data);
        try std.testing.expectEqual(@as(u64, 21000), result.gas_used);
        try std.testing.expectEqual(funds - 21000 * c.paid, state.getBalance(0x1));
        try std.testing.expectEqual(21000 * (c.paid - 10), state.getBalance(0xc0));
    }
}

test "EIP-1559: a transaction that cannot cover the base fee is invalid" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 1_000_000_000);
    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    evm.block.fork = .london;
    evm.block.base_fee = 10;

    var legacy = testTx();
    legacy.to = 0xdd;
    legacy.gas_price = 9;
    try std.testing.expectError(error.GasPriceBelowBaseFee, evm.executeTransaction(legacy, 0x1));

    var fee_market = testTx();
    fee_market.to = 0xdd;
    fee_market.gas_price = 9;
    fee_market.max_priority_fee = 1;
    try std.testing.expectError(error.MaxFeeBelowBaseFee, evm.executeTransaction(fee_market, 0x1));

    fee_market.gas_price = 20;
    fee_market.max_priority_fee = 21;
    try std.testing.expectError(error.PriorityFeeAboveMaxFee, evm.executeTransaction(fee_market, 0x1));
}

test "EIP-3529 caps the refund at a fifth of gas used instead of a half" {
    // 21000 intrinsic + 50000 executed = 71000 spent, with a refund of 50000.
    try std.testing.expectEqual(@as(u64, 71000 - 71000 / 2), gasUsed(.stopped, 50000, 50000, 0, 100000, 21000, .berlin));
    try std.testing.expectEqual(@as(u64, 71000 - 71000 / 5), gasUsed(.stopped, 50000, 50000, 0, 100000, 21000, .london));
    // A refund under the cap is paid in full either way.
    try std.testing.expectEqual(@as(u64, 71000 - 1000), gasUsed(.stopped, 50000, 1000, 0, 100000, 21000, .london));
}

test "EIP-3541: deployed code may not start with 0xEF from London on" {
    // Init code: MSTORE8 0xEF at 0, RETURN one byte.
    const init = [_]u8{ 0x60, 0xef, 0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0xf3 };
    for ([_]Fork{ .berlin, .london }) |fork| {
        var state = State.init(std.testing.allocator);
        defer state.deinit();
        try state.setBalance(0x1, 1000);
        var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
        evm.block.fork = fork;
        var tx = testTx();
        tx.data = &init;

        const result = try evm.executeTransaction(tx, 0x1);
        defer std.testing.allocator.free(result.return_data);
        if (fork == .london) {
            try std.testing.expectEqual(Interpreter.Status.out_of_gas, result.status);
            try std.testing.expectEqual(tx.gas_limit, result.gas_used);
            try std.testing.expectEqual(@as(usize, 0), state.getCode(result.created_address.?).len);
        } else {
            try std.testing.expectEqual(Interpreter.Status.stopped, result.status);
            try std.testing.expectEqualSlices(u8, &.{0xef}, state.getCode(result.created_address.?));
        }
    }
}

test "EIP-3651: the coinbase starts warm from Shanghai on" {
    const OpCode = @import("OpCode.zig").OpCode;
    const code = [_]u8{ @intFromEnum(OpCode.COINBASE), @intFromEnum(OpCode.BALANCE), @intFromEnum(OpCode.STOP) };
    var used: [2]u64 = undefined;
    for ([_]Fork{ .merge, .shanghai }, &used) |fork, *u| {
        var state = State.init(std.testing.allocator);
        defer state.deinit();
        try state.setCode(0xdd, &code);
        var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = fork, .coinbase = 0xcc } };
        var tx = testTx();
        tx.to = 0xdd;
        const result = try evm.executeTransaction(tx, 0x1);
        defer std.testing.allocator.free(result.return_data);
        u.* = result.gas_used;
    }
    // A cold account access (2600) against a warm one (100).
    try std.testing.expectEqual(used[0] - 2500, used[1]);
}

test "EIP-3860: a contract-creation transaction's init code pays per word from Shanghai on" {
    const init_code = [_]u8{0} ** 64; // STOPs at once
    var used: [2]u64 = undefined;
    for ([_]Fork{ .merge, .shanghai }, &used) |fork, *u| {
        var state = State.init(std.testing.allocator);
        defer state.deinit();
        var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = fork } };
        var tx = testTx();
        tx.data = &init_code;
        const result = try evm.executeTransaction(tx, 0x1);
        defer std.testing.allocator.free(result.return_data);
        u.* = result.gas_used;
    }
    try std.testing.expectEqual(used[0] + 2 * gas.initcode_word, used[1]);
}

test "EIP-3860: a contract-creation transaction over max_initcode_size is invalid from Shanghai on" {
    const init_code = [_]u8{0} ** (Interpreter.max_initcode_size + 1);
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = .shanghai } };
    var tx = testTx();
    tx.data = &init_code;
    try std.testing.expectError(error.InitcodeTooLarge, evm.executeTransaction(tx, 0x1));
}

test "EIP-4895: withdrawals credit their amount in gwei, and a zero amount creates nothing" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0xa1, 5);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    try evm.processBlock(.{
        .number = 17_034_870,
        .miner = 0xaa,
        .transactions = &.{},
        .withdrawals = &.{
            .{ .address = 0xa1, .amount = 3 },
            .{ .address = 0xa2, .amount = 0 },
            .{ .address = 0xa1, .amount = 1 },
        },
    });
    try std.testing.expectEqual(@as(u256, 5 + 4_000_000_000), state.getBalance(0xa1));
    try std.testing.expect(!state.exists(0xa2));
    try std.testing.expectEqual(@as(u256, 0), state.getBalance(0xaa));
}

test "EIP-4844: a blob transaction pays its blob gas at the blob base fee, all of it burned" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 1_000_000_000_000);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .coinbase = 0xcc, .fork = .cancun, .blob_base_fee = 3 } };
    var tx = testTx();
    tx.to = 0xdd;
    tx.gas_limit = 21_000;
    tx.max_fee_per_blob_gas = 10;
    tx.blob_versioned_hashes = &.{ 0x01aa, 0x01bb };

    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);
    try std.testing.expectEqual(Interpreter.Status.stopped, result.status);
    // Two blobs at 3 wei per blob gas: what the sender loses, and nobody gains.
    try std.testing.expectEqual(@as(u256, 1_000_000_000_000 - 2 * gas.blob_gas_per_blob * 3), state.getBalance(0x1));
    try std.testing.expectEqual(@as(u256, 0), state.getBalance(0xcc));
}

test "EIP-4844: a blob fee cap below the blob base fee is invalid, and the balance check counts the cap" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = .cancun, .blob_base_fee = 3 } };
    var tx = testTx();
    tx.to = 0xdd;
    tx.gas_limit = 21_000;
    tx.blob_versioned_hashes = &.{0x01aa};

    tx.max_fee_per_blob_gas = 2;
    try state.setBalance(0x1, 1_000_000_000_000);
    try std.testing.expectError(error.BlobFeeBelowBaseFee, evm.executeTransaction(tx, 0x1));

    // Enough for the blob gas at the base fee, not at the cap of 10.
    tx.max_fee_per_blob_gas = 10;
    try state.setBalance(0x2, gas.blob_gas_per_blob * 3);
    try std.testing.expectError(error.InsufficientBalance, evm.executeTransaction(tx, 0x2));
}

test "EIP-4788: from Cancun on, processBlock first calls the beacon roots contract from the system address" {
    const OpCode = @import("OpCode.zig").OpCode;
    // Stores the caller in slot 0 and the calldata word in slot 1.
    const code = [_]u8{
        @intFromEnum(OpCode.CALLER),       @intFromEnum(OpCode.PUSH0),        @intFromEnum(OpCode.SSTORE),
        @intFromEnum(OpCode.PUSH0),        @intFromEnum(OpCode.CALLDATALOAD), @intFromEnum(OpCode.PUSH1),
        1,                                 @intFromEnum(OpCode.SSTORE),       @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(beacon_roots_address, &code);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    try evm.processBlock(.{ .number = 19_426_587, .miner = 0xaa, .transactions = &.{}, .parent_beacon_block_root = 0x1234 });
    try std.testing.expectEqual(@as(u256, system_address), state.getStorage(beacon_roots_address, 0));
    try std.testing.expectEqual(@as(u256, 0x1234), state.getStorage(beacon_roots_address, 1));
    // A system call: no gas toward the block, no account for the sender.
    try std.testing.expectEqual(@as(u64, 0), evm.block_gas_used);
    try std.testing.expect(!state.exists(system_address));

    // Not before Cancun.
    try evm.processBlock(.{ .number = 19_426_586, .miner = 0xaa, .transactions = &.{}, .parent_beacon_block_root = 0x5678 });
    try std.testing.expectEqual(@as(u256, 0x1234), state.getStorage(beacon_roots_address, 1));
}

test "from Cancun on, the point evaluation precompile starts warm" {
    const OpCode = @import("OpCode.zig").OpCode;
    const code = [_]u8{ @intFromEnum(OpCode.PUSH1), 0x0a, @intFromEnum(OpCode.BALANCE), @intFromEnum(OpCode.STOP) };
    var gas_used: [2]u64 = undefined;
    for ([_]Fork{ .shanghai, .cancun }, &gas_used) |fork, *used| {
        var state = State.init(std.testing.allocator);
        defer state.deinit();
        try state.setCode(0xdd, &code);
        var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = fork } };
        var tx = testTx();
        tx.to = 0xdd;
        const result = try evm.executeTransaction(tx, 0x1);
        defer std.testing.allocator.free(result.return_data);
        used.* = result.gas_used;
    }
    try std.testing.expectEqual(gas.cold_account_access_2929 - gas.warm_storage_read_2929, gas_used[0] - gas_used[1]);
}

// libsecp256k1's signing half, only needed to produce test authorizations.
extern fn secp256k1_context_create(flags: c_uint) ?*anyopaque;
extern fn secp256k1_context_destroy(ctx: *anyopaque) void;
extern fn secp256k1_ecdsa_sign_recoverable(ctx: *anyopaque, sig: *[65]u8, msghash32: *const [32]u8, seckey: *const [32]u8, noncefp: ?*const anyopaque, ndata: ?*const anyopaque) c_int;
extern fn secp256k1_ecdsa_recoverable_signature_serialize_compact(ctx: *anyopaque, output64: *[64]u8, recid: *c_int, sig: *const [65]u8) c_int;

/// A chain-1 authorization for `address` at `nonce` (below 0x80), signed with
/// `key`, and the authority that signed it. The signed message is built by
/// hand rather than with `Rlp`, so a mistake in `recoverAuthority`'s
/// encoding recovers a different authority and the tests notice.
fn signTestAuthorization(key: [32]u8, address: Address, nonce: u8) !struct { auth: Authorization, authority: Address } {
    std.debug.assert(nonce < 0x80);
    // 0x05 || rlp([1, address, nonce]): a 23-byte list payload.
    var preimage: [25]u8 = undefined;
    preimage[0] = 0x05;
    preimage[1] = 0xc0 + 23;
    preimage[2] = 0x01;
    preimage[3] = 0x80 + 20;
    std.mem.writeInt(u160, preimage[4..24], address, .big);
    preimage[24] = if (nonce == 0) 0x80 else nonce;
    var hash: [32]u8 = undefined;
    std.mem.writeInt(u256, &hash, keccak256(&preimage), .big);

    const ctx = secp256k1_context_create(1) orelse return error.ContextFailed;
    defer secp256k1_context_destroy(ctx);
    var sig: [65]u8 = undefined;
    if (secp256k1_ecdsa_sign_recoverable(ctx, &sig, &hash, &key, null, null) != 1) return error.SignFailed;
    var compact: [64]u8 = undefined;
    var recid: c_int = undefined;
    _ = secp256k1_ecdsa_recoverable_signature_serialize_compact(ctx, &compact, &recid, &sig);
    const recovered = Precompiles.ecrecover(hash, 27 + @as(u8, @intCast(recid)), compact[0..32].*, compact[32..64].*) orelse return error.RecoverFailed;
    return .{
        .auth = .{
            .chain_id = 1,
            .address = address,
            .nonce = nonce,
            .y_parity = @intCast(recid),
            .r = std.mem.readInt(u256, compact[0..32], .big),
            .s = std.mem.readInt(u256, compact[32..64], .big),
        },
        .authority = std.mem.readInt(u160, &recovered, .big),
    };
}

const test_key = [_]u8{0x11} ** 32;

test "EIP-7702: a set-code transaction delegates its authority, and calling it runs the delegate's code" {
    const OpCode = @import("OpCode.zig").OpCode;
    // Stores 1 in slot 0 of whichever account runs it.
    const delegate_code = [_]u8{ @intFromEnum(OpCode.PUSH1), 1, @intFromEnum(OpCode.PUSH0), @intFromEnum(OpCode.SSTORE), @intFromEnum(OpCode.STOP) };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xdd, &delegate_code);
    const signed = try signTestAuthorization(test_key, 0xdd, 0);
    // An authority that already exists earns back part of the authorization's cost.
    try state.setBalance(signed.authority, 1);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = .prague } };
    var tx = testTx();
    tx.to = signed.authority;
    tx.authorization_list = &.{signed.auth};
    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);

    try std.testing.expectEqual(Interpreter.Status.stopped, result.status);
    var indicator: [23]u8 = undefined;
    indicator[0..3].* = .{ 0xef, 0x01, 0x00 };
    std.mem.writeInt(u160, indicator[3..23], 0xdd, .big);
    try std.testing.expectEqualSlices(u8, &indicator, state.getCode(signed.authority));
    try std.testing.expectEqual(@as(u64, 1), state.get(signed.authority).nonce);
    try std.testing.expectEqual(@as(u256, 1), state.getStorage(signed.authority, 0));
    try std.testing.expectEqual(@as(u256, 0), state.getStorage(0xdd, 0));
    // Intrinsic 21000 + 25000 per authorization, then PUSH1 + PUSH0 + a cold
    // zero-to-nonzero SSTORE, less the 12500 refund (under the 1/5 cap).
    const spent: u64 = 21000 + 25000 + 3 + 2 + 22100;
    try std.testing.expectEqual(spent - 12500, result.gas_used);
}

test "EIP-7702: authorizations that fail a check are skipped but still paid for" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    const wrong_nonce = try signTestAuthorization(test_key, 0xdd, 5);
    var wrong_chain = wrong_nonce;
    wrong_chain.auth.chain_id = 2;
    wrong_chain.auth.nonce = 0;
    try state.setBalance(wrong_nonce.authority, 1);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = .prague } };
    var tx = testTx();
    tx.to = wrong_nonce.authority;
    tx.authorization_list = &.{ wrong_nonce.auth, wrong_chain.auth };
    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);

    try std.testing.expectEqual(@as(usize, 0), state.getCode(wrong_nonce.authority).len);
    try std.testing.expectEqual(@as(u64, 0), state.get(wrong_nonce.authority).nonce);
    try std.testing.expectEqual(@as(u64, 21000 + 2 * 25000), result.gas_used);
}

test "EIP-7702: an authorization for the zero address clears the delegation" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    const signed = try signTestAuthorization(test_key, 0, 0);
    try state.setDelegation(signed.authority, &(.{ 0xef, 0x01, 0x00 } ++ [_]u8{0xdd} ** 20));

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = .prague } };
    var tx = testTx();
    tx.to = 0xee;
    tx.authorization_list = &.{signed.auth};
    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);

    try std.testing.expectEqual(@as(usize, 0), state.getCode(signed.authority).len);
    try std.testing.expectEqual(@as(u64, 1), state.get(signed.authority).nonce);
}

test "EIP-7702: CALL to a delegated account runs the delegate's code and pays to load it" {
    const OpCode = @import("OpCode.zig").OpCode;
    const delegate_code = [_]u8{ @intFromEnum(OpCode.PUSH1), 1, @intFromEnum(OpCode.PUSH0), @intFromEnum(OpCode.SSTORE), @intFromEnum(OpCode.STOP) };
    const authority: Address = 0xaa;
    // CALL(gas, authority, 0, 0, 0, 0, 0).
    const caller_code = [_]u8{@intFromEnum(OpCode.PUSH0)} ** 5 ++ [_]u8{ @intFromEnum(OpCode.PUSH1), 0xaa, @intFromEnum(OpCode.GAS), @intFromEnum(OpCode.CALL), @intFromEnum(OpCode.STOP) };
    const indicator = [_]u8{ 0xef, 0x01, 0x00 } ++ [_]u8{0} ** 19 ++ [_]u8{0xdd};

    var gas_used: [2]u64 = undefined;
    for ([_]bool{ true, false }, &gas_used) |delegated, *used| {
        var state = State.init(std.testing.allocator);
        defer state.deinit();
        try state.setCode(0xcc, &caller_code);
        try state.setCode(0xdd, &delegate_code);
        if (delegated) try state.setDelegation(authority, &indicator) else try state.setCode(authority, &delegate_code);
        var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = .prague } };
        var tx = testTx();
        tx.to = 0xcc;
        const result = try evm.executeTransaction(tx, 0x1);
        defer std.testing.allocator.free(result.return_data);
        try std.testing.expectEqual(@as(u256, 1), state.getStorage(authority, 0));
        used.* = result.gas_used;
    }
    // The same code either way; the delegated call also loads 0xdd, cold.
    try std.testing.expectEqual(gas.cold_account_access_2929, gas_used[0] - gas_used[1]);
}

test "EIP-7623: from Prague on, a transaction pays at least the calldata floor" {
    const data = [_]u8{1} ** 1000;
    var gas_used: [2]u64 = undefined;
    for ([_]Fork{ .cancun, .prague }, &gas_used) |fork, *used| {
        var state = State.init(std.testing.allocator);
        defer state.deinit();
        var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = fork } };
        var tx = testTx();
        tx.to = 0xdd;
        tx.data = &data;
        const result = try evm.executeTransaction(tx, 0x1);
        defer std.testing.allocator.free(result.return_data);
        used.* = result.gas_used;
    }
    try std.testing.expectEqual(@as(u64, 21000 + 16 * 1000), gas_used[0]);
    try std.testing.expectEqual(@as(u64, 21000 + 10 * 4 * 1000), gas_used[1]);

    // A gas limit that covers the old intrinsic cost but not the floor is invalid.
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .fork = .prague } };
    var tx = testTx();
    tx.to = 0xdd;
    tx.data = &data;
    tx.gas_limit = 60_000;
    try std.testing.expectError(error.GasLimitBelowCalldataFloor, evm.executeTransaction(tx, 0x1));
}

test "Prague's system calls: the parent hash before the transactions, the request queues after" {
    const OpCode = @import("OpCode.zig").OpCode;
    // Stores the calldata word in slot 0 and the caller in slot 1.
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH0),  @intFromEnum(OpCode.CALLDATALOAD), @intFromEnum(OpCode.PUSH0),
        @intFromEnum(OpCode.SSTORE), @intFromEnum(OpCode.CALLER),       @intFromEnum(OpCode.PUSH1),
        1,                           @intFromEnum(OpCode.SSTORE),       @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    for ([_]Address{ history_storage_address, withdrawal_request_address, consolidation_request_address }) |address| {
        try state.setCode(address, &code);
    }
    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    try evm.processBlock(.{ .number = 22_431_084, .miner = 0xaa, .transactions = &.{}, .parent_hash = 0xabcd });
    try std.testing.expectEqual(@as(u256, 0xabcd), state.getStorage(history_storage_address, 0));
    for ([_]Address{ history_storage_address, withdrawal_request_address, consolidation_request_address }) |address| {
        try std.testing.expectEqual(@as(u256, system_address), state.getStorage(address, 1));
    }
    // The request queues are called with no calldata.
    try std.testing.expectEqual(@as(u256, 0), state.getStorage(withdrawal_request_address, 0));
    try std.testing.expectEqual(@as(u64, 0), evm.block_gas_used);

    // Unlike the history contract, a missing request contract invalidates the block.
    var bare = State.init(std.testing.allocator);
    defer bare.deinit();
    var bare_evm = Evm{ .allocator = std.testing.allocator, .state = &bare };
    try std.testing.expectError(error.SystemCallFailed, bare_evm.processBlock(.{ .number = 22_431_084, .miner = 0xaa, .transactions = &.{} }));
}
