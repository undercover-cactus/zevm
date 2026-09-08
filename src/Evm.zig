//! Executes a decoded `Transaction` against a `State`.
//!
//! Only Frontier through Byzantium are implemented. `processBlock` panics
//! on any block from a later fork (see `Fork`) instead of silently
//! applying stale rules.

const std = @import("std");
const Address = @import("Address.zig").Address;
const State = @import("State.zig");
const Interpreter = @import("Interpreter.zig");
const Transaction = @import("Transaction.zig").Transaction;
const Block = @import("Block.zig").Block;
const Fork = @import("Fork.zig").Fork;
const DaoFork = @import("DaoFork.zig");
const gas = @import("gas.zig");
const Precompiles = @import("Precompiles.zig");

allocator: std.mem.Allocator,
state: *State,
/// The block currently being processed. Set automatically by
/// `processBlock`; set it directly if calling `executeTransaction` on its
/// own and the code reads block-context opcodes.
block: Interpreter.BlockContext = .{},
/// The transaction currently executing, set by `executeTransaction` itself.
tx: Interpreter.TxContext = .{},

const Evm = @This();

/// Miner reward for a block with no uncles: Frontier's flat 5 ETH, cut to
/// 3 ETH by EIP-649 at Byzantium.
fn blockReward(fork: Fork) u256 {
    return if (fork.atLeast(.byzantium)) 3_000_000_000_000_000_000 else 5_000_000_000_000_000_000;
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

pub fn executeTransaction(self: *Evm, tx: Transaction, from: Address) !Result {
    // DEBUG: resets Interpreter's step-count safety valve (see its doc
    // comment) so it measures *this* transaction's total, not a running
    // total across the whole replay.
    Interpreter.debug_total_step_count = 0;

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
    const gas_fee = @as(u256, tx.gas_limit) * tx.gas_price;
    const upfront_cost = gas_fee + tx.value;
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
    try self.state.setBalance(from, balance_before - gas_fee);

    // A transaction's nonce always advances, whether it succeeds, reverts,
    // or fails outright.
    try self.state.setNonce(from, current_nonce + 1);

    self.tx = .{ .origin = from, .gas_price = tx.gas_price };

    const result = if (tx.to) |to|
        try self.call(tx.value, tx.data, tx.gas_limit, from, to)
    else
        try self.create(tx.nonce, tx.value, tx.data, tx.gas_limit, from);

    // Refund unused gas, then pay the miner, via `creditBalance` (unjournaled,
    // like block rewards): a transaction's gas fee is never undone by a revert.
    const unused = @as(u256, tx.gas_limit - result.gas_used) * tx.gas_price;
    if (unused != 0) try self.state.creditBalance(from, unused);
    if (result.gas_used != 0 and tx.gas_price != 0) {
        try self.state.creditBalance(self.block.coinbase, @as(u256, result.gas_used) * tx.gas_price);
    }

    // Any `SELFDESTRUCT` that survived to here (a reverted one never
    // reaches `pending_destructions` in the first place) is now permanent:
    // erase those accounts from state entirely, same as real Ethereum does
    // at the end of a transaction.
    self.state.finalizeTransaction();

    return result;
}

/// Runs every transaction in `block`, then credits block and uncle rewards.
/// Per-transaction `Result`s aren't surfaced; call `executeTransaction`
/// directly if you need them.
pub fn processBlock(self: *Evm, block: Block) !void {
    State.debug_block_number = block.number;
    const fork = Fork.at(block.number);
    if (fork.atLeast(.constantinople)) {
        std.debug.panic(
            "block {d} is past Byzantium (fork: {s}): this Evm only implements up to Byzantium's rules",
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
    };

    for (block.transactions) |entry| {
        const result = try self.executeTransaction(entry.tx, entry.from);
        self.allocator.free(result.return_data);
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
}

fn call(self: *Evm, value: u256, data: []const u8, gas_limit: u64, from: Address, to: Address) !Result {
    const cp = self.state.checkpoint();

    // The intrinsic cost is paid before any code runs; real Ethereum
    // forfeits the whole limit if gas_limit can't cover it.
    const intrinsic = gas.intrinsicCost(data);
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
            .gas_used = intrinsic,
        };
    }

    const execution_gas_limit = gas_limit - intrinsic;

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
            .gas_used = gasUsed(status, result.gas_remaining, 0, execution_gas_limit, intrinsic),
        };
    }

    const code = self.state.getCode(to);

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
            .gas_used = intrinsic,
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
        .jumpdest = self.state.getJumpdest(to),
    });
    defer interp.deinit();
    try interp.run();

    if (self.block.fork.atLeast(.spurious_dragon)) try self.state.markTouchedIfEmpty(to);
    if (interp.status != .stopped) self.state.revertTo(cp);

    return .{
        .status = interp.status,
        .return_data = try self.allocator.dupe(u8, interp.return_data),
        .gas_used = gasUsed(interp.status, interp.gas_remaining, interp.refund, execution_gas_limit, intrinsic),
    };
}

/// The gas actually charged: `intrinsic` plus what the interpreter spent,
/// minus any refund. The refund cap applies to the total including
/// intrinsic (matching real Ethereum, so padding calldata can't dodge it),
/// and only applies on `.stopped`. Any other halt forfeits it. Exceptional
/// halts (`.out_of_gas`, `.invalid_opcode`, `.invalid_jump`,
/// `.stack_overflow`, `.stack_underflow`) forfeit the entire limit;
/// `.reverted` is the exception that only spends what actually ran.
fn gasUsed(status: Interpreter.Status, gas_remaining: u64, refund: u64, execution_gas_limit: u64, intrinsic: u64) u64 {
    switch (status) {
        .out_of_gas, .invalid_opcode, .invalid_jump, .stack_overflow, .stack_underflow => return execution_gas_limit + intrinsic,
        else => {},
    }
    const spent = intrinsic + (execution_gas_limit - gas_remaining);
    if (status != .stopped) return spent;
    return spent - @min(refund, spent / gas.max_refund_denominator);
}

fn create(self: *Evm, nonce: u64, value: u256, data: []const u8, gas_limit: u64, from: Address) !Result {
    const new_address = try Interpreter.createAddress(self.allocator, from, nonce);
    const cp = self.state.checkpoint();

    // EIP-161, from Spurious Dragon on: a freshly created contract's own
    // nonce starts at 1, not 0 (mirrors `Interpreter.createOp`'s nested
    // `CREATE`/`CREATE2`).
    if (self.block.fork.atLeast(.spurious_dragon)) try self.state.setNonce(new_address, 1);

    // EIP-2 (Homestead): a top-level contract-creation transaction pays an
    // extra `create_base` surcharge on top of the usual intrinsic cost.
    // Nested `CREATE`/`CREATE2` (`Interpreter.createOp`) are unaffected.
    var intrinsic = gas.intrinsicCost(data);
    if (self.block.fork != .frontier) intrinsic += gas.create_base;
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

    // Mirrors `Interpreter.createOp`: a successful init code run still has
    // to afford storing its returned code, at `code_deposit_byte` gas/byte.
    var success = interp.status == .stopped and !oversized;
    var status: Interpreter.Status = if (oversized) .out_of_gas else interp.status;
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
        .gas_used = gasUsed(status, interp.gas_remaining, interp.refund, gas_limit - intrinsic, intrinsic),
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

test "processBlock with no transactions credits the flat block reward" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    try evm.processBlock(.{ .number = 10, .miner = 0xaa, .transactions = &.{} });

    try std.testing.expectEqual(@as(u256, 5_000_000_000_000_000_000), state.getBalance(0xaa));
}

test "processBlock credits the reduced 3 ETH block reward from Byzantium on" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    try evm.processBlock(.{ .number = 4_370_000, .miner = 0xaa, .transactions = &.{} });

    try std.testing.expectEqual(@as(u256, 3_000_000_000_000_000_000), state.getBalance(0xaa));
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
