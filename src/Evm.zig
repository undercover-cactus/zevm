//! Executes a decoded `Transaction` against a `State`.
//!
//! Only Frontier is implemented. `processBlock` panics on any block from a
//! later fork (see `Fork`) instead of silently applying stale rules.

const std = @import("std");
const Address = @import("Address.zig").Address;
const State = @import("State.zig");
const Interpreter = @import("Interpreter.zig");
const Transaction = @import("Transaction.zig").Transaction;
const Block = @import("Block.zig").Block;
const Fork = @import("Fork.zig").Fork;
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

/// Miner reward for a block with no uncles: Frontier's flat 5 ETH.
const block_reward: u256 = 5_000_000_000_000_000_000;

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
    // A nonce mismatch means we fed transactions out of order, not that the
    // transaction itself is invalid. Worth panicking on immediately.
    const current_nonce = self.state.get(from).nonce;
    if (tx.nonce != current_nonce) {
        std.debug.panic(
            "nonce mismatch for {x}: transaction has {d}, state has {d}",
            .{ from, tx.nonce, current_nonce },
        );
    }

    // Real Ethereum reserves the full potential fee up front and refunds
    // what's unused after execution. Unlike insufficient balance for
    // `value` alone (handled gracefully in `call`/`create`), failing this
    // check on a replayed transaction means our balance has already
    // drifted from real chain state.
    const upfront_cost = @as(u256, tx.gas_limit) * tx.gas_price;
    const balance_before = self.state.getBalance(from);
    if (upfront_cost > balance_before) {
        return error.InsufficientBalance;
    }
    try self.state.setBalance(from, balance_before - upfront_cost);

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

    return result;
}

/// Runs every transaction in `block`, then credits block and uncle rewards.
/// Per-transaction `Result`s aren't surfaced; call `executeTransaction`
/// directly if you need them.
pub fn processBlock(self: *Evm, block: Block) !void {
    const fork = Fork.at(block.number);
    if (fork != .frontier) {
        std.debug.panic(
            "block {d} is past Frontier (fork: {s}): this Evm only implements Frontier's rules",
            .{ block.number, @tagName(fork) },
        );
    }

    self.block = .{
        .number = block.number,
        .timestamp = block.timestamp,
        .coinbase = block.miner,
        .gas_limit = block.gas_limit,
        .difficulty = block.difficulty,
        .base_fee = block.base_fee,
        .chain_id = block.chain_id,
        .recent_hashes = block.recent_hashes,
    };

    for (block.transactions) |entry| {
        const result = try self.executeTransaction(entry.tx, entry.from);
        self.allocator.free(result.return_data);
    }

    // A whole block is never rolled back once processed, so rewards credit
    // directly rather than through `setBalance`'s journaled bookkeeping.
    var miner_reward = block_reward;
    for (block.uncles) |uncle| {
        const distance = block.number - uncle.number;
        const uncle_reward = block_reward * (8 - distance) / 8;
        try self.state.creditBalance(uncle.miner, uncle_reward);
        miner_reward += block_reward / 32; // "nephew" bonus for including it
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
    // paying only the intrinsic cost.
    if (value != 0 and !try self.state.transfer(from, to, value)) {
        self.state.revertTo(cp);
        return .{
            .status = .reverted,
            .return_data = try self.allocator.alloc(u8, 0),
            .gas_used = intrinsic,
        };
    }

    const execution_gas_limit = gas_limit - intrinsic;

    // A transaction can target a precompile directly, same as `Interpreter.call`.
    if (try Precompiles.call(self.allocator, to, data, execution_gas_limit)) |result| {
        const status: Interpreter.Status = if (result.success) .stopped else .out_of_gas;
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
    });
    defer interp.deinit();
    try interp.run();

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

    const intrinsic = gas.intrinsicCost(data);
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

    // Mirrors `Interpreter.createOp`: a successful init code run still has
    // to afford storing its returned code, at `code_deposit_byte` gas/byte.
    var success = interp.status == .stopped;
    if (success) {
        const deposit_cost = gas.code_deposit_byte * @as(u64, interp.return_data.len);
        if (interp.gas_remaining < deposit_cost) {
            success = false;
        } else {
            interp.gas_remaining -= deposit_cost;
        }
    }
    if (success) {
        try self.state.setCode(new_address, interp.return_data);
    } else {
        self.state.revertTo(cp);
    }

    return .{
        .status = interp.status,
        .return_data = try self.allocator.dupe(u8, interp.return_data),
        .created_address = new_address,
        .gas_used = gasUsed(interp.status, interp.gas_remaining, interp.refund, gas_limit - intrinsic, intrinsic),
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

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
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

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state, .block = .{ .coinbase = 0xcc } };
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

test "insufficient balance for value alone fails just that transaction, not the whole block" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 10);

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    var tx = testTx();
    tx.to = 0xdd;
    tx.value = 100;

    // Insufficient value alone reverts gracefully; it doesn't abort the block.
    const result = try evm.executeTransaction(tx, 0x1);
    defer std.testing.allocator.free(result.return_data);
    try std.testing.expectEqual(Interpreter.Status.reverted, result.status);
    try std.testing.expectEqual(@as(u256, 10), state.getBalance(0x1));
    // the nonce still advances: a failed transfer doesn't unwind the
    // nonce increment, which happens before the transfer is attempted.
    try std.testing.expectEqual(@as(u64, 1), state.get(0x1).nonce);
}

test "processBlock with no transactions credits the flat block reward" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    var evm = Evm{ .allocator = std.testing.allocator, .state = &state };
    try evm.processBlock(.{ .number = 10, .miner = 0xaa, .transactions = &.{} });

    try std.testing.expectEqual(@as(u256, 5_000_000_000_000_000_000), state.getBalance(0xaa));
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
