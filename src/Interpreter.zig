//! The bytecode interpreter: a fetch/decode/dispatch loop over a `Stack`
//! and `Memory`, charging static per-opcode gas plus memory expansion.
//! Implements the full Frontier opcode set against a real, shared `State`.
//! Block/environment context is threaded in from `Evm`, not read through a
//! separate `Host` interface; this concrete design is deliberate, see
//! `State.zig`'s own doc comment.

const std = @import("std");
const OpCode = @import("OpCode.zig").OpCode;
const Stack = @import("Stack.zig");
const Memory = @import("Memory.zig");
const keccak256 = @import("Hash.zig").keccak256;
const Hash = @import("Hash.zig").Hash;
const Address = @import("Address.zig").Address;
const State = @import("State.zig");
const Rlp = @import("Rlp.zig");
const gas = @import("gas.zig");
const Precompiles = @import("Precompiles.zig");

pub const Status = enum {
    running,
    stopped,
    reverted,
    out_of_gas,
    invalid_opcode,
    invalid_jump,
    stack_overflow,
    stack_underflow,
};

/// The block a transaction executes inside, the same for every transaction
/// and every nested call within one block, unlike `address`/`caller`/`value`
/// which change per call.
pub const BlockContext = struct {
    number: u64 = 0,
    timestamp: u64 = 0,
    coinbase: Address = 0,
    gas_limit: u64 = 0,
    /// DIFFICULTY pre-merge, PREVRANDAO post-merge (same opcode byte).
    difficulty: u256 = 0,
    /// 0 pre-London (EIP-1559).
    base_fee: u256 = 0,
    chain_id: u256 = 1,
    /// The preceding blocks' hashes, most recent first, what `BLOCKHASH`
    /// looks up into. Real Ethereum only ever makes the last 256 available,
    /// so a shorter (or empty) slice just reads as 0 further back.
    recent_hashes: []const Hash = &.{},
};

/// The transaction currently executing, constant across every nested call
/// within it, unlike `caller`/`value` which change per frame.
pub const TxContext = struct {
    origin: Address = 0,
    gas_price: u256 = 0,
};

/// No realistic gas budget reaches this much memory; bounding offsets/sizes
/// to it up front keeps the cost-formula arithmetic below from overflowing.
const max_memory_bytes: usize = 1 << 32;

/// Matches the real EVM's hard cap on call-stack depth.
const max_call_depth: u16 = 1024;

/// EIP-170: a CREATE/CREATE2 whose init code returns more than this many
/// bytes of runtime code fails.
const max_code_size: usize = 24576;

allocator: std.mem.Allocator,
code: []const u8,
pc: usize = 0,
stack: Stack,
memory: Memory,
gas_remaining: u64,
/// Accumulated gas refund (Frontier's flat `SSTORE`-clears-a-slot rule, see
/// `sstore`). Not capped here, since the cap only makes sense relative to a
/// transaction's total gas used, which this frame alone doesn't know.
refund: u64 = 0,
status: Status = .running,
jumpdest: std.DynamicBitSetUnmanaged,

/// Output captured by `RETURN`/`REVERT`, owned by this interpreter. Empty
/// (not an error) if execution halted via `STOP` or ran off the end of code.
return_data: []const u8 = &.{},
/// The most recently completed nested call/create's output, what
/// `RETURNDATASIZE`/`RETURNDATACOPY` read, distinct from `return_data`
/// (this frame's own eventual output). Owned (duped from the child before
/// it's torn down), and freed/replaced after every nested call.
last_return_data: []const u8 = &.{},

/// This frame's own address, msg.sender, and msg.value. Defaulted to zero
/// for plain `init`, which just runs bytecode with no calling context.
address: Address = 0,
caller: Address = 0,
value: u256 = 0,
calldata: []const u8 = &.{},
tx: TxContext = .{},
/// True inside a `STATICCALL` (or anything nested under one): state-changing
/// opcodes must halt as invalid rather than execute.
is_static: bool = false,
/// Call-stack depth, for the 1024-deep limit and for deriving child depth.
depth: u16 = 0,
/// Shared account store for `CALL`-family opcodes. `null` (the `init`
/// default) means those opcodes halt as invalid instead of pretending to
/// succeed against nothing.
state: ?*State = null,
block: BlockContext = .{},

const Interpreter = @This();

pub fn init(allocator: std.mem.Allocator, code: []const u8, gas_limit: u64) !Interpreter {
    return initCall(allocator, code, gas_limit, .{});
}

pub const CallParams = struct {
    address: Address = 0,
    caller: Address = 0,
    value: u256 = 0,
    calldata: []const u8 = &.{},
    tx: TxContext = .{},
    is_static: bool = false,
    depth: u16 = 0,
    state: ?*State = null,
    block: BlockContext = .{},
};

pub fn initCall(allocator: std.mem.Allocator, code: []const u8, gas_limit: u64, params: CallParams) !Interpreter {
    return .{
        .allocator = allocator,
        .code = code,
        .memory = Memory.init(allocator),
        .gas_remaining = gas_limit,
        .jumpdest = try analyzeJumpdests(allocator, code),
        .stack = try Stack.init(allocator),
        .address = params.address,
        .caller = params.caller,
        .value = params.value,
        .calldata = params.calldata,
        .tx = params.tx,
        .is_static = params.is_static,
        .depth = params.depth,
        .state = params.state,
        .block = params.block,
    };
}

pub fn deinit(self: *Interpreter) void {
    self.stack.deinit();
    self.memory.deinit();
    self.jumpdest.deinit(self.allocator);
    if (self.return_data.len != 0) self.allocator.free(self.return_data);
    if (self.last_return_data.len != 0) self.allocator.free(self.last_return_data);
}

/// A byte is only a valid `JUMPDEST` if it's not inside a `PUSH`'s immediate data.
fn analyzeJumpdests(allocator: std.mem.Allocator, code: []const u8) !std.DynamicBitSetUnmanaged {
    var set = try std.DynamicBitSetUnmanaged.initEmpty(allocator, code.len);
    var i: usize = 0;
    while (i < code.len) {
        const byte = code[i];
        if (byte == @intFromEnum(OpCode.JUMPDEST)) {
            set.set(i);
            i += 1;
        } else if (byte >= @intFromEnum(OpCode.PUSH1) and byte <= @intFromEnum(OpCode.PUSH32)) {
            const push_len = byte - @intFromEnum(OpCode.PUSH1) + 1;
            i += 1 + push_len;
        } else {
            i += 1;
        }
    }
    return set;
}

// Explicit rather than inferred: `run` -> `step` -> `call` -> `run` (for a
// nested call) is a real recursive cycle, and Zig can't infer an error set
// through recursion. Allocator failure is the only error that propagates
// this way; everything EVM-level halts via `Status` instead.
pub fn run(self: *Interpreter) std.mem.Allocator.Error!void {
    while (self.status == .running) {
        try self.step();
    }
}

fn step(self: *Interpreter) !void {
    if (self.pc >= self.code.len) {
        self.status = .stopped;
        return;
    }

    const byte = self.code[self.pc];

    if (byte >= @intFromEnum(OpCode.PUSH1) and byte <= @intFromEnum(OpCode.PUSH32)) {
        self.pushN(byte - @intFromEnum(OpCode.PUSH1) + 1);
        return;
    }
    if (byte >= @intFromEnum(OpCode.DUP1) and byte <= @intFromEnum(OpCode.DUP16)) {
        self.dupN(byte - @intFromEnum(OpCode.DUP1) + 1);
        return;
    }
    if (byte >= @intFromEnum(OpCode.SWAP1) and byte <= @intFromEnum(OpCode.SWAP16)) {
        self.swapN(byte - @intFromEnum(OpCode.SWAP1) + 1);
        return;
    }

    // `OpCode` is non-exhaustive (see its own doc comment) so this is a
    // direct O(1) cast; an unmatched byte falls into the `switch`'s `else`.
    const op: OpCode = @enumFromInt(byte);

    switch (op) {
        .STOP => self.status = .stopped,

        .ADD => self.binaryOp(gas.verylow, add),
        .MUL => self.binaryOp(gas.low, mul),
        .SUB => self.binaryOp(gas.verylow, sub),
        .DIV => self.binaryOp(gas.low, div),
        .SDIV => self.binaryOp(gas.low, sdiv),
        .MOD => self.binaryOp(gas.low, mod),
        .SMOD => self.binaryOp(gas.low, smod),
        .ADDMOD => self.ternaryOp(gas.mid, addmod),
        .MULMOD => self.ternaryOp(gas.mid, mulmod),
        .EXP => self.expOpcode(),
        .SIGNEXTEND => self.binaryOp(gas.low, signextend),

        .LT => self.binaryOp(gas.verylow, lt),
        .GT => self.binaryOp(gas.verylow, gt),
        .SLT => self.binaryOp(gas.verylow, slt),
        .SGT => self.binaryOp(gas.verylow, sgt),
        .EQ => self.binaryOp(gas.verylow, eq),
        .ISZERO => self.unaryOp(gas.verylow, iszero),
        .AND => self.binaryOp(gas.verylow, bitAnd),
        .OR => self.binaryOp(gas.verylow, bitOr),
        .XOR => self.binaryOp(gas.verylow, bitXor),
        .NOT => self.unaryOp(gas.verylow, bitNot),
        .BYTE => self.binaryOp(gas.verylow, byteOp),
        .SHL => self.binaryOp(gas.verylow, shl),
        .SHR => self.binaryOp(gas.verylow, shr),
        .SAR => self.binaryOp(gas.verylow, sar),

        .KECCAK256 => try self.keccak256Opcode(),

        .POP => {
            if (!self.chargeGas(gas.base)) return;
            _ = self.popStack() orelse return;
            self.pc += 1;
        },

        .MLOAD => try self.mload(),
        .MSTORE => try self.mstore(),
        .MSTORE8 => try self.mstore8(),
        .MSIZE => {
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(@as(u256, self.memory.len()));
            self.pc += 1;
        },

        .PUSH0 => {
            if (!self.chargeGas(gas.verylow)) return;
            self.pushStack(0);
            self.pc += 1;
        },

        .PC => {
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(@as(u256, self.pc));
            self.pc += 1;
        },
        .GAS => {
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(@as(u256, self.gas_remaining));
            self.pc += 1;
        },
        .JUMPDEST => {
            if (!self.chargeGas(gas.jumpdest)) return;
            self.pc += 1;
        },
        .JUMP => {
            if (!self.chargeGas(gas.mid)) return;
            const dest = self.popStack() orelse return;
            _ = self.jumpTo(dest);
        },
        .JUMPI => {
            if (!self.chargeGas(gas.high)) return;
            const dest = self.popStack() orelse return;
            const cond = self.popStack() orelse return;
            if (cond != 0) {
                _ = self.jumpTo(dest);
            } else {
                self.pc += 1;
            }
        },

        .ADDRESS => {
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(@as(u256, self.address));
            self.pc += 1;
        },
        .BALANCE => {
            if (!self.chargeGas(gas.balance)) return;
            const address256 = self.popStack() orelse return;
            const state = self.state orelse {
                self.status = .invalid_opcode;
                return;
            };
            self.pushStack(state.getBalance(@truncate(address256)));
            self.pc += 1;
        },
        .ORIGIN => {
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(@as(u256, self.tx.origin));
            self.pc += 1;
        },
        .CALLER => {
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(@as(u256, self.caller));
            self.pc += 1;
        },
        .CALLVALUE => {
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(self.value);
            self.pc += 1;
        },
        .CALLDATASIZE => {
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(@as(u256, self.calldata.len));
            self.pc += 1;
        },
        .CALLDATALOAD => self.calldataload(),
        .CALLDATACOPY => try self.calldatacopy(),
        .CODESIZE => {
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(@as(u256, self.code.len));
            self.pc += 1;
        },
        .CODECOPY => try self.codecopy(),
        .GASPRICE => {
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(self.tx.gas_price);
            self.pc += 1;
        },
        .EXTCODESIZE => {
            if (!self.chargeGas(gas.extcode)) return;
            const address256 = self.popStack() orelse return;
            const state = self.state orelse {
                self.status = .invalid_opcode;
                return;
            };
            self.pushStack(@as(u256, state.getCode(@truncate(address256)).len));
            self.pc += 1;
        },
        .EXTCODECOPY => try self.extcodecopy(),
        .RETURNDATASIZE => {
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(@as(u256, self.last_return_data.len));
            self.pc += 1;
        },
        .RETURNDATACOPY => try self.returndatacopy(),
        .EXTCODEHASH => {
            if (!self.chargeGas(gas.extcode)) return;
            const address256 = self.popStack() orelse return;
            const state = self.state orelse {
                self.status = .invalid_opcode;
                return;
            };
            const address: Address = @truncate(address256);
            self.pushStack(if (state.exists(address)) keccak256(state.getCode(address)) else 0);
            self.pc += 1;
        },
        .BLOCKHASH => {
            if (!self.chargeGas(gas.blockhash)) return;
            const requested = self.popStack() orelse return;
            self.pushStack(self.blockHash(requested));
            self.pc += 1;
        },

        .NUMBER => {
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(@as(u256, self.block.number));
            self.pc += 1;
        },
        .TIMESTAMP => {
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(@as(u256, self.block.timestamp));
            self.pc += 1;
        },
        .COINBASE => {
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(@as(u256, self.block.coinbase));
            self.pc += 1;
        },
        .GASLIMIT => {
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(@as(u256, self.block.gas_limit));
            self.pc += 1;
        },
        .PREVRANDAO => {
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(self.block.difficulty);
            self.pc += 1;
        },
        .BASEFEE => {
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(self.block.base_fee);
            self.pc += 1;
        },
        .CHAINID => {
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(self.block.chain_id);
            self.pc += 1;
        },
        .SELFBALANCE => {
            if (!self.chargeGas(gas.low)) return;
            const state = self.state orelse {
                self.status = .invalid_opcode;
                return;
            };
            self.pushStack(state.getBalance(self.address));
            self.pc += 1;
        },

        .SLOAD => try self.sload(),
        .SSTORE => try self.sstore(),

        .RETURN => try self.haltWithOutput(.stopped),
        .REVERT => try self.haltWithOutput(.reverted),

        .CALL => try self.call(.call),
        .CALLCODE => try self.call(.callcode),
        .STATICCALL => try self.call(.staticcall),
        .DELEGATECALL => try self.call(.delegatecall),

        .CREATE => try self.createOp(.create),
        .CREATE2 => try self.createOp(.create2),

        .LOG0 => try self.log(0),
        .LOG1 => try self.log(1),
        .LOG2 => try self.log(2),
        .LOG3 => try self.log(3),
        .LOG4 => try self.log(4),

        .SELFDESTRUCT => try self.selfdestruct(),

        else => self.status = .invalid_opcode,
    }
}

// --- gas / stack helpers ---

fn chargeGas(self: *Interpreter, amount: u64) bool {
    if (self.gas_remaining < amount) {
        self.status = .out_of_gas;
        return false;
    }
    self.gas_remaining -= amount;
    return true;
}

fn popStack(self: *Interpreter) ?u256 {
    return self.stack.pop() catch {
        self.status = .stack_underflow;
        return null;
    };
}

fn pushStack(self: *Interpreter, value: u256) void {
    self.stack.push(value) catch {
        self.status = .stack_overflow;
    };
}

fn binaryOp(self: *Interpreter, cost: u64, comptime f: fn (u256, u256) u256) void {
    if (!self.chargeGas(cost)) return;
    const a = self.popStack() orelse return;
    const b = self.popStack() orelse return;
    self.pushStack(f(a, b));
    self.pc += 1;
}

fn unaryOp(self: *Interpreter, cost: u64, comptime f: fn (u256) u256) void {
    if (!self.chargeGas(cost)) return;
    const a = self.popStack() orelse return;
    self.pushStack(f(a));
    self.pc += 1;
}

fn ternaryOp(self: *Interpreter, cost: u64, comptime f: fn (u256, u256, u256) u256) void {
    if (!self.chargeGas(cost)) return;
    const a = self.popStack() orelse return;
    const b = self.popStack() orelse return;
    const c = self.popStack() orelse return;
    self.pushStack(f(a, b, c));
    self.pc += 1;
}

fn pushN(self: *Interpreter, n: u8) void {
    if (!self.chargeGas(gas.verylow)) return;
    var value: u256 = 0;
    var i: usize = 0;
    while (i < n) : (i += 1) {
        const idx = self.pc + 1 + i;
        const byte: u8 = if (idx < self.code.len) self.code[idx] else 0;
        value = (value << 8) | byte;
    }
    self.pushStack(value);
    self.pc += 1 + @as(usize, n);
}

fn dupN(self: *Interpreter, n: u8) void {
    if (!self.chargeGas(gas.verylow)) return;
    self.stack.dup(n) catch |err| {
        self.status = if (err == error.StackOverflow) .stack_overflow else .stack_underflow;
        return;
    };
    self.pc += 1;
}

fn swapN(self: *Interpreter, n: u8) void {
    if (!self.chargeGas(gas.verylow)) return;
    self.stack.swap(n) catch {
        self.status = .stack_underflow;
        return;
    };
    self.pc += 1;
}

fn jumpTo(self: *Interpreter, dest: u256) bool {
    const dest_usize = std.math.cast(usize, dest) orelse {
        self.status = .invalid_jump;
        return false;
    };
    if (dest_usize >= self.code.len or !self.jumpdest.isSet(dest_usize)) {
        self.status = .invalid_jump;
        return false;
    }
    self.pc = dest_usize;
    return true;
}

fn expOpcode(self: *Interpreter) void {
    const base_val = self.popStack() orelse return;
    const exponent = self.popStack() orelse return;
    if (!self.chargeGas(gas.expCost(exponent))) return;
    self.pushStack(expOp(base_val, exponent));
    self.pc += 1;
}

// --- memory helpers ---

fn toMemIndex(self: *Interpreter, value: u256) ?usize {
    const v = std.math.cast(usize, value) orelse {
        self.status = .out_of_gas;
        return null;
    };
    if (v > max_memory_bytes) {
        self.status = .out_of_gas;
        return null;
    }
    return v;
}

fn chargeMemoryExpansion(self: *Interpreter, offset: usize, size: usize) bool {
    return self.chargeGas(gas.memoryExpansionCost(self.memory.len(), offset, size));
}

// Allocator failure (`Memory`'s backing buffer growing) is a real,
// unrecoverable error, not an EVM-level `Status` halt, so these propagate
// it via `!void` instead of mapping it to a status.

fn mload(self: *Interpreter) !void {
    if (!self.chargeGas(gas.verylow)) return;
    const offset256 = self.popStack() orelse return;
    const offset = self.toMemIndex(offset256) orelse return;
    if (!self.chargeMemoryExpansion(offset, 32)) return;
    const value = try self.memory.readWord(offset);
    self.pushStack(value);
    self.pc += 1;
}

fn mstore(self: *Interpreter) !void {
    if (!self.chargeGas(gas.verylow)) return;
    const offset256 = self.popStack() orelse return;
    const value = self.popStack() orelse return;
    const offset = self.toMemIndex(offset256) orelse return;
    if (!self.chargeMemoryExpansion(offset, 32)) return;
    try self.memory.writeWord(offset, value);
    self.pc += 1;
}

fn mstore8(self: *Interpreter) !void {
    if (!self.chargeGas(gas.verylow)) return;
    const offset256 = self.popStack() orelse return;
    const value = self.popStack() orelse return;
    const offset = self.toMemIndex(offset256) orelse return;
    if (!self.chargeMemoryExpansion(offset, 1)) return;
    try self.memory.write(offset, &[_]u8{@truncate(value)});
    self.pc += 1;
}

fn keccak256Opcode(self: *Interpreter) !void {
    if (!self.chargeGas(gas.keccak256_base)) return;
    const offset256 = self.popStack() orelse return;
    const size256 = self.popStack() orelse return;
    const offset = self.toMemIndex(offset256) orelse return;
    const size = self.toMemIndex(size256) orelse return;
    if (!self.chargeMemoryExpansion(offset, size)) return;
    if (!self.chargeGas(gas.keccak256_word * ((size + 31) / 32))) return;
    const data = try self.memory.read(offset, size);
    self.pushStack(keccak256(data));
    self.pc += 1;
}

/// `BLOCKHASH`'s lookup: 0 for the current/a future block (nothing to look
/// up yet), 0 past the last 256 blocks (real Ethereum doesn't keep more
/// than that either), otherwise `self.block.recent_hashes[distance - 1]`.
fn blockHash(self: *const Interpreter, requested: u256) u256 {
    if (requested >= self.block.number) return 0;
    const distance = @as(u256, self.block.number) - requested;
    if (distance > 256) return 0;
    const index: usize = @intCast(distance - 1);
    if (index >= self.block.recent_hashes.len) return 0;
    return self.block.recent_hashes[index];
}

// --- calldata ---

/// Reads a byte from `data` at `index`, or 0 if beyond `data`'s bounds.
/// Calldata (and code) reads are always zero-padded, unlike memory/stack.
fn readPadded(data: []const u8, index: usize) u8 {
    return if (index < data.len) data[index] else 0;
}

fn calldataload(self: *Interpreter) void {
    if (!self.chargeGas(gas.verylow)) return;
    const offset256 = self.popStack() orelse return;
    var word: [32]u8 = [_]u8{0} ** 32;
    if (std.math.cast(usize, offset256)) |offset| {
        var i: usize = 0;
        while (i < 32) : (i += 1) {
            word[i] = readPadded(self.calldata, offset +| i);
        }
    }
    self.pushStack(std.mem.readInt(u256, &word, .big));
    self.pc += 1;
}

/// Shared by `CALLDATACOPY`/`CODECOPY`/`EXTCODECOPY`: all three copy from
/// some byte slice into memory with the same zero-padded semantics (see
/// `readPadded`); only the source slice and the caller's own base gas differ.
fn copyToMemory(self: *Interpreter, src: []const u8, dest256: u256, offset256: u256, size256: u256) !void {
    const dest = self.toMemIndex(dest256) orelse return;
    const size = self.toMemIndex(size256) orelse return;
    if (!self.chargeMemoryExpansion(dest, size)) return;
    if (!self.chargeGas(gas.copy_word * ((size + 31) / 32))) return;
    if (size == 0) {
        self.pc += 1;
        return;
    }

    const src_offset = std.math.cast(usize, offset256) orelse std.math.maxInt(usize);
    const buf = try self.allocator.alloc(u8, size);
    defer self.allocator.free(buf);
    var i: usize = 0;
    while (i < size) : (i += 1) {
        buf[i] = readPadded(src, src_offset +| i);
    }
    try self.memory.write(dest, buf);
    self.pc += 1;
}

fn calldatacopy(self: *Interpreter) !void {
    if (!self.chargeGas(gas.verylow)) return;
    const dest256 = self.popStack() orelse return;
    const offset256 = self.popStack() orelse return;
    const size256 = self.popStack() orelse return;
    try self.copyToMemory(self.calldata, dest256, offset256, size256);
}

fn codecopy(self: *Interpreter) !void {
    if (!self.chargeGas(gas.verylow)) return;
    const dest256 = self.popStack() orelse return;
    const offset256 = self.popStack() orelse return;
    const size256 = self.popStack() orelse return;
    try self.copyToMemory(self.code, dest256, offset256, size256);
}

fn extcodecopy(self: *Interpreter) !void {
    if (!self.chargeGas(gas.extcode)) return;
    const address256 = self.popStack() orelse return;
    const dest256 = self.popStack() orelse return;
    const offset256 = self.popStack() orelse return;
    const size256 = self.popStack() orelse return;
    const state = self.state orelse {
        self.status = .invalid_opcode;
        return;
    };
    try self.copyToMemory(state.getCode(@truncate(address256)), dest256, offset256, size256);
}

/// Unlike `CALLDATACOPY`/`CODECOPY`, `RETURNDATACOPY` doesn't zero-pad past
/// the end of `last_return_data`: reading out of bounds is invalid
/// (EIP-211), not silently zero-filled.
fn returndatacopy(self: *Interpreter) !void {
    if (!self.chargeGas(gas.verylow)) return;
    const dest256 = self.popStack() orelse return;
    const offset256 = self.popStack() orelse return;
    const size256 = self.popStack() orelse return;
    const dest = self.toMemIndex(dest256) orelse return;
    const offset = self.toMemIndex(offset256) orelse return;
    const size = self.toMemIndex(size256) orelse return;
    if (offset + size > self.last_return_data.len) {
        self.status = .invalid_opcode;
        return;
    }
    if (!self.chargeMemoryExpansion(dest, size)) return;
    if (!self.chargeGas(gas.copy_word * ((size + 31) / 32))) return;
    if (size == 0) {
        self.pc += 1;
        return;
    }
    try self.memory.write(dest, self.last_return_data[offset..][0..size]);
    self.pc += 1;
}

fn haltWithOutput(self: *Interpreter, status: Status) !void {
    const offset256 = self.popStack() orelse return;
    const size256 = self.popStack() orelse return;
    const offset = self.toMemIndex(offset256) orelse return;
    const size = self.toMemIndex(size256) orelse return;
    if (!self.chargeMemoryExpansion(offset, size)) return;
    const data = try self.memory.read(offset, size);
    self.return_data = try self.allocator.dupe(u8, data);
    self.status = status;
}

// --- storage ---
//
// Gas here is Frontier's real flat rule, not EIP-2200/2929's later
// net-metering-plus-refund-plus-warm/cold machine (that needs the `Host`
// interface, a later milestone). `SSTORE`'s refund is fully implemented,
// since Frontier's flat rule needs no access tracking or "undo if
// re-set" bookkeeping, just a flat refund every time a slot clears.

fn sload(self: *Interpreter) !void {
    if (!self.chargeGas(gas.sload)) return;
    const slot = self.popStack() orelse return;
    const state = self.state orelse {
        self.status = .invalid_opcode;
        return;
    };
    self.pushStack(state.getStorage(self.address, slot));
    self.pc += 1;
}

fn sstore(self: *Interpreter) !void {
    if (self.is_static) {
        self.status = .invalid_opcode;
        return;
    }
    const slot = self.popStack() orelse return;
    const value = self.popStack() orelse return;
    const state = self.state orelse {
        self.status = .invalid_opcode;
        return;
    };
    const old = state.getStorage(self.address, slot);
    if (!self.chargeGas(if (old == 0 and value != 0) gas.sstore_set else gas.sstore_reset)) return;
    if (old != 0 and value == 0) {
        self.refund += gas.sstore_clear_refund;
    }
    try state.setStorage(self.address, slot, value);
    self.pc += 1;
}

// --- calls ---

const CallKind = enum { call, callcode, staticcall, delegatecall };

/// What a CALL/CALLCODE/DELEGATECALL/STATICCALL produced, whether it ran a
/// precompile or interpreted bytecode: unified so the success determination,
/// gas refund, and return-data handling below don't need to know which.
const CallOutcome = struct {
    status: Status,
    gas_remaining: u64,
    refund: u64 = 0,
    /// Always allocator-owned (a fresh copy either way), freed once by the
    /// caller; this outcome has no `deinit` of its own to rely on.
    return_data: []const u8,
};

fn call(self: *Interpreter, kind: CallKind) !void {
    const requested_gas = self.popStack() orelse return;
    const target256 = self.popStack() orelse return;
    const value: u256 = if (kind == .call or kind == .callcode) (self.popStack() orelse return) else 0;
    const args_offset256 = self.popStack() orelse return;
    const args_size256 = self.popStack() orelse return;
    const ret_offset256 = self.popStack() orelse return;
    const ret_size256 = self.popStack() orelse return;

    if (kind == .call and self.is_static and value != 0) {
        self.status = .invalid_opcode;
        return;
    }

    const target: Address = @truncate(target256);
    const args_offset = self.toMemIndex(args_offset256) orelse return;
    const args_size = self.toMemIndex(args_size256) orelse return;
    const ret_offset = self.toMemIndex(ret_offset256) orelse return;
    const ret_size = self.toMemIndex(ret_size256) orelse return;

    if (!self.chargeMemoryExpansion(args_offset, args_size)) return;
    if (!self.chargeMemoryExpansion(ret_offset, ret_size)) return;

    const state = self.state orelse {
        self.status = .invalid_opcode;
        return;
    };

    var cost: u64 = gas.call_base;
    if (value != 0) cost += gas.call_value;
    // Only a plain CALL can bring a not-yet-touched account into being by
    // sending it value; CALLCODE/DELEGATECALL never move value to `target`
    // (see below), just borrow its code.
    const is_new_account = kind == .call and value != 0 and !state.exists(target);
    if (is_new_account) cost += gas.call_new_account;
    if (!self.chargeGas(cost)) return;

    // Pre-EIP-150 geth rejects a requested-gas value that doesn't fit in a
    // u64 (`ErrGasUintOverflow`) rather than capping it. A contract
    // computing this via unchecked subtraction can easily push a value
    // near 2^256, and real Ethereum treats that as an immediate
    // out-of-gas, not "forward everything remaining".
    const forwarded_requested = std.math.cast(u64, requested_gas) orelse {
        self.status = .out_of_gas;
        return;
    };

    if (self.depth >= max_call_depth) {
        self.pushStack(0);
        self.pc += 1;
        return;
    }

    const cp = state.checkpoint();

    // Pre-EIP-150: forward up to whatever's available, uncapped by the
    // 63/64ths rule that fork later introduced. Real EVM reserves this
    // (plus the stipend) before checking whether `value` can be afforded,
    // so a failed check below returns the whole reservation untouched.
    var forwarded = forwarded_requested;
    if (forwarded > self.gas_remaining) forwarded = self.gas_remaining;
    self.gas_remaining -= forwarded;
    const stipend: u64 = if (value != 0) gas.call_stipend else 0;
    const child_gas_limit = forwarded + stipend;

    if (value != 0) {
        // CALLCODE never leaves its own storage context, so `value`
        // "moves" from this account to itself: a no-op balance-wise, but
        // it still has to afford it.
        const recipient = if (kind == .callcode) self.address else target;
        if (!try state.transfer(self.address, recipient, value)) {
            self.gas_remaining += child_gas_limit;
            self.pushStack(0);
            self.pc += 1;
            return;
        }
    }

    const args = try self.memory.read(args_offset, args_size);

    // A precompile has no bytecode to interpret; `state.getCode` would just
    // return empty, so it's checked first, before creating a child `Interpreter`.
    const target_code = state.getCode(target);

    const outcome: CallOutcome = if (try Precompiles.call(self.allocator, target, args, child_gas_limit)) |result|
        .{
            .status = if (result.success) .stopped else .out_of_gas,
            .gas_remaining = result.gas_remaining,
            .return_data = result.output,
        }
    else if (target_code.len == 0)
        // A call to an address with no code is an immediate, trivial
        // success, skipping construction of a full child `Interpreter`
        // (a measured fixed cost from stack-probing, see `Stack.zig`).
        // All forwarded gas comes right back.
        .{ .status = .stopped, .gas_remaining = child_gas_limit, .return_data = &.{} }
    else run: {
        // CALLCODE keeps this frame's own address/storage (like
        // DELEGATECALL) but resets caller/value to itself rather than
        // preserving the grandparent's: "run target's code as my own,"
        // not "run target's code as if I weren't here."
        var child = try Interpreter.initCall(self.allocator, target_code, child_gas_limit, .{
            .address = if (kind == .delegatecall or kind == .callcode) self.address else target,
            .caller = if (kind == .delegatecall) self.caller else self.address,
            .value = if (kind == .delegatecall) self.value else value,
            .calldata = args,
            .tx = self.tx,
            .is_static = self.is_static or kind == .staticcall,
            .depth = self.depth + 1,
            .state = state,
            .block = self.block,
        });
        defer child.deinit();
        try child.run();
        break :run .{
            .status = child.status,
            .gas_remaining = child.gas_remaining,
            .refund = child.refund,
            .return_data = try self.allocator.dupe(u8, child.return_data),
        };
    };
    defer self.allocator.free(outcome.return_data);

    const success = outcome.status == .stopped;
    if (!success) state.revertTo(cp);
    // The stipend is free money handed to the callee, not a loan against
    // the caller: real geth adds a call's entire leftover gas straight
    // back with no clawback, so an unused stipend comes back in full.
    if (success or outcome.status == .reverted) {
        self.gas_remaining += outcome.gas_remaining;
    }
    // A reverted child's storage changes are undone above, so any refund it
    // accumulated must be dropped too, not just its unused gas (matches
    // revm's `handle_reservoir_remaining_gas`).
    if (success) self.refund += outcome.refund;

    if (self.last_return_data.len != 0) self.allocator.free(self.last_return_data);
    self.last_return_data = try self.allocator.dupe(u8, outcome.return_data);

    // Always expand to the full reserved `ret_size`, what
    // `chargeMemoryExpansion` above already charged for, so a callee
    // returning less can't leave the region un-grown and get charged for
    // the same expansion again next time something touches it.
    try self.memory.expand(ret_offset, ret_size);
    const copy_len = @min(outcome.return_data.len, ret_size);
    if (copy_len != 0) try self.memory.write(ret_offset, outcome.return_data[0..copy_len]);

    self.pushStack(if (success) 1 else 0);
    self.pc += 1;
}

// --- create ---

const CreateKind = enum { create, create2 };

/// The address a new contract gets from a plain `CREATE`:
/// `keccak256(rlp([sender, nonce]))`'s low 160 bits. `nonce` is the
/// sender's nonce at the point of creation.
pub fn createAddress(allocator: std.mem.Allocator, sender: Address, nonce: u64) !Address {
    var sender_bytes: [20]u8 = undefined;
    std.mem.writeInt(u160, &sender_bytes, sender, .big);
    const sender_rlp = try Rlp.encodeBytes(allocator, &sender_bytes);
    defer allocator.free(sender_rlp);
    const nonce_rlp = try Rlp.encodeInt(allocator, nonce);
    defer allocator.free(nonce_rlp);
    const list = try Rlp.encodeList(allocator, &.{ sender_rlp, nonce_rlp });
    defer allocator.free(list);
    return @truncate(keccak256(list));
}

fn create2Address(sender: Address, salt: u256, init_code: []const u8) Address {
    var buf: [1 + 20 + 32 + 32]u8 = undefined;
    buf[0] = 0xff;
    std.mem.writeInt(u160, buf[1..21], sender, .big);
    std.mem.writeInt(u256, buf[21..53], salt, .big);
    std.mem.writeInt(u256, buf[53..85], keccak256(init_code), .big);
    return @truncate(keccak256(&buf));
}

fn createOp(self: *Interpreter, kind: CreateKind) !void {
    const value = self.popStack() orelse return;
    const offset256 = self.popStack() orelse return;
    const size256 = self.popStack() orelse return;
    const salt: u256 = if (kind == .create2) (self.popStack() orelse return) else 0;

    if (self.is_static) {
        self.status = .invalid_opcode;
        return;
    }

    const offset = self.toMemIndex(offset256) orelse return;
    const size = self.toMemIndex(size256) orelse return;
    if (!self.chargeMemoryExpansion(offset, size)) return;
    if (!self.chargeGas(gas.create_base)) return;
    if (kind == .create2 and !self.chargeGas(gas.keccak256_word * ((size + 31) / 32))) return;

    const state = self.state orelse {
        self.status = .invalid_opcode;
        return;
    };

    if (self.depth >= max_call_depth) {
        self.pushStack(0);
        self.pc += 1;
        return;
    }

    const init_code = try self.memory.read(offset, size);
    const new_address = switch (kind) {
        .create => try createAddress(self.allocator, self.address, state.get(self.address).nonce),
        .create2 => create2Address(self.address, salt, init_code),
    };

    const cp = state.checkpoint();

    try state.setNonce(self.address, state.get(self.address).nonce + 1);

    if (value != 0 and !try state.transfer(self.address, new_address, value)) {
        state.revertTo(cp);
        self.pushStack(0);
        self.pc += 1;
        return;
    }

    const max_forwardable = self.gas_remaining - self.gas_remaining / 64;
    self.gas_remaining -= max_forwardable;

    var child = try Interpreter.initCall(self.allocator, init_code, max_forwardable, .{
        .address = new_address,
        .caller = self.address,
        .value = value,
        .tx = self.tx,
        .is_static = self.is_static,
        .depth = self.depth + 1,
        .state = state,
        .block = self.block,
    });
    defer child.deinit();
    try child.run();

    var success = child.status == .stopped and child.return_data.len <= max_code_size;
    if (success) {
        const deposit_cost = gas.code_deposit_byte * @as(u64, child.return_data.len);
        if (child.gas_remaining < deposit_cost) {
            success = false;
        } else {
            child.gas_remaining -= deposit_cost;
        }
    }

    if (success) {
        try state.setCode(new_address, child.return_data);
    } else {
        state.revertTo(cp);
    }

    if (child.status == .stopped or child.status == .reverted) {
        self.gas_remaining += child.gas_remaining;
    }
    // See the equivalent comment in `call`: a failed/reverted create's
    // storage changes are undone, so its refund doesn't count either.
    if (success) self.refund += child.refund;

    // A successful create's return data was its deployed code, not
    // something RETURNDATACOPY should expose; only a failure's revert
    // reason (if any) is visible afterward.
    if (self.last_return_data.len != 0) self.allocator.free(self.last_return_data);
    self.last_return_data = if (success) &.{} else try self.allocator.dupe(u8, child.return_data);

    self.pushStack(if (success) @as(u256, new_address) else 0);
    self.pc += 1;
}

// --- logs / selfdestruct ---

/// `LOG0`-`LOG4`: validates and charges gas for emitting an event like real
/// Ethereum does, but doesn't persist the topics/data anywhere, since
/// nothing in this codebase reads logs yet.
fn log(self: *Interpreter, topic_count: u8) !void {
    if (self.is_static) {
        self.status = .invalid_opcode;
        return;
    }
    const offset256 = self.popStack() orelse return;
    const size256 = self.popStack() orelse return;
    var i: u8 = 0;
    while (i < topic_count) : (i += 1) {
        _ = self.popStack() orelse return;
    }
    const offset = self.toMemIndex(offset256) orelse return;
    const size = self.toMemIndex(size256) orelse return;
    if (!self.chargeMemoryExpansion(offset, size)) return;
    const cost = gas.log_base + gas.log_topic * @as(u64, topic_count) + gas.log_data_byte * @as(u64, size);
    if (!self.chargeGas(cost)) return;
    _ = try self.memory.read(offset, size);
    self.pc += 1;
}

fn selfdestruct(self: *Interpreter) !void {
    if (self.is_static) {
        self.status = .invalid_opcode;
        return;
    }
    const beneficiary256 = self.popStack() orelse return;
    const state = self.state orelse {
        self.status = .invalid_opcode;
        return;
    };
    const beneficiary: Address = @truncate(beneficiary256);
    const balance = state.getBalance(self.address);

    if (!self.chargeGas(gas.selfdestruct_base)) return;

    if (balance != 0 and beneficiary != self.address) {
        // Already confirmed the balance is there; `transfer` can only
        // fail on insufficient balance, which can't happen here.
        _ = try state.transfer(self.address, beneficiary, balance);
    } else if (beneficiary == self.address and balance != 0) {
        // Destroying yourself to yourself just burns the balance.
        try state.setBalance(self.address, 0);
    }

    try state.destroyAccount(self.address);
    self.refund += gas.selfdestruct_refund;
    self.status = .stopped;
}

// --- pure opcode semantics ---

fn add(a: u256, b: u256) u256 {
    return a +% b;
}
fn mul(a: u256, b: u256) u256 {
    return a *% b;
}
fn sub(a: u256, b: u256) u256 {
    return a -% b;
}
fn div(a: u256, b: u256) u256 {
    return if (b == 0) 0 else a / b;
}
fn sdiv(a: u256, b: u256) u256 {
    if (b == 0) return 0;
    const ai: i256 = @bitCast(a);
    const bi: i256 = @bitCast(b);
    if (bi == -1 and ai == std.math.minInt(i256)) return a;
    return @bitCast(@divTrunc(ai, bi));
}
fn mod(a: u256, b: u256) u256 {
    return if (b == 0) 0 else a % b;
}
fn smod(a: u256, b: u256) u256 {
    if (b == 0) return 0;
    const ai: i256 = @bitCast(a);
    const bi: i256 = @bitCast(b);
    if (bi == -1) return 0;
    return @bitCast(@rem(ai, bi));
}
fn addmod(a: u256, b: u256, n: u256) u256 {
    if (n == 0) return 0;
    const sum: u512 = @as(u512, a) + @as(u512, b);
    return @truncate(sum % @as(u512, n));
}
fn mulmod(a: u256, b: u256, n: u256) u256 {
    if (n == 0) return 0;
    const prod: u512 = @as(u512, a) * @as(u512, b);
    return @truncate(prod % @as(u512, n));
}
fn expOp(base_val: u256, exponent: u256) u256 {
    var result: u256 = 1;
    var b = base_val;
    var e = exponent;
    while (e > 0) : (e >>= 1) {
        if (e & 1 == 1) result = result *% b;
        b = b *% b;
    }
    return result;
}
fn signextend(byte_index: u256, x: u256) u256 {
    if (byte_index >= 32) return x;
    const bits: u16 = @intCast((byte_index + 1) * 8);
    const shift: u8 = @intCast(256 - bits);
    const shifted_left = x << shift;
    const signed: i256 = @bitCast(shifted_left);
    return @bitCast(signed >> shift);
}

fn lt(a: u256, b: u256) u256 {
    return if (a < b) 1 else 0;
}
fn gt(a: u256, b: u256) u256 {
    return if (a > b) 1 else 0;
}
fn slt(a: u256, b: u256) u256 {
    return if (@as(i256, @bitCast(a)) < @as(i256, @bitCast(b))) 1 else 0;
}
fn sgt(a: u256, b: u256) u256 {
    return if (@as(i256, @bitCast(a)) > @as(i256, @bitCast(b))) 1 else 0;
}
fn eq(a: u256, b: u256) u256 {
    return if (a == b) 1 else 0;
}
fn iszero(a: u256) u256 {
    return if (a == 0) 1 else 0;
}
fn bitAnd(a: u256, b: u256) u256 {
    return a & b;
}
fn bitOr(a: u256, b: u256) u256 {
    return a | b;
}
fn bitXor(a: u256, b: u256) u256 {
    return a ^ b;
}
fn bitNot(a: u256) u256 {
    return ~a;
}
fn byteOp(index: u256, x: u256) u256 {
    if (index >= 32) return 0;
    const shift: u8 = @intCast((31 - index) * 8);
    return (x >> shift) & 0xff;
}
fn shl(shift_amount: u256, value: u256) u256 {
    if (shift_amount >= 256) return 0;
    return value << @as(u8, @intCast(shift_amount));
}
fn shr(shift_amount: u256, value: u256) u256 {
    if (shift_amount >= 256) return 0;
    return value >> @as(u8, @intCast(shift_amount));
}
fn sar(shift_amount: u256, value: u256) u256 {
    const vi: i256 = @bitCast(value);
    if (shift_amount >= 256) return if (vi < 0) std.math.maxInt(u256) else 0;
    const s: u8 = @intCast(shift_amount);
    return @bitCast(vi >> s);
}

// --- tests ---

fn expectBinaryOp(op: OpCode, a: u256, b: u256, expected: u256) !void {
    var code: std.ArrayList(u8) = .empty;
    defer code.deinit(std.testing.allocator);
    try appendPush32(&code, b);
    try appendPush32(&code, a);
    try code.append(std.testing.allocator, @intFromEnum(op));
    try code.append(std.testing.allocator, @intFromEnum(OpCode.STOP));

    var interp = try Interpreter.init(std.testing.allocator, code.items, 1_000_000);
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(expected, try interp.stack.pop());
}

fn expectTernaryOp(op: OpCode, a: u256, b: u256, c: u256, expected: u256) !void {
    var code: std.ArrayList(u8) = .empty;
    defer code.deinit(std.testing.allocator);
    try appendPush32(&code, c);
    try appendPush32(&code, b);
    try appendPush32(&code, a);
    try code.append(std.testing.allocator, @intFromEnum(op));
    try code.append(std.testing.allocator, @intFromEnum(OpCode.STOP));

    var interp = try Interpreter.init(std.testing.allocator, code.items, 1_000_000);
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(expected, try interp.stack.pop());
}

fn appendPush32(list: *std.ArrayList(u8), value: u256) !void {
    try list.append(std.testing.allocator, @intFromEnum(OpCode.PUSH32));
    var buf: [32]u8 = undefined;
    std.mem.writeInt(u256, &buf, value, .big);
    try list.appendSlice(std.testing.allocator, &buf);
}

const max_u256 = std.math.maxInt(u256);
const min_i256_as_u256: u256 = @bitCast(@as(i256, std.math.minInt(i256)));

test "ADD wraps on overflow" {
    try expectBinaryOp(.ADD, max_u256, 1, 0);
}
test "SUB" {
    try expectBinaryOp(.SUB, 10, 3, 7);
}
test "SUB underflow wraps" {
    try expectBinaryOp(.SUB, 0, 1, max_u256);
}
test "MUL" {
    try expectBinaryOp(.MUL, 3, 4, 12);
}
test "DIV" {
    try expectBinaryOp(.DIV, 10, 3, 3);
}
test "DIV by zero is zero, not a trap" {
    try expectBinaryOp(.DIV, 10, 0, 0);
}
test "SDIV of negative numbers" {
    // -10 / 3 == -3 (truncating toward zero)
    try expectBinaryOp(.SDIV, @bitCast(@as(i256, -10)), 3, @bitCast(@as(i256, -3)));
}
test "SDIV overflow (minInt / -1) wraps to minInt" {
    try expectBinaryOp(.SDIV, min_i256_as_u256, max_u256, min_i256_as_u256);
}
test "MOD" {
    try expectBinaryOp(.MOD, 10, 3, 1);
}
test "SMOD keeps the dividend's sign" {
    try expectBinaryOp(.SMOD, @bitCast(@as(i256, -10)), 3, @bitCast(@as(i256, -1)));
}
test "ADDMOD" {
    try expectTernaryOp(.ADDMOD, 10, 10, 8, 4);
}
test "ADDMOD does not overflow when a + b exceeds u256" {
    try expectTernaryOp(.ADDMOD, max_u256, max_u256, 10, 0);
}
test "MULMOD does not overflow when a * b exceeds u256" {
    try expectTernaryOp(.MULMOD, max_u256, max_u256, 10, 5);
}
test "EXP" {
    try expectBinaryOp(.EXP, 2, 10, 1024);
}
test "SIGNEXTEND of a negative byte fills with ones" {
    try expectBinaryOp(.SIGNEXTEND, 0, 0xff, max_u256);
}
test "SIGNEXTEND of a positive byte is unchanged" {
    try expectBinaryOp(.SIGNEXTEND, 0, 0x7f, 0x7f);
}

test "LT" {
    try expectBinaryOp(.LT, 1, 2, 1);
}
test "SLT treats operands as signed" {
    try expectBinaryOp(.SLT, @bitCast(@as(i256, -1)), 1, 1);
}
test "GT" {
    try expectBinaryOp(.GT, 2, 1, 1);
}
test "EQ" {
    try expectBinaryOp(.EQ, 5, 5, 1);
}
test "ISZERO" {
    var code: std.ArrayList(u8) = .empty;
    defer code.deinit(std.testing.allocator);
    try appendPush32(&code, 0);
    try code.append(std.testing.allocator, @intFromEnum(OpCode.ISZERO));
    try code.append(std.testing.allocator, @intFromEnum(OpCode.STOP));
    var interp = try Interpreter.init(std.testing.allocator, code.items, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 1), try interp.stack.pop());
}
test "AND" {
    try expectBinaryOp(.AND, 0b1100, 0b1010, 0b1000);
}
test "BYTE extracts the big-endian byte at the given index" {
    try expectBinaryOp(.BYTE, 31, 0xab, 0xab);
}
test "SHL" {
    try expectBinaryOp(.SHL, 1, 4, 8);
}
test "SHR" {
    try expectBinaryOp(.SHR, 1, 8, 4);
}
test "SHR by 256 or more is zero" {
    try expectBinaryOp(.SHR, 256, max_u256, 0);
}
test "SAR sign-extends when shifting a negative value" {
    try expectBinaryOp(.SAR, 1, @bitCast(@as(i256, -2)), @bitCast(@as(i256, -1)));
}
test "SAR by 256 or more of a negative value saturates to all ones" {
    try expectBinaryOp(.SAR, 256, min_i256_as_u256, max_u256);
}

test "PUSH0 pushes zero" {
    const code = [_]u8{ @intFromEnum(OpCode.PUSH0), @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
}

test "PUSH1 reads one immediate byte" {
    const code = [_]u8{ @intFromEnum(OpCode.PUSH1), 0x42, @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 0x42), try interp.stack.pop());
}

test "PUSH2 reads two immediate bytes big-endian" {
    const code = [_]u8{ @intFromEnum(OpCode.PUSH2), 0x01, 0x02, @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 0x0102), try interp.stack.pop());
}

test "PUSH zero-pads immediate data that runs off the end of code" {
    const code = [_]u8{ @intFromEnum(OpCode.PUSH2), 0x42 };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 0x4200), try interp.stack.pop());
}

test "DUP1 duplicates the top of the stack" {
    const code = [_]u8{ @intFromEnum(OpCode.PUSH1), 7, @intFromEnum(OpCode.DUP1), @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(usize, 2), interp.stack.len);
    try std.testing.expectEqual(@as(u256, 7), try interp.stack.pop());
    try std.testing.expectEqual(@as(u256, 7), try interp.stack.pop());
}

test "SWAP1 swaps the top two items" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 1,
        @intFromEnum(OpCode.PUSH1), 2,
        @intFromEnum(OpCode.SWAP1),
        @intFromEnum(OpCode.STOP),
    };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 1), try interp.stack.pop());
    try std.testing.expectEqual(@as(u256, 2), try interp.stack.pop());
}

test "POP discards the top of the stack" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 1,
        @intFromEnum(OpCode.PUSH1), 2,
        @intFromEnum(OpCode.POP),
        @intFromEnum(OpCode.STOP),
    };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(usize, 1), interp.stack.len);
    try std.testing.expectEqual(@as(u256, 1), try interp.stack.pop());
}

test "MSTORE then MLOAD round-trips" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0x42,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.MLOAD),
        @intFromEnum(OpCode.STOP),
    };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 0x42), try interp.stack.pop());
}

test "MSTORE8 writes a single byte" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xff,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.MSTORE8),
        @intFromEnum(OpCode.MSIZE),
        @intFromEnum(OpCode.STOP),
    };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 32), try interp.stack.pop());
}

test "KECCAK256 of empty memory range matches the known constant" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.KECCAK256),
        @intFromEnum(OpCode.STOP),
    };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(
        @as(u256, 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470),
        try interp.stack.pop(),
    );
}

test "running off the end of code halts as if by STOP" {
    const code = [_]u8{@intFromEnum(OpCode.PUSH1)};
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.stopped, interp.status);
}

test "an unassigned opcode byte halts as invalid" {
    const code = [_]u8{0x0c};
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.invalid_opcode, interp.status);
}

test "insufficient gas halts as out_of_gas" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 1,
        @intFromEnum(OpCode.PUSH1), 2,
        @intFromEnum(OpCode.ADD),
        @intFromEnum(OpCode.STOP),
    };
    var interp = try Interpreter.init(std.testing.allocator, &code, 5);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.out_of_gas, interp.status);
}

test "popping an empty stack halts as stack_underflow" {
    const code = [_]u8{@intFromEnum(OpCode.ADD)};
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.stack_underflow, interp.status);
}

test "jumping to a non-JUMPDEST byte halts as invalid_jump" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 4,
        @intFromEnum(OpCode.JUMP),
        @intFromEnum(OpCode.STOP),
    };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.invalid_jump, interp.status);
}

test "jumping into a PUSH's immediate data halts as invalid_jump" {
    // Offset 2 holds the byte value 0x5b (JUMPDEST's own opcode byte), but
    // it's the second immediate-data byte of the PUSH2 at offset 0, not a
    // real instruction, so it must not be a valid jump target.
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH2), 0xaa, 0x5b,
        @intFromEnum(OpCode.PUSH1), 2,
        @intFromEnum(OpCode.JUMP),
        @intFromEnum(OpCode.STOP),
    };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.invalid_jump, interp.status);
}

test "JUMP/JUMPI loop counts a stack value down to zero" {
    const push1 = @intFromEnum(OpCode.PUSH1);
    const code = [_]u8{
        push1, 5, // 0,1: counter = 5
        @intFromEnum(OpCode.JUMPDEST), // 2: loop:
        @intFromEnum(OpCode.DUP1), // 3
        @intFromEnum(OpCode.ISZERO), // 4
        push1, 15, // 5,6: push end
        @intFromEnum(OpCode.JUMPI), // 7: if counter == 0, goto end
        push1, 1, // 8,9
        @intFromEnum(OpCode.SWAP1), // 10
        @intFromEnum(OpCode.SUB), // 11: counter -= 1
        push1, 2, // 12,13: push loop
        @intFromEnum(OpCode.JUMP), // 14: goto loop
        @intFromEnum(OpCode.JUMPDEST), // 15: end:
        @intFromEnum(OpCode.STOP), // 16
    };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
}

// --- M2: calling context, RETURN/REVERT, CALL family ---

test "ADDRESS pushes this frame's own address" {
    const code = [_]u8{ @intFromEnum(OpCode.ADDRESS), @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .address = 0x42 });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 0x42), try interp.stack.pop());
}

test "CALLER pushes msg.sender" {
    const code = [_]u8{ @intFromEnum(OpCode.CALLER), @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .caller = 0x99 });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 0x99), try interp.stack.pop());
}

test "CALLVALUE pushes msg.value" {
    const code = [_]u8{ @intFromEnum(OpCode.CALLVALUE), @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .value = 777 });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 777), try interp.stack.pop());
}

test "NUMBER pushes the current block number" {
    const code = [_]u8{ @intFromEnum(OpCode.NUMBER), @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .block = .{ .number = 46147 } });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 46147), try interp.stack.pop());
}

test "TIMESTAMP pushes the current block's timestamp" {
    const code = [_]u8{ @intFromEnum(OpCode.TIMESTAMP), @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .block = .{ .timestamp = 1438269973 } });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 1438269973), try interp.stack.pop());
}

test "COINBASE pushes the current block's miner" {
    const code = [_]u8{ @intFromEnum(OpCode.COINBASE), @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .block = .{ .coinbase = 0xaa } });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 0xaa), try interp.stack.pop());
}

test "GASLIMIT pushes the current block's gas limit" {
    const code = [_]u8{ @intFromEnum(OpCode.GASLIMIT), @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .block = .{ .gas_limit = 5000 } });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 5000), try interp.stack.pop());
}

test "PREVRANDAO pushes the current block's difficulty" {
    const code = [_]u8{ @intFromEnum(OpCode.PREVRANDAO), @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .block = .{ .difficulty = 12345 } });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 12345), try interp.stack.pop());
}

test "BASEFEE pushes the current block's base fee" {
    const code = [_]u8{ @intFromEnum(OpCode.BASEFEE), @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .block = .{ .base_fee = 7 } });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 7), try interp.stack.pop());
}

test "CHAINID pushes the chain id" {
    const code = [_]u8{ @intFromEnum(OpCode.CHAINID), @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .block = .{ .chain_id = 1 } });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 1), try interp.stack.pop());
}

test "SELFBALANCE pushes this frame's own balance from state" {
    const code = [_]u8{ @intFromEnum(OpCode.SELFBALANCE), @intFromEnum(OpCode.STOP) };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x42, 1000);

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .address = 0x42, .state = &state });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 1000), try interp.stack.pop());
}

test "block context is inherited by nested calls" {
    // target: returns NUMBER as a word.
    const target_code = [_]u8{
        @intFromEnum(OpCode.NUMBER),
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1), 32,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.RETURN),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xdd, &target_code);

    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 32, // retSize
        @intFromEnum(OpCode.PUSH1), 0, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH1), 0, // argsOffset
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.PUSH1), 0xdd, // address
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10, // gas
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.STOP),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .number = 46147 },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u256, 1), try interp.stack.pop());
    try std.testing.expectEqual(@as(u256, 46147), try interp.memory.readWord(0));
}

test "CALLDATASIZE pushes the calldata length" {
    const code = [_]u8{ @intFromEnum(OpCode.CALLDATASIZE), @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .calldata = "hello" });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 5), try interp.stack.pop());
}

test "CALLDATALOAD reads a word, zero-padded past the end of calldata" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.CALLDATALOAD),
        @intFromEnum(OpCode.STOP),
    };
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .calldata = &.{0xff} });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 0xff) << (31 * 8), try interp.stack.pop());
}

test "CALLDATACOPY copies calldata into memory, zero-padded past the end" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 4, // size
        @intFromEnum(OpCode.PUSH1), 0, // offset
        @intFromEnum(OpCode.PUSH1), 0, // destOffset
        @intFromEnum(OpCode.CALLDATACOPY),
        @intFromEnum(OpCode.STOP),
    };
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .calldata = &.{ 1, 2 } });
    defer interp.deinit();
    try interp.run();
    const written = try interp.memory.read(0, 4);
    try std.testing.expectEqualSlices(u8, &.{ 1, 2, 0, 0 }, written);
}

test "RETURN captures the memory range as return_data" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0x42,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1), 32,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.RETURN),
    };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 0x42), std.mem.readInt(u256, interp.return_data[0..32], .big));
}

test "REVERT halts as .reverted and still captures output" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0x99,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1), 32,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.REVERT),
    };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.reverted, interp.status);
    try std.testing.expectEqual(@as(u256, 0x99), std.mem.readInt(u256, interp.return_data[0..32], .big));
}

test "CALL runs the callee, transfers value, and copies its return data back" {
    // callee: returns its own CALLVALUE as a 32-byte word.
    const callee_code = [_]u8{
        @intFromEnum(OpCode.CALLVALUE),
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1), 32,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.RETURN),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    const callee_addr: Address = 0xcc;
    try state.setCode(callee_addr, &callee_code);
    try state.setBalance(0xaa, 1000);

    // caller: CALL(gas=10000, addr=0xcc, value=42, argsOffset=0, argsSize=0, retOffset=0, retSize=32)
    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 32, // retSize
        @intFromEnum(OpCode.PUSH1), 0, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH1), 0, // argsOffset
        @intFromEnum(OpCode.PUSH1), 42, // value
        @intFromEnum(OpCode.PUSH1), 0xcc, // address
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10, // gas
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.STOP),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 1), try interp.stack.pop());
    try std.testing.expectEqual(@as(u256, 42), try interp.memory.readWord(0));
    try std.testing.expectEqual(@as(u256, 958), state.getBalance(0xaa));
    try std.testing.expectEqual(@as(u256, 42), state.getBalance(callee_addr));
}

test "DELEGATECALL preserves the caller's own address, caller, and value" {
    // target: returns ADDRESS, CALLER, CALLVALUE as three consecutive words.
    const target_code = [_]u8{
        @intFromEnum(OpCode.ADDRESS),
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.CALLER),
        @intFromEnum(OpCode.PUSH1), 32,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.CALLVALUE),
        @intFromEnum(OpCode.PUSH1), 64,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1), 96,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.RETURN),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xdd, &target_code);

    // caller: DELEGATECALL(gas=10000, addr=0xdd, argsOffset=0, argsSize=0, retOffset=0, retSize=96)
    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 96, // retSize
        @intFromEnum(OpCode.PUSH1), 0, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH1), 0, // argsOffset
        @intFromEnum(OpCode.PUSH1), 0xdd, // address
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10, // gas
        @intFromEnum(OpCode.DELEGATECALL),
        @intFromEnum(OpCode.STOP),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .caller = 0xbb,
        .value = 777,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u256, 1), try interp.stack.pop());
    try std.testing.expectEqual(@as(u256, 0xaa), try interp.memory.readWord(0));
    try std.testing.expectEqual(@as(u256, 0xbb), try interp.memory.readWord(32));
    try std.testing.expectEqual(@as(u256, 777), try interp.memory.readWord(64));
}

test "a value-transferring CALL nested inside a STATICCALL is rejected" {
    // inner: attempts a value-transferring CALL, which must fail in a static context.
    const inner_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // retSize
        @intFromEnum(OpCode.PUSH1), 0, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH1), 0, // argsOffset
        @intFromEnum(OpCode.PUSH1), 1, // value
        @intFromEnum(OpCode.PUSH1), 0xee, // address
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10, // gas
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.STOP),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xdd, &inner_code);

    // caller: STATICCALL(gas, addr=0xdd, argsOffset=0, argsSize=0, retOffset=0, retSize=0)
    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0xdd,
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10,
        @intFromEnum(OpCode.STATICCALL),
        @intFromEnum(OpCode.STOP),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
}

test "REVERT inside a CALL rolls back the value transfer that led to it" {
    const callee_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.REVERT),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xcc, &callee_code);
    try state.setBalance(0xaa, 1000);

    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 42,
        @intFromEnum(OpCode.PUSH1), 0xcc,
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10,
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.STOP),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
    try std.testing.expectEqual(@as(u256, 1000), state.getBalance(0xaa));
    try std.testing.expectEqual(@as(u256, 0), state.getBalance(0xcc));
}

test "CALL at the depth limit fails without executing the callee" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0xcc,
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10,
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
        .depth = max_call_depth,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
}

test "CALL with insufficient balance fails without transferring or executing" {
    const callee_code = [_]u8{@intFromEnum(OpCode.INVALID)};
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xcc, &callee_code);
    try state.setBalance(0xaa, 10);

    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 42,
        @intFromEnum(OpCode.PUSH1), 0xcc,
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10,
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.STOP),
    };
    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
    try std.testing.expectEqual(@as(u256, 10), state.getBalance(0xaa));
    try std.testing.expectEqual(@as(u256, 0), state.getBalance(0xcc));
}

test "CREATE2 address derivation is deterministic and depends on the salt" {
    const addr1 = create2Address(0xaa, 1, "code");
    const addr2 = create2Address(0xaa, 1, "code");
    const addr3 = create2Address(0xaa, 2, "code");
    try std.testing.expectEqual(addr1, addr2);
    try std.testing.expect(addr1 != addr3);
}

test "CREATE deploys the init code's returned bytes as the new account's code" {
    // init code: pushes 3 bytes of "runtime code" as a right-aligned 32-byte
    // word, stores it at memory[0..32], then RETURNs just those 3 bytes
    // (the last 3 of that word, at offset 32-3=29).
    const init_code = [_]u8{
        @intFromEnum(OpCode.PUSH3), 0x60, 0x2a, 0x00,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1), 3,
        @intFromEnum(OpCode.PUSH1), 29,
        @intFromEnum(OpCode.RETURN),
    };
    // PUSH12 below embeds this directly, so it must be exactly 12 bytes.
    try std.testing.expectEqual(@as(usize, 12), init_code.len);

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0xaa, 1000);

    var caller_code: std.ArrayList(u8) = .empty;
    defer caller_code.deinit(std.testing.allocator);
    try caller_code.append(std.testing.allocator, @intFromEnum(OpCode.PUSH12));
    try caller_code.appendSlice(std.testing.allocator, &init_code);
    try caller_code.appendSlice(std.testing.allocator, &.{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1), 12, // size
        @intFromEnum(OpCode.PUSH1), 20, // offset (32 - 12)
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.CREATE),
        @intFromEnum(OpCode.STOP),
    });

    var interp = try Interpreter.initCall(std.testing.allocator, caller_code.items, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    const new_address_word = try interp.stack.pop();
    try std.testing.expect(new_address_word != 0);

    const new_address: Address = @truncate(new_address_word);
    try std.testing.expectEqualSlices(u8, &.{ 0x60, 0x2a, 0x00 }, state.getCode(new_address));
    try std.testing.expectEqual(@as(u64, 1), state.get(0xaa).nonce);
}

test "SSTORE then SLOAD round-trips within the same execution" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 42,
        @intFromEnum(OpCode.PUSH1), 1,
        @intFromEnum(OpCode.SSTORE),
        @intFromEnum(OpCode.PUSH1), 1,
        @intFromEnum(OpCode.SLOAD),
        @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 42), try interp.stack.pop());
    try std.testing.expectEqual(@as(u256, 42), state.getStorage(0xaa, 1));
}

test "SSTORE clearing a nonzero slot to zero accumulates a refund" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 1,
        @intFromEnum(OpCode.SSTORE),
        @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setStorage(0xaa, 1, 99);

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(gas.sstore_clear_refund, interp.refund);
}

test "SSTORE writing a nonzero value accumulates no refund" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 42,
        @intFromEnum(OpCode.PUSH1), 1,
        @intFromEnum(OpCode.SSTORE),
        @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u64, 0), interp.refund);
}

test "SSTORE clearing an already-zero slot accumulates no refund" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 1,
        @intFromEnum(OpCode.SSTORE),
        @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u64, 0), interp.refund);
}

test "a nested CALL's refund propagates to the caller on success" {
    const callee_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.PUSH1), 1, // slot
        @intFromEnum(OpCode.SSTORE),
        @intFromEnum(OpCode.STOP),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xdd, &callee_code);
    try state.setStorage(0xdd, 1, 99); // pre-existing value the callee clears

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

    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(gas.sstore_clear_refund, interp.refund);
}

test "a reverted nested CALL's refund is dropped, not propagated" {
    const callee_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.PUSH1), 1, // slot
        @intFromEnum(OpCode.SSTORE),
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.REVERT),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xdd, &callee_code);
    try state.setStorage(0xdd, 1, 99);

    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0xdd,
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10,
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.STOP),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u64, 0), interp.refund);
    try std.testing.expectEqual(@as(u256, 99), state.getStorage(0xdd, 1)); // reverted, unchanged
}

test "SSTORE inside a STATICCALL is rejected" {
    const inner_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 1,
        @intFromEnum(OpCode.PUSH1), 1,
        @intFromEnum(OpCode.SSTORE),
        @intFromEnum(OpCode.STOP),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xdd, &inner_code);

    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0xdd,
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10,
        @intFromEnum(OpCode.STATICCALL),
        @intFromEnum(OpCode.STOP),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
    try std.testing.expectEqual(@as(u256, 0), state.getStorage(0xdd, 1));
}

test "a successful CALL's storage write persists" {
    const callee_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 99,
        @intFromEnum(OpCode.PUSH1), 1,
        @intFromEnum(OpCode.SSTORE),
        @intFromEnum(OpCode.STOP),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xcc, &callee_code);

    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // retSize
        @intFromEnum(OpCode.PUSH1), 0, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH1), 0, // argsOffset
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.PUSH1), 0xcc, // address
        @intFromEnum(OpCode.PUSH3), 0x03, 0x0d, 0x40, // gas (200000, enough for SSTORE_SET)
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.STOP),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u256, 1), try interp.stack.pop());
    try std.testing.expectEqual(@as(u256, 99), state.getStorage(0xcc, 1));
}

test "REVERT inside a CALL rolls back its storage write" {
    const callee_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 99,
        @intFromEnum(OpCode.PUSH1), 1,
        @intFromEnum(OpCode.SSTORE),
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.REVERT),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xcc, &callee_code);

    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // retSize
        @intFromEnum(OpCode.PUSH1), 0, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH1), 0, // argsOffset
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.PUSH1), 0xcc, // address
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10, // gas
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.STOP),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
    try std.testing.expectEqual(@as(u256, 0), state.getStorage(0xcc, 1));
}

test "BALANCE reads another account's balance" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xbb,
        @intFromEnum(OpCode.BALANCE),
        @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0xbb, 555);

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 555), try interp.stack.pop());
}

test "ORIGIN pushes the transaction's original sender, not the immediate caller" {
    const code = [_]u8{ @intFromEnum(OpCode.ORIGIN), @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .caller = 0xbb,
        .tx = .{ .origin = 0xcc },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u256, 0xcc), try interp.stack.pop());
}

test "GASPRICE pushes the transaction's gas price" {
    const code = [_]u8{ @intFromEnum(OpCode.GASPRICE), @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .tx = .{ .gas_price = 42 },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u256, 42), try interp.stack.pop());
}

test "CODESIZE pushes this frame's own code length" {
    const code = [_]u8{ @intFromEnum(OpCode.CODESIZE), @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u256, code.len), try interp.stack.pop());
}

test "CODECOPY copies this frame's own code into memory, zero-padded past the end" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 4, // size
        @intFromEnum(OpCode.PUSH1), 0, // offset
        @intFromEnum(OpCode.PUSH1), 0, // dest
        @intFromEnum(OpCode.CODECOPY),
        @intFromEnum(OpCode.STOP),
    };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    var word_bytes: [32]u8 = undefined;
    std.mem.writeInt(u256, &word_bytes, try interp.memory.readWord(0), .big);
    var expected: [32]u8 = [_]u8{0} ** 32;
    @memcpy(expected[0..4], code[0..4]);
    try std.testing.expectEqualSlices(u8, &expected, &word_bytes);
}

test "EXTCODESIZE reads another account's code length" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xbb,
        @intFromEnum(OpCode.EXTCODESIZE),
        @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xbb, &.{ 1, 2, 3 });

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u256, 3), try interp.stack.pop());
}

test "EXTCODECOPY copies another account's code into memory" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 3, // size
        @intFromEnum(OpCode.PUSH1), 0, // offset
        @intFromEnum(OpCode.PUSH1), 0, // dest
        @intFromEnum(OpCode.PUSH1), 0xbb, // address
        @intFromEnum(OpCode.EXTCODECOPY),
        @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xbb, &.{ 0xaa, 0xbb, 0xcc });

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    var word_bytes: [32]u8 = undefined;
    std.mem.writeInt(u256, &word_bytes, try interp.memory.readWord(0), .big);
    try std.testing.expectEqualSlices(u8, &.{ 0xaa, 0xbb, 0xcc }, word_bytes[0..3]);
}

test "EXTCODEHASH is 0 for an account that's never been touched" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xbb,
        @intFromEnum(OpCode.EXTCODEHASH),
        @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
}

test "EXTCODEHASH of an existing account is keccak256 of its code" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xbb,
        @intFromEnum(OpCode.EXTCODEHASH),
        @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xbb, &.{ 1, 2, 3 });

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(keccak256(&.{ 1, 2, 3 }), try interp.stack.pop());
}

test "BLOCKHASH looks up a recent block's hash from recent_hashes" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 8, // block 10 - 2 = 8
        @intFromEnum(OpCode.BLOCKHASH),
        @intFromEnum(OpCode.STOP),
    };
    const recent_hashes = [_]u256{ 0xaa, 0xbb, 0xcc }; // blocks 9, 8, 7
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .block = .{ .number = 10, .recent_hashes = &recent_hashes },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u256, 0xbb), try interp.stack.pop());
}

test "BLOCKHASH returns 0 for the current block, a future block, or one over 256 back" {
    const recent_hashes = [_]u256{0xaa};
    const block: BlockContext = .{ .number = 300, .recent_hashes = &recent_hashes };

    for ([_]u256{ 300, 301, 43 }) |requested| {
        const code = [_]u8{
            @intFromEnum(OpCode.PUSH2), @truncate(requested >> 8), @truncate(requested),
            @intFromEnum(OpCode.BLOCKHASH),
            @intFromEnum(OpCode.STOP),
        };
        var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .block = block });
        defer interp.deinit();
        try interp.run();
        try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
    }
}

test "BLOCKHASH returns 0 for a block beyond how much recent_hashes actually covers" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 5, // block 10 - 5 = 5, within the 256-block window but past what's supplied
        @intFromEnum(OpCode.BLOCKHASH),
        @intFromEnum(OpCode.STOP),
    };
    const recent_hashes = [_]u256{ 0xaa, 0xbb }; // only blocks 9 and 8
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .block = .{ .number = 10, .recent_hashes = &recent_hashes },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
}

test "RETURNDATASIZE returns the last CALL's output length" {
    const callee_code = [_]u8{
        @intFromEnum(OpCode.PUSH4), 0xde, 0xad, 0xbe, 0xef,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1), 4,
        @intFromEnum(OpCode.PUSH1), 28,
        @intFromEnum(OpCode.RETURN),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xcc, &callee_code);

    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // retSize
        @intFromEnum(OpCode.PUSH1), 0, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH1), 0, // argsOffset
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.PUSH1), 0xcc, // address
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10, // gas
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.POP), // discard CALL's success flag
        @intFromEnum(OpCode.RETURNDATASIZE),
        @intFromEnum(OpCode.STOP),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 4), try interp.stack.pop());
}

test "RETURNDATACOPY copies the last CALL's output into memory" {
    const callee_code = [_]u8{
        @intFromEnum(OpCode.PUSH4), 0xde, 0xad, 0xbe, 0xef,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1), 4,
        @intFromEnum(OpCode.PUSH1), 28,
        @intFromEnum(OpCode.RETURN),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xcc, &callee_code);

    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // retSize (don't copy via CALL itself)
        @intFromEnum(OpCode.PUSH1), 0, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH1), 0, // argsOffset
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.PUSH1), 0xcc, // address
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10, // gas
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.POP), // discard CALL's success flag
        @intFromEnum(OpCode.PUSH1), 4, // size
        @intFromEnum(OpCode.PUSH1), 0, // offset
        @intFromEnum(OpCode.PUSH1), 0, // dest
        @intFromEnum(OpCode.RETURNDATACOPY),
        @intFromEnum(OpCode.STOP),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    var word_bytes: [32]u8 = undefined;
    std.mem.writeInt(u256, &word_bytes, try interp.memory.readWord(0), .big);
    try std.testing.expectEqualSlices(u8, &.{ 0xde, 0xad, 0xbe, 0xef }, word_bytes[0..4]);
}

test "RETURNDATACOPY reading past the last call's output is invalid" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 1, // size: nothing has been called yet, so any size is out of bounds
        @intFromEnum(OpCode.PUSH1), 0, // offset
        @intFromEnum(OpCode.PUSH1), 0, // dest
        @intFromEnum(OpCode.RETURNDATACOPY),
    };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.invalid_opcode, interp.status);
}

test "LOG0 charges gas and reads memory without erroring" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 4,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.LOG0),
        @intFromEnum(OpCode.STOP),
    };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expect(interp.gas_remaining < 1_000_000);
}

test "LOG1 inside a STATICCALL is rejected" {
    const inner_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // topic
        @intFromEnum(OpCode.PUSH1), 0, // size
        @intFromEnum(OpCode.PUSH1), 0, // offset
        @intFromEnum(OpCode.LOG1),
        @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xdd, &inner_code);

    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0xdd,
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10,
        @intFromEnum(OpCode.STATICCALL),
        @intFromEnum(OpCode.STOP),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
}

test "CALLCODE keeps this frame's own storage context but resets caller/value" {
    // target: returns ADDRESS, CALLER, CALLVALUE as three consecutive words.
    const target_code = [_]u8{
        @intFromEnum(OpCode.ADDRESS),
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.CALLER),
        @intFromEnum(OpCode.PUSH1), 32,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.CALLVALUE),
        @intFromEnum(OpCode.PUSH1), 64,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1), 96,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.RETURN),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xdd, &target_code);
    try state.setBalance(0xaa, 1000);

    // caller: CALLCODE(gas=10000, addr=0xdd, value=55, argsOffset=0, argsSize=0, retOffset=0, retSize=96)
    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 96, // retSize
        @intFromEnum(OpCode.PUSH1), 0, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH1), 0, // argsOffset
        @intFromEnum(OpCode.PUSH1), 55, // value
        @intFromEnum(OpCode.PUSH1), 0xdd, // address
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10, // gas
        @intFromEnum(OpCode.CALLCODE),
        @intFromEnum(OpCode.STOP),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .caller = 0xbb,
        .value = 777,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u256, 1), try interp.stack.pop());
    try std.testing.expectEqual(@as(u256, 0xaa), try interp.memory.readWord(0)); // own storage context
    try std.testing.expectEqual(@as(u256, 0xaa), try interp.memory.readWord(32)); // caller reset to self, not preserved
    try std.testing.expectEqual(@as(u256, 55), try interp.memory.readWord(64)); // value is this call's own, not preserved
    // Value "moved" from 0xaa to itself: net no-op, but still had to afford it.
    try std.testing.expectEqual(@as(u256, 1000), state.getBalance(0xaa));
}

test "SELFDESTRUCT transfers balance to the beneficiary and wipes code" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xbb,
        @intFromEnum(OpCode.SELFDESTRUCT),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xaa, &code);
    try state.setBalance(0xaa, 500);
    try state.setBalance(0xbb, 10);

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 0), state.getBalance(0xaa));
    try std.testing.expectEqual(@as(u256, 510), state.getBalance(0xbb));
    try std.testing.expectEqualSlices(u8, &.{}, state.getCode(0xaa));
    try std.testing.expectEqual(gas.selfdestruct_refund, interp.refund);
}

test "SELFDESTRUCT to yourself burns the balance instead of moving it" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xaa,
        @intFromEnum(OpCode.SELFDESTRUCT),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xaa, &code);
    try state.setBalance(0xaa, 500);

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u256, 0), state.getBalance(0xaa));
}

test "SELFDESTRUCT inside a reverted CALL restores the destroyed account's code" {
    const callee_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xbb,
        @intFromEnum(OpCode.SELFDESTRUCT),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xcc, &callee_code);
    try state.setBalance(0xcc, 500);

    // caller: CALL(gas, addr=0xcc, ...), then REVERT unconditionally.
    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // retSize
        @intFromEnum(OpCode.PUSH1), 0, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH1), 0, // argsOffset
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.PUSH1), 0xcc, // address
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10, // gas
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.POP),
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.REVERT),
    };

    // Mirrors what `Evm.call` does around every top-level interpreter run;
    // without it the outer REVERT below would have nothing to undo.
    const cp = state.checkpoint();
    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();
    if (interp.status != .stopped) state.revertTo(cp);

    try std.testing.expectEqual(Status.reverted, interp.status);
    try std.testing.expectEqual(@as(u256, 500), state.getBalance(0xcc));
    try std.testing.expectEqualSlices(u8, &callee_code, state.getCode(0xcc));
}
