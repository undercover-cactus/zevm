//! The bytecode interpreter: a fetch/decode/dispatch loop over a `Stack`
//! and `Memory`, charging static per-opcode gas plus memory expansion.
//! Implements the full Frontier opcode set against a real, shared `State`.
//! Block/environment context is threaded in from `Evm`, not read through a
//! separate `Host` interface; this concrete design is deliberate, see
//! `State.zig`'s own doc comment.

const std = @import("std");
const builtin = @import("builtin");
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
const Fork = @import("Fork.zig").Fork;

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
    /// Which fork's rules apply to this block, for the few opcode/gas
    /// behaviors that differ across forks (e.g. `DELEGATECALL`'s
    /// availability, `CREATE`'s code-deposit-OOG behavior).
    fork: Fork = .frontier,
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
/// bytes of runtime code fails. Also used by `Evm.create` for top-level
/// contract-creation transactions.
pub const max_code_size: usize = 24576;

/// The RIPEMD160 precompile. In block 2,675,119, it was touched-and-cleared
/// (EIP-161) despite the calling frame running out of gas — an obscure,
/// real client bug preserved in consensus (see `call`'s use of this).
const ripemd160_address: Address = 0x03;

allocator: std.mem.Allocator,
code: []const u8,
pc: usize = 0,
stack: Stack,
memory: Memory,
gas_remaining: u64,
/// Accumulated gas refund (Frontier's flat `SSTORE`-clears-a-slot rule, see
/// `sstore`). Not capped here, since the cap only makes sense relative to a
/// transaction's total gas used, which this frame alone doesn't know.
/// Signed, because EIP-2200 can take a refund back: a nested frame that
/// writes a slot its caller had cleared subtracts the clear refund, and that
/// frame's own counter starts at zero, so it legitimately goes negative
/// before being folded into the caller's.
refund: i64 = 0,
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
    /// Already-analyzed jumpdests for `code`, when the caller has one on
    /// hand (`State.getJumpdest`, for an existing on-chain contract) —
    /// cloned rather than re-scanning `code` from scratch. `null` (the
    /// default: every test, and `CREATE`'s one-shot init code) falls back
    /// to analyzing `code` directly, same as always.
    jumpdest: ?*const std.DynamicBitSetUnmanaged = null,
};

pub fn initCall(allocator: std.mem.Allocator, code: []const u8, gas_limit: u64, params: CallParams) !Interpreter {
    return .{
        .allocator = allocator,
        .code = code,
        .memory = Memory.init(allocator),
        .gas_remaining = gas_limit,
        .jumpdest = if (params.jumpdest) |precomputed|
            try precomputed.clone(allocator)
        else
            try analyzeJumpdests(allocator, code),
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
/// Scans `code` once for valid `JUMPDEST` positions. Pure function of the
/// bytecode alone, so `State` caches the result per account (see
/// `State.getJumpdest`) rather than this running again on every single
/// `CALL` to the same already-deployed contract — a real, measured hot
/// path (~60% of total CPU time replaying real mainnet history, since
/// popular contracts get called over and over).
pub fn analyzeJumpdests(allocator: std.mem.Allocator, code: []const u8) !std.DynamicBitSetUnmanaged {
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
        if (step_trace_enabled) try self.stepTraced() else try self.step();
    }
}

// DEBUG: one-off single-transaction opcode tracer, for diffing zevm's
// execution against revm's EIP-3155 trace of the same real historical
// transaction (see `examples/rpc_compare.zig`) — built during the
// investigation of a genuine balance divergence found deep into Byzantium
// era1 validation (a real historical transaction under-crediting an
// account relative to its real receipt). Deliberately a separate flag from
// `debug_trace_enabled` above: that one is throttled (every 1000 steps) to
// stay safe across a multi-million-block replay, whereas this prints every
// single step unthrottled — fine for one transaction, not for a replay.
pub var step_trace_enabled: bool = false;

fn stepTraced(self: *Interpreter) !void {
    const pc_before = self.pc;
    const gas_before = self.gas_remaining;
    const op_byte: u8 = if (pc_before < self.code.len) self.code[pc_before] else 0;
    const op_name: []const u8 = if (pc_before >= self.code.len)
        "STOP"
    else if (op_byte >= @intFromEnum(OpCode.PUSH1) and op_byte <= @intFromEnum(OpCode.PUSH32))
        "PUSH"
    else if (op_byte >= @intFromEnum(OpCode.DUP1) and op_byte <= @intFromEnum(OpCode.DUP16))
        "DUP"
    else if (op_byte >= @intFromEnum(OpCode.SWAP1) and op_byte <= @intFromEnum(OpCode.SWAP16))
        "SWAP"
    else
        @tagName(@as(OpCode, @enumFromInt(op_byte)));

    std.debug.print("{{\"pc\":{d},\"depth\":{d},\"opName\":\"{s}\",\"op\":{d},\"gas\":\"0x{x}\",\"stack\":[", .{ pc_before, self.depth, op_name, op_byte, gas_before });
    for (self.stack.items[0..self.stack.len], 0..) |v, i| {
        if (i != 0) std.debug.print(",", .{});
        std.debug.print("\"0x{x}\"", .{v});
    }
    std.debug.print("]}}\n", .{});

    try self.step();
}

// DEBUG: era1-replay divergence hunt scaffolding, left in place per user
// request. Set `debug_trace_address` and flip `debug_trace_enabled` to
// `true`, then rebuild, to trace a specific frame's own opcode-by-opcode
// execution (pc, opcode byte, gas_remaining) against a real/revm trace.
// `debug_trace_enabled` gates every check below, so it's always a hard
// no-op when off — no address value is a safe "definitely inactive"
// sentinel to rely on instead (`0x0` looked inert but isn't, see
// `State.zig`'s `debug_enabled`); leaving this pointed at a stale address
// from an earlier hunt (enabled or not) silently reintroduces a per-opcode
// `std.debug.print` that dominates wall time over a multi-million-block
// replay (confirmed: ~13x slower, 23M+ lines for one prior run) without
// anyone noticing until the run looks "stuck."
const debug_trace_enabled = false;
const debug_trace_address: Address = 0x0;
// DEBUG: gates the `is_new_account` trace in `call()` — see its own
// comment there.
const debug_is_new_account_enabled = false;
// Retargeted at the "fromshanghaiwithlove" DoS contract's 256-call loop in
// block 2,327,528, where zevm charges two fewer 25,000 new-account fees
// than real chain.
const debug_is_new_account_block: u64 = 2_327_528;
const debug_is_new_account_caller: Address = 0xe53c52acf5f396d978e84ab48f16c13fb03eeffe;
// DEBUG: temporary safety valve for a genuine multi-hour stall found around
// block 2,707,868 during Spurious Dragon validation. Unlike
// `debug_trace_address` (which only fires for one specific address, and
// turned out to be the wrong culprit to chase — a prior guess based on it
// panicked at block 1,976,111, in already-validated pre-Spurious-Dragon
// territory, just from legitimate cumulative activity across many
// unrelated transactions), this counts *every* opcode step across *every*
// address, reset at the start of each transaction by
// `Evm.executeTransaction`. No real transaction can legitimately execute
// anywhere near this many steps (even an all-zero-cost-opcode adversarial
// sequence would need a code buffer this codebase can't hold), so tripping
// it means a genuine unbounded loop within a single transaction.
//
// Off unless re-enabled: it ran on every opcode of every replay, a global
// load, increment and compare that came to ~2-3% of all replay time once
// the hunt it was built for was long over. `debug_trace_enabled` needs the
// count too, so either flag turns it back on.
const debug_step_limit_enabled = false;
pub var debug_total_step_count: u64 = 0;
const debug_total_step_limit: u64 = 20_000_000;

fn step(self: *Interpreter) !void {
    if (self.pc >= self.code.len) {
        self.status = .stopped;
        return;
    }

    const byte = self.code[self.pc];
    if (debug_step_limit_enabled or debug_trace_enabled) debug_total_step_count += 1;
    if (debug_step_limit_enabled and debug_total_step_count > debug_total_step_limit) {
        std.debug.panic(
            "a single transaction exceeded {d} total opcode steps: block={d} address={x} pc={d} op={x} gas_remaining={d} depth={d}",
            .{ debug_total_step_limit, self.block.number, self.address, self.pc, byte, self.gas_remaining, self.depth },
        );
    }
    if (debug_trace_enabled and self.address == debug_trace_address) {
        if (debug_total_step_count % 1000 == 0) {
            std.debug.print("DEBUG step: block={d} pc={d} op={x} gas={d} step_count={d}\n", .{ self.block.number, self.pc, byte, self.gas_remaining, debug_total_step_count });
        }
    }

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
        .SHL => {
            // EIP-145: not available before Constantinople.
            if (!self.block.fork.atLeast(.constantinople)) {
                self.status = .invalid_opcode;
            } else {
                self.binaryOp(gas.verylow, shl);
            }
        },
        .SHR => {
            if (!self.block.fork.atLeast(.constantinople)) {
                self.status = .invalid_opcode;
            } else {
                self.binaryOp(gas.verylow, shr);
            }
        },
        .SAR => {
            if (!self.block.fork.atLeast(.constantinople)) {
                self.status = .invalid_opcode;
            } else {
                self.binaryOp(gas.verylow, sar);
            }
        },

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
            // EIP-3855: not available before Shanghai.
            if (!self.block.fork.atLeast(.shanghai)) {
                self.status = .invalid_opcode;
                return;
            }
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
            const address256 = self.popStack() orelse return;
            const state = self.state orelse {
                self.status = .invalid_opcode;
                return;
            };
            const address: Address = @truncate(address256);
            if (!self.chargeGas(try self.accountAccessCost(state, address, if (self.block.fork.atLeast(.istanbul))
                gas.balance_1884
            else if (self.block.fork.atLeast(.tangerine_whistle))
                gas.balance_150
            else
                gas.balance))) return;
            self.pushStack(state.getBalance(address));
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
            const address256 = self.popStack() orelse return;
            const state = self.state orelse {
                self.status = .invalid_opcode;
                return;
            };
            const address: Address = @truncate(address256);
            if (!self.chargeGas(try self.accountAccessCost(state, address, if (self.block.fork.atLeast(.tangerine_whistle)) gas.extcode_150 else gas.extcode))) return;
            self.pushStack(@as(u256, state.getCode(address).len));
            self.pc += 1;
        },
        .EXTCODECOPY => try self.extcodecopy(),
        .RETURNDATASIZE => {
            // EIP-211: not available before Byzantium.
            if (!self.block.fork.atLeast(.byzantium)) {
                self.status = .invalid_opcode;
                return;
            }
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(@as(u256, self.last_return_data.len));
            self.pc += 1;
        },
        .RETURNDATACOPY => {
            // EIP-211: not available before Byzantium.
            if (!self.block.fork.atLeast(.byzantium)) {
                self.status = .invalid_opcode;
                return;
            }
            try self.returndatacopy();
        },
        .EXTCODEHASH => {
            // EIP-1052: not available before Constantinople.
            if (!self.block.fork.atLeast(.constantinople)) {
                self.status = .invalid_opcode;
                return;
            }
            // 400 per EIP-1052, not `gas.extcode`: that is Frontier's 20 for
            // EXTCODESIZE, and charging it here undercharged every
            // EXTCODEHASH by 380 gas. Found at mainnet block 7,398,462.
            const address256 = self.popStack() orelse return;
            const state = self.state orelse {
                self.status = .invalid_opcode;
                return;
            };
            const address: Address = @truncate(address256);
            if (!self.chargeGas(try self.accountAccessCost(state, address, if (self.block.fork.atLeast(.istanbul)) gas.extcodehash_1884 else gas.extcodehash))) return;
            // EIP-1052 returns 0 for an account that "does not exist or is
            // empty (as defined by EIP-161)" — so `isAlive`, not `exists`.
            // An existing-but-empty account (zero nonce, zero balance, no
            // code) hashes to 0 here, *not* to `keccak256("")`; those are
            // different answers and only the first one is correct.
            self.pushStack(if (state.isAlive(address)) keccak256(state.getCode(address)) else 0);
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
            // EIP-3198: not available before London.
            if (!self.block.fork.atLeast(.london)) {
                self.status = .invalid_opcode;
                return;
            }
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(self.block.base_fee);
            self.pc += 1;
        },
        .CHAINID => {
            // EIP-1344: not available before Istanbul.
            if (!self.block.fork.atLeast(.istanbul)) {
                self.status = .invalid_opcode;
                return;
            }
            if (!self.chargeGas(gas.base)) return;
            self.pushStack(self.block.chain_id);
            self.pc += 1;
        },
        .SELFBALANCE => {
            // EIP-1884: not available before Istanbul.
            if (!self.block.fork.atLeast(.istanbul)) {
                self.status = .invalid_opcode;
                return;
            }
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
        .REVERT => {
            // EIP-140: not available before Byzantium. Real pre-Byzantium
            // mainnet treats this byte as any other undefined opcode — an
            // immediate exceptional halt forfeiting all remaining gas —
            // not a graceful revert-with-output. A real contract can
            // still contain this byte pre-Byzantium (e.g. a Solidity
            // compiler already emitting REVERT for require()/assert()
            // ahead of the fork that gives it meaning), so this isn't
            // just a defensive check; real mainnet has already been
            // observed hitting it.
            if (self.block.fork.atLeast(.byzantium)) {
                try self.haltWithOutput(.reverted);
            } else {
                self.status = .invalid_opcode;
            }
        },

        .CALL => try self.call(.call),
        .CALLCODE => try self.call(.callcode),
        .STATICCALL => {
            // EIP-214: not available before Byzantium.
            if (!self.block.fork.atLeast(.byzantium)) {
                self.status = .invalid_opcode;
            } else {
                try self.call(.staticcall);
            }
        },
        .DELEGATECALL => {
            // EIP-7: not available before Homestead.
            if (self.block.fork == .frontier) {
                self.status = .invalid_opcode;
            } else {
                try self.call(.delegatecall);
            }
        },

        .CREATE => try self.createOp(.create),
        .CREATE2 => {
            // EIP-1014: not available before Constantinople.
            if (!self.block.fork.atLeast(.constantinople)) {
                self.status = .invalid_opcode;
            } else {
                try self.createOp(.create2);
            }
        },

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

/// What touching `address` costs from Berlin on (EIP-2929): warm or cold,
/// warming it either way. Before Berlin there was no access tracking, and
/// the opcode's own flat `pre_berlin` price applies instead.
fn accountAccessCost(self: *Interpreter, state: *State, address: Address, pre_berlin: u64) !u64 {
    if (!self.block.fork.atLeast(.berlin)) return pre_berlin;
    return if (try state.warmAddress(address)) gas.warm_storage_read_2929 else gas.cold_account_access_2929;
}

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
    if (!self.chargeGas(gas.expCost(exponent, self.block.fork.atLeast(.spurious_dragon)))) return;
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

/// Converts an `(offset, size)` memory-region pair, mirroring real
/// Ethereum's rule that a zero-size region never touches memory at all —
/// so `offset` isn't validated in that case either. Real bytecode routinely
/// leaves a stale, arbitrarily large leftover value in the offset slot
/// when size is 0 and expects it to be ignored: the standard Solidity
/// `.transfer()`/`.send()` compiles to exactly this (`CALL` with
/// `argsSize`/`retSize` both 0 and whatever the free-memory pointer
/// happened to be sitting in the offset slots), so validating offset
/// unconditionally makes an ordinary, successful real-mainnet call fail
/// with a bogus out-of-gas — confirmed via a real historical transaction
/// during Byzantium era1 validation (block 4,890,213, a CryptoKitties
/// auction payout) that zevm rejected this way despite it succeeding on
/// real mainnet with gas to spare.
fn toMemRegion(self: *Interpreter, offset256: u256, size256: u256) ?struct { offset: usize, size: usize } {
    const size = self.toMemIndex(size256) orelse return null;
    if (size == 0) return .{ .offset = 0, .size = 0 };
    const offset = self.toMemIndex(offset256) orelse return null;
    return .{ .offset = offset, .size = size };
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
    const region = self.toMemRegion(offset256, size256) orelse return;
    if (!self.chargeMemoryExpansion(region.offset, region.size)) return;
    if (!self.chargeGas(gas.keccak256_word * ((region.size + 31) / 32))) return;
    const data = try self.memory.read(region.offset, region.size);
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
    const region = self.toMemRegion(dest256, size256) orelse return;
    if (!self.chargeMemoryExpansion(region.offset, region.size)) return;
    if (!self.chargeGas(gas.copy_word * ((region.size + 31) / 32))) return;
    if (region.size == 0) {
        self.pc += 1;
        return;
    }

    const src_offset = std.math.cast(usize, offset256) orelse std.math.maxInt(usize);
    const buf = try self.allocator.alloc(u8, region.size);
    defer self.allocator.free(buf);
    var i: usize = 0;
    while (i < region.size) : (i += 1) {
        buf[i] = readPadded(src, src_offset +| i);
    }
    try self.memory.write(region.offset, buf);
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
    const address256 = self.popStack() orelse return;
    const dest256 = self.popStack() orelse return;
    const offset256 = self.popStack() orelse return;
    const size256 = self.popStack() orelse return;
    const state = self.state orelse {
        self.status = .invalid_opcode;
        return;
    };
    const address: Address = @truncate(address256);
    if (!self.chargeGas(try self.accountAccessCost(state, address, if (self.block.fork.atLeast(.tangerine_whistle)) gas.extcode_150 else gas.extcode))) return;
    try self.copyToMemory(state.getCode(address), dest256, offset256, size256);
}

/// Unlike `CALLDATACOPY`/`CODECOPY`, `RETURNDATACOPY` doesn't zero-pad past
/// the end of `last_return_data`: reading out of bounds is invalid
/// (EIP-211), not silently zero-filled.
fn returndatacopy(self: *Interpreter) !void {
    if (!self.chargeGas(gas.verylow)) return;
    const dest256 = self.popStack() orelse return;
    const offset256 = self.popStack() orelse return;
    const size256 = self.popStack() orelse return;
    const src_region = self.toMemRegion(offset256, size256) orelse return;
    if (src_region.offset + src_region.size > self.last_return_data.len) {
        self.status = .invalid_opcode;
        return;
    }
    const dest_region = self.toMemRegion(dest256, size256) orelse return;
    if (!self.chargeMemoryExpansion(dest_region.offset, dest_region.size)) return;
    if (!self.chargeGas(gas.copy_word * ((dest_region.size + 31) / 32))) return;
    if (dest_region.size == 0) {
        self.pc += 1;
        return;
    }
    try self.memory.write(dest_region.offset, self.last_return_data[src_region.offset..][0..src_region.size]);
    self.pc += 1;
}

fn haltWithOutput(self: *Interpreter, status: Status) !void {
    const offset256 = self.popStack() orelse return;
    const size256 = self.popStack() orelse return;
    const region = self.toMemRegion(offset256, size256) orelse return;
    if (!self.chargeMemoryExpansion(region.offset, region.size)) return;
    const data = try self.memory.read(region.offset, region.size);
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
    const slot = self.popStack() orelse return;
    const state = self.state orelse {
        self.status = .invalid_opcode;
        return;
    };
    const cost = if (self.block.fork.atLeast(.berlin))
        if (try state.warmSlot(self.address, slot)) gas.warm_storage_read_2929 else gas.cold_sload_2929
    else if (self.block.fork.atLeast(.istanbul))
        gas.sload_1884
    else if (self.block.fork.atLeast(.tangerine_whistle))
        gas.sload_150
    else
        gas.sload;
    if (!self.chargeGas(cost)) return;
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
    const current = state.getStorage(self.address, slot);

    if (self.block.fork.atLeast(.istanbul)) {
        // EIP-2200's sentry: an SSTORE needs strictly more than the 2300-gas
        // stipend in hand before it may begin. Checked before any charge,
        // and an exceptional halt rather than a graceful stop.
        if (self.gas_remaining <= gas.sstore_sentry_2200) {
            self.status = .out_of_gas;
            self.gas_remaining = 0;
            return;
        }

        // EIP-2929 (Berlin) keeps EIP-2200's structure and reprices it: a
        // cold slot pays the cold surcharge once, up front; "looking" costs
        // a warm read; and a real reset is cheaper by exactly the cold
        // surcharge, since that lookup has already been paid for. The
        // restore refunds below are written as differences between these,
        // which is what makes them land on the EIP's 19,900 and 2,800.
        const berlin = self.block.fork.atLeast(.berlin);
        if (berlin and !try state.warmSlot(self.address, slot)) {
            if (!self.chargeGas(gas.cold_sload_2929)) return;
        }
        const original = state.originalStorage(self.address, slot);
        const sload_cost = if (berlin) gas.warm_storage_read_2929 else gas.sload_1884;
        const reset_cost = if (berlin) gas.sstore_reset - gas.cold_sload_2929 else gas.sstore_reset;
        // EIP-3529 (London): clearing a slot refunds only what it saves.
        const clear_refund: i64 = if (self.block.fork.atLeast(.london)) gas.sstore_clear_refund_3529 else gas.sstore_clear_refund;

        if (current == value) {
            // A write that changes nothing pays only for having looked.
            if (!self.chargeGas(sload_cost)) return;
        } else if (original == current) {
            // First change to this slot in this transaction, so the slot is
            // genuinely moving and is priced as a real write.
            if (original == 0) {
                if (!self.chargeGas(gas.sstore_set)) return;
            } else {
                if (!self.chargeGas(reset_cost)) return;
                if (value == 0) self.refund += clear_refund;
            }
        } else {
            // The slot has already been changed in this transaction, so the
            // expensive part is paid for; this write costs a lookup, and the
            // refund bookkeeping is corrected for where the slot ends up.
            if (!self.chargeGas(sload_cost)) return;
            if (original != 0) {
                // A refund granted when the slot was cleared is taken back
                // if it is being filled again, and granted if it is being
                // cleared now. This is the subtraction that lets a nested
                // frame's counter go negative.
                if (current == 0) self.refund -= clear_refund;
                if (value == 0) self.refund += clear_refund;
            }
            if (original == value) {
                // Put back exactly as it was found, so the difference between
                // what a real write would have cost and what was actually
                // charged along the way is returned.
                if (original == 0) {
                    self.refund += @intCast(gas.sstore_set - sload_cost);
                } else {
                    self.refund += @intCast(reset_cost - sload_cost);
                }
            }
        }
    } else {
        if (!self.chargeGas(if (current == 0 and value != 0) gas.sstore_set else gas.sstore_reset)) return;
        if (current != 0 and value == 0) {
            self.refund += @intCast(gas.sstore_clear_refund);
        }
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
    refund: i64 = 0,
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
    const args_region = self.toMemRegion(args_offset256, args_size256) orelse return;
    const ret_region = self.toMemRegion(ret_offset256, ret_size256) orelse return;
    const args_offset = args_region.offset;
    const args_size = args_region.size;
    const ret_offset = ret_region.offset;
    const ret_size = ret_region.size;

    // Growing memory is part of charging for it, not something to leave to
    // whoever reads the region later: the args are only read on the path
    // where the call actually runs, so a call that exits early (depth
    // limit, unaffordable value) would otherwise pay for growth that never
    // happened and let the *next* opcode touching those bytes be billed for
    // the very same growth a second time. Expanding between the two charges
    // also makes them cumulative, so two overlapping regions cost what
    // growing once to cover both costs, rather than each measuring from the
    // original length.
    if (!self.chargeMemoryExpansion(args_offset, args_size)) return;
    try self.memory.expand(args_offset, args_size);
    if (!self.chargeMemoryExpansion(ret_offset, ret_size)) return;
    try self.memory.expand(ret_offset, ret_size);

    const state = self.state orelse {
        self.status = .invalid_opcode;
        return;
    };

    const is_tangerine_whistle = self.block.fork.atLeast(.tangerine_whistle);
    const is_spurious_dragon = self.block.fork.atLeast(.spurious_dragon);
    // From Berlin (EIP-2929) the base cost is the access price of the code
    // address, whichever variant this is: DELEGATECALL and CALLCODE still
    // have to load `target`'s code even though they run as this frame.
    var cost: u64 = try self.accountAccessCost(state, target, if (is_tangerine_whistle) gas.call_base_150 else gas.call_base);
    if (value != 0) cost += gas.call_value;
    // Pre-Spurious-Dragon, the new-account surcharge and the value-transfer
    // surcharge are independent (execution-specs' `calculate_message_call_gas`):
    // a zero-value CALL to a not-yet-existing address still pays it. From
    // Spurious Dragon on (EIP-161), an existing-but-empty target is *also*
    // treated as "not really there" (`isAlive`, not `exists`), but only a
    // value-transferring call can "create" an account this way — a
    // zero-value call no longer pays the surcharge at all. Only a plain
    // CALL can create an account this way; CALLCODE/DELEGATECALL check
    // `self.address` here instead (via `to = self` in the real spec's
    // callcode), which always already exists.
    const is_new_account = if (is_spurious_dragon)
        kind == .call and value != 0 and !state.isAlive(target)
    else
        kind == .call and !state.exists(target);
    if (is_new_account) cost += gas.call_new_account;
    // DEBUG: era1-replay divergence hunt scaffolding from an earlier
    // investigation, left in place per user request. `debug_is_new_account_enabled`
    // gates this — flip it to `true` (and retarget the two hardcoded
    // addresses below) to trace a specific CALL's new-account gas
    // decision. Confirmed to fire often enough on real mainnet history to
    // dominate wall time over a multi-million-block replay when left on
    // (this is what several "is the replay stuck?" false alarms earlier
    // this session actually traced back to — not the other debug hooks).
    if (debug_is_new_account_enabled and
        self.block.number == debug_is_new_account_block and
        self.address == debug_is_new_account_caller)
    {
        std.debug.print(
            "DEBUG is_new_account check: block={d} depth={d} kind={s} target={x} exists={} is_new_account={} value={d} requested_gas={d}\n",
            .{ self.block.number, self.depth, @tagName(kind), target, state.exists(target), is_new_account, value, requested_gas },
        );
    }

    var forwarded: u64 = undefined;
    if (is_tangerine_whistle) {
        // EIP-150: charge only the static cost, hard-failing if even that
        // can't be afforded (same as the pre-150 branch below). Once that's
        // paid, cap the forwarded amount to 63/64ths of what's left rather
        // than failing outright just because the *request* was large —
        // the callee gets "as much as we can spare," not "exactly what it
        // asked for or nothing." execution-specs' `min(gas,
        // max_message_call_gas(...))` uses Python's arbitrary-precision
        // integers, so a requested value too big to fit in a u64 (a
        // contract computing it via unchecked subtraction can easily wrap
        // near 2^256 — a real, observed mainnet pattern) is just another
        // oversized request the cap reduces to something affordable, not a
        // hard failure the way it is pre-150.
        if (!self.chargeGas(cost)) return;
        const max_forwardable = self.gas_remaining - self.gas_remaining / 64;
        const requested = std.math.cast(u64, requested_gas) orelse std.math.maxInt(u64);
        forwarded = @min(requested, max_forwardable);
        self.gas_remaining -= forwarded;
    } else {
        // Pre-EIP-150 geth rejects a requested-gas value that doesn't fit
        // in a u64 (`ErrGasUintOverflow`) rather than capping it, treating
        // it as an immediate out-of-gas rather than "forward everything
        // remaining". execution-specs' `calculate_message_call_gas` folds
        // that *entire* requested-gas value (straight off the stack,
        // uncapped) into this opcode's own static cost: `cost = base +
        // gas + surcharges`, charged as one unit via `charge_gas`. If the
        // caller can't afford that, the whole CALL fails outright (this
        // frame goes out-of-gas) rather than silently forwarding whatever
        // happens to be left over.
        const forwarded_requested = std.math.cast(u64, requested_gas) orelse {
            self.status = .out_of_gas;
            return;
        };
        const total_cost = std.math.add(u64, cost, forwarded_requested) catch {
            self.status = .out_of_gas;
            return;
        };
        if (!self.chargeGas(total_cost)) return;
        forwarded = forwarded_requested;
    }

    const stipend: u64 = if (value != 0) gas.call_stipend else 0;
    const child_gas_limit = forwarded + stipend;

    // Real Ethereum resets RETURNDATASIZE/RETURNDATACOPY to empty for any
    // CALL variant that never actually reaches a callee (depth limit,
    // insufficient balance): there's no call to have returned data. Found
    // via a real ~18 gwei era1 divergence at block 5,529,623 — this early
    // return used to leave `last_return_data` stale from an earlier call
    // in the same transaction, making a later RETURNDATACOPY over-copy.
    if (self.depth >= max_call_depth) {
        self.gas_remaining += child_gas_limit;
        if (self.last_return_data.len != 0) self.allocator.free(self.last_return_data);
        self.last_return_data = &.{};
        self.pushStack(0);
        self.pc += 1;
        return;
    }

    const cp = state.checkpoint();

    if (kind == .call or kind == .callcode) {
        // CALLCODE never leaves its own storage context, so `value`
        // "moves" from this account to itself: a no-op balance-wise, but
        // it still has to afford it. Always calls `transfer`, even for
        // value == 0, since it still has to touch the recipient.
        const recipient = if (kind == .callcode) self.address else target;
        if (!try state.transfer(self.address, recipient, value)) {
            self.gas_remaining += child_gas_limit;
            if (self.last_return_data.len != 0) self.allocator.free(self.last_return_data);
            self.last_return_data = &.{};
            self.pushStack(0);
            self.pc += 1;
            return;
        }
    }

    const args = try self.memory.read(args_offset, args_size);

    // A precompile has no bytecode to interpret; `state.getCode` would just
    // return empty, so it's checked first, before creating a child `Interpreter`.
    const target_code = state.getCode(target);

    // The address the callee executes *as*: DELEGATECALL/CALLCODE run
    // target's code but keep this frame's own address/storage, so from
    // EIP-161's perspective it's `self.address`, not `target`, that gets
    // touched.
    const callee_address = if (kind == .delegatecall or kind == .callcode) self.address else target;

    const outcome: CallOutcome = if (try Precompiles.call(self.allocator, target, args, child_gas_limit, self.block.fork)) |result|
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
            .address = callee_address,
            .caller = if (kind == .delegatecall) self.caller else self.address,
            .value = if (kind == .delegatecall) self.value else value,
            .calldata = args,
            .tx = self.tx,
            .is_static = self.is_static or kind == .staticcall,
            .depth = self.depth + 1,
            .state = state,
            .block = self.block,
            .jumpdest = try state.getJumpdest(target),
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
    // EIP-161, from Spurious Dragon on: mark the callee touched regardless
    // of whether this call ends up succeeding — `markTouchedIfEmpty` is
    // journaled, so a revert below automatically discards it, matching
    // real Ethereum's "a reverted call's touches never happened" rule.
    if (is_spurious_dragon) try state.markTouchedIfEmpty(callee_address);
    if (!success) {
        state.revertTo(cp);
        if (is_spurious_dragon and callee_address == ripemd160_address) {
            // Real client bug, preserved in consensus: RIPEMD160 stays
            // touched even though this call failed (see
            // `ripemd160_address`'s doc comment). Re-applies the touch
            // the revert above just undid.
            try state.markTouchedIfEmpty(ripemd160_address);
        }
    }
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

pub fn create2Address(sender: Address, salt: u256, init_code: []const u8) Address {
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

    const region = self.toMemRegion(offset256, size256) orelse return;
    const offset = region.offset;
    const size = region.size;
    // Same reasoning as `call`: grow the memory as part of paying for it,
    // so an early exit can't leave the growth charged but undone.
    if (!self.chargeMemoryExpansion(offset, size)) return;
    try self.memory.expand(offset, size);
    if (!self.chargeGas(gas.create_base)) return;
    if (kind == .create2 and !self.chargeGas(gas.keccak256_word * ((size + 31) / 32))) return;

    const state = self.state orelse {
        self.status = .invalid_opcode;
        return;
    };

    if (self.depth >= max_call_depth) {
        if (self.last_return_data.len != 0) self.allocator.free(self.last_return_data);
        self.last_return_data = &.{};
        self.pushStack(0);
        self.pc += 1;
        return;
    }

    const init_code = try self.memory.read(offset, size);
    const new_address = switch (kind) {
        .create => try createAddress(self.allocator, self.address, state.get(self.address).nonce),
        .create2 => create2Address(self.address, salt, init_code),
    };
    // EIP-2929 (Berlin): the new address is warm from here on, whether or
    // not the creation goes ahead. Warmed in this frame, before the child's
    // checkpoint below, so a failed creation does not cool it again.
    if (self.block.fork.atLeast(.berlin)) _ = try state.warmAddress(new_address);

    // Order matters here, and it isn't the obvious one (see
    // execution-specs' `create`): the endowment and depth checks come
    // first and bail out *without* touching the creator's nonce; only then
    // is the nonce incremented; and only after that does the child's own
    // snapshot begin. So a create whose init code fails still consumes the
    // creator's nonce — that increment is deliberately outside everything
    // `revertTo` undoes. Taking the checkpoint too early instead rolls the
    // nonce back on failure, which shifts every later CREATE address that
    // account derives: found via a real era1 divergence where a clone
    // factory's nonce sat one behind real chain (9 vs 10), so its next
    // CREATE produced a different address entirely and execution diverged
    // from there on.
    if (value != 0 and state.getBalance(self.address) < value) {
        if (self.last_return_data.len != 0) self.allocator.free(self.last_return_data);
        self.last_return_data = &.{};
        self.pushStack(0);
        self.pc += 1;
        return;
    }

    try state.setNonce(self.address, state.get(self.address).nonce + 1);

    // EIP-684: creating to an address that already has code or a nonzero
    // nonce fails immediately, "with exactly the same behavior as would
    // arise if the first byte in the init code were an invalid opcode" —
    // so the init code never runs and every bit of gas handed to the
    // creation is forfeit, unlike the endowment and depth bail-outs above
    // which hand it all back. The creator's nonce increment above still
    // stands. `CREATE` derives its address from that nonce and so can
    // essentially never collide, which is why this went unnoticed for
    // 7.75M blocks; `CREATE2` picks the address by salt, so hitting an
    // occupied one is trivial and deliberate. Found at mainnet block
    // 7,753,545, where zevm ran the init code real chain had refused and
    // came out 333,570 gas light.
    const collides = state.get(new_address).nonce != 0 or state.getCode(new_address).len != 0;

    // Real Frontier/Homestead/DAO forward *all* remaining gas to a nested
    // CREATE (`create_message_gas = evm.gas_left; evm.gas_left = 0`); the
    // 63/64ths reservation is EIP-150/Tangerine Whistle's rule, same as
    // `call`'s.
    const forwarded = if (self.block.fork.atLeast(.tangerine_whistle))
        self.gas_remaining - self.gas_remaining / 64
    else
        self.gas_remaining;
    self.gas_remaining -= forwarded;

    if (collides) {
        // `forwarded` is deliberately not returned: that is what makes this
        // an exceptional halt rather than a graceful failure.
        if (self.last_return_data.len != 0) self.allocator.free(self.last_return_data);
        self.last_return_data = &.{};
        self.pushStack(0);
        self.pc += 1;
        return;
    }

    const cp = state.checkpoint();

    // EIP-161, from Spurious Dragon on: a freshly created contract's own
    // nonce starts at 1, not 0 — set before its init code runs (real
    // Frontier/Homestead/Tangerine Whistle never touch the new address's
    // nonce at all here). This is what keeps a contract from ever being
    // mistaken for "empty" while its own constructor is still running, or
    // if it ends up deploying zero bytes of code.
    if (self.block.fork.atLeast(.spurious_dragon)) try state.setNonce(new_address, 1);

    if (value != 0) {
        // The endowment check above already ruled out the short case, so
        // this only ever moves the value.
        const moved = try state.transfer(self.address, new_address, value);
        std.debug.assert(moved);
    }

    // Same as `Evm.create`: execution-specs' `process_message` touches the
    // new contract's address before its init code runs. Without it a
    // zero-value pre-Spurious-Dragon creation leaves the address absent
    // while its constructor executes, so a `SELFDESTRUCT` in that
    // constructor registers nothing and the contract outlives the
    // transaction that should have erased it.
    try state.touch(new_address);

    var child = try Interpreter.initCall(self.allocator, init_code, forwarded, .{
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

    // EIP-170, from Spurious Dragon on: deployed code over this size is
    // rejected as an exceptional halt (real Ethereum's `OutOfGasError`),
    // forfeiting all remaining gas rather than a graceful stop. No limit
    // at all before this fork.
    const oversized = self.block.fork.atLeast(.spurious_dragon) and child.return_data.len > max_code_size;
    // EIP-3541 (London): new code may not start with 0xEF, reserving that
    // byte for a future code format. Rejected the same way as oversized
    // code, as an exceptional halt.
    const ef_prefixed = self.block.fork.atLeast(.london) and child.return_data.len > 0 and child.return_data[0] == 0xef;
    const rejected = oversized or ef_prefixed;
    var success = child.status == .stopped and !rejected;
    var status = if (rejected) .out_of_gas else child.status;
    var deployed_code: []const u8 = child.return_data;
    if (success) {
        const deposit_cost = gas.code_deposit_byte * @as(u64, child.return_data.len);
        if (child.gas_remaining < deposit_cost) {
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
            child.gas_remaining -= deposit_cost;
        }
    }

    if (success) {
        try state.setCode(new_address, deployed_code);
    } else {
        state.revertTo(cp);
    }

    if (status == .stopped or status == .reverted) {
        self.gas_remaining += child.gas_remaining;
    }
    // See the equivalent comment in `call`: a failed/reverted create's
    // storage changes are undone, so its refund doesn't count either.
    if (success) self.refund += child.refund;

    // A successful create's return data was its deployed code, not
    // something RETURNDATACOPY should expose; only a genuine `REVERT`'s
    // reason is visible afterward. An *exceptional* halt (`status ==
    // .out_of_gas`, whether from the child running out of gas mid-execution
    // or from this function's own post-hoc deposit-cost/EIP-170 checks)
    // has no return data at all: real Ethereum clears it, the same as any
    // other exceptional halt. Found via a real ~2,880,000,000,000 wei era1
    // divergence — a CREATE whose constructor legitimately RETURNed real
    // bytes (so `child.return_data` is non-empty) but then failed the
    // deposit-cost check, leaving a later RETURNDATACOPY seeing stale
    // "revert reason" bytes that were never actually a revert reason.
    if (self.last_return_data.len != 0) self.allocator.free(self.last_return_data);
    self.last_return_data = if (status == .reverted) try self.allocator.dupe(u8, child.return_data) else &.{};

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
    const region = self.toMemRegion(offset256, size256) orelse return;
    const offset = region.offset;
    const size = region.size;
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

    const is_tangerine_whistle = self.block.fork.atLeast(.tangerine_whistle);
    const is_spurious_dragon = self.block.fork.atLeast(.spurious_dragon);
    var cost: u64 = if (is_tangerine_whistle) gas.selfdestruct_base_150 else gas.selfdestruct_base;
    // EIP-2929 (Berlin): a cold beneficiary adds the cold surcharge. Unlike
    // the other account-touching opcodes there is no warm price to replace,
    // just this addition to the 5000 base.
    if (self.block.fork.atLeast(.berlin) and !try state.warmAddress(beneficiary)) {
        cost += gas.cold_account_access_2929;
    }
    // From Spurious Dragon on (EIP-161), the new-account surcharge swaps
    // `exists` for `isAlive` (an existing-but-empty beneficiary still
    // counts as "not really there"), and only applies if there's actually
    // a nonzero balance being moved to it — nothing to move means no
    // account gets created either way.
    if (is_spurious_dragon) {
        if (!state.isAlive(beneficiary) and balance != 0) cost += gas.selfdestruct_new_account;
    } else if (is_tangerine_whistle and !state.exists(beneficiary)) {
        cost += gas.selfdestruct_new_account;
    }
    if (!self.chargeGas(cost)) return;

    // Real Ethereum assigns the beneficiary's balance unconditionally, and
    // that assignment *materialises* the account even when the amount moved
    // is zero — a zero-balance SELFDESTRUCT still leaves an empty
    // beneficiary behind in the state trie. Skipping it when `balance == 0`
    // left zevm one account short of real chain, which shows up as nothing
    // at all until a state root is compared (or until a later CALL to that
    // address is charged the 25,000 new-account fee zevm no longer expects).
    // From Spurious Dragon on, `markTouchedIfEmpty` below hands that same
    // empty account to the EIP-161 sweep, so it only survives where it should.
    if (beneficiary != self.address) {
        // Already confirmed the balance is there; `transfer` can only
        // fail on insufficient balance, which can't happen here.
        _ = try state.transfer(self.address, beneficiary, balance);
    } else if (balance != 0) {
        // Destroying yourself to yourself just burns the balance.
        try state.setBalance(self.address, 0);
    }

    // EIP-161, from Spurious Dragon on: the beneficiary counts as touched
    // too (a no-op if it just received a nonzero transfer above, since
    // `markTouchedIfEmpty` only ever acts on a currently-empty account).
    if (is_spurious_dragon) try state.markTouchedIfEmpty(beneficiary);

    // Real Ethereum's refund is a set-membership check, not a per-call
    // counter: an address earns it only the first time it's destroyed in
    // this transaction, so a contract that gets `CALL`ed (and
    // self-destructs) repeatedly doesn't rack up the refund again on
    // every repeat.
    const already_marked = state.isPendingDestruction(self.address);
    try state.destroyAccount(self.address);
    // EIP-3529 (London) removed this refund outright.
    if (!already_marked and !self.block.fork.atLeast(.london)) self.refund += @intCast(gas.selfdestruct_refund);
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
/// `/` and `%` on `u256` have no instruction behind them and compile to
/// compiler-rt's generic wide long division, which was 9% of the
/// interpreter's own time for `DIV` alone. Most operands are token amounts
/// that fit in far fewer bits, so the narrowest width that holds both is
/// tried first, down to the CPU's own 64-bit divide.
fn div(a: u256, b: u256) u256 {
    if (b == 0 or a < b) return 0;
    if (a <= std.math.maxInt(u64)) return @as(u64, @intCast(a)) / @as(u64, @intCast(b));
    if (a <= std.math.maxInt(u128)) return @as(u128, @intCast(a)) / @as(u128, @intCast(b));
    return fromLimbs(divRemLimbs(4, toLimbs(4, a), toLimbs(4, b)).q);
}
fn sdiv(a: u256, b: u256) u256 {
    if (b == 0) return 0;
    const ai: i256 = @bitCast(a);
    const bi: i256 = @bitCast(b);
    if (bi == -1 and ai == std.math.minInt(i256)) return a;
    return @bitCast(@divTrunc(ai, bi));
}
/// See `div`. `a < b` is `a` itself.
fn mod(a: u256, b: u256) u256 {
    if (b == 0) return 0;
    if (a < b) return a;
    if (a <= std.math.maxInt(u64)) return @as(u64, @intCast(a)) % @as(u64, @intCast(b));
    if (a <= std.math.maxInt(u128)) return @as(u128, @intCast(a)) % @as(u128, @intCast(b));
    return fromLimbs(divRemLimbs(4, toLimbs(4, a), toLimbs(4, b)).r);
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
/// `a * b mod n` over the full 512-bit product.
///
/// The generic path is a 512-bit `%`, a software long division, and was 27%
/// of the interpreter's own time on 2021 blocks: Uniswap V3's
/// `FullMath.mulDiv` runs on every swap and computes `mulmod(x, y, not(0))`.
/// For that modulus no division is needed. `2^256 = 1 (mod 2^256 - 1)`, so
/// `hi * 2^256 + lo` reduces to `hi + lo`; a carry out of that sum is one
/// more `2^256`, so one more 1. `hi < 2^256 - 1` always, which keeps the
/// result below the modulus after that single fold, except for the value
/// `2^256 - 1` itself, which is 0. A product that fits in 256 bits goes to
/// `mod` and its narrow paths instead.
fn mulmod(a: u256, b: u256, n: u256) u256 {
    if (n == 0) return 0;
    const prod: u512 = @as(u512, a) * @as(u512, b);
    const hi: u256 = @truncate(prod >> 256);
    const lo: u256 = @truncate(prod);
    if (n == std.math.maxInt(u256)) {
        const sum = @addWithOverflow(lo, hi);
        const folded = sum[0] + @as(u256, sum[1]);
        return if (folded == n) 0 else folded;
    }
    if (hi == 0) return mod(lo, n);
    return fromLimbs(divRemLimbs(8, toLimbs(8, prod), toLimbs(4, n)).r);
}

/// `x` as little-endian 64-bit limbs.
fn toLimbs(comptime N: usize, x: std.meta.Int(.unsigned, 64 * N)) [N]u64 {
    var out: [N]u64 = undefined;
    inline for (0..N) |i| out[i] = @truncate(x >> (64 * i));
    return out;
}

/// The first four limbs as a `u256`. Callers only pass values known to fit.
fn fromLimbs(limbs: anytype) u256 {
    var x: u256 = 0;
    inline for (0..4) |i| x |= @as(u256, limbs[i]) << (64 * i);
    return x;
}

/// `(hi * 2^64 + lo) / d` and its remainder, for `hi < d` so the quotient
/// fits in 64 bits. On x86-64 that is one `div` instruction (the same inline
/// asm compiler-rt uses for this); elsewhere, the plain 128-bit expression.
inline fn div2by1(hi: u64, lo: u64, d: u64) struct { q: u64, r: u64 } {
    if (comptime builtin.target.cpu.arch == .x86_64) {
        var r: u64 = undefined;
        const q = asm (
            \\divq %[d]
            : [_] "={rax}" (-> u64),
              [_] "={rdx}" (r),
            : [d] "r" (d),
              [_] "{rax}" (lo),
              [_] "{rdx}" (hi),
        );
        return .{ .q = q, .r = r };
    }
    const n = (@as(u128, hi) << 64) | lo;
    return .{ .q = @intCast(n / d), .r = @intCast(n % d) };
}

/// Test builds only: how often `divRemLimbs` took its rare add-back step, so
/// the tests can show they reached it rather than assume so.
var add_back_count: u64 = 0;

/// `u / v` and `u % v` for a dividend of `N` 64-bit limbs and a nonzero
/// divisor of up to four: Knuth's Algorithm D (TAOCP 4.3.1), in the shape of
/// Hacker's Delight's `divmnu`, with 64-bit limbs.
///
/// compiler-rt runs the same algorithm for `/` and `%` on wide integers, but
/// one generic version serves every width up to 65,535 bits, on 32-bit limbs.
/// Here the sizes are fixed and each quotient digit is estimated with a single
/// hardware 128-by-64 division, so a 512-by-256 remainder is about a quarter
/// of the limb work. That remainder (`MULMOD`'s general case, from Uniswap V3's
/// `FullMath.mulDiv`) was 15% of all replay time on 2021 blocks.
fn divRemLimbs(comptime N: usize, u: [N]u64, v: [4]u64) struct { q: [N]u64, r: [4]u64 } {
    var q: [N]u64 = .{0} ** N;
    var r: [4]u64 = .{0} ** 4;

    var n: usize = 4;
    while (v[n - 1] == 0) n -= 1;
    var m: usize = N;
    while (m > 0 and u[m - 1] == 0) m -= 1;

    // Fewer significant limbs than the divisor: the quotient is 0.
    if (m < n) {
        for (0..m) |i| r[i] = u[i];
        return .{ .q = q, .r = r };
    }

    // A one-limb divisor needs no normalisation or correction.
    if (n == 1) {
        var rem: u64 = 0;
        var i = m;
        while (i > 0) {
            i -= 1;
            const d = div2by1(rem, u[i], v[0]);
            q[i] = d.q;
            rem = d.r;
        }
        r[0] = rem;
        return .{ .q = q, .r = r };
    }

    // Normalise so the divisor's top limb has its top bit set, which is what
    // makes the two-limb quotient estimate below at most 2 too large.
    const s: u7 = @clz(v[n - 1]);
    var vn: [4]u64 = undefined;
    var i: usize = n - 1;
    while (i > 0) : (i -= 1) vn[i] = @truncate((((@as(u128, v[i]) << 64) | v[i - 1]) << s) >> 64);
    vn[0] = @truncate(@as(u128, v[0]) << s);

    var un: [N + 1]u64 = undefined;
    un[m] = @truncate((@as(u128, u[m - 1]) << s) >> 64);
    i = m - 1;
    while (i > 0) : (i -= 1) un[i] = @truncate((((@as(u128, u[i]) << 64) | u[i - 1]) << s) >> 64);
    un[0] = @truncate(@as(u128, u[0]) << s);

    var j: usize = m - n + 1;
    while (j > 0) {
        j -= 1;
        // Estimate this quotient digit from the window's top two limbs. The
        // window's top limb never exceeds the divisor's, and when they are
        // equal the true digit is the largest one, b - 1.
        var qhat: u64 = undefined;
        var rhat: u128 = undefined;
        if (un[j + n] >= vn[n - 1]) {
            qhat = std.math.maxInt(u64);
            rhat = @as(u128, un[j + n - 1]) + vn[n - 1];
        } else {
            const d = div2by1(un[j + n], un[j + n - 1], vn[n - 1]);
            qhat = d.q;
            rhat = d.r;
        }
        while (rhat <= std.math.maxInt(u64) and
            @as(u128, qhat) * vn[n - 2] > ((rhat << 64) | un[j + n - 2]))
        {
            qhat -= 1;
            rhat += vn[n - 1];
        }

        // Multiply and subtract `qhat * vn` from the window.
        var borrow: i128 = 0;
        for (0..n) |k| {
            const p = @as(u128, qhat) * vn[k];
            const t = @as(i128, un[k + j]) - borrow - @as(i128, @as(u64, @truncate(p)));
            un[k + j] = @truncate(@as(u128, @bitCast(t)));
            borrow = @as(i128, @intCast(p >> 64)) - (t >> 64);
        }
        const top = @as(i128, un[j + n]) - borrow;
        un[j + n] = @truncate(@as(u128, @bitCast(top)));

        // The estimate was still one too large: add one divisor back.
        if (top < 0) {
            if (builtin.is_test) add_back_count += 1;
            qhat -= 1;
            var carry: u128 = 0;
            for (0..n) |k| {
                const t = @as(u128, un[k + j]) + vn[k] + carry;
                un[k + j] = @truncate(t);
                carry = t >> 64;
            }
            un[j + n] = @truncate(@as(u128, un[j + n]) + carry);
        }
        q[j] = qhat;
    }

    // Undo the normalisation shift on the remainder, which is what is left
    // in the window's low `n` limbs.
    for (0..n) |k| {
        const above: u64 = if (k + 1 < n) un[k + 1] else 0;
        r[k] = @truncate((((@as(u128, above) << 64) | un[k])) >> s);
    }
    return .{ .q = q, .r = r };
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
    return expectBinaryOpFork(op, a, b, expected, .frontier);
}

/// `SHL`/`SHR`/`SAR` are Constantinople-only (EIP-145), unlike every other
/// binary op `expectBinaryOp` exercises, so those three tests need a later
/// fork explicitly rather than sharing `expectBinaryOp`'s frontier default.
fn expectBinaryOpFork(op: OpCode, a: u256, b: u256, expected: u256, fork: Fork) !void {
    var code: std.ArrayList(u8) = .empty;
    defer code.deinit(std.testing.allocator);
    try appendPush32(&code, b);
    try appendPush32(&code, a);
    try code.append(std.testing.allocator, @intFromEnum(op));
    try code.append(std.testing.allocator, @intFromEnum(OpCode.STOP));

    var interp = try Interpreter.initCall(std.testing.allocator, code.items, 1_000_000, .{ .block = .{ .fork = fork } });
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

test "EXP costs more per exponent byte from Spurious Dragon on" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH2), 0x01, 0x00, // exponent: 256 (2 significant bytes)
        @intFromEnum(OpCode.PUSH1), 2, // base
        @intFromEnum(OpCode.EXP),
        @intFromEnum(OpCode.STOP),
    };

    var frontier_state = State.init(std.testing.allocator);
    defer frontier_state.deinit();
    var frontier_interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &frontier_state,
    });
    defer frontier_interp.deinit();
    try frontier_interp.run();

    var sd_state = State.init(std.testing.allocator);
    defer sd_state.deinit();
    var sd_interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &sd_state,
        .block = .{ .fork = .spurious_dragon },
    });
    defer sd_interp.deinit();
    try sd_interp.run();

    try std.testing.expectEqual(Status.stopped, frontier_interp.status);
    try std.testing.expectEqual(Status.stopped, sd_interp.status);
    try std.testing.expectEqual(
        (gas.exp_byte_160 - gas.exp_byte) * 2,
        frontier_interp.gas_remaining - sd_interp.gas_remaining,
    );
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
    try expectBinaryOpFork(.SHL, 1, 4, 8, .constantinople);
}
test "SHR" {
    try expectBinaryOpFork(.SHR, 1, 8, 4, .constantinople);
}
test "SHR by 256 or more is zero" {
    try expectBinaryOpFork(.SHR, 256, max_u256, 0, .constantinople);
}
test "SAR sign-extends when shifting a negative value" {
    try expectBinaryOpFork(.SAR, 1, @bitCast(@as(i256, -2)), @bitCast(@as(i256, -1)), .constantinople);
}
test "SAR by 256 or more of a negative value saturates to all ones" {
    try expectBinaryOpFork(.SAR, 256, min_i256_as_u256, max_u256, .constantinople);
}

test "PUSH0 pushes zero" {
    const code = [_]u8{ @intFromEnum(OpCode.PUSH0), @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .block = .{ .fork = .shanghai } });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
}

test "PUSH0 is invalid before Shanghai" {
    const code = [_]u8{@intFromEnum(OpCode.PUSH0)};
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.invalid_opcode, interp.status);
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
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .block = .{ .base_fee = 7, .fork = .london } });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 7), try interp.stack.pop());
}

test "BASEFEE is invalid before London" {
    const code = [_]u8{@intFromEnum(OpCode.BASEFEE)};
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.invalid_opcode, interp.status);
}

test "CHAINID pushes the chain id" {
    const code = [_]u8{ @intFromEnum(OpCode.CHAINID), @intFromEnum(OpCode.STOP) };
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .block = .{ .chain_id = 1, .fork = .istanbul } });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 1), try interp.stack.pop());
}

test "CHAINID is invalid before Istanbul" {
    const code = [_]u8{@intFromEnum(OpCode.CHAINID)};
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.invalid_opcode, interp.status);
}

test "SELFBALANCE pushes this frame's own balance from state" {
    const code = [_]u8{ @intFromEnum(OpCode.SELFBALANCE), @intFromEnum(OpCode.STOP) };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x42, 1000);

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .address = 0x42, .state = &state, .block = .{ .fork = .istanbul } });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(@as(u256, 1000), try interp.stack.pop());
}

test "SELFBALANCE is invalid before Istanbul" {
    const code = [_]u8{@intFromEnum(OpCode.SELFBALANCE)};
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.invalid_opcode, interp.status);
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
    // REVERT is Byzantium-only (EIP-140); see the "REVERT is invalid before
    // Byzantium" test below for the pre-fork behavior.
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{ .block = .{ .fork = .byzantium } });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.reverted, interp.status);
    try std.testing.expectEqual(@as(u256, 0x99), std.mem.readInt(u256, interp.return_data[0..32], .big));
}

test "REVERT is invalid before Byzantium" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.REVERT),
    };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.invalid_opcode, interp.status);
}

test "a CALLed contract's own internal JUMP loop runs correctly through State's cached jumpdest analysis" {
    // callee: the same counts-a-stack-value-down-to-zero loop as the
    // JUMP/JUMPDEST unit test above, but reached via `state.setCode` +
    // `CALL` instead of a bare `Interpreter.init`, so this exercises
    // `State.getJumpdest`'s cached bitset (cloned into the child
    // `Interpreter`) rather than a fresh `analyzeJumpdests` scan — the
    // two must validate `JUMP`/`JUMPI` identically.
    const push1 = @intFromEnum(OpCode.PUSH1);
    const callee_code = [_]u8{
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
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1), 32,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.RETURN),
    };

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xcc, &callee_code);

    // caller: CALL(gas=10000, addr=0xcc, value=0, argsOffset=0, argsSize=0, retOffset=0, retSize=32)
    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 32, // retSize
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

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 1), try interp.stack.pop());
    try std.testing.expectEqual(@as(u256, 0), try interp.memory.readWord(0));
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

test "a CALL with argsSize/retSize both 0 succeeds despite huge, unfit-in-usize offsets" {
    // The classic Solidity `.transfer()`/`.send()` compilation: no calldata,
    // no expected return data, and offset slots holding whatever the
    // free-memory pointer (or other stale stack value) happened to be —
    // real Ethereum never actually dereferences them when size is 0, so an
    // arbitrarily large offset must not fail the call. Found via a real
    // historical mainnet transaction (block 4,890,213) that zevm rejected
    // as out-of-gas despite it succeeding on real mainnet: a CryptoKitties
    // auction paying out proceeds via exactly this bytecode pattern.
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0xaa, 1000);

    // caller: CALL(gas=10000, addr=0xdd, value=0, argsOffset=huge,
    // argsSize=0, retOffset=huge, retSize=0)
    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // retSize
        @intFromEnum(OpCode.PUSH32), 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH32), 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, // argsOffset
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
    try std.testing.expectEqual(@as(u256, 1), try interp.stack.pop());
}

test "a zero-value CALL still touches (creates) a not-yet-existing target" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0xaa, 1000);

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

    try std.testing.expect(!state.exists(0xdd));
    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 1), try interp.stack.pop());
    try std.testing.expect(state.exists(0xdd));
    try std.testing.expectEqual(@as(u256, 0), state.getBalance(0xdd));
}

test "a zero-value CALL to a not-yet-existing address still pays the new-account surcharge" {
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

    // Baseline: 0xdd already exists (pre-touched), so no new-account charge.
    var existing_state = State.init(std.testing.allocator);
    defer existing_state.deinit();
    try existing_state.setBalance(0xdd, 0);
    var existing_interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &existing_state,
    });
    defer existing_interp.deinit();
    try existing_interp.run();

    // 0xdd doesn't exist yet: real Frontier (per execution-specs'
    // `calculate_message_call_gas`) charges the new-account surcharge for
    // *any* CALL to a not-yet-existing address, independent of value.
    var new_state = State.init(std.testing.allocator);
    defer new_state.deinit();
    var new_interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &new_state,
    });
    defer new_interp.deinit();
    try new_interp.run();

    try std.testing.expectEqual(Status.stopped, existing_interp.status);
    try std.testing.expectEqual(Status.stopped, new_interp.status);
    try std.testing.expectEqual(
        gas.call_new_account,
        existing_interp.gas_remaining - new_interp.gas_remaining,
    );
}

test "from Spurious Dragon on, a zero-value CALL no longer pays the new-account surcharge" {
    // Same caller code as the pre-161 test above: CALL(..., value=0, ...).
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

    var existing_state = State.init(std.testing.allocator);
    defer existing_state.deinit();
    try existing_state.setBalance(0xdd, 0);
    var existing_interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &existing_state,
        .block = .{ .fork = .spurious_dragon },
    });
    defer existing_interp.deinit();
    try existing_interp.run();

    var new_state = State.init(std.testing.allocator);
    defer new_state.deinit();
    var new_interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &new_state,
        .block = .{ .fork = .spurious_dragon },
    });
    defer new_interp.deinit();
    try new_interp.run();

    try std.testing.expectEqual(Status.stopped, existing_interp.status);
    try std.testing.expectEqual(Status.stopped, new_interp.status);
    try std.testing.expectEqual(existing_interp.gas_remaining, new_interp.gas_remaining);
}

test "from Spurious Dragon on, a value-transferring CALL to an existing-but-empty address still pays the new-account surcharge" {
    // caller: CALL(gas=10000, addr=0xdd, value=100, argsOffset=0, argsSize=0, retOffset=0, retSize=0)
    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // retSize
        @intFromEnum(OpCode.PUSH1), 0, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH1), 0, // argsOffset
        @intFromEnum(OpCode.PUSH1), 100, // value
        @intFromEnum(OpCode.PUSH1), 0xdd, // address
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10, // gas
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.STOP),
    };

    // Baseline: 0xdd already alive (nonzero balance), so no surcharge.
    var alive_state = State.init(std.testing.allocator);
    defer alive_state.deinit();
    try alive_state.setBalance(0xaa, 1000);
    try alive_state.setBalance(0xdd, 1);
    var alive_interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &alive_state,
        .block = .{ .fork = .spurious_dragon },
    });
    defer alive_interp.deinit();
    try alive_interp.run();

    // 0xdd exists but is empty (a zero-balance shell, e.g. from an earlier
    // zero-value touch): `isAlive` is false, so the surcharge still
    // applies, unlike pre-161's plain `exists` check.
    var empty_state = State.init(std.testing.allocator);
    defer empty_state.deinit();
    try empty_state.setBalance(0xaa, 1000);
    try empty_state.setBalance(0xdd, 0);
    var empty_interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &empty_state,
        .block = .{ .fork = .spurious_dragon },
    });
    defer empty_interp.deinit();
    try empty_interp.run();

    try std.testing.expectEqual(Status.stopped, alive_interp.status);
    try std.testing.expectEqual(Status.stopped, empty_interp.status);
    try std.testing.expectEqual(
        gas.call_new_account,
        alive_interp.gas_remaining - empty_interp.gas_remaining,
    );
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
        .block = .{ .fork = .homestead },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u256, 1), try interp.stack.pop());
    try std.testing.expectEqual(@as(u256, 0xaa), try interp.memory.readWord(0));
    try std.testing.expectEqual(@as(u256, 0xbb), try interp.memory.readWord(32));
    try std.testing.expectEqual(@as(u256, 777), try interp.memory.readWord(64));
}

test "DELEGATECALL before Homestead halts as invalid_opcode" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xdd, &.{@intFromEnum(OpCode.STOP)});

    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // retSize
        @intFromEnum(OpCode.PUSH1), 0, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH1), 0, // argsOffset
        @intFromEnum(OpCode.PUSH1), 0xdd, // address
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10, // gas
        @intFromEnum(OpCode.DELEGATECALL),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.invalid_opcode, interp.status);
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
        .block = .{ .fork = .byzantium }, // STATICCALL is Byzantium-only (EIP-214).
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
}

test "STATICCALL is invalid before Byzantium" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0xdd,
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10,
        @intFromEnum(OpCode.STATICCALL),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{});
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.invalid_opcode, interp.status);
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

test "a CALL requesting more gas than the caller has left fails outright, not capped" {
    // callee: trivial, would succeed if ever reached.
    const callee_code = [_]u8{@intFromEnum(OpCode.STOP)};
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xcc, &callee_code);

    // caller: CALL(gas=1_000_000, addr=0xcc, value=0, argsOffset=0, argsSize=0, retOffset=0, retSize=0)
    // with far too little gas of its own to cover that request.
    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // retSize
        @intFromEnum(OpCode.PUSH1), 0, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH1), 0, // argsOffset
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.PUSH1), 0xcc, // address
        @intFromEnum(OpCode.PUSH3), 0x0f, 0x42, 0x40, // gas = 1,000,000
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.STOP),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 10_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    // execution-specs' `calculate_message_call_gas` (Frontier/Homestead)
    // charges `base + the full requested gas value (uncapped) +
    // surcharges` as one static cost, hard-failing the whole frame if
    // that's unaffordable — it does not silently cap the forwarded amount
    // to whatever's left. That capping is EIP-150 behavior, introduced
    // later, not something Frontier or Homestead ever did.
    try std.testing.expectEqual(Status.out_of_gas, interp.status);
}

test "from Tangerine Whistle on, a CALL requesting more gas than available is capped at 63/64ths, not failed" {
    // callee: trivial, succeeds immediately either way.
    const callee_code = [_]u8{@intFromEnum(OpCode.STOP)};
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xcc, &callee_code);

    // Same setup as the pre-150 hard-fail test above: caller has only
    // 10,000 gas but requests 1,000,000 for the CALL.
    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // retSize
        @intFromEnum(OpCode.PUSH1), 0, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH1), 0, // argsOffset
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.PUSH1), 0xcc, // address
        @intFromEnum(OpCode.PUSH3), 0x0f, 0x42, 0x40, // gas = 1,000,000
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.STOP),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 10_000, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = .tangerine_whistle },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 1), try interp.stack.pop());
}

test "from Tangerine Whistle on, a requested-gas value too large to fit a u64 is capped, not an immediate out-of-gas" {
    // A real, observed mainnet pattern: a contract computes the gas to
    // forward via unchecked subtraction (e.g. `msg.gas() - N`), which
    // wraps around near 2^256 if it underflows. execution-specs'
    // `min(gas, max_message_call_gas(...))` uses Python's
    // arbitrary-precision integers, so this is just another oversized
    // request the 63/64ths cap reduces to something affordable — pre-150
    // treats the very same u64-overflow as an immediate hard failure
    // instead (see the sibling "fails outright, not capped" test), but
    // that rule doesn't carry over here.
    const callee_code = [_]u8{@intFromEnum(OpCode.STOP)};
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
        @intFromEnum(OpCode.PUSH32),
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, // gas = 2^256 - 1
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.STOP),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 10_000, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = .tangerine_whistle },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 1), try interp.stack.pop());
}

test "from Tangerine Whistle on, a CALL still fails outright if even its static cost is unaffordable" {
    const callee_code = [_]u8{@intFromEnum(OpCode.STOP)};
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xcc, &callee_code);

    // caller: CALL(gas=0, addr=0xcc, ...) but doesn't even have the 700
    // gas call_base_150 requires.
    const caller_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // retSize
        @intFromEnum(OpCode.PUSH1), 0, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH1), 0, // argsOffset
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.PUSH1), 0xcc, // address
        @intFromEnum(OpCode.PUSH1), 0, // gas
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.STOP),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 100, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = .tangerine_whistle },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.out_of_gas, interp.status);
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

test "nested CREATE forwards all remaining gas pre-150, only 63/64ths from Tangerine Whistle" {
    // init code: an infinite loop (JUMPDEST, PUSH1 0, JUMP) that only ever
    // halts by running out of whatever gas it's given — isolates exactly
    // how much was forwarded, since an out-of-gas child returns nothing.
    const init_code = [_]u8{
        @intFromEnum(OpCode.JUMPDEST),
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.JUMP),
    };

    var caller_code: std.ArrayList(u8) = .empty;
    defer caller_code.deinit(std.testing.allocator);
    try caller_code.append(std.testing.allocator, @intFromEnum(OpCode.PUSH4));
    try caller_code.appendSlice(std.testing.allocator, &init_code);
    try caller_code.appendSlice(std.testing.allocator, &.{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1), 4, // size
        @intFromEnum(OpCode.PUSH1), 28, // offset (32 - 4)
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.CREATE),
        @intFromEnum(OpCode.STOP),
    });

    const gas_limit: u64 = 1_000_000;

    var frontier_state = State.init(std.testing.allocator);
    defer frontier_state.deinit();
    var frontier_interp = try Interpreter.initCall(std.testing.allocator, caller_code.items, gas_limit, .{
        .address = 0xaa,
        .state = &frontier_state,
    });
    defer frontier_interp.deinit();
    try frontier_interp.run();

    var tw_state = State.init(std.testing.allocator);
    defer tw_state.deinit();
    var tw_interp = try Interpreter.initCall(std.testing.allocator, caller_code.items, gas_limit, .{
        .address = 0xaa,
        .state = &tw_state,
        .block = .{ .fork = .tangerine_whistle },
    });
    defer tw_interp.deinit();
    try tw_interp.run();

    try std.testing.expectEqual(Status.stopped, frontier_interp.status);
    try std.testing.expectEqual(Status.stopped, tw_interp.status);

    // Everything before CREATE itself: PUSH4/PUSH1/MSTORE/PUSH1/PUSH1/PUSH1,
    // six verylow-tier ops, plus MSTORE's own memory expansion to fit the
    // 32-byte word (CREATE's [28, 32) read is already covered by then).
    const prefix_cost = gas.verylow * 6 + gas.memoryExpansionCost(0, 0, 32);
    const static_cost = prefix_cost + gas.create_base;
    const available_after_static = gas_limit - static_cost;

    // Pre-150 forwards *everything* left after static costs, so nothing
    // comes back from the never-ending child; Tangerine Whistle reserves
    // 1/64th for the caller instead, which shows up directly as extra
    // gas_remaining once the (identical) static/prefix costs cancel out.
    try std.testing.expectEqual(
        available_after_static / 64,
        tw_interp.gas_remaining - frontier_interp.gas_remaining,
    );
}

/// Init code that returns 5000 bytes (all zero) of "runtime code" — its
/// code-deposit cost (200 gas/byte = 1,000,000 gas) is deliberately far
/// beyond what a modest gas budget can afford, to exercise the
/// insufficient-deposit-gas fork branch below without needing to hit an
/// exact gas boundary.
fn bigReturnInitCode() [12]u8 {
    return .{
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.PUSH2), 0x13, 0x87, // offset = 4999
        @intFromEnum(OpCode.MSTORE8),
        @intFromEnum(OpCode.PUSH2), 0x13, 0x88, // size = 5000
        @intFromEnum(OpCode.PUSH1), 0, // offset = 0
        @intFromEnum(OpCode.RETURN),
    };
}

fn buildCreateCaller(allocator: std.mem.Allocator, init_code: [12]u8) !std.ArrayList(u8) {
    var caller_code: std.ArrayList(u8) = .empty;
    try caller_code.append(allocator, @intFromEnum(OpCode.PUSH12));
    try caller_code.appendSlice(allocator, &init_code);
    try caller_code.appendSlice(allocator, &.{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1), 12, // size
        @intFromEnum(OpCode.PUSH1), 20, // offset (32 - 12)
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.CREATE),
        @intFromEnum(OpCode.STOP),
    });
    return caller_code;
}

test "CREATE with insufficient deposit gas still succeeds on Frontier, with no code stored" {
    const init_code = bigReturnInitCode();
    var caller_code = try buildCreateCaller(std.testing.allocator, init_code);
    defer caller_code.deinit(std.testing.allocator);

    var state = State.init(std.testing.allocator);
    defer state.deinit();

    const new_address = try Interpreter.createAddress(std.testing.allocator, 0xaa, 0);

    var interp = try Interpreter.initCall(std.testing.allocator, caller_code.items, 50_000, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = .frontier },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, new_address), try interp.stack.pop());
    try std.testing.expect(state.exists(new_address));
    try std.testing.expectEqualSlices(u8, &.{}, state.getCode(new_address));
}

test "CREATE with insufficient deposit gas fails entirely on Homestead" {
    const init_code = bigReturnInitCode();
    var caller_code = try buildCreateCaller(std.testing.allocator, init_code);
    defer caller_code.deinit(std.testing.allocator);

    var state = State.init(std.testing.allocator);
    defer state.deinit();

    const new_address = try Interpreter.createAddress(std.testing.allocator, 0xaa, 0);

    var interp = try Interpreter.initCall(std.testing.allocator, caller_code.items, 50_000, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = .homestead },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
    try std.testing.expect(!state.exists(new_address));
}

test "a failed CREATE still consumes the creator's nonce, so its next CREATE lands at a different address" {
    const init_code = bigReturnInitCode(); // returns 5000 bytes; deposit cost unaffordable
    var caller_code = try buildCreateCaller(std.testing.allocator, init_code);
    defer caller_code.deinit(std.testing.allocator);

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setNonce(0xaa, 7);

    var interp = try Interpreter.initCall(std.testing.allocator, caller_code.items, 50_000, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = .byzantium },
    });
    defer interp.deinit();
    try interp.run();

    // The create itself failed (0 pushed, no account stored)...
    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
    // ...but the nonce it consumed is *not* rolled back with the rest of
    // the child's state, matching execution-specs' `create`: the increment
    // happens before the child's snapshot begins. Real chain relies on
    // this — a factory whose nonce lags by one derives a different address
    // for every later CREATE.
    try std.testing.expectEqual(@as(u64, 8), state.get(0xaa).nonce);
}

test "a CREATE that can't afford its endowment leaves the creator's nonce alone" {
    const init_code = bigReturnInitCode();
    var caller_code: std.ArrayList(u8) = .empty;
    defer caller_code.deinit(std.testing.allocator);
    try caller_code.append(std.testing.allocator, @intFromEnum(OpCode.PUSH12));
    try caller_code.appendSlice(std.testing.allocator, &init_code);
    try caller_code.appendSlice(std.testing.allocator, &.{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1), 12, // size
        @intFromEnum(OpCode.PUSH1), 20, // offset (32 - 12)
        @intFromEnum(OpCode.PUSH1), 99, // value: more than the creator has
        @intFromEnum(OpCode.CREATE),
        @intFromEnum(OpCode.STOP),
    });

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setNonce(0xaa, 7);
    try state.setBalance(0xaa, 1); // short of the 99 endowment

    var interp = try Interpreter.initCall(std.testing.allocator, caller_code.items, 200_000, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = .byzantium },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
    // Unlike the failed-init-code case above, the endowment check bails
    // out *before* the nonce is touched at all.
    try std.testing.expectEqual(@as(u64, 7), state.get(0xaa).nonce);
}

test "CREATE failing on insufficient deposit gas clears RETURNDATASIZE, not exposing the deployed code it couldn't afford to store" {
    const init_code = bigReturnInitCode();
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
        @intFromEnum(OpCode.POP), // discard CREATE's own result (0, since it failed)
        @intFromEnum(OpCode.RETURNDATASIZE),
        @intFromEnum(OpCode.STOP),
    });

    var state = State.init(std.testing.allocator);
    defer state.deinit();

    // Tangerine Whistle on (not Homestead, unlike the sibling test above):
    // Homestead-era `CREATE` forwards *all* remaining gas to the child,
    // leaving nothing for this test's own follow-up opcodes regardless of
    // how large a budget it's given — EIP-150's 63/64ths reservation is
    // what leaves the caller anything to work with after an all-gas-forfeiting
    // failure like this one.
    var interp = try Interpreter.initCall(std.testing.allocator, caller_code.items, 50_000, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = .byzantium },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
}

/// Init code that RETURNs `max_code_size + 1` bytes read straight out of
/// never-written (so all-zero) memory — no need to actually fill that much
/// memory, just to charge for expanding into it and return the range.
fn oversizedReturnInitCode() [6]u8 {
    return .{
        @intFromEnum(OpCode.PUSH2), 0x60, 0x01, // size = 24577 (max_code_size + 1)
        @intFromEnum(OpCode.PUSH1), 0, // offset = 0
        @intFromEnum(OpCode.RETURN),
    };
}

fn buildOversizedCreateCaller(allocator: std.mem.Allocator, init_code: [6]u8) !std.ArrayList(u8) {
    var caller_code: std.ArrayList(u8) = .empty;
    try caller_code.append(allocator, @intFromEnum(OpCode.PUSH6));
    try caller_code.appendSlice(allocator, &init_code);
    try caller_code.appendSlice(allocator, &.{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.MSTORE),
        @intFromEnum(OpCode.PUSH1), 6, // size
        @intFromEnum(OpCode.PUSH1), 26, // offset (32 - 6)
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.CREATE),
        @intFromEnum(OpCode.STOP),
    });
    return caller_code;
}

test "nested CREATE rejects code over max_code_size from Spurious Dragon on, not before" {
    const init_code = oversizedReturnInitCode();
    var caller_code = try buildOversizedCreateCaller(std.testing.allocator, init_code);
    defer caller_code.deinit(std.testing.allocator);

    const new_address = try Interpreter.createAddress(std.testing.allocator, 0xaa, 0);

    // Pre-Spurious-Dragon: no limit at all, the oversized code is stored.
    var tw_state = State.init(std.testing.allocator);
    defer tw_state.deinit();
    var tw_interp = try Interpreter.initCall(std.testing.allocator, caller_code.items, 10_000_000, .{
        .address = 0xaa,
        .state = &tw_state,
        .block = .{ .fork = .tangerine_whistle },
    });
    defer tw_interp.deinit();
    try tw_interp.run();

    try std.testing.expectEqual(Status.stopped, tw_interp.status);
    try std.testing.expectEqual(@as(u256, new_address), try tw_interp.stack.pop());
    try std.testing.expectEqual(@as(usize, 24577), tw_state.getCode(new_address).len);

    // From Spurious Dragon on: an exceptional halt, nothing stored.
    var sd_state = State.init(std.testing.allocator);
    defer sd_state.deinit();
    var sd_interp = try Interpreter.initCall(std.testing.allocator, caller_code.items, 10_000_000, .{
        .address = 0xaa,
        .state = &sd_state,
        .block = .{ .fork = .spurious_dragon },
    });
    defer sd_interp.deinit();
    try sd_interp.run();

    try std.testing.expectEqual(Status.stopped, sd_interp.status);
    try std.testing.expectEqual(@as(u256, 0), try sd_interp.stack.pop());
    try std.testing.expect(!sd_state.exists(new_address));
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

test "SLOAD costs more from Tangerine Whistle on" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 1,
        @intFromEnum(OpCode.SLOAD),
        @intFromEnum(OpCode.STOP),
    };

    var frontier_state = State.init(std.testing.allocator);
    defer frontier_state.deinit();
    var frontier_interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &frontier_state,
    });
    defer frontier_interp.deinit();
    try frontier_interp.run();

    var tw_state = State.init(std.testing.allocator);
    defer tw_state.deinit();
    var tw_interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &tw_state,
        .block = .{ .fork = .tangerine_whistle },
    });
    defer tw_interp.deinit();
    try tw_interp.run();

    try std.testing.expectEqual(Status.stopped, frontier_interp.status);
    try std.testing.expectEqual(Status.stopped, tw_interp.status);
    try std.testing.expectEqual(
        gas.sload_150 - gas.sload,
        frontier_interp.gas_remaining - tw_interp.gas_remaining,
    );
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
    try std.testing.expectEqual(@as(i64, gas.sstore_clear_refund), interp.refund);
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

    try std.testing.expectEqual(@as(i64, 0), interp.refund);
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

    try std.testing.expectEqual(@as(i64, 0), interp.refund);
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
    try std.testing.expectEqual(@as(i64, gas.sstore_clear_refund), interp.refund);
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
    try std.testing.expectEqual(@as(i64, 0), interp.refund);
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
        .block = .{ .fork = .byzantium }, // STATICCALL is Byzantium-only (EIP-214).
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

test "BALANCE costs more from Tangerine Whistle on" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xbb,
        @intFromEnum(OpCode.BALANCE),
        @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0xbb, 555);

    var frontier_interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer frontier_interp.deinit();
    try frontier_interp.run();

    var tw_interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = .tangerine_whistle },
    });
    defer tw_interp.deinit();
    try tw_interp.run();

    try std.testing.expectEqual(Status.stopped, frontier_interp.status);
    try std.testing.expectEqual(Status.stopped, tw_interp.status);
    try std.testing.expectEqual(
        gas.balance_150 - gas.balance,
        frontier_interp.gas_remaining - tw_interp.gas_remaining,
    );
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

test "EXTCODESIZE costs more from Tangerine Whistle on" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xbb,
        @intFromEnum(OpCode.EXTCODESIZE),
        @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xbb, &.{ 1, 2, 3 });

    var frontier_interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer frontier_interp.deinit();
    try frontier_interp.run();

    var tw_interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = .tangerine_whistle },
    });
    defer tw_interp.deinit();
    try tw_interp.run();

    try std.testing.expectEqual(Status.stopped, frontier_interp.status);
    try std.testing.expectEqual(Status.stopped, tw_interp.status);
    try std.testing.expectEqual(
        gas.extcode_150 - gas.extcode,
        frontier_interp.gas_remaining - tw_interp.gas_remaining,
    );
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
        .block = .{ .fork = .constantinople },
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
        .block = .{ .fork = .constantinople },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(keccak256(&.{ 1, 2, 3 }), try interp.stack.pop());
}

test "EXTCODEHASH of an existing but empty account is 0, not the hash of empty code" {
    // EIP-1052 defers to EIP-161's notion of "empty": zero nonce, zero
    // balance, no code. Such an account exists in state yet must hash to 0,
    // which is a different answer from `keccak256("")` (0xc5d2...). Using
    // plain existence here returns the wrong one.
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xbb,
        @intFromEnum(OpCode.EXTCODEHASH),
        @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    // Materialised, but with nothing in it — exactly EIP-161's "empty".
    try state.setBalance(0xbb, 0);
    try std.testing.expect(state.exists(0xbb));

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = .constantinople },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
}

test "EXTCODEHASH of a codeless account holding a balance is the hash of empty code" {
    // Balance alone makes it non-empty, so it is "alive" and hashes as a
    // real account with no code — the other side of the rule above.
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xbb,
        @intFromEnum(OpCode.EXTCODEHASH),
        @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0xbb, 1);

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = .constantinople },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(keccak256(""), try interp.stack.pop());
}

/// Runs `writes` as consecutive SSTOREs to one slot under `fork`, starting
/// from `initial`, and reports what the whole sequence cost and refunded.
fn runSstoreSequence(fork: Fork, initial: u256, writes: []const u256) !struct { spent: u64, refund: i64 } {
    var code: std.ArrayList(u8) = .empty;
    defer code.deinit(std.testing.allocator);
    for (writes) |value| {
        // PUSH32 value, PUSH1 slot, SSTORE
        try code.append(std.testing.allocator, @intFromEnum(OpCode.PUSH32));
        var word: [32]u8 = undefined;
        std.mem.writeInt(u256, &word, value, .big);
        try code.appendSlice(std.testing.allocator, &word);
        try code.appendSlice(std.testing.allocator, &.{ @intFromEnum(OpCode.PUSH1), 0x01, @intFromEnum(OpCode.SSTORE) });
    }
    try code.append(std.testing.allocator, @intFromEnum(OpCode.STOP));

    var state = State.init(std.testing.allocator);
    defer state.deinit();
    if (initial != 0) try state.setStorage(0xaa, 1, initial);
    // The slot's value now counts as its transaction-start value.
    state.finalizeTransaction();

    const limit: u64 = 1_000_000;
    var interp = try Interpreter.initCall(std.testing.allocator, code.items, limit, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = fork },
    });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.stopped, interp.status);

    // Each write costs a PUSH32 and a PUSH1 beyond the SSTORE itself.
    const pushes = 6 * writes.len;
    return .{ .spent = limit - interp.gas_remaining - @as(u64, @intCast(pushes)), .refund = interp.refund };
}

test "EIP-2200 prices a first write by what the slot was, not what it becomes" {
    // Zero to nonzero is a real new entry in the trie: full price.
    var r = try runSstoreSequence(.istanbul, 0, &.{7});
    try std.testing.expectEqual(@as(u64, gas.sstore_set), r.spent);
    try std.testing.expectEqual(@as(i64, 0), r.refund);

    // Nonzero to nonzero only rewrites an entry already there.
    r = try runSstoreSequence(.istanbul, 5, &.{7});
    try std.testing.expectEqual(@as(u64, gas.sstore_reset), r.spent);
    try std.testing.expectEqual(@as(i64, 0), r.refund);

    // Nonzero to zero removes it, and earns the clear refund.
    r = try runSstoreSequence(.istanbul, 5, &.{0});
    try std.testing.expectEqual(@as(u64, gas.sstore_reset), r.spent);
    try std.testing.expectEqual(@as(i64, gas.sstore_clear_refund), r.refund);
}

test "EIP-2200 charges a no-op write the price of a lookup" {
    // This is the heart of net metering: writing a slot the value it already
    // holds is not a state change and must not be charged as one.
    const r = try runSstoreSequence(.istanbul, 7, &.{7});
    try std.testing.expectEqual(@as(u64, gas.sload_1884), r.spent);
    try std.testing.expectEqual(@as(i64, 0), r.refund);
}

test "EIP-2200 charges only a lookup for repeated writes to an already-dirty slot" {
    // The first write pays the real price; the second has nothing left to
    // pay for, because the slot is already dirty in this transaction.
    const r = try runSstoreSequence(.istanbul, 0, &.{ 1, 2 });
    try std.testing.expectEqual(@as(u64, gas.sstore_set + gas.sload_1884), r.spent);
    try std.testing.expectEqual(@as(i64, 0), r.refund);
}

test "EIP-2200 refunds the difference when a slot is put back as it was found" {
    // Changed and then restored: the transaction leaves no trace, so the
    // difference between what a real write cost and what the lookups cost
    // comes back.
    var r = try runSstoreSequence(.istanbul, 0, &.{ 1, 0 });
    try std.testing.expectEqual(@as(u64, gas.sstore_set + gas.sload_1884), r.spent);
    try std.testing.expectEqual(@as(i64, gas.sstore_set - gas.sload_1884), r.refund);

    r = try runSstoreSequence(.istanbul, 5, &.{ 9, 5 });
    try std.testing.expectEqual(@as(u64, gas.sstore_reset + gas.sload_1884), r.spent);
    try std.testing.expectEqual(@as(i64, gas.sstore_reset - gas.sload_1884), r.refund);
}

test "EIP-2200 takes the clear refund back when a cleared slot is filled again" {
    // Clearing earns 15000; filling it again in the same transaction must
    // give that back, or a contract could farm refunds by thrashing a slot.
    const r = try runSstoreSequence(.istanbul, 5, &.{ 0, 9 });
    try std.testing.expectEqual(@as(u64, gas.sstore_reset + gas.sload_1884), r.spent);
    try std.testing.expectEqual(@as(i64, 0), r.refund);
}

test "EIP-2200's sentry stops an SSTORE that has only the call stipend" {
    // The guard EIP-1283 lacked. With 2300 gas or less in hand an SSTORE is
    // an exceptional halt, which is what lets a contract keep treating the
    // stipend as unable to change state.
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0x07,
        @intFromEnum(OpCode.PUSH1), 0x01,
        @intFromEnum(OpCode.SSTORE),
        @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    // Exactly the stipend, plus the two pushes, so the SSTORE begins with
    // precisely 2300 and must refuse.
    var interp = try Interpreter.initCall(std.testing.allocator, &code, gas.sstore_sentry_2200 + 6, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = .istanbul },
    });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.out_of_gas, interp.status);
    try std.testing.expectEqual(@as(u256, 0), state.getStorage(0xaa, 1));

    // One more gas and it goes through.
    var ok = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = .istanbul },
    });
    defer ok.deinit();
    try ok.run();
    try std.testing.expectEqual(Status.stopped, ok.status);
    try std.testing.expectEqual(@as(u256, 7), state.getStorage(0xaa, 1));
}

test "SSTORE keeps the flat pre-Istanbul pricing before the fork" {
    // Petersburg withdrew EIP-1283, so nothing between Byzantium and
    // Istanbul uses net metering: a no-op write still costs a full reset.
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0x07,
        @intFromEnum(OpCode.PUSH1), 0x01,
        @intFromEnum(OpCode.SSTORE),
        @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setStorage(0xaa, 1, 7);
    state.finalizeTransaction();

    const limit: u64 = 1_000_000;
    var interp = try Interpreter.initCall(std.testing.allocator, &code, limit, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = .petersburg },
    });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u64, gas.sstore_reset + 6), limit - interp.gas_remaining);
}

test "EIP-1884 reprices SLOAD, BALANCE and EXTCODEHASH at Istanbul" {
    // All three read state whose size had grown well past what their
    // Byzantium-era prices assumed, which is the whole premise of EIP-1884.
    const cases = [_]struct { op: OpCode, before: u64, after: u64 }{
        .{ .op = .SLOAD, .before = 200, .after = 800 },
        .{ .op = .BALANCE, .before = 400, .after = 700 },
        .{ .op = .EXTCODEHASH, .before = 400, .after = 700 },
    };
    for (cases) |case| {
        const code = [_]u8{
            @intFromEnum(OpCode.PUSH1), 0x01,
            @intFromEnum(case.op),
            @intFromEnum(OpCode.STOP),
        };
        for ([_]struct { fork: Fork, cost: u64 }{
            .{ .fork = .petersburg, .cost = case.before },
            .{ .fork = .istanbul, .cost = case.after },
        }) |variant| {
            var state = State.init(std.testing.allocator);
            defer state.deinit();
            try state.setBalance(0x01, 1);

            var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
                .address = 0xaa,
                .state = &state,
                .block = .{ .fork = variant.fork },
            });
            defer interp.deinit();
            try interp.run();

            try std.testing.expectEqual(Status.stopped, interp.status);
            // PUSH1 is 3; the rest is the opcode under test.
            try std.testing.expectEqual(@as(u64, 1_000_000 - 3 - variant.cost), interp.gas_remaining);
        }
    }
}

test "EXTCODEHASH costs 400 gas, its own EIP-1052 price" {
    // Not EXTCODESIZE's price in either era: 700 after EIP-150 would be an
    // overcharge, and Frontier's 20 (which this once charged by reusing
    // `gas.extcode`) undercharges by 380. The latter left every transaction
    // that touched EXTCODEHASH 380 gas cheaper than real chain, first seen
    // as a miner-balance mismatch at mainnet block 7,398,462.
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xbb,
        @intFromEnum(OpCode.EXTCODEHASH),
        @intFromEnum(OpCode.STOP),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0xbb, 1);

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = .constantinople },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    // PUSH1 (3) + EXTCODEHASH (400) + STOP (0).
    try std.testing.expectEqual(@as(u64, 1_000_000 - 3 - 400), interp.gas_remaining);
}

test "EXTCODEHASH is invalid before Constantinople" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xbb,
        @intFromEnum(OpCode.EXTCODEHASH),
    };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.invalid_opcode, interp.status);
}

test "CREATE2 is invalid before Constantinople" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.CREATE2),
    };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.invalid_opcode, interp.status);
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
        .block = .{ .fork = .byzantium }, // RETURNDATASIZE is Byzantium-only (EIP-211).
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 4), try interp.stack.pop());
}

test "RETURNDATASIZE is invalid before Byzantium" {
    const code = [_]u8{@intFromEnum(OpCode.RETURNDATASIZE)};
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.invalid_opcode, interp.status);
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
        .block = .{ .fork = .byzantium }, // RETURNDATACOPY is Byzantium-only (EIP-211).
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    var word_bytes: [32]u8 = undefined;
    std.mem.writeInt(u256, &word_bytes, try interp.memory.readWord(0), .big);
    try std.testing.expectEqualSlices(u8, &.{ 0xde, 0xad, 0xbe, 0xef }, word_bytes[0..4]);
}

test "RETURNDATACOPY is invalid before Byzantium" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.RETURNDATACOPY),
    };
    var interp = try Interpreter.init(std.testing.allocator, &code, 1_000_000);
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.invalid_opcode, interp.status);
}

test "RETURNDATACOPY reading past the last call's output is invalid" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 1, // size: nothing has been called yet, so any size is out of bounds
        @intFromEnum(OpCode.PUSH1), 0, // offset
        @intFromEnum(OpCode.PUSH1), 0, // dest
        @intFromEnum(OpCode.RETURNDATACOPY),
    };
    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .block = .{ .fork = .byzantium },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.invalid_opcode, interp.status);
}

test "a CALL that fails for insufficient balance clears RETURNDATASIZE, not leaving a stale value from an earlier successful call" {
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
    try state.setBalance(0xaa, 0); // can't afford the second CALL's value

    const caller_code = [_]u8{
        // First: a real CALL that succeeds and returns 4 bytes.
        @intFromEnum(OpCode.PUSH1), 0, // retSize
        @intFromEnum(OpCode.PUSH1), 0, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH1), 0, // argsOffset
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.PUSH1), 0xcc, // address
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10, // gas
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.POP), // discard CALL's success flag
        // Second: a CALL with a value the caller can't afford (address
        // 0xcc has no code either, but that's beside the point: the
        // balance check rejects it before a callee would ever run).
        @intFromEnum(OpCode.PUSH1), 0, // retSize
        @intFromEnum(OpCode.PUSH1), 0, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH1), 0, // argsOffset
        @intFromEnum(OpCode.PUSH1), 1, // value: unaffordable
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
        .block = .{ .fork = .byzantium },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u256, 0), try interp.stack.pop());
}

test "a CALL that exits early still grows the memory it charged for" {
    // The args region reaches past the end of memory, so the CALL pays a
    // memory-expansion charge. It then exits early on an unaffordable
    // value, never reading those bytes. If the growth is charged but not
    // performed, the following MSTORE into the same region is billed for
    // it all over again — which is exactly how zevm overcharged a real
    // mainnet transaction (block 6,228,137) by 3 gas.
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0xaa, 0); // can't afford the CALL's value

    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // retSize
        @intFromEnum(OpCode.PUSH1), 160, // retOffset
        @intFromEnum(OpCode.PUSH1), 2, // argsSize: reaches byte 162
        @intFromEnum(OpCode.PUSH1), 160, // argsOffset
        @intFromEnum(OpCode.PUSH1), 1, // value: unaffordable
        @intFromEnum(OpCode.PUSH1), 0xcc, // address
        @intFromEnum(OpCode.PUSH2), 0x27, 0x10, // gas
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.POP),
        @intFromEnum(OpCode.STOP),
    };

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = .byzantium },
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, interp.status);
    // Grown to cover byte 162, rounded up to a whole word: 6 words.
    try std.testing.expectEqual(@as(usize, 192), interp.memory.len());
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
        .block = .{ .fork = .byzantium }, // STATICCALL is Byzantium-only (EIP-214).
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

test "SELFDESTRUCT transfers balance to the beneficiary immediately, but its code only at transaction end" {
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
    try std.testing.expectEqual(@as(i64, gas.selfdestruct_refund), interp.refund);

    // Balance moves immediately, but real Ethereum only deletes the
    // account itself (code included) once the transaction fully commits —
    // until `finalizeTransaction`, a later call within the same
    // transaction would still find this same code here.
    try std.testing.expectEqualSlices(u8, &code, state.getCode(0xaa));
    state.finalizeTransaction();
    try std.testing.expectEqualSlices(u8, &.{}, state.getCode(0xaa));
}

test "from Tangerine Whistle on, SELFDESTRUCT costs 5000 base plus a new-account surcharge for a not-yet-existing beneficiary" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xbb,
        @intFromEnum(OpCode.SELFDESTRUCT),
    };

    // Baseline: 0xbb already exists (pre-touched), so no surcharge — just
    // the flat 5000 base.
    var existing_state = State.init(std.testing.allocator);
    defer existing_state.deinit();
    try existing_state.setCode(0xaa, &code);
    try existing_state.setBalance(0xbb, 0);
    var existing_interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &existing_state,
        .block = .{ .fork = .tangerine_whistle },
    });
    defer existing_interp.deinit();
    try existing_interp.run();

    // 0xbb doesn't exist yet: pays the extra 25000.
    var new_state = State.init(std.testing.allocator);
    defer new_state.deinit();
    try new_state.setCode(0xaa, &code);
    var new_interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &new_state,
        .block = .{ .fork = .tangerine_whistle },
    });
    defer new_interp.deinit();
    try new_interp.run();

    // Pre-150, for comparison: no charge at all (base is 0, and the
    // new-account surcharge doesn't exist yet).
    var frontier_state = State.init(std.testing.allocator);
    defer frontier_state.deinit();
    try frontier_state.setCode(0xaa, &code);
    var frontier_interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &frontier_state,
    });
    defer frontier_interp.deinit();
    try frontier_interp.run();

    try std.testing.expectEqual(Status.stopped, existing_interp.status);
    try std.testing.expectEqual(Status.stopped, new_interp.status);
    try std.testing.expectEqual(Status.stopped, frontier_interp.status);
    try std.testing.expectEqual(gas.selfdestruct_new_account, existing_interp.gas_remaining - new_interp.gas_remaining);
    try std.testing.expectEqual(gas.selfdestruct_base_150, frontier_interp.gas_remaining - existing_interp.gas_remaining);
}

test "from Spurious Dragon on, SELFDESTRUCT's new-account surcharge only applies if there's actually a balance to move" {
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xbb,
        @intFromEnum(OpCode.SELFDESTRUCT),
    };

    // 0xbb doesn't exist (not alive), but 0xaa has zero balance: nothing
    // would actually move, so no surcharge despite the not-alive beneficiary.
    var zero_balance_state = State.init(std.testing.allocator);
    defer zero_balance_state.deinit();
    try zero_balance_state.setCode(0xaa, &code);
    var zero_balance_interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &zero_balance_state,
        .block = .{ .fork = .spurious_dragon },
    });
    defer zero_balance_interp.deinit();
    try zero_balance_interp.run();

    // Same, but 0xaa has a nonzero balance to move: the surcharge applies,
    // same as Tangerine Whistle's rule.
    var nonzero_balance_state = State.init(std.testing.allocator);
    defer nonzero_balance_state.deinit();
    try nonzero_balance_state.setCode(0xaa, &code);
    try nonzero_balance_state.setBalance(0xaa, 100);
    var nonzero_balance_interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &nonzero_balance_state,
        .block = .{ .fork = .spurious_dragon },
    });
    defer nonzero_balance_interp.deinit();
    try nonzero_balance_interp.run();

    try std.testing.expectEqual(Status.stopped, zero_balance_interp.status);
    try std.testing.expectEqual(Status.stopped, nonzero_balance_interp.status);
    try std.testing.expectEqual(
        gas.selfdestruct_new_account,
        zero_balance_interp.gas_remaining - nonzero_balance_interp.gas_remaining,
    );
}

test "a zero-balance SELFDESTRUCT still materialises its beneficiary" {
    // Real chain assigns the beneficiary's balance unconditionally, so even
    // moving nothing leaves an empty account behind in the state trie. This
    // is a state-root-visible difference that produces no other symptom at
    // the time: mainnet block 113,121 destroyed a zero-balance contract to a
    // brand-new beneficiary, and zevm's root diverged from the header there
    // while every balance still matched.
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xbb, // beneficiary, which does not exist yet
        @intFromEnum(OpCode.SELFDESTRUCT),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xaa, &code);
    // Balance deliberately left at zero: nothing moves.
    try std.testing.expect(!state.exists(0xbb));

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expect(state.exists(0xbb));
    try std.testing.expectEqual(@as(u256, 0), state.getBalance(0xbb));
}

test "a zero-balance SELFDESTRUCT to yourself does not resurrect anything" {
    // The beneficiary-is-self case must not go through the transfer path:
    // there is no separate account to materialise.
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xaa,
        @intFromEnum(OpCode.SELFDESTRUCT),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xaa, &code);

    var interp = try Interpreter.initCall(std.testing.allocator, &code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(@as(u256, 0), state.getBalance(0xaa));
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

test "a CALL to an address that just self-destructed, within the same transaction, still runs its code" {
    // callee: PUSH1 0, CALLDATALOAD, SELFDESTRUCT — pre-EIP-150, this costs
    // exactly 6 gas (3+3+0) and halts, moving whatever balance it has to
    // beneficiary 0 (empty calldata reads as zero). Mirrors a real,
    // observed mainnet pattern: a "self-destructing helper" contract that
    // legitimately gets `CALL`ed, and destructs, more than once in one
    // transaction.
    const selfdestruct_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0,
        @intFromEnum(OpCode.CALLDATALOAD),
        @intFromEnum(OpCode.SELFDESTRUCT),
    };
    // caller: CALL(gas=6, addr=0xcc, value=0, all sizes/offsets 0), twice, then STOP.
    const call_once = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // retSize
        @intFromEnum(OpCode.PUSH1), 0, // retOffset
        @intFromEnum(OpCode.PUSH1), 0, // argsSize
        @intFromEnum(OpCode.PUSH1), 0, // argsOffset
        @intFromEnum(OpCode.PUSH1), 0, // value
        @intFromEnum(OpCode.PUSH1), 0xcc, // address
        @intFromEnum(OpCode.PUSH1), 6, // gas
        @intFromEnum(OpCode.CALL),
        @intFromEnum(OpCode.POP),
    };
    const caller_code = call_once ++ call_once ++ [_]u8{@intFromEnum(OpCode.STOP)};

    // Baseline: 0xcc pre-exists with no code at all, so both CALLs hit the
    // trivial "no code" success path and forward nothing.
    var baseline_state = State.init(std.testing.allocator);
    defer baseline_state.deinit();
    try baseline_state.setBalance(0xcc, 0);
    var baseline_interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &baseline_state,
    });
    defer baseline_interp.deinit();
    try baseline_interp.run();

    // Test: 0xcc starts out not existing at all and holds the
    // self-destructing code above.
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xcc, &selfdestruct_code);
    var interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer interp.deinit();
    try interp.run();

    try std.testing.expectEqual(Status.stopped, baseline_interp.status);
    try std.testing.expectEqual(Status.stopped, interp.status);
    // `setCode` already touches 0xcc into existence in both scenarios, so
    // no new-account surcharge is in play here — this isolates just the
    // forwarded-gas question. Both CALLs fully spend their forwarded 6 gas
    // running the callee's code, including the second, even though the
    // first CALL already self-destructed it. If a self-destruct wiped code
    // immediately instead of only at `finalizeTransaction`, the second
    // CALL would wrongly hit the "no code" trivial-success path and refund
    // its 6 gas back, making this difference 6 less than expected.
    try std.testing.expectEqual(
        2 * 6,
        baseline_interp.gas_remaining - interp.gas_remaining,
    );
    // Real Ethereum's SELFDESTRUCT refund is earned once per address per
    // transaction (a set-membership check against `accounts_to_delete`),
    // not once per call: destroying the same already-destroyed contract a
    // second time doesn't pay out again. A contract repeatedly `CALL`ed to
    // self-destruct itself, like this real-world mainnet pattern, would
    // otherwise rack up an inflated refund, hit the per-transaction cap,
    // and badly under-report gas_used.
    try std.testing.expectEqual(@as(i64, gas.selfdestruct_refund), interp.refund);
}

test "a CALL to a previously-self-destructed address pays the new-account surcharge again" {
    const selfdestruct_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xbb,
        @intFromEnum(OpCode.SELFDESTRUCT),
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0xcc, &selfdestruct_code);

    var destroyer = try Interpreter.initCall(std.testing.allocator, &selfdestruct_code, 1_000_000, .{
        .address = 0xcc,
        .state = &state,
    });
    defer destroyer.deinit();
    try destroyer.run();
    // Mirrors what `Evm.executeTransaction` does once a transaction's own
    // call/create is done: only past this point is a self-destruct real.
    state.finalizeTransaction();
    try std.testing.expect(!state.exists(0xcc));

    // caller: CALL(gas=10000, addr=0xcc, value=0, argsOffset=0, argsSize=0, retOffset=0, retSize=0)
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

    // Baseline: an ordinary, never-destroyed account, so no surcharge.
    var existing_state = State.init(std.testing.allocator);
    defer existing_state.deinit();
    try existing_state.setBalance(0xcc, 0);
    var existing_interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &existing_state,
    });
    defer existing_interp.deinit();
    try existing_interp.run();

    var post_destruct_interp = try Interpreter.initCall(std.testing.allocator, &caller_code, 1_000_000, .{
        .address = 0xaa,
        .state = &state,
    });
    defer post_destruct_interp.deinit();
    try post_destruct_interp.run();

    try std.testing.expectEqual(Status.stopped, existing_interp.status);
    try std.testing.expectEqual(Status.stopped, post_destruct_interp.status);
    try std.testing.expectEqual(
        gas.call_new_account,
        existing_interp.gas_remaining - post_destruct_interp.gas_remaining,
    );
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
        .block = .{ .fork = .byzantium }, // REVERT is Byzantium-only (EIP-140).
    });
    defer interp.deinit();
    try interp.run();
    if (interp.status != .stopped) state.revertTo(cp);

    try std.testing.expectEqual(Status.reverted, interp.status);
    try std.testing.expectEqual(@as(u256, 500), state.getBalance(0xcc));
    try std.testing.expectEqualSlices(u8, &callee_code, state.getCode(0xcc));
}

test "EIP-2929 reprices SSTORE: cold surcharge once, warm reads, cheaper resets" {
    // The slot starts cold in every sequence below. Numbers are the EIP's,
    // written out rather than derived from the constants they test.
    var r = try runSstoreSequence(.berlin, 0, &.{7});
    try std.testing.expectEqual(@as(u64, 2100 + 20000), r.spent);
    try std.testing.expectEqual(@as(i64, 0), r.refund);

    // A reset is 5000 in total once the cold lookup is counted in.
    r = try runSstoreSequence(.berlin, 5, &.{7});
    try std.testing.expectEqual(@as(u64, 5000), r.spent);

    r = try runSstoreSequence(.berlin, 5, &.{0});
    try std.testing.expectEqual(@as(u64, 5000), r.spent);
    try std.testing.expectEqual(@as(i64, 15000), r.refund);

    // A write that changes nothing pays the cold lookup and a warm read.
    r = try runSstoreSequence(.berlin, 5, &.{5});
    try std.testing.expectEqual(@as(u64, 2100 + 100), r.spent);

    // Restoring the original value refunds what the round trip overpaid:
    // 19,900 from an empty slot, 2,800 from an occupied one.
    r = try runSstoreSequence(.berlin, 0, &.{ 7, 0 });
    try std.testing.expectEqual(@as(u64, 2100 + 20000 + 100), r.spent);
    try std.testing.expectEqual(@as(i64, 19900), r.refund);

    r = try runSstoreSequence(.berlin, 5, &.{ 7, 5 });
    try std.testing.expectEqual(@as(u64, 5000 + 100), r.spent);
    try std.testing.expectEqual(@as(i64, 2800), r.refund);
}

test "EIP-2929: SLOAD and BALANCE are cold the first time and warm after" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setStorage(0xaa, 1, 42);
    state.finalizeTransaction();

    // PUSH1 1, SLOAD, POP, twice over.
    const sload_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0x01, @intFromEnum(OpCode.SLOAD), @intFromEnum(OpCode.POP),
        @intFromEnum(OpCode.PUSH1), 0x01, @intFromEnum(OpCode.SLOAD), @intFromEnum(OpCode.POP),
        @intFromEnum(OpCode.STOP),
    };
    var interp = try Interpreter.initCall(std.testing.allocator, &sload_code, 100_000, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = .berlin },
    });
    defer interp.deinit();
    try interp.run();
    try std.testing.expectEqual(Status.stopped, interp.status);
    try std.testing.expectEqual(@as(u64, (3 + 2100 + 2) + (3 + 100 + 2)), 100_000 - interp.gas_remaining);

    // PUSH1 0xbb, BALANCE, POP, twice over.
    const balance_code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0xbb, @intFromEnum(OpCode.BALANCE), @intFromEnum(OpCode.POP),
        @intFromEnum(OpCode.PUSH1), 0xbb, @intFromEnum(OpCode.BALANCE), @intFromEnum(OpCode.POP),
        @intFromEnum(OpCode.STOP),
    };
    var interp2 = try Interpreter.initCall(std.testing.allocator, &balance_code, 100_000, .{
        .address = 0xaa,
        .state = &state,
        .block = .{ .fork = .berlin },
    });
    defer interp2.deinit();
    try interp2.run();
    try std.testing.expectEqual(Status.stopped, interp2.status);
    try std.testing.expectEqual(@as(u64, (3 + 2600 + 2) + (3 + 100 + 2)), 100_000 - interp2.gas_remaining);
}

test "EIP-3529: clearing a slot refunds 4800 and SELFDESTRUCT refunds nothing from London on" {
    var r = try runSstoreSequence(.london, 5, &.{0});
    try std.testing.expectEqual(@as(u64, 5000), r.spent);
    try std.testing.expectEqual(@as(i64, 4800), r.refund);
    // The restore refunds are untouched by EIP-3529.
    r = try runSstoreSequence(.london, 5, &.{ 7, 5 });
    try std.testing.expectEqual(@as(i64, 2800), r.refund);

    // PUSH1 0xbb, SELFDESTRUCT.
    const code = [_]u8{ @intFromEnum(OpCode.PUSH1), 0xbb, @intFromEnum(OpCode.SELFDESTRUCT) };
    for ([_]Fork{ .berlin, .london }) |fork| {
        var state = State.init(std.testing.allocator);
        defer state.deinit();
        var interp = try Interpreter.initCall(std.testing.allocator, &code, 100_000, .{
            .address = 0xaa,
            .state = &state,
            .block = .{ .fork = fork },
        });
        defer interp.deinit();
        try interp.run();
        try std.testing.expectEqual(Status.stopped, interp.status);
        try std.testing.expectEqual(@as(i64, if (fork == .london) 0 else 24000), interp.refund);
    }
}

test "DIV, MOD and MULMOD fast paths agree with plain wide arithmetic" {
    // The references are exactly what these opcodes computed before their
    // fast paths existed.
    const max = std.math.maxInt(u256);
    var prng: std.Random.DefaultPrng = .init(0x6d756c6d);
    const rand = prng.random();
    // Values spread across the widths each fast path keys on.
    const edges = [_]u256{ 0, 1, 2, 3, 7, std.math.maxInt(u64) - 1, std.math.maxInt(u64), @as(u256, std.math.maxInt(u64)) + 1, std.math.maxInt(u128), @as(u256, std.math.maxInt(u128)) + 1, max - 2, max - 1, max };
    var values: [13 + 60]u256 = undefined;
    @memcpy(values[0..13], &edges);
    for (values[13..], 0..) |*v, i| v.* = switch (i % 3) {
        0 => rand.int(u64),
        1 => rand.int(u128),
        else => rand.int(u256),
    };
    for (values) |a| for (values) |b| {
        try std.testing.expectEqual(if (b == 0) 0 else a / b, div(a, b));
        try std.testing.expectEqual(if (b == 0) 0 else a % b, mod(a, b));
    };
    // MULMOD: every modulus class, with 2^256 - 1 (Uniswap's) included.
    for (values[0..40]) |a| for (values[0..40]) |b| for (values) |n| {
        const expected: u256 = if (n == 0) 0 else @truncate((@as(u512, a) * @as(u512, b)) % @as(u512, n));
        try std.testing.expectEqual(expected, mulmod(a, b, n));
    };
    // The fold's boundaries: products whose `hi + lo` lands exactly on, or
    // one past, the modulus.
    try std.testing.expectEqual(@as(u256, 0), mulmod(max, 1, max));
    try std.testing.expectEqual(@as(u256, 0), mulmod(max, max, max));
    try std.testing.expectEqual(@as(u256, 1), mulmod(max - 1, max - 1, max));
}

test "the 64-bit-limb Algorithm D agrees with compiler-rt's wide division" {
    // compiler-rt's `/` and `%` are the reference. Limbs are drawn from a
    // structured set as well as at random: uniformly random limbs almost never
    // reach the rare "add one divisor back" step, while limbs such as 0, 2^63
    // and 2^64 - 1 hit it regularly.
    const special = [_]u64{ 0, 1, 2, (1 << 63) - 1, 1 << 63, (1 << 63) + 1, std.math.maxInt(u64) - 1, std.math.maxInt(u64) };
    var prng: std.Random.DefaultPrng = .init(0x6b6e7574);
    const rand = prng.random();
    const limb = struct {
        fn pick(r: std.Random, sp: []const u64) u64 {
            return if (r.boolean()) sp[r.uintLessThan(usize, sp.len)] else r.int(u64);
        }
    }.pick;
    for (0..60_000) |_| {
        var u_limbs: [8]u64 = undefined;
        var v_limbs: [4]u64 = undefined;
        for (&u_limbs) |*x| x.* = limb(rand, &special);
        for (&v_limbs) |*x| x.* = limb(rand, &special);
        // Vary how many limbs are significant, so every divisor length and
        // dividend-shorter-than-divisor case is covered.
        const vlen = rand.uintLessThan(usize, 4) + 1;
        for (v_limbs[vlen..]) |*x| x.* = 0;
        const ulen = rand.uintLessThan(usize, 9);
        for (u_limbs[ulen..]) |*x| x.* = 0;
        var v: u256 = 0;
        for (v_limbs, 0..) |x, k| v |= @as(u256, x) << @intCast(64 * k);
        if (v == 0) continue;
        var u: u512 = 0;
        for (u_limbs, 0..) |x, k| u |= @as(u512, x) << @intCast(64 * k);

        const wide = divRemLimbs(8, toLimbs(8, u), toLimbs(4, v));
        try std.testing.expectEqual(@as(u256, @truncate(u % v)), fromLimbs(wide.r));
        var q: u512 = 0;
        for (wide.q, 0..) |x, k| q |= @as(u512, x) << @intCast(64 * k);
        try std.testing.expectEqual(u / v, q);

        const u256v: u256 = @truncate(u);
        const narrow = divRemLimbs(4, toLimbs(4, u256v), toLimbs(4, v));
        try std.testing.expectEqual(u256v / v, fromLimbs(narrow.q));
        try std.testing.expectEqual(u256v % v, fromLimbs(narrow.r));
    }
    // The randomized cases must have exercised the add-back branch.
    try std.testing.expect(add_back_count > 0);
    // Hacker's Delight's own add-back case, scaled to 64-bit limbs.
    const u_hd: [4]u64 = .{ 0, 0, 1 << 63, (1 << 63) - 1 };
    const v_hd: [4]u64 = .{ 1, 0, 1 << 63, 0 };
    const hd = divRemLimbs(4, u_hd, v_hd);
    const uu = fromLimbs(u_hd);
    const vv = fromLimbs(v_hd);
    try std.testing.expectEqual(uu / vv, fromLimbs(hd.q));
    try std.testing.expectEqual(uu % vv, fromLimbs(hd.r));
}
