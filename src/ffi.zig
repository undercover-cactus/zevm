//! The C ABI surface exposed to other languages (e.g. the Rust FFI
//! benchmark). Kept separate from `root.zig`'s normal Zig-facing API since
//! none of `Evm`/`State`/`Transaction`'s real types (slices, optionals, an
//! allocator, tagged unions) have a natural C representation.
//!
//! Scoped to exactly what's needed to replay blocks from Rust: create a
//! `State`, load genesis balances into it, create an `Evm`, then feed it
//! blocks. `Address` is 20 bytes and `u256` is 32 bytes, both big-endian.

const std = @import("std");
const zevm = @import("root.zig");

/// Handles outlive any single call, so there's no natural point to run leak
/// detection, unlike `zevm_run_basic_demo`'s self-contained scope below.
/// `smp_allocator` rather than `page_allocator`, since `page_allocator`
/// syscalls per allocation and `zevm_evm_process_block` allocates on every call.
const ffi_allocator = std.heap.smp_allocator;

fn stateFromHandle(handle: *anyopaque) *zevm.State {
    return @ptrCast(@alignCast(handle));
}

fn evmFromHandle(handle: *anyopaque) *zevm.Evm {
    return @ptrCast(@alignCast(handle));
}

export fn zevm_state_create() callconv(.c) ?*anyopaque {
    const state = ffi_allocator.create(zevm.State) catch return null;
    state.* = zevm.State.init(ffi_allocator);
    return state;
}

export fn zevm_state_destroy(handle: *anyopaque) callconv(.c) void {
    const state = stateFromHandle(handle);
    state.deinit();
    ffi_allocator.destroy(state);
}

/// For loading genesis balances before replaying any blocks.
export fn zevm_state_set_balance(
    handle: *anyopaque,
    address: *const [20]u8,
    balance: *const [32]u8,
) callconv(.c) c_int {
    stateFromHandle(handle).setBalance(
        std.mem.readInt(u160, address, .big),
        std.mem.readInt(u256, balance, .big),
    ) catch return -1;
    return 0;
}

export fn zevm_state_get_balance(
    handle: *anyopaque,
    address: *const [20]u8,
    out_balance: *[32]u8,
) callconv(.c) void {
    const balance = stateFromHandle(handle).getBalance(std.mem.readInt(u160, address, .big));
    std.mem.writeInt(u256, out_balance, balance, .big);
}

/// Mirrors `state.accountCount()`, the summary both `examples/sync.zig`
/// and `rzevm/examples/sync.rs` print at the end of a replay.
export fn zevm_state_accounts_count(handle: *anyopaque) callconv(.c) usize {
    return stateFromHandle(handle).accountCount();
}

export fn zevm_evm_create(state_handle: *anyopaque) callconv(.c) ?*anyopaque {
    const evm = ffi_allocator.create(zevm.Evm) catch return null;
    evm.* = .{ .allocator = ffi_allocator, .state = stateFromHandle(state_handle) };
    return evm;
}

export fn zevm_evm_destroy(handle: *anyopaque) callconv(.c) void {
    ffi_allocator.destroy(evmFromHandle(handle));
}

/// A C-compatible mirror of `Block.Entry`. `has_to == false` means a
/// contract-creation transaction (matching `Transaction.to == null`).
pub const CTransaction = extern struct {
    from: [20]u8,
    nonce: u64,
    gas_price: [32]u8,
    gas_limit: u64,
    has_to: bool,
    to: [20]u8,
    value: [32]u8,
    data_ptr: [*]const u8,
    data_len: usize,
    v: u64,
    r: [32]u8,
    s: [32]u8,
};

pub const CUncle = extern struct {
    number: u64,
    miner: [20]u8,
};

/// The C-ABI equivalent of `Evm.processBlock`. Panics under the same
/// conditions if `number` is past Frontier.
export fn zevm_evm_process_block(
    evm_handle: *anyopaque,
    number: u64,
    miner: *const [20]u8,
    timestamp: u64,
    gas_limit: u64,
    difficulty: *const [32]u8,
    transactions_ptr: [*]const CTransaction,
    transactions_len: usize,
    uncles_ptr: [*]const CUncle,
    uncles_len: usize,
    /// `BLOCKHASH`'s lookup window, most recent first: index 0 is
    /// `number - 1`'s hash, up to 256 entries. May be shorter (or empty);
    /// see `Interpreter.BlockContext.recent_hashes`.
    recent_hashes_ptr: [*]const [32]u8,
    recent_hashes_len: usize,
) callconv(.c) c_int {
    const evm = evmFromHandle(evm_handle);

    const entries = ffi_allocator.alloc(zevm.Block.Entry, transactions_len) catch return -1;
    defer ffi_allocator.free(entries);
    for (transactions_ptr[0..transactions_len], entries) |ctx, *entry| {
        entry.* = .{
            .from = std.mem.readInt(u160, &ctx.from, .big),
            .tx = .{
                .nonce = ctx.nonce,
                .gas_price = std.mem.readInt(u256, &ctx.gas_price, .big),
                .gas_limit = ctx.gas_limit,
                .to = if (ctx.has_to) std.mem.readInt(u160, &ctx.to, .big) else null,
                .value = std.mem.readInt(u256, &ctx.value, .big),
                .data = ctx.data_ptr[0..ctx.data_len],
                .v = ctx.v,
                .r = std.mem.readInt(u256, &ctx.r, .big),
                .s = std.mem.readInt(u256, &ctx.s, .big),
            },
        };
    }

    const uncles = ffi_allocator.alloc(zevm.Block.Uncle, uncles_len) catch return -1;
    defer ffi_allocator.free(uncles);
    for (uncles_ptr[0..uncles_len], uncles) |cu, *u| {
        u.* = .{ .number = cu.number, .miner = std.mem.readInt(u160, &cu.miner, .big) };
    }

    const recent_hashes = ffi_allocator.alloc(zevm.Hash, recent_hashes_len) catch return -1;
    defer ffi_allocator.free(recent_hashes);
    for (recent_hashes_ptr[0..recent_hashes_len], recent_hashes) |h, *out| {
        out.* = std.mem.readInt(u256, &h, .big);
    }

    evm.processBlock(.{
        .number = number,
        .miner = std.mem.readInt(u160, miner, .big),
        .transactions = entries,
        .uncles = uncles,
        .timestamp = timestamp,
        .gas_limit = gas_limit,
        .difficulty = std.mem.readInt(u256, difficulty, .big),
        .recent_hashes = recent_hashes,
    }) catch return -1;

    return 0;
}

/// Reproduces `examples/basic.zig`'s scenario through a C ABI. Balances are
/// `u64` here as a stand-in; real values would need a wider representation
/// (e.g. `[32]u8`) across the boundary.
export fn zevm_run_basic_demo(
    sender_before: *u64,
    sender_after: *u64,
    recipient_after: *u64,
) callconv(.c) c_int {
    var gpa = std.heap.DebugAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    var state = zevm.State.init(allocator);
    defer state.deinit();
    state.setBalance(0x1, 1000) catch return -1;
    sender_before.* = @intCast(state.getBalance(0x1));

    var evm = zevm.Evm{ .allocator = allocator, .state = &state };
    const result = evm.executeTransaction(.{
        .nonce = 0,
        .gas_price = 0,
        .gas_limit = 21000,
        .to = 0xdd,
        .value = 100,
        .data = &.{},
        .v = 0,
        .r = 0,
        .s = 0,
    }, 0x1) catch return -1;
    defer allocator.free(result.return_data);

    sender_after.* = @intCast(state.getBalance(0x1));
    recipient_after.* = @intCast(state.getBalance(0xdd));
    return 0;
}
