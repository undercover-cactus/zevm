//! Static EVM gas costs and the memory-expansion cost formula.
//!
//! These are per-opcode base costs only; access-list warm/cold pricing
//! (EIP-2929) and anything needing the `Host` interface are later milestones.

const std = @import("std");

pub const zero: u64 = 0;
pub const jumpdest: u64 = 1;
pub const base: u64 = 2;
pub const verylow: u64 = 3;
pub const low: u64 = 5;
pub const mid: u64 = 8;
pub const high: u64 = 10;

pub const keccak256_base: u64 = 30;
pub const keccak256_word: u64 = 6;

pub const exp_base: u64 = 10;
/// Pre-EIP-160 (Spurious Dragon) value; that fork later raised this to 50.
pub const exp_byte: u64 = 10;
pub const exp_byte_160: u64 = 50;

pub const copy_word: u64 = 3;

/// Pre-EIP-150 value; that fork raised this to `sload_150`.
pub const sload: u64 = 50;
pub const sload_150: u64 = 200;
/// Setting a zero slot to a nonzero value.
pub const sstore_set: u64 = 20000;
/// Any other SSTORE. Frontier's flat rule, not EIP-2200's net-metered successor.
pub const sstore_reset: u64 = 5000;

/// Pre-EIP-150 value; that fork raised this to `call_base_150` and added the
/// 63/64ths gas-forwarding cap (see `Interpreter.call`).
pub const call_base: u64 = 40;
pub const call_base_150: u64 = 700;
pub const call_value: u64 = 9000;
pub const call_new_account: u64 = 25000;
/// Free gas granted to the callee on top of whatever was forwarded, only
/// when the call transfers value. Not charged to the caller.
pub const call_stipend: u64 = 2300;

pub const create_base: u64 = 32000;
/// Per-byte cost of storing the code a CREATE/CREATE2's init code returns.
pub const code_deposit_byte: u64 = 200;

/// Pre-EIP-150 value; that fork raised this to `balance_150`. Both are
/// superseded by EIP-2929 warm/cold pricing later still.
pub const balance: u64 = 20;
pub const balance_150: u64 = 400;
/// Pre-EIP-150 value (`EXTCODESIZE`/`EXTCODECOPY`'s base cost); that fork
/// raised this to `extcode_150`.
pub const extcode: u64 = 20;
pub const extcode_150: u64 = 700;
pub const blockhash: u64 = 20;

pub const log_base: u64 = 375;
pub const log_topic: u64 = 375;
pub const log_data_byte: u64 = 8;

/// Pre-EIP-150 value; that fork raised this to `selfdestruct_base_150` and
/// added `selfdestruct_new_account`, a surcharge for destructing to a
/// beneficiary that doesn't exist yet (mirrors `call_new_account`).
pub const selfdestruct_base: u64 = 0;
pub const selfdestruct_base_150: u64 = 5000;
pub const selfdestruct_new_account: u64 = 25000;
/// Refunded once per address `SELFDESTRUCT`ed per transaction (removed
/// entirely by EIP-3529/London) — `State.isPendingDestruction` is what
/// keeps a repeat `SELFDESTRUCT` of the same still-live address (real
/// Ethereum only deletes an account at the end of its transaction, so this
/// can legitimately happen) from earning it twice.
pub const selfdestruct_refund: u64 = 24000;

/// Frontier's flat refund for `SSTORE` clearing a slot from nonzero to
/// zero, with no "undo if set back to nonzero later" bookkeeping (that
/// came later, with EIP-1283/2200). Capped at half the transaction's net
/// gas used, see `Evm.zig`.
pub const sstore_clear_refund: u64 = 15000;
/// A transaction's total refund can never exceed this fraction of its raw
/// gas used, preventing gas-usage inflation just to farm refunds.
pub const max_refund_denominator: u64 = 2;

/// Flat cost every transaction pays before any of its code runs, for
/// simply being included in a block.
pub const tx_base: u64 = 21000;
pub const tx_data_zero: u64 = 4;
/// Pre-Istanbul value; Istanbul later reduced this to 16.
pub const tx_data_nonzero: u64 = 68;

/// The gas a transaction must pay before any of its code runs: `tx_base`
/// plus a per-byte cost for its calldata/init code. A top-level
/// contract-creation transaction pays no extra surcharge here in Frontier;
/// that didn't exist until Homestead (EIP-2, block 1,150,000).
pub fn intrinsicCost(data: []const u8) u64 {
    var cost = tx_base;
    for (data) |byte| cost += if (byte == 0) tx_data_zero else tx_data_nonzero;
    return cost;
}

/// Bytes required to represent `value` with no leading zero byte (0 for value == 0).
pub fn byteLength(value: u256) u64 {
    const bits_used: u16 = 256 - @clz(value);
    return (bits_used + 7) / 8;
}

/// EIP-160 EXP gas: a base cost plus a per-byte cost for the exponent's significant bytes.
pub fn expCost(exponent: u256, is_spurious_dragon: bool) u64 {
    const per_byte = if (is_spurious_dragon) exp_byte_160 else exp_byte;
    return exp_base + per_byte * byteLength(exponent);
}

fn memoryWordCost(words: u64) u64 {
    return 3 * words + (words * words) / 512;
}

fn wordsFor(byte_len: u64) u64 {
    return (byte_len + 31) / 32;
}

/// Additional gas to charge for growing memory from `old_len` to cover
/// `[offset, offset + size)`. Returns 0 if `size == 0` or the range is
/// already covered. Callers must bound `offset`/`size` first (see
/// `Interpreter.max_memory_bytes`) so this can't overflow.
pub fn memoryExpansionCost(old_len: usize, offset: usize, size: usize) u64 {
    if (size == 0) return 0;
    const needed = offset + size;
    if (needed <= old_len) return 0;
    const old_words = wordsFor(@intCast(old_len));
    const new_words = wordsFor(@intCast(needed));
    return memoryWordCost(new_words) - memoryWordCost(old_words);
}

test "intrinsicCost of a plain call with no data is just the flat base" {
    try std.testing.expectEqual(@as(u64, 21000), intrinsicCost(&.{}));
}

test "intrinsicCost charges zero and nonzero data bytes differently" {
    try std.testing.expectEqual(@as(u64, 21000 + 4 + 68), intrinsicCost(&.{ 0, 1 }));
}

test "byteLength of zero is zero" {
    try std.testing.expectEqual(@as(u64, 0), byteLength(0));
}

test "byteLength of 1 is 1" {
    try std.testing.expectEqual(@as(u64, 1), byteLength(1));
}

test "byteLength of 256 is 2" {
    try std.testing.expectEqual(@as(u64, 2), byteLength(256));
}

test "memoryExpansionCost charges nothing for an already-covered range" {
    try std.testing.expectEqual(@as(u64, 0), memoryExpansionCost(64, 0, 32));
}

test "memoryExpansionCost charges for growth beyond current size" {
    try std.testing.expectEqual(@as(u64, 3), memoryExpansionCost(0, 0, 32));
}

test "memoryExpansionCost charges only the delta for further growth" {
    const first = memoryExpansionCost(0, 0, 32);
    const total = memoryExpansionCost(0, 0, 64);
    try std.testing.expectEqual(total - first, memoryExpansionCost(32, 32, 32));
}
