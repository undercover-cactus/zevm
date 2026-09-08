//! Frontier's four precompiled contracts: `ECRECOVER` (0x01), `SHA256`
//! (0x02), `RIPEMD160` (0x03), and `IDENTITY` (0x04), plus Byzantium's four
//! (EIP-198, EIP-196, EIP-197): `MODEXP` (0x05), `ECADD` (0x06), `ECMUL`
//! (0x07), `ECPAIRING` (0x08). Calling one of these fixed addresses runs
//! native logic at a computed gas cost, instead of interpreted bytecode.
//! `call` is the single entry point both `Interpreter.call` and `Evm.call`
//! check before falling back to running `state.getCode(target)` as
//! ordinary bytecode.

const std = @import("std");
const Address = @import("Address.zig").Address;
const keccak256 = @import("Hash.zig").keccak256;
const Ripemd160 = @import("Ripemd160.zig");
const secp256k1 = @import("Secp256k1.zig");
const bn128 = @import("Bn128.zig");
const Fork = @import("Fork.zig").Fork;

const Kind = enum {
    ecrecover,
    sha256,
    ripemd160,
    identity,
    modexp,
    ecadd,
    ecmul,
    ecpairing,

    /// Addresses 5-8 (Byzantium's MODEXP/ECADD/ECMUL/ECPAIRING) only
    /// resolve to a precompile from Byzantium on; before that, real
    /// mainnet has no code at those addresses, so the caller should fall
    /// through to ordinary (empty-code, trivially successful) execution.
    fn fromAddress(address: Address, fork: Fork) ?Kind {
        const byzantium = fork.atLeast(.byzantium);
        return switch (address) {
            1 => .ecrecover,
            2 => .sha256,
            3 => .ripemd160,
            4 => .identity,
            5 => if (byzantium) .modexp else null,
            6 => if (byzantium) .ecadd else null,
            7 => if (byzantium) .ecmul else null,
            8 => if (byzantium) .ecpairing else null,
            else => null,
        };
    }

    /// Every Frontier precompile's cost is `base + word_cost * ceil(input_len
    /// / 32)` except `ECRECOVER`, which is a flat fee regardless of input
    /// size (its input is always exactly 128 bytes' worth of fixed fields).
    /// `ECADD`/`ECMUL` are flat fees too; `ECPAIRING` is flat-per-pair;
    /// `MODEXP`'s formula is complex enough to live in its own function.
    fn gasCost(kind: Kind, input: []const u8) u64 {
        const words = (input.len + 31) / 32;
        return switch (kind) {
            .ecrecover => 3000,
            .sha256 => 60 + 12 * words,
            .ripemd160 => 600 + 120 * words,
            .identity => 15 + 3 * words,
            .modexp => modexpGasCost(input),
            .ecadd => 500,
            .ecmul => 40000,
            .ecpairing => 100000 + 80000 * (input.len / 192),
        };
    }
};

pub const Result = struct {
    success: bool,
    gas_remaining: u64,
    /// Allocator-owned (with the same allocator `call` was given). Empty
    /// (`&.{}`) on failure, needs no special-casing to free either way.
    output: []const u8,
};

/// `null` if `address` isn't one of the eight precompiles active at `fork`;
/// the caller should fall back to running `state.getCode(address)` as
/// ordinary bytecode.
pub fn call(allocator: std.mem.Allocator, address: Address, input: []const u8, gas_limit: u64, fork: Fork) !?Result {
    const kind = Kind.fromAddress(address, fork) orelse return null;
    const cost = kind.gasCost(input);
    // Insufficient gas forfeits the whole forwarded amount, not just `cost`
    // (see `Evm.gasUsed`'s doc comment for the same rule one layer up). Also
    // where MODEXP/ECADD/ECMUL/ECPAIRING's "invalid input" failures land:
    // real mainnet treats a bad field element, an off-curve point, or a
    // malformed ECPAIRING length as an exceptional halt that forfeits all
    // forwarded gas, not a soft per-precompile failure — the same shape as
    // insufficient gas, so it's handled the same way here.
    if (cost > gas_limit) return .{ .success = false, .gas_remaining = 0, .output = &.{} };

    const output: []const u8 = switch (kind) {
        .ecrecover => try ecrecoverOutput(allocator, input),
        .sha256 => try sha256Output(allocator, input),
        .ripemd160 => try ripemd160Output(allocator, input),
        .identity => try allocator.dupe(u8, input),
        .modexp => try modexpOutput(allocator, input),
        .ecadd => bn128AddOutput(allocator, input) catch |err| switch (err) {
            error.InvalidPoint => return .{ .success = false, .gas_remaining = 0, .output = &.{} },
            else => |e| return e,
        },
        .ecmul => bn128MulOutput(allocator, input) catch |err| switch (err) {
            error.InvalidPoint => return .{ .success = false, .gas_remaining = 0, .output = &.{} },
            else => |e| return e,
        },
        .ecpairing => bn128PairingOutput(allocator, input) catch |err| switch (err) {
            error.InvalidPoint => return .{ .success = false, .gas_remaining = 0, .output = &.{} },
            else => |e| return e,
        },
    };
    return .{ .success = true, .gas_remaining = gas_limit - cost, .output = output };
}

fn sha256Output(allocator: std.mem.Allocator, input: []const u8) ![]const u8 {
    var out: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(input, &out, .{});
    return allocator.dupe(u8, &out);
}

fn ripemd160Output(allocator: std.mem.Allocator, input: []const u8) ![]const u8 {
    const digest = Ripemd160.hash(input);
    // Left-padded to 32 bytes: the digest is only 20 bytes, but every
    // precompile output is word-aligned.
    var out: [32]u8 = [_]u8{0} ** 32;
    @memcpy(out[12..32], &digest);
    return allocator.dupe(u8, &out);
}

fn ecrecoverOutput(allocator: std.mem.Allocator, input: []const u8) ![]const u8 {
    // Fixed 128-byte input (hash, v, r, s, each a 32-byte word), zero-padded
    // on the right if the caller supplied less.
    var padded: [128]u8 = [_]u8{0} ** 128;
    @memcpy(padded[0..@min(input.len, 128)], input[0..@min(input.len, 128)]);

    const hash = padded[0..32].*;
    const r = padded[64..96].*;
    const s = padded[96..128].*;

    // `v` is a full 32-byte word but only ever valid as exactly 27 or 28.
    // Anything else in it fails outright, same as an invalid signature would.
    for (padded[32..63]) |b| {
        if (b != 0) return allocator.dupe(u8, &.{});
    }
    const v = padded[63];

    const recovered = ecrecover(hash, v, r, s) orelse return allocator.dupe(u8, &.{});
    var out: [32]u8 = [_]u8{0} ** 32;
    @memcpy(out[12..32], &recovered);
    return allocator.dupe(u8, &out);
}

/// A libsecp256k1 context, created once and reused: context creation isn't
/// free, and recreating it every `ECRECOVER` call would itself be a
/// hot-path cost. Not thread-safe, matching the rest of this codebase.
var cached_secp: ?secp256k1.Secp256k1 = null;

fn secp() secp256k1.Secp256k1 {
    if (cached_secp) |s| return s;
    const s = secp256k1.Secp256k1.init() catch @panic("secp256k1 context creation failed");
    cached_secp = s;
    return s;
}

/// ECDSA public-key recovery over secp256k1, via real libsecp256k1 (see
/// `build.zig`'s doc comment: pure-Zig `std.crypto` recovery measured at
/// ~24% of a real historical replay's total CPU cycles, the single biggest
/// cost found in this project). `null` for any invalid input, matching real
/// `ECRECOVER`'s silent-failure behavior; libsecp256k1 validates internally.
/// `pub`: also used directly by `examples/sync_era1.zig` to derive a raw
/// transaction's sender.
pub fn ecrecover(hash: [32]u8, v: u8, r: [32]u8, s: [32]u8) ?[20]u8 {
    if (v != 27 and v != 28) return null;

    var sig: secp256k1.Signature = undefined;
    sig[0..32].* = r;
    sig[32..64].* = s;
    sig[64] = v - 27;

    const pubkey = secp().recoverPubkey(hash, sig) catch return null;
    // Skip `pubkey[0]`, the uncompressed-key format byte (0x04). An
    // Ethereum address is the low 160 bits of Keccak256 over the raw
    // 64-byte (x, y) coordinates alone.
    const pubkey_hash = keccak256(pubkey[1..65]);
    const addr: Address = @truncate(pubkey_hash);
    var out: [20]u8 = undefined;
    std.mem.writeInt(u160, &out, addr, .big);
    return out;
}

// --- MODEXP (0x05, EIP-198) ---

/// Reads `len` bytes starting at `offset` into `buf` (which must be exactly
/// `len` bytes), zero-padding whatever runs past `data`'s end. Mirrors the
/// spec's `buffer_read`: call data is "infinitely right-padded with zero
/// bytes" for every precompile that reads fixed-offset fields.
fn bufferReadInto(buf: []u8, data: []const u8, offset: usize) void {
    @memset(buf, 0);
    if (offset < data.len) {
        const avail = @min(buf.len, data.len - offset);
        @memcpy(buf[0..avail], data[offset .. offset + avail]);
    }
}

fn readLength(data: []const u8, offset: usize) u256 {
    var buf: [32]u8 = undefined;
    bufferReadInto(&buf, data, offset);
    return std.mem.readInt(u256, &buf, .big);
}

/// Above this, `mult_complexity` alone already exceeds any real `u64` gas
/// limit (even at the minimum 1 iteration), so treating it as unaffordable
/// without computing exact magnitudes avoids doing u256 squaring on an
/// attacker-chosen length that could otherwise approach 2^256.
const modexp_length_cap: u256 = 1 << 40;

/// `mult_complexity` from EIP-198, verbatim (this is Byzantium's original
/// formula — EIP-2565's Berlin repricing changed both this and
/// `GQUADDIVISOR`, but that's a later fork this Evm doesn't implement yet).
fn mulComplexity(x: u512) u512 {
    if (x <= 64) return x * x;
    if (x <= 1024) return x * x / 4 + 96 * x - 3072;
    return x * x / 16 + 480 * x - 199680;
}

fn bitLength(x: u256) u32 {
    return if (x == 0) 0 else 256 - @clz(x);
}

/// `ADJUSTED_EXPONENT_LENGTH` from EIP-198, verbatim.
fn iterationsCount(exp_length: u256, exp_head: u256) u512 {
    const head_bits: u512 = bitLength(exp_head);
    const head_part: u512 = if (head_bits > 0) head_bits - 1 else 0;
    const adjusted: u512 = if (exp_length < 32)
        head_part
    else
        8 * (@as(u512, @intCast(exp_length)) - 32) + head_part;
    return @max(adjusted, 1);
}

/// The three 32-byte length fields plus whatever's needed to locate the
/// exponent's first 32 bytes (for the gas formula) — computed once and
/// shared between `modexpGasCost` and `modexpOutput` so they can't disagree
/// on layout.
const ModexpLayout = struct {
    base_length: u256,
    exp_length: u256,
    modulus_length: u256,
    exp_start: u256,
    exp_head: u256,
    /// True if any length is beyond `modexp_length_cap` — the caller should
    /// treat this as unaffordable without inspecting anything else.
    too_large: bool,

    fn parse(data: []const u8) ModexpLayout {
        const base_length = readLength(data, 0);
        const exp_length = readLength(data, 32);
        const modulus_length = readLength(data, 64);
        if (base_length > modexp_length_cap or exp_length > modexp_length_cap or modulus_length > modexp_length_cap) {
            return .{
                .base_length = base_length,
                .exp_length = exp_length,
                .modulus_length = modulus_length,
                .exp_start = 0,
                .exp_head = 0,
                .too_large = true,
            };
        }
        const exp_start = 96 + base_length;
        // `exponent_head` is `U256.from_be_bytes` of just the first
        // `min(32, exp_length)` bytes — a short byte string decodes as a
        // small-magnitude number, so those bytes belong at the *low*-order
        // end of this 32-byte buffer, not zero-padded on the right.
        var head_buf: [32]u8 = [_]u8{0} ** 32;
        const head_len: usize = @intCast(@min(@as(u256, 32), exp_length));
        bufferReadInto(head_buf[32 - head_len ..], data, @intCast(exp_start));
        const exp_head = std.mem.readInt(u256, &head_buf, .big);
        return .{
            .base_length = base_length,
            .exp_length = exp_length,
            .modulus_length = modulus_length,
            .exp_start = exp_start,
            .exp_head = exp_head,
            .too_large = false,
        };
    }
};

fn modexpGasCost(input: []const u8) u64 {
    const layout = ModexpLayout.parse(input);
    if (layout.too_large) return std.math.maxInt(u64);

    const max_length: u512 = @max(layout.base_length, layout.modulus_length);
    const complexity = mulComplexity(max_length);
    const iters = iterationsCount(layout.exp_length, layout.exp_head);
    const cost_wide: u512 = (complexity * iters) / 20;
    return if (cost_wide > std.math.maxInt(u64)) std.math.maxInt(u64) else @intCast(cost_wide);
}

/// Reads an unsigned big-endian byte string into a `Managed`.
fn bigFromBytes(allocator: std.mem.Allocator, bytes: []const u8) !std.math.big.int.Managed {
    var result = try std.math.big.int.Managed.init(allocator);
    errdefer result.deinit();
    const bit_count = bytes.len * 8;
    try result.ensureTwosCompCapacity(bit_count);
    var m = result.toMutable();
    m.readTwosComplement(bytes, bit_count, .big, .unsigned);
    result.setMetadata(m.positive, m.len);
    return result;
}

/// `pow(base, exp, modulus)`, arbitrary precision, encoded as exactly
/// `modulus_bytes.len` big-endian bytes — matches the spec's output framing
/// exactly. `modulus_bytes` must not represent zero (that's special-cased
/// by the caller before this is ever reached).
fn modPow(allocator: std.mem.Allocator, base_bytes: []const u8, exp_bytes: []const u8, modulus_bytes: []const u8) ![]u8 {
    const Managed = std.math.big.int.Managed;

    var modulus = try bigFromBytes(allocator, modulus_bytes);
    defer modulus.deinit();

    var base = try bigFromBytes(allocator, base_bytes);
    defer base.deinit();
    var q = try Managed.init(allocator);
    defer q.deinit();
    {
        var r = try Managed.init(allocator);
        defer r.deinit();
        try Managed.divTrunc(&q, &r, &base, &modulus);
        try base.copy(r.toConst());
    }

    // `result` starts at 1 mod modulus (not just 1) so an all-zero exponent
    // is already correct even when modulus == 1 (pow(x, 0, 1) == 0).
    var result = try Managed.initSet(allocator, 1);
    defer result.deinit();
    {
        var r = try Managed.init(allocator);
        defer r.deinit();
        try Managed.divTrunc(&q, &r, &result, &modulus);
        try result.copy(r.toConst());
    }

    var i = exp_bytes.len;
    while (i > 0) {
        i -= 1;
        const byte = exp_bytes[i];
        var bit: u3 = 0;
        while (true) : (bit += 1) {
            if ((byte >> bit) & 1 == 1) {
                var t = try Managed.init(allocator);
                defer t.deinit();
                try t.mul(&result, &base);
                var r = try Managed.init(allocator);
                defer r.deinit();
                try Managed.divTrunc(&q, &r, &t, &modulus);
                try result.copy(r.toConst());
            }
            var t2 = try Managed.init(allocator);
            defer t2.deinit();
            try t2.mul(&base, &base);
            var r2 = try Managed.init(allocator);
            defer r2.deinit();
            try Managed.divTrunc(&q, &r2, &t2, &modulus);
            try base.copy(r2.toConst());

            if (bit == 7) break;
        }
    }

    const out = try allocator.alloc(u8, modulus_bytes.len);
    errdefer allocator.free(out);
    result.toConst().writeTwosComplement(out, .big);
    return out;
}

fn modexpOutput(allocator: std.mem.Allocator, input: []const u8) ![]const u8 {
    const layout = ModexpLayout.parse(input);
    // Already established affordable by `modexpGasCost` before `call`
    // reaches here, so lengths fit comfortably in `usize`.
    const base_length: usize = @intCast(layout.base_length);
    const exp_length: usize = @intCast(layout.exp_length);
    const modulus_length: usize = @intCast(layout.modulus_length);

    if (base_length == 0 and modulus_length == 0) return allocator.alloc(u8, 0);

    const exp_start: usize = @intCast(layout.exp_start);

    const base = try allocator.alloc(u8, base_length);
    defer allocator.free(base);
    bufferReadInto(base, input, 96);

    const exp = try allocator.alloc(u8, exp_length);
    defer allocator.free(exp);
    bufferReadInto(exp, input, exp_start);

    const modulus = try allocator.alloc(u8, modulus_length);
    defer allocator.free(modulus);
    bufferReadInto(modulus, input, exp_start + exp_length);

    for (modulus) |b| {
        if (b != 0) return modPow(allocator, base, exp, modulus);
    }
    const zero_output = try allocator.alloc(u8, modulus_length);
    @memset(zero_output, 0);
    return zero_output;
}

// --- ECADD / ECMUL / ECPAIRING (0x06/0x07/0x08, EIP-196/EIP-197) ---

const InvalidPoint = error{InvalidPoint};

fn decodeG1Checked(input: []const u8, offset: usize) InvalidPoint!?bn128.G1Point {
    var buf: [64]u8 = undefined;
    bufferReadInto(&buf, input, offset);
    const x = std.mem.readInt(u256, buf[0..32], .big);
    const y = std.mem.readInt(u256, buf[32..64], .big);
    if (x >= bn128.field_modulus or y >= bn128.field_modulus) return error.InvalidPoint;
    if (x == 0 and y == 0) return null;
    const p: bn128.G1Point = .{ .x = bn128.Fq.init(x), .y = bn128.Fq.init(y) };
    if (!bn128.isOnCurve(bn128.Fq, p, bn128.b1)) return error.InvalidPoint;
    return p;
}

fn decodeG2Checked(input: []const u8, offset: usize) InvalidPoint!?bn128.G2Point {
    var buf: [128]u8 = undefined;
    bufferReadInto(&buf, input, offset);
    const x0 = std.mem.readInt(u256, buf[0..32], .big);
    const x1 = std.mem.readInt(u256, buf[32..64], .big);
    const y0 = std.mem.readInt(u256, buf[64..96], .big);
    const y1 = std.mem.readInt(u256, buf[96..128], .big);
    if (x0 >= bn128.field_modulus or x1 >= bn128.field_modulus or
        y0 >= bn128.field_modulus or y1 >= bn128.field_modulus) return error.InvalidPoint;
    if (x0 == 0 and x1 == 0 and y0 == 0 and y1 == 0) return null;
    const p: bn128.G2Point = .{
        .x = .{ .coeffs = .{ bn128.Fq.init(x1), bn128.Fq.init(x0) } },
        .y = .{ .coeffs = .{ bn128.Fq.init(y1), bn128.Fq.init(y0) } },
    };
    if (!bn128.isOnCurve(bn128.Fq2, p, bn128.b2)) return error.InvalidPoint;
    return p;
}

fn encodeG1(allocator: std.mem.Allocator, pt: ?bn128.G1Point) ![]u8 {
    const out = try allocator.alloc(u8, 64);
    @memset(out, 0);
    if (pt) |p| {
        std.mem.writeInt(u256, out[0..32], p.x.n, .big);
        std.mem.writeInt(u256, out[32..64], p.y.n, .big);
    }
    return out;
}

fn bn128AddOutput(allocator: std.mem.Allocator, input: []const u8) ![]const u8 {
    const p0 = try decodeG1Checked(input, 0);
    const p1 = try decodeG1Checked(input, 64);
    return encodeG1(allocator, bn128.add(bn128.Fq, p0, p1));
}

fn bn128MulOutput(allocator: std.mem.Allocator, input: []const u8) ![]const u8 {
    const p0 = try decodeG1Checked(input, 0);
    var buf: [32]u8 = undefined;
    bufferReadInto(&buf, input, 64);
    const n = std.mem.readInt(u256, &buf, .big);
    return encodeG1(allocator, bn128.multiply(bn128.Fq, p0, n));
}

fn bn128PairingOutput(allocator: std.mem.Allocator, input: []const u8) ![]const u8 {
    if (input.len % 192 != 0) return error.InvalidPoint;

    var result = bn128.Fq12.one;
    var i: usize = 0;
    while (i < input.len) : (i += 192) {
        const p = try decodeG1Checked(input, i);
        const q = try decodeG2Checked(input, i + 64);
        // Subgroup check: both points must be in the curve_order-torsion
        // subgroup. Trivially true for every valid G1 point (G1's own order
        // equals curve_order), but real G2 points off the twist's larger
        // curve can fail this, so it's checked uniformly for both, matching
        // the spec exactly.
        if (bn128.multiply(bn128.Fq, p, bn128.curve_order) != null) return error.InvalidPoint;
        if (bn128.multiply(bn128.Fq2, q, bn128.curve_order) != null) return error.InvalidPoint;
        result = result.mul(bn128.pairing(q, p));
    }

    const out = try allocator.alloc(u8, 32);
    @memset(out, 0);
    if (result.eq(bn128.Fq12.one)) out[31] = 1;
    return out;
}

test "IDENTITY echoes its input back unchanged" {
    const result = (try call(std.testing.allocator, 4, "hello", 1000, .frontier)).?;
    defer std.testing.allocator.free(result.output);
    try std.testing.expect(result.success);
    try std.testing.expectEqualStrings("hello", result.output);
    try std.testing.expectEqual(@as(u64, 1000 - (15 + 3)), result.gas_remaining);
}

test "SHA256 hashes its input" {
    const result = (try call(std.testing.allocator, 2, "abc", 1000, .frontier)).?;
    defer std.testing.allocator.free(result.output);
    try std.testing.expect(result.success);
    var expected: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash("abc", &expected, .{});
    try std.testing.expectEqualSlices(u8, &expected, result.output);
    try std.testing.expectEqual(@as(u64, 1000 - (60 + 12)), result.gas_remaining);
}

test "RIPEMD160 hashes its input, left-padded to 32 bytes" {
    const result = (try call(std.testing.allocator, 3, "abc", 1000, .frontier)).?;
    defer std.testing.allocator.free(result.output);
    try std.testing.expect(result.success);
    try std.testing.expectEqual(@as(usize, 32), result.output.len);
    try std.testing.expectEqualSlices(u8, &([_]u8{0} ** 12), result.output[0..12]);
    try std.testing.expectEqualSlices(u8, &Ripemd160.hash("abc"), result.output[12..32]);
}

test "a call to a non-precompile address returns null" {
    // Address 5 doubles as MODEXP's pre-Byzantium fallthrough check: not a
    // precompile yet at Frontier, so this must resolve to null too.
    try std.testing.expectEqual(@as(?Result, null), try call(std.testing.allocator, 5, "abc", 1000, .frontier));
    try std.testing.expectEqual(@as(?Result, null), try call(std.testing.allocator, 0, "abc", 1000, .frontier));
}

test "insufficient gas fails and forfeits everything, not just the shortfall" {
    const result = (try call(std.testing.allocator, 4, "hello", 5, .frontier)).?;
    defer std.testing.allocator.free(result.output);
    try std.testing.expect(!result.success);
    try std.testing.expectEqual(@as(u64, 0), result.gas_remaining);
    try std.testing.expectEqual(@as(usize, 0), result.output.len);
}

test "ECRECOVER recovers the correct address from a known-good signature" {
    // Cross-validated against the Rust `secp256k1` crate: signed the same
    // message hash with a fixed test key and confirmed the recovered
    // address matches, not just internal self-consistency.
    var input: [128]u8 = undefined;
    _ = try std.fmt.hexToBytes(input[0..32], "590217dae16ca989f0540b03185b5e81d27142f96e09edcbf93be9135a566c40");
    input[32..63].* = [_]u8{0} ** 31;
    input[63] = 27;
    _ = try std.fmt.hexToBytes(input[64..96], "94e9527fa8d8f6885340e713ca33663ef2d88397c788f458b129991723a00ec6");
    _ = try std.fmt.hexToBytes(input[96..128], "47e6e762afa28ec1caa7d33951b41fb8d0114ef7ef2cc690a8dc3337fa050f64");

    const result = (try call(std.testing.allocator, 1, &input, 10000, .frontier)).?;
    defer std.testing.allocator.free(result.output);
    try std.testing.expect(result.success);

    var expected: [32]u8 = [_]u8{0} ** 32;
    _ = try std.fmt.hexToBytes(expected[12..32], "01bd712bd7964c1eaf58b02393d4cf684c4d4a35");
    try std.testing.expectEqualSlices(u8, &expected, result.output);
}

test "ECRECOVER returns empty output (not a zero address) for an invalid v" {
    var input: [128]u8 = [_]u8{0} ** 128;
    input[63] = 29; // only 27/28 are valid
    input[95] = 1; // nonzero r
    input[127] = 1; // nonzero s

    const result = (try call(std.testing.allocator, 1, &input, 10000, .frontier)).?;
    defer std.testing.allocator.free(result.output);
    try std.testing.expect(result.success); // the CALL itself still succeeds
    try std.testing.expectEqual(@as(usize, 0), result.output.len);
}

test "ECRECOVER returns empty output for r == 0" {
    var input: [128]u8 = [_]u8{0} ** 128;
    input[63] = 27;
    input[127] = 1; // nonzero s, but r stays 0

    const result = (try call(std.testing.allocator, 1, &input, 10000, .frontier)).?;
    defer std.testing.allocator.free(result.output);
    try std.testing.expect(result.success);
    try std.testing.expectEqual(@as(usize, 0), result.output.len);
}

// --- Byzantium precompile conformance vectors, from go-ethereum's own
// test suite (`core/vm/testdata/precompiles/`) — real known-answer tests
// for EIP-198/EIP-196/EIP-197, not just internal self-consistency. ---

const ConformanceVector = struct { input: []const u8, expected: []const u8, name: []const u8, gas: u64 };

fn parseConformanceVectors(allocator: std.mem.Allocator, data: []const u8) ![]ConformanceVector {
    const parsed = try std.json.parseFromSlice(std.json.Value, allocator, data, .{});
    var list = std.ArrayList(ConformanceVector).empty;
    for (parsed.value.array.items) |item| {
        const input_hex = item.object.get("Input").?.string;
        const expected_hex = item.object.get("Expected").?.string;
        const input = try allocator.alloc(u8, input_hex.len / 2);
        _ = try std.fmt.hexToBytes(input, input_hex);
        const expected = try allocator.alloc(u8, expected_hex.len / 2);
        _ = try std.fmt.hexToBytes(expected, expected_hex);
        try list.append(allocator, .{
            .input = input,
            .expected = expected,
            .name = item.object.get("Name").?.string,
            .gas = @intCast(item.object.get("Gas").?.integer),
        });
    }
    return list.toOwnedSlice(allocator);
}

/// `check_gas`: MODEXP's conformance vectors carry Byzantium-accurate gas
/// figures (cross-checked against EIP-198's own worked example), so those
/// are asserted exactly. The BN128 (ECADD/ECMUL/ECPAIRING) vectors' `Gas`
/// field is go-ethereum's *current* (Istanbul/EIP-1108-repriced) cost, not
/// Byzantium's original 500/40000/100000+80000k — this Evm only implements
/// Byzantium, so those vectors are run with ample gas and checked for
/// output correctness only; Byzantium's costs are exercised directly by
/// the flat-fee tests below instead.
fn runConformanceVectors(address: Address, data: []const u8, check_gas: bool) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const vectors = try parseConformanceVectors(allocator, data);
    for (vectors) |v| {
        const gas_limit: u64 = if (check_gas) v.gas else 10_000_000;
        const result = (try call(allocator, address, v.input, gas_limit, .byzantium)).?;
        std.testing.expect(result.success) catch |err| {
            std.debug.print("{s}: expected success\n", .{v.name});
            return err;
        };
        std.testing.expectEqualSlices(u8, v.expected, result.output) catch |err| {
            std.debug.print("{s}: output mismatch\n", .{v.name});
            return err;
        };
        if (check_gas) {
            std.testing.expectEqual(@as(u64, 0), result.gas_remaining) catch |err| {
                std.debug.print("{s}: expected exactly {d} gas to be charged\n", .{ v.name, v.gas });
                return err;
            };
        }
    }
}

test "MODEXP matches go-ethereum's EIP-198 conformance vectors, gas cost included" {
    try runConformanceVectors(5, @embedFile("testdata/modexp.json"), true);
}

test "ECADD matches go-ethereum's EIP-196 conformance vectors" {
    try runConformanceVectors(6, @embedFile("testdata/bn256Add.json"), false);
}

test "ECMUL matches go-ethereum's EIP-196 conformance vectors" {
    try runConformanceVectors(7, @embedFile("testdata/bn256ScalarMul.json"), false);
}

test "ECPAIRING matches go-ethereum's EIP-197 conformance vectors" {
    try runConformanceVectors(8, @embedFile("testdata/bn256Pairing.json"), false);
}

test "MODEXP special case: base_length == 0 and modulus_length == 0 returns empty output" {
    var full_input: [97]u8 = [_]u8{0} ** 97;
    // exponent_length = 1, exponent = 0xff, doesn't matter: base/modulus length both 0.
    full_input[63] = 1;
    full_input[96] = 0xff;

    const result = (try call(std.testing.allocator, 5, &full_input, 1_000_000, .byzantium)).?;
    defer std.testing.allocator.free(result.output);
    try std.testing.expect(result.success);
    try std.testing.expectEqual(@as(usize, 0), result.output.len);
}

test "MODEXP special case: modulus == 0 returns modulus_length zero bytes" {
    var full_input: [98]u8 = [_]u8{0} ** 98;
    full_input[31] = 1; // base_length = 1
    full_input[63] = 1; // exponent_length = 1
    full_input[95] = 4; // modulus_length = 4
    full_input[96] = 5; // base = 5
    full_input[97] = 3; // exponent = 3
    // modulus (4 bytes) is left as the trailing zero-padding beyond `full_input`.

    const result = (try call(std.testing.allocator, 5, &full_input, 1_000_000, .byzantium)).?;
    defer std.testing.allocator.free(result.output);
    try std.testing.expect(result.success);
    try std.testing.expectEqualSlices(u8, &([_]u8{0} ** 4), result.output);
}

test "MODEXP, ECADD, ECMUL, ECPAIRING are not available before Byzantium" {
    var input: [1]u8 = .{0};
    for ([_]Address{ 5, 6, 7, 8 }) |addr| {
        try std.testing.expectEqual(@as(?Result, null), try call(std.testing.allocator, addr, &input, 1_000_000, .spurious_dragon));
    }
}

test "ECADD fails as an exceptional halt, forfeiting all gas, on a point not on the curve" {
    var input: [128]u8 = [_]u8{0} ** 128;
    input[31] = 1; // x0 = 1
    input[63] = 1; // y0 = 1 -- (1,1) is not on y^2 = x^3 + 3
    input[95] = 1; // x1 = 1
    input[127] = 2; // y1 = 2 -- (1,2) is the valid generator

    const result = (try call(std.testing.allocator, 6, &input, 1_000_000, .byzantium)).?;
    defer std.testing.allocator.free(result.output);
    try std.testing.expect(!result.success);
    try std.testing.expectEqual(@as(u64, 0), result.gas_remaining);
    try std.testing.expectEqual(@as(usize, 0), result.output.len);
}

test "ECPAIRING fails as an exceptional halt on a length that isn't a multiple of 192" {
    var input: [100]u8 = [_]u8{0} ** 100;
    const result = (try call(std.testing.allocator, 8, &input, 1_000_000, .byzantium)).?;
    defer std.testing.allocator.free(result.output);
    try std.testing.expect(!result.success);
    try std.testing.expectEqual(@as(u64, 0), result.gas_remaining);
}

test "ECADD, ECMUL, ECPAIRING charge Byzantium's original flat gas costs, not a later fork's" {
    // (0,0) + (0,0): the point-at-infinity encoding, cheapest possible ECADD input.
    var add_input: [128]u8 = [_]u8{0} ** 128;
    const add_result = (try call(std.testing.allocator, 6, &add_input, 500, .byzantium)).?;
    defer std.testing.allocator.free(add_result.output);
    try std.testing.expect(add_result.success);
    try std.testing.expectEqual(@as(u64, 0), add_result.gas_remaining);
    const add_underfunded = (try call(std.testing.allocator, 6, &add_input, 499, .byzantium)).?;
    defer std.testing.allocator.free(add_underfunded.output);
    try std.testing.expect(!add_underfunded.success);

    var mul_input: [96]u8 = [_]u8{0} ** 96;
    const mul_result = (try call(std.testing.allocator, 7, &mul_input, 40000, .byzantium)).?;
    defer std.testing.allocator.free(mul_result.output);
    try std.testing.expect(mul_result.success);
    try std.testing.expectEqual(@as(u64, 0), mul_result.gas_remaining);
    const mul_underfunded = (try call(std.testing.allocator, 7, &mul_input, 39999, .byzantium)).?;
    defer std.testing.allocator.free(mul_underfunded.output);
    try std.testing.expect(!mul_underfunded.success);

    // Empty input: 0 pairs, so gas is just the flat 100000 base.
    const pairing_result = (try call(std.testing.allocator, 8, &.{}, 100000, .byzantium)).?;
    defer std.testing.allocator.free(pairing_result.output);
    try std.testing.expect(pairing_result.success);
    try std.testing.expectEqual(@as(u64, 0), pairing_result.gas_remaining);
    const pairing_underfunded = (try call(std.testing.allocator, 8, &.{}, 99999, .byzantium)).?;
    defer std.testing.allocator.free(pairing_underfunded.output);
    try std.testing.expect(!pairing_underfunded.success);
}
