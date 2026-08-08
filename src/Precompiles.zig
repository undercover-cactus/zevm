//! Frontier's four precompiled contracts: `ECRECOVER` (0x01), `SHA256`
//! (0x02), `RIPEMD160` (0x03), and `IDENTITY` (0x04). Calling one of these
//! fixed addresses runs native logic at a fixed gas cost, instead of
//! interpreted bytecode. `call` is the single entry point both
//! `Interpreter.call` and `Evm.call` check before falling back to running
//! `state.getCode(target)` as ordinary bytecode.

const std = @import("std");
const Address = @import("Address.zig").Address;
const keccak256 = @import("Hash.zig").keccak256;
const Ripemd160 = @import("Ripemd160.zig");
const secp256k1 = @import("Secp256k1.zig");

const Kind = enum {
    ecrecover,
    sha256,
    ripemd160,
    identity,

    fn fromAddress(address: Address) ?Kind {
        return switch (address) {
            1 => .ecrecover,
            2 => .sha256,
            3 => .ripemd160,
            4 => .identity,
            else => null,
        };
    }

    /// Every precompile's cost is `base + word_cost * ceil(input_len / 32)`
    /// except `ECRECOVER`, which is a flat fee regardless of input size
    /// (its input is always exactly 128 bytes' worth of fixed fields).
    fn gasCost(kind: Kind, input_len: usize) u64 {
        const words = (input_len + 31) / 32;
        return switch (kind) {
            .ecrecover => 3000,
            .sha256 => 60 + 12 * words,
            .ripemd160 => 600 + 120 * words,
            .identity => 15 + 3 * words,
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

/// `null` if `address` isn't one of the four precompiles; the caller should
/// fall back to running `state.getCode(address)` as ordinary bytecode.
pub fn call(allocator: std.mem.Allocator, address: Address, input: []const u8, gas_limit: u64) !?Result {
    const kind = Kind.fromAddress(address) orelse return null;
    const cost = kind.gasCost(input.len);
    // Insufficient gas forfeits the whole forwarded amount, not just `cost`
    // (see `Evm.gasUsed`'s doc comment for the same rule one layer up).
    if (cost > gas_limit) return .{ .success = false, .gas_remaining = 0, .output = &.{} };

    const output: []const u8 = switch (kind) {
        .ecrecover => try ecrecoverOutput(allocator, input),
        .sha256 => try sha256Output(allocator, input),
        .ripemd160 => try ripemd160Output(allocator, input),
        .identity => try allocator.dupe(u8, input),
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

test "IDENTITY echoes its input back unchanged" {
    const result = (try call(std.testing.allocator, 4, "hello", 1000)).?;
    defer std.testing.allocator.free(result.output);
    try std.testing.expect(result.success);
    try std.testing.expectEqualStrings("hello", result.output);
    try std.testing.expectEqual(@as(u64, 1000 - (15 + 3)), result.gas_remaining);
}

test "SHA256 hashes its input" {
    const result = (try call(std.testing.allocator, 2, "abc", 1000)).?;
    defer std.testing.allocator.free(result.output);
    try std.testing.expect(result.success);
    var expected: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash("abc", &expected, .{});
    try std.testing.expectEqualSlices(u8, &expected, result.output);
    try std.testing.expectEqual(@as(u64, 1000 - (60 + 12)), result.gas_remaining);
}

test "RIPEMD160 hashes its input, left-padded to 32 bytes" {
    const result = (try call(std.testing.allocator, 3, "abc", 1000)).?;
    defer std.testing.allocator.free(result.output);
    try std.testing.expect(result.success);
    try std.testing.expectEqual(@as(usize, 32), result.output.len);
    try std.testing.expectEqualSlices(u8, &([_]u8{0} ** 12), result.output[0..12]);
    try std.testing.expectEqualSlices(u8, &Ripemd160.hash("abc"), result.output[12..32]);
}

test "a call to a non-precompile address returns null" {
    try std.testing.expectEqual(@as(?Result, null), try call(std.testing.allocator, 5, "abc", 1000));
    try std.testing.expectEqual(@as(?Result, null), try call(std.testing.allocator, 0, "abc", 1000));
}

test "insufficient gas fails and forfeits everything, not just the shortfall" {
    const result = (try call(std.testing.allocator, 4, "hello", 5)).?;
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

    const result = (try call(std.testing.allocator, 1, &input, 10000)).?;
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

    const result = (try call(std.testing.allocator, 1, &input, 10000)).?;
    defer std.testing.allocator.free(result.output);
    try std.testing.expect(result.success); // the CALL itself still succeeds
    try std.testing.expectEqual(@as(usize, 0), result.output.len);
}

test "ECRECOVER returns empty output for r == 0" {
    var input: [128]u8 = [_]u8{0} ** 128;
    input[63] = 27;
    input[127] = 1; // nonzero s, but r stays 0

    const result = (try call(std.testing.allocator, 1, &input, 10000)).?;
    defer std.testing.allocator.free(result.output);
    try std.testing.expect(result.success);
    try std.testing.expectEqual(@as(usize, 0), result.output.len);
}
