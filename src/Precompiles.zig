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
const Kzg = @import("Kzg.zig");

const Kind = enum {
    ecrecover,
    sha256,
    ripemd160,
    identity,
    modexp,
    ecadd,
    ecmul,
    ecpairing,
    blake2f,
    point_evaluation,

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
            9 => if (fork.atLeast(.istanbul)) .blake2f else null,
            0x0a => if (fork.atLeast(.cancun)) .point_evaluation else null,
            else => null,
        };
    }

    /// Every Frontier precompile's cost is `base + word_cost * ceil(input_len
    /// / 32)` except `ECRECOVER`, which is a flat fee regardless of input
    /// size (its input is always exactly 128 bytes' worth of fixed fields).
    /// `ECADD`/`ECMUL` are flat fees too; `ECPAIRING` is flat-per-pair;
    /// `MODEXP`'s formula is complex enough to live in its own function.
    fn gasCost(kind: Kind, input: []const u8, fork: Fork) u64 {
        // EIP-1108 (Istanbul) cut the alt_bn128 costs hard, on the basis
        // that faster implementations had made the Byzantium prices a large
        // overcharge. The arithmetic is unchanged; only the fee moved.
        const istanbul = fork.atLeast(.istanbul);
        const words = (input.len + 31) / 32;
        return switch (kind) {
            .ecrecover => 3000,
            .sha256 => 60 + 12 * words,
            .ripemd160 => 600 + 120 * words,
            .identity => 15 + 3 * words,
            .modexp => modexpGasCost(input, fork),
            .ecadd => if (istanbul) 150 else 500,
            .ecmul => if (istanbul) 6000 else 40000,
            .ecpairing => if (istanbul)
                45000 + 34000 * (input.len / 192)
            else
                100000 + 80000 * (input.len / 192),
            // EIP-152: one gas per round, and the round count is attacker
            // chosen, so the price has to scale with it. A malformed input
            // is charged nothing because it never gets this far.
            .blake2f => if (input.len == 213) std.mem.readInt(u32, input[0..4], .big) else 0,
            // EIP-4844: flat, whatever the input.
            .point_evaluation => 50000,
        };
    }
};

/// BLAKE2b's compression function `F` (RFC 7693 section 3.2), which is what
/// EIP-152's precompile exposes: not a hash, one call to the round function
/// over a caller-supplied state, message block, offset counters and final
/// flag. The round count is a parameter rather than BLAKE2b's fixed 12, which
/// is the whole point (it lets a contract verify another chain's BLAKE2b
/// work at a chosen cost) and also why the gas is charged per round.
const blake2b_iv = [8]u64{
    0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179,
};

const blake2b_sigma = [10][16]u8{
    .{ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 },
    .{ 14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3 },
    .{ 11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4 },
    .{ 7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8 },
    .{ 9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13 },
    .{ 2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9 },
    .{ 12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11 },
    .{ 13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10 },
    .{ 6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5 },
    .{ 10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0 },
};

fn blake2bMix(v: *[16]u64, a: usize, b: usize, c: usize, d: usize, x: u64, y: u64) void {
    v[a] = v[a] +% v[b] +% x;
    v[d] = std.math.rotr(u64, v[d] ^ v[a], 32);
    v[c] = v[c] +% v[d];
    v[b] = std.math.rotr(u64, v[b] ^ v[c], 24);
    v[a] = v[a] +% v[b] +% y;
    v[d] = std.math.rotr(u64, v[d] ^ v[a], 16);
    v[c] = v[c] +% v[d];
    v[b] = std.math.rotr(u64, v[b] ^ v[c], 63);
}

/// Applies `rounds` rounds of `F` to `h` in place.
fn blake2bCompress(rounds: u32, h: *[8]u64, m: [16]u64, t: [2]u64, final: bool) void {
    var v: [16]u64 = undefined;
    @memcpy(v[0..8], h);
    @memcpy(v[8..16], &blake2b_iv);
    v[12] ^= t[0];
    v[13] ^= t[1];
    if (final) v[14] = ~v[14];

    var round: u32 = 0;
    while (round < rounds) : (round += 1) {
        // The schedule repeats every ten rounds, which is what lets the
        // round count exceed BLAKE2b's own twelve.
        const sigma = blake2b_sigma[round % 10];
        blake2bMix(&v, 0, 4, 8, 12, m[sigma[0]], m[sigma[1]]);
        blake2bMix(&v, 1, 5, 9, 13, m[sigma[2]], m[sigma[3]]);
        blake2bMix(&v, 2, 6, 10, 14, m[sigma[4]], m[sigma[5]]);
        blake2bMix(&v, 3, 7, 11, 15, m[sigma[6]], m[sigma[7]]);
        blake2bMix(&v, 0, 5, 10, 15, m[sigma[8]], m[sigma[9]]);
        blake2bMix(&v, 1, 6, 11, 12, m[sigma[10]], m[sigma[11]]);
        blake2bMix(&v, 2, 7, 8, 13, m[sigma[12]], m[sigma[13]]);
        blake2bMix(&v, 3, 4, 9, 14, m[sigma[14]], m[sigma[15]]);
    }

    for (h, 0..) |*word, i| word.* ^= v[i] ^ v[i + 8];
}

/// EIP-152's layout: 4 bytes of rounds big-endian, then 64 bytes of state,
/// 128 of message, 16 of offset counters, and one final-block flag, all
/// little-endian. Anything else about the input is invalid, and invalid
/// means an exceptional halt that forfeits the forwarded gas rather than a
/// soft failure, same as the curve precompiles.
fn blake2fOutput(allocator: std.mem.Allocator, input: []const u8) ![]const u8 {
    if (input.len != 213) return error.InvalidInput;
    const flag = input[212];
    if (flag > 1) return error.InvalidInput;

    const rounds = std.mem.readInt(u32, input[0..4], .big);
    var h: [8]u64 = undefined;
    for (&h, 0..) |*word, i| word.* = std.mem.readInt(u64, input[4 + i * 8 ..][0..8], .little);
    var m: [16]u64 = undefined;
    for (&m, 0..) |*word, i| word.* = std.mem.readInt(u64, input[68 + i * 8 ..][0..8], .little);
    const t = [2]u64{
        std.mem.readInt(u64, input[196..][0..8], .little),
        std.mem.readInt(u64, input[204..][0..8], .little),
    };

    blake2bCompress(rounds, &h, m, t, flag == 1);

    const out = try allocator.alloc(u8, 64);
    for (h, 0..) |word, i| std.mem.writeInt(u64, out[i * 8 ..][0..8], word, .little);
    return out;
}

test "BLAKE2F's compression function reproduces BLAKE2b-512 of \"abc\"" {
    // Checked against std's BLAKE2b rather than a copied vector, so this
    // tests the implementation rather than my transcription. Hashing a
    // single short message is exactly one call to `F`: the state starts at
    // the IV with the parameter block mixed in, the message block is the
    // input zero-padded to 128 bytes, the counter is the byte length, and
    // the final-block flag is set.
    const message = "abc";
    var input: [213]u8 = [_]u8{0} ** 213;
    std.mem.writeInt(u32, input[0..4], 12, .big); // BLAKE2b's own round count

    // Parameter block for an unkeyed 64-byte digest: fanout 1, depth 1.
    var h = blake2b_iv;
    h[0] ^= 0x01010040;
    for (h, 0..) |word, i| std.mem.writeInt(u64, input[4 + i * 8 ..][0..8], word, .little);
    @memcpy(input[68..][0..message.len], message);
    std.mem.writeInt(u64, input[196..][0..8], message.len, .little);
    input[212] = 1; // final block

    const out = try blake2fOutput(std.testing.allocator, &input);
    defer std.testing.allocator.free(out);

    var expected: [64]u8 = undefined;
    std.crypto.hash.blake2.Blake2b512.hash(message, &expected, .{});
    try std.testing.expectEqualSlices(u8, &expected, out);
}

test "BLAKE2F with zero rounds still folds the state and the IV together" {
    // Zero rounds is legal and is not a no-op: `F` always finishes by
    // XORing the two halves of the working vector back into the state.
    var input: [213]u8 = [_]u8{0} ** 213;
    std.mem.writeInt(u32, input[0..4], 0, .big);
    for (blake2b_iv, 0..) |word, i| std.mem.writeInt(u64, input[4 + i * 8 ..][0..8], word, .little);

    const out = try blake2fOutput(std.testing.allocator, &input);
    defer std.testing.allocator.free(out);

    // v[0..8] is h and v[8..16] is the IV, both the IV here, so every word
    // XORs with itself twice and the state is unchanged.
    for (blake2b_iv, 0..) |word, i| {
        try std.testing.expectEqual(word, std.mem.readInt(u64, out[i * 8 ..][0..8], .little));
    }
}

test "BLAKE2F rejects a malformed input rather than failing softly" {
    // EIP-152 requires exactly 213 bytes and a final flag of 0 or 1.
    var short: [212]u8 = [_]u8{0} ** 212;
    try std.testing.expectError(error.InvalidInput, blake2fOutput(std.testing.allocator, &short));
    var long: [214]u8 = [_]u8{0} ** 214;
    try std.testing.expectError(error.InvalidInput, blake2fOutput(std.testing.allocator, &long));

    var bad_flag: [213]u8 = [_]u8{0} ** 213;
    bad_flag[212] = 2;
    try std.testing.expectError(error.InvalidInput, blake2fOutput(std.testing.allocator, &bad_flag));

    // And through `call`, a malformed input forfeits the whole forwarded
    // amount rather than returning a failed-but-cheap result.
    const result = (try call(std.testing.allocator, 9, &bad_flag, 100_000, .istanbul)).?;
    try std.testing.expect(!result.success);
    try std.testing.expectEqual(@as(u64, 0), result.gas_remaining);
}

test "BLAKE2F is not a precompile before Istanbul, and costs one gas per round" {
    var input: [213]u8 = [_]u8{0} ** 213;
    std.mem.writeInt(u32, input[0..4], 7, .big);

    // Address 9 is nothing at all until Istanbul, so the caller falls back
    // to running whatever code is there (none).
    try std.testing.expectEqual(@as(?Result, null), try call(std.testing.allocator, 9, &input, 1000, .petersburg));

    const result = (try call(std.testing.allocator, 9, &input, 1000, .istanbul)).?;
    defer std.testing.allocator.free(result.output);
    try std.testing.expect(result.success);
    try std.testing.expectEqual(@as(u64, 1000 - 7), result.gas_remaining);
}

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
    const cost = kind.gasCost(input, fork);
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
        .blake2f => blake2fOutput(allocator, input) catch |err| switch (err) {
            error.InvalidInput => return .{ .success = false, .gas_remaining = 0, .output = &.{} },
            else => |e| return e,
        },
        .point_evaluation => pointEvaluationOutput(allocator, input) catch |err| switch (err) {
            error.InvalidInput => return .{ .success = false, .gas_remaining = 0, .output = &.{} },
            else => |e| return e,
        },
    };
    return .{ .success = true, .gas_remaining = gas_limit - cost, .output = output };
}

/// The BLS12-381 scalar field's modulus, which the point evaluation
/// precompile returns alongside the blob size.
const bls_modulus: u256 = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001;
/// Field elements in a blob (EIP-4844).
const field_elements_per_blob: u256 = 4096;

/// EIP-4844's point evaluation precompile (0x0a, Cancun). Its 192 bytes are
/// `versioned_hash | z | y | commitment | proof`: it checks that the
/// commitment is the one the versioned hash names (`0x01` followed by the
/// last 31 bytes of its SHA-256), then that `proof` shows the committed
/// polynomial takes the value `y` at `z`. Any failure, malformed input
/// included, is `error.InvalidInput`, which forfeits all gas.
fn pointEvaluationOutput(allocator: std.mem.Allocator, input: []const u8) ![]const u8 {
    if (input.len != 192) return error.InvalidInput;
    const commitment = input[96..144];
    var hash: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(commitment, &hash, .{});
    hash[0] = 0x01;
    if (!std.mem.eql(u8, &hash, input[0..32])) return error.InvalidInput;
    if (!Kzg.verifyProof(commitment[0..48], input[32..64], input[64..96], input[144..192])) return error.InvalidInput;

    const out = try allocator.alloc(u8, 64);
    std.mem.writeInt(u256, out[0..32], field_elements_per_blob, .big);
    std.mem.writeInt(u256, out[32..64], bls_modulus, .big);
    return out;
}

/// A point evaluation input for c-kzg's test vector
/// `verify_kzg_proof_case_*_proof_3_3`, with the versioned hash computed from
/// the commitment unless `hash` overrides it.
fn pointEvaluationInput(proof_hex: []const u8, hash: ?[32]u8) ![192]u8 {
    var input: [192]u8 = undefined;
    _ = try std.fmt.hexToBytes(input[32..64], "5eb7004fe57383e6c88b99d839937fddf3f99279353aaf8d5c9a75f91ce33c62");
    _ = try std.fmt.hexToBytes(input[64..96], "2c9ae4f1d6d08558d7027df9cc6b248c21290075d2c0df8a4084d02090b3fa14");
    _ = try std.fmt.hexToBytes(input[96..144], "b49d88afcd7f6c61a8ea69eff5f609d2432b47e7e4cd50b02cdddb4e0c1460517e8df02e4e64dc55e3d8ca192d57193a");
    _ = try std.fmt.hexToBytes(input[144..192], proof_hex);
    if (hash) |h| {
        input[0..32].* = h;
    } else {
        std.crypto.hash.sha2.Sha256.hash(input[96..144], input[0..32], .{});
        input[0] = 0x01;
    }
    return input;
}

test "point evaluation: a correct proof returns the blob size and the BLS modulus for 50000 gas" {
    const input = try pointEvaluationInput("b059c60125debbbf29d041bac20fd853951b64b5f31bfe2fa825e18ff49a259953e734b3d57119ae66f7bd79de3027f6", null);
    const result = (try call(std.testing.allocator, 0x0a, &input, 60000, .cancun)).?;
    defer std.testing.allocator.free(result.output);
    try std.testing.expect(result.success);
    try std.testing.expectEqual(@as(u64, 10000), result.gas_remaining);
    try std.testing.expectEqual(field_elements_per_blob, std.mem.readInt(u256, result.output[0..32], .big));
    try std.testing.expectEqual(bls_modulus, std.mem.readInt(u256, result.output[32..64], .big));
}

test "point evaluation: an incorrect proof, a wrong versioned hash or a wrong length fails and forfeits all gas" {
    const wrong_proof = try pointEvaluationInput("a4cc8c419ade0cf043cbf30f43c8f7ee6da3ab8d2c15070f323e5a13a8178fe07c8f89686e5fd16565247b520028251b", null);
    var bad_hash = try pointEvaluationInput("b059c60125debbbf29d041bac20fd853951b64b5f31bfe2fa825e18ff49a259953e734b3d57119ae66f7bd79de3027f6", null);
    bad_hash[0] = 0x02; // a version other than KZG's 0x01
    for ([_][]const u8{ &wrong_proof, &bad_hash, bad_hash[0..191] }) |input| {
        const result = (try call(std.testing.allocator, 0x0a, input, 60000, .cancun)).?;
        try std.testing.expect(!result.success);
        try std.testing.expectEqual(@as(u64, 0), result.gas_remaining);
    }
}

test "point evaluation is not a precompile before Cancun" {
    try std.testing.expect(try call(std.testing.allocator, 0x0a, &.{}, 60000, .shanghai) == null);
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
/// hot-path cost. Created lazily, which is not thread-safe: anything running
/// precompiles on several threads at once calls `initSecp` first, after which
/// the context is only ever read, which libsecp256k1 allows concurrently.
var cached_secp: ?secp256k1.Secp256k1 = null;

/// Creates the shared secp256k1 context now rather than on first use.
pub fn initSecp() void {
    _ = secp();
}

/// Loads the KZG trusted setup now rather than on first use, for the same
/// reason as `initSecp`: loading is not thread-safe, verifying is.
pub fn initKzg() void {
    Kzg.init();
}

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

/// `mult_complexity` from EIP-198, verbatim: Byzantium's original formula,
/// replaced at Berlin by `mulComplexity2565`.
fn mulComplexity(x: u512) u512 {
    if (x <= 64) return x * x;
    if (x <= 1024) return x * x / 4 + 96 * x - 3072;
    return x * x / 16 + 480 * x - 199680;
}

/// EIP-2565 (Berlin): the square of the operand length in 64-bit words.
/// EIP-198's piecewise curve modelled schoolbook multiplication on bytes and
/// overpriced every realistic input.
fn mulComplexity2565(x: u512) u512 {
    const words = (x + 7) / 8;
    return words * words;
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

fn modexpGasCost(input: []const u8, fork: Fork) u64 {
    const layout = ModexpLayout.parse(input);
    if (layout.too_large) return std.math.maxInt(u64);

    const max_length: u512 = @max(layout.base_length, layout.modulus_length);
    const iters = iterationsCount(layout.exp_length, layout.exp_head);
    // EIP-2565 (Berlin) swaps the complexity curve, divides by 3 instead of
    // 20, and puts a 200 floor under the result. The iteration count is
    // unchanged.
    const cost_wide: u512 = if (fork.atLeast(.berlin))
        @max(200, (mulComplexity2565(max_length) * iters) / 3)
    else
        (mulComplexity(max_length) * iters) / 20;
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
        std.mem.writeInt(u256, out[0..32], p.x.toInt(), .big);
        std.mem.writeInt(u256, out[32..64], p.y.toInt(), .big);
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

    // The Miller loops are accumulated and exponentiated once at the end
    // rather than per pair: `e(a,b) * e(c,d) == (ML(a,b) * ML(c,d))^exponent`,
    // and the final exponentiation is the expensive half of a pairing. A
    // Groth16 proof is four pairs, so this is four of them down to one.
    var accumulated = bn128.Fq12.one;
    var i: usize = 0;
    while (i < input.len) : (i += 192) {
        const p = try decodeG1Checked(input, i);
        const q = try decodeG2Checked(input, i + 64);
        // Subgroup check: both points must be in the curve_order-torsion
        // subgroup. Only G2's can fail. G1 is the whole curve
        // `y^2 = x^3 + 3` over Fq, which has exactly `curve_order` points,
        // so any point `decodeG1Checked` accepted is already in it and
        // multiplying by `curve_order` always lands on infinity. That check
        // was 254 doublings per pair that could only ever say yes. The
        // twist G2 lives on has more points than that, so its check is real.
        if (bn128.multiply(bn128.Fq2, q, bn128.curve_order) != null) return error.InvalidPoint;
        accumulated = accumulated.mul(bn128.millerLoop(q, p));
    }
    const result = bn128.finalExponentiate(accumulated);

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

test "ECPAIRING checks a product of pairings, not each pairing separately" {
    // Exercises the accumulate-then-exponentiate-once path with real input.
    // Built from the generators rather than transcribed hex, so the G2
    // coefficient order here cannot silently disagree with the decoder's.
    const bn = bn128;
    var pair: [192]u8 = undefined;
    const writeG1 = struct {
        fn f(buf: []u8, pt: bn.G1Point) void {
            std.mem.writeInt(u256, buf[0..32], pt.x.toInt(), .big);
            std.mem.writeInt(u256, buf[32..64], pt.y.toInt(), .big);
        }
    }.f;
    const writeG2 = struct {
        fn f(buf: []u8, pt: bn.G2Point) void {
            std.mem.writeInt(u256, buf[0..32], pt.x.coeffs[1].toInt(), .big);
            std.mem.writeInt(u256, buf[32..64], pt.x.coeffs[0].toInt(), .big);
            std.mem.writeInt(u256, buf[64..96], pt.y.coeffs[1].toInt(), .big);
            std.mem.writeInt(u256, buf[96..128], pt.y.coeffs[0].toInt(), .big);
        }
    }.f;

    // A single pair: e(G1, G2) is not 1, so the result word is 0.
    writeG1(pair[0..64], bn.g1);
    writeG2(pair[64..192], bn.g2);
    const one_pair = (try call(std.testing.allocator, 8, &pair, 1_000_000, .istanbul)).?;
    defer std.testing.allocator.free(one_pair.output);
    try std.testing.expect(one_pair.success);
    try std.testing.expectEqual(@as(u8, 0), one_pair.output[31]);

    // Two pairs whose product is 1: e(G1, G2) * e(-G1, G2) == 1.
    var two: [384]u8 = undefined;
    @memcpy(two[0..192], &pair);
    writeG1(two[192..256], .{ .x = bn.g1.x, .y = bn.g1.y.neg() });
    writeG2(two[256..384], bn.g2);
    const two_pairs = (try call(std.testing.allocator, 8, &two, 1_000_000, .istanbul)).?;
    defer std.testing.allocator.free(two_pairs.output);
    try std.testing.expect(two_pairs.success);
    try std.testing.expectEqual(@as(u8, 1), two_pairs.output[31]);

    // Empty input is an empty product, which is 1.
    const empty = (try call(std.testing.allocator, 8, &.{}, 1_000_000, .istanbul)).?;
    defer std.testing.allocator.free(empty.output);
    try std.testing.expect(empty.success);
    try std.testing.expectEqual(@as(u8, 1), empty.output[31]);
}

test "EIP-2565 puts a 200 floor under MODEXP and reprices it at Berlin" {
    // base, exponent and modulus each one byte long: 3^1 mod 5.
    var input = [_]u8{0} ** (96 + 3);
    input[31] = 1;
    input[63] = 1;
    input[95] = 1;
    input[96] = 3;
    input[97] = 1;
    input[98] = 5;
    // EIP-198 prices this at 1 * 1 / 20 = 0; EIP-2565 at max(200, 1 * 1 / 3).
    try std.testing.expectEqual(@as(u64, 0), modexpGasCost(&input, .istanbul));
    try std.testing.expectEqual(@as(u64, 200), modexpGasCost(&input, .berlin));

    // 64-byte base and modulus, 32-byte exponent with its top bit set, so
    // 255 iterations. EIP-2565: ceil(64 / 8)^2 * 255 / 3 = 64 * 255 / 3.
    var big = [_]u8{0} ** (96 + 64 + 32 + 64);
    big[31] = 64;
    big[63] = 32;
    big[95] = 64;
    big[96 + 64] = 0x80;
    try std.testing.expectEqual(@as(u64, 64 * 255 / 3), modexpGasCost(&big, .berlin));
    // EIP-198 for the same input: mult_complexity(64) = 64^2, / 20.
    try std.testing.expectEqual(@as(u64, 64 * 64 * 255 / 20), modexpGasCost(&big, .istanbul));
}
