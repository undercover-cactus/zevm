//! RIPEMD-160, needed for the `RIPEMD160` precompile (address 0x03): not in
//! `std.crypto`, unlike the other three precompiles' hash functions. A
//! minimal one-shot implementation following the reference specification
//! (Dobbertin, Bosselaers, Preneel, 1996).

const std = @import("std");

const rol = std.math.rotl;

// Left line: message word index per step (rounds of 16, concatenated).
const r_left = [80]u5{
    0,  1,  2,  3,  4,  5,  6,  7,  8,  9,  10, 11, 12, 13, 14, 15,
    7,  4,  13, 1,  10, 6,  15, 3,  12, 0,  9,  5,  2,  14, 11, 8,
    3,  10, 14, 4,  9,  15, 8,  1,  2,  7,  0,  6,  13, 11, 5,  12,
    1,  9,  11, 10, 0,  8,  12, 4,  13, 3,  7,  15, 14, 5,  6,  2,
    4,  0,  5,  9,  7,  12, 2,  10, 14, 1,  3,  8,  11, 6,  15, 13,
};
// Right line: message word index per step.
const r_right = [80]u5{
    5,  14, 7,  0,  9,  2,  11, 4,  13, 6,  15, 8,  1,  10, 3,  12,
    6,  11, 3,  7,  0,  13, 5,  10, 14, 15, 8,  12, 4,  9,  1,  2,
    15, 5,  1,  3,  7,  14, 6,  9,  11, 8,  12, 2,  10, 0,  4,  13,
    8,  6,  4,  1,  3,  11, 15, 0,  5,  12, 2,  13, 9,  7,  10, 14,
    12, 15, 10, 4,  1,  5,  8,  7,  6,  2,  13, 14, 0,  3,  9,  11,
};
// Left line: rotation amount per step.
const s_left = [80]u5{
    11, 14, 15, 12, 5,  8,  7,  9,  11, 13, 14, 15, 6,  7,  9,  8,
    7,  6,  8,  13, 11, 9,  7,  15, 7,  12, 15, 9,  11, 7,  13, 12,
    11, 13, 6,  7,  14, 9,  13, 15, 14, 8,  13, 6,  5,  12, 7,  5,
    11, 12, 14, 15, 14, 15, 9,  8,  9,  14, 5,  6,  8,  6,  5,  12,
    9,  15, 5,  11, 6,  8,  13, 12, 5,  12, 13, 14, 11, 8,  5,  6,
};
// Right line: rotation amount per step.
const s_right = [80]u5{
    8,  9,  9,  11, 13, 15, 15, 5,  7,  7,  8,  11, 14, 14, 12, 6,
    9,  13, 15, 7,  12, 8,  9,  11, 7,  7,  12, 7,  6,  15, 13, 11,
    9,  7,  15, 11, 8,  6,  6,  14, 12, 13, 5,  14, 13, 13, 7,  5,
    15, 5,  8,  11, 14, 14, 6,  14, 6,  9,  12, 9,  12, 5,  15, 8,
    8,  5,  12, 9,  12, 5,  14, 6,  8,  13, 6,  5,  15, 13, 11, 11,
};

// Round constants, one per round of 16 steps (index = step / 16).
const k_left = [5]u32{ 0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E };
const k_right = [5]u32{ 0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000 };

fn f(round: usize, x: u32, y: u32, z: u32) u32 {
    return switch (round) {
        0 => x ^ y ^ z,
        1 => (x & y) | (~x & z),
        2 => (x | ~y) ^ z,
        3 => (x & z) | (y & ~z),
        4 => x ^ (y | ~z),
        else => unreachable,
    };
}

/// A block's worth (64 bytes) of message schedule, as 16 little-endian
/// 32-bit words.
fn loadBlock(block: *const [64]u8) [16]u32 {
    var x: [16]u32 = undefined;
    for (&x, 0..) |*w, i| w.* = std.mem.readInt(u32, block[i * 4 ..][0..4], .little);
    return x;
}

fn compress(state: *[5]u32, block: *const [64]u8) void {
    const x = loadBlock(block);

    var a = state[0];
    var b = state[1];
    var c = state[2];
    var d = state[3];
    var e = state[4];
    var ap = state[0];
    var bp = state[1];
    var cp = state[2];
    var dp = state[3];
    var ep = state[4];

    for (0..80) |j| {
        const round = j / 16;

        const t = rol(u32, a +% f(round, b, c, d) +% x[r_left[j]] +% k_left[round], s_left[j]) +% e;
        a = e;
        e = d;
        d = rol(u32, c, 10);
        c = b;
        b = t;

        const tp = rol(u32, ap +% f(4 - round, bp, cp, dp) +% x[r_right[j]] +% k_right[round], s_right[j]) +% ep;
        ap = ep;
        ep = dp;
        dp = rol(u32, cp, 10);
        cp = bp;
        bp = tp;
    }

    const t = state[1] +% c +% dp;
    state[1] = state[2] +% d +% ep;
    state[2] = state[3] +% e +% ap;
    state[3] = state[4] +% a +% bp;
    state[4] = state[0] +% b +% cp;
    state[0] = t;
}

/// RIPEMD-160 of `data`, in one call: no streaming API, matching how
/// the `RIPEMD160` precompile hashes its whole call-data input at once.
pub fn hash(data: []const u8) [20]u8 {
    var state = [5]u32{ 0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0 };

    var full_blocks = data.len / 64;
    var offset: usize = 0;
    while (full_blocks > 0) : (full_blocks -= 1) {
        compress(&state, data[offset..][0..64]);
        offset += 64;
    }

    // Padding: 0x80, then zeros, then the 64-bit little-endian bit length,
    // filling out to a multiple of 64 bytes (one or two final blocks).
    var tail: [128]u8 = [_]u8{0} ** 128;
    const remaining = data.len - offset;
    @memcpy(tail[0..remaining], data[offset..]);
    tail[remaining] = 0x80;
    const tail_blocks: usize = if (remaining < 56) 64 else 128;
    std.mem.writeInt(u64, tail[tail_blocks - 8 ..][0..8], @as(u64, data.len) * 8, .little);

    var tail_offset: usize = 0;
    while (tail_offset < tail_blocks) : (tail_offset += 64) {
        compress(&state, tail[tail_offset..][0..64]);
    }

    var out: [20]u8 = undefined;
    for (state, 0..) |w, i| std.mem.writeInt(u32, out[i * 4 ..][0..4], w, .little);
    return out;
}

test "RIPEMD160 of empty input matches the known constant" {
    try std.testing.expectEqualSlices(
        u8,
        &[_]u8{ 0x9c, 0x11, 0x85, 0xa5, 0xc5, 0xe9, 0xfc, 0x54, 0x61, 0x28, 0x08, 0x97, 0x7e, 0xe8, 0xf5, 0x48, 0xb2, 0x25, 0x8d, 0x31 },
        &hash(""),
    );
}

test "RIPEMD160 of \"abc\" matches the known constant" {
    try std.testing.expectEqualSlices(
        u8,
        &[_]u8{ 0x8e, 0xb2, 0x08, 0xf7, 0xe0, 0x5d, 0x98, 0x7a, 0x9b, 0x04, 0x4a, 0x8e, 0x98, 0xc6, 0xb0, 0x87, 0xf1, 0x5a, 0x0b, 0xfc },
        &hash("abc"),
    );
}

test "RIPEMD160 of a message spanning multiple blocks matches the known constant" {
    // "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
    const msg = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    try std.testing.expectEqualSlices(
        u8,
        &[_]u8{ 0x12, 0xa0, 0x53, 0x38, 0x4a, 0x9c, 0x0c, 0x88, 0xe4, 0x05, 0xa0, 0x6c, 0x27, 0xdc, 0xf4, 0x9a, 0xda, 0x62, 0xeb, 0x2b },
        &hash(msg),
    );
}

test "RIPEMD160 of one million 'a' characters matches the known constant" {
    const allocator = std.testing.allocator;
    const data = try allocator.alloc(u8, 1_000_000);
    defer allocator.free(data);
    @memset(data, 'a');
    try std.testing.expectEqualSlices(
        u8,
        &[_]u8{ 0x52, 0x78, 0x32, 0x43, 0xc1, 0x69, 0x7b, 0xdb, 0xe1, 0x6d, 0x37, 0xf9, 0x7f, 0x68, 0xf0, 0x83, 0x25, 0xdc, 0x15, 0x28 },
        &hash(data),
    );
}
