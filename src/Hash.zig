//! A 32-byte Keccak-256 hash, represented natively as `u256`: the same
//! width as an EVM stack word, since `KECCAK256` pushes its result directly.

const std = @import("std");

pub const Hash = u256;

pub fn keccak256(data: []const u8) Hash {
    var out: [32]u8 = undefined;
    std.crypto.hash.sha3.Keccak256.hash(data, &out, .{});
    return std.mem.readInt(u256, &out, .big);
}

test "keccak256 of empty input matches the known constant" {
    try std.testing.expectEqual(
        @as(Hash, 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470),
        keccak256(""),
    );
}

test "hashes compare with native equality" {
    try std.testing.expect(keccak256("") == keccak256(""));
    try std.testing.expect(keccak256("a") != keccak256("b"));
}
