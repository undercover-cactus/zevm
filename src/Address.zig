//! A 20-byte (160-bit) Ethereum account address, represented natively as
//! `u160` rather than a byte array.

const std = @import("std");

pub const Address = u160;

pub fn toHex(address: Address) [42]u8 {
    var raw: [20]u8 = undefined;
    std.mem.writeInt(u160, &raw, address, .big);
    var out: [42]u8 = undefined;
    out[0] = '0';
    out[1] = 'x';
    out[2..].* = std.fmt.bytesToHex(raw, .lower);
    return out;
}

test "zero address formats as 0x followed by 40 zeros" {
    try std.testing.expectEqualStrings("0x" ++ "00" ** 20, &toHex(0));
}

test "toHex encodes lowercase with a 0x prefix" {
    const addr: Address = std.mem.readInt(u160, &([_]u8{0xab} ** 20), .big);
    try std.testing.expectEqualStrings("0x" ++ "ab" ** 20, &toHex(addr));
}

test "addresses compare with native equality" {
    const a: Address = 1;
    const b: Address = 1;
    const c: Address = 2;
    try std.testing.expect(a == b);
    try std.testing.expect(a != c);
}
