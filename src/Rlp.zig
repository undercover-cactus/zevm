//! RLP (Recursive Length Prefix) encoding and decoding: Ethereum's standard
//! serialization format for transactions, blocks, and tries.
//!
//! Encoding functions each return a freshly allocated, caller-owned slice.
//! Decoding produces a generic `Item` tree that borrows string payloads
//! directly from the input rather than copying them; only the list
//! structure itself is allocated. Doesn't reject non-canonical encodings;
//! real chain data is always produced by conforming encoders.

const std = @import("std");

/// A decoded RLP value: either a byte string (an empty string reads as
/// zero, per RLP convention; see `encodeInt`) or a list of items.
pub const Item = union(enum) {
    string: []const u8,
    list: []const Item,

    pub fn deinit(self: Item, allocator: std.mem.Allocator) void {
        switch (self) {
            .string => {},
            .list => |items| {
                for (items) |item| item.deinit(allocator);
                allocator.free(items);
            },
        }
    }
};

pub const DecodeError = error{
    UnexpectedEndOfInput,
    TrailingBytes,
} || std.mem.Allocator.Error;

/// Decodes exactly one RLP-encoded item from `bytes`: the entry point for a
/// full transaction, block, etc. Errors on trailing bytes rather than
/// silently ignoring them.
pub fn decode(allocator: std.mem.Allocator, bytes: []const u8) DecodeError!Item {
    var pos: usize = 0;
    const item = try decodeItem(allocator, bytes, &pos);
    if (pos != bytes.len) return error.TrailingBytes;
    return item;
}

fn decodeItem(allocator: std.mem.Allocator, bytes: []const u8, pos: *usize) DecodeError!Item {
    if (pos.* >= bytes.len) return error.UnexpectedEndOfInput;
    const prefix = bytes[pos.*];

    if (prefix <= 0x7f) {
        const str = bytes[pos.* .. pos.* + 1];
        pos.* += 1;
        return .{ .string = str };
    }
    if (prefix <= 0xb7) {
        pos.* += 1;
        return .{ .string = try readString(bytes, pos, prefix - 0x80) };
    }
    if (prefix <= 0xbf) {
        pos.* += 1;
        const len = try readLength(bytes, pos, prefix - 0xb7);
        return .{ .string = try readString(bytes, pos, len) };
    }
    if (prefix <= 0xf7) {
        pos.* += 1;
        return decodeListPayload(allocator, bytes, pos, prefix - 0xc0);
    }
    pos.* += 1;
    const len = try readLength(bytes, pos, prefix - 0xf7);
    return decodeListPayload(allocator, bytes, pos, len);
}

fn readString(bytes: []const u8, pos: *usize, len: usize) DecodeError![]const u8 {
    if (pos.* + len > bytes.len) return error.UnexpectedEndOfInput;
    const str = bytes[pos.* .. pos.* + len];
    pos.* += len;
    return str;
}

/// Reads a big-endian length made of `len_of_len` bytes (the "long form"
/// prefix's own length field, never longer than 8 bytes in practice).
fn readLength(bytes: []const u8, pos: *usize, len_of_len: u8) DecodeError!usize {
    if (pos.* + len_of_len > bytes.len) return error.UnexpectedEndOfInput;
    var len: usize = 0;
    for (bytes[pos.* .. pos.* + len_of_len]) |b| len = (len << 8) | b;
    pos.* += len_of_len;
    return len;
}

fn decodeListPayload(allocator: std.mem.Allocator, bytes: []const u8, pos: *usize, len: usize) DecodeError!Item {
    if (pos.* + len > bytes.len) return error.UnexpectedEndOfInput;
    const end = pos.* + len;
    var items: std.ArrayList(Item) = .empty;
    errdefer {
        for (items.items) |item| item.deinit(allocator);
        items.deinit(allocator);
    }
    while (pos.* < end) {
        const item = try decodeItem(allocator, bytes, pos);
        try items.append(allocator, item);
    }
    if (pos.* != end) return error.TrailingBytes;
    return .{ .list = try items.toOwnedSlice(allocator) };
}

/// A single byte in [0x00, 0x7f] encodes as itself; otherwise a length
/// prefix (`0x80 + len` for len <= 55, `0xb7 + len-of-len` followed by the
/// length for longer strings) precedes the raw bytes.
pub fn encodeBytes(allocator: std.mem.Allocator, bytes: []const u8) ![]u8 {
    if (bytes.len == 1 and bytes[0] <= 0x7f) {
        return allocator.dupe(u8, bytes);
    }
    return prefixed(allocator, bytes, 0x80);
}

/// Encodes a non-negative integer as its minimal big-endian byte string.
/// Per RLP, zero is the *empty* string, not a zero byte.
pub fn encodeInt(allocator: std.mem.Allocator, value: u256) ![]u8 {
    if (value == 0) {
        const out = try allocator.alloc(u8, 1);
        out[0] = 0x80;
        return out;
    }
    var buf: [32]u8 = undefined;
    std.mem.writeInt(u256, &buf, value, .big);
    var start: usize = 0;
    while (buf[start] == 0) : (start += 1) {}
    return encodeBytes(allocator, buf[start..]);
}

/// Wraps already RLP-encoded `items` as an RLP list (`0xc0 + len` for len <=
/// 55, `0xf7 + len-of-len` followed by the length for longer payloads).
pub fn encodeList(allocator: std.mem.Allocator, items: []const []const u8) ![]u8 {
    var total: usize = 0;
    for (items) |item| total += item.len;
    const payload = try allocator.alloc(u8, total);
    defer allocator.free(payload);
    var offset: usize = 0;
    for (items) |item| {
        @memcpy(payload[offset..][0..item.len], item);
        offset += item.len;
    }
    return prefixed(allocator, payload, 0xc0);
}

fn prefixed(allocator: std.mem.Allocator, payload: []const u8, base: u8) ![]u8 {
    if (payload.len <= 55) {
        const out = try allocator.alloc(u8, 1 + payload.len);
        out[0] = base + @as(u8, @intCast(payload.len));
        @memcpy(out[1..], payload);
        return out;
    }
    var len_buf: [8]u8 = undefined;
    std.mem.writeInt(u64, &len_buf, payload.len, .big);
    var start: usize = 0;
    while (len_buf[start] == 0) : (start += 1) {}
    const len_bytes = len_buf[start..];
    const out = try allocator.alloc(u8, 1 + len_bytes.len + payload.len);
    out[0] = base + 55 + @as(u8, @intCast(len_bytes.len));
    @memcpy(out[1 .. 1 + len_bytes.len], len_bytes);
    @memcpy(out[1 + len_bytes.len ..], payload);
    return out;
}

test "encodeBytes: empty string" {
    const out = try encodeBytes(std.testing.allocator, "");
    defer std.testing.allocator.free(out);
    try std.testing.expectEqualSlices(u8, &.{0x80}, out);
}

test "encodeBytes: single byte below 0x80 encodes as itself" {
    const out = try encodeBytes(std.testing.allocator, "a");
    defer std.testing.allocator.free(out);
    try std.testing.expectEqualSlices(u8, &.{0x61}, out);
}

test "encodeBytes: single byte at or above 0x80 needs a length prefix" {
    const out = try encodeBytes(std.testing.allocator, &.{0x80});
    defer std.testing.allocator.free(out);
    try std.testing.expectEqualSlices(u8, &.{ 0x81, 0x80 }, out);
}

test "encodeBytes: short string" {
    const out = try encodeBytes(std.testing.allocator, "dog");
    defer std.testing.allocator.free(out);
    try std.testing.expectEqualSlices(u8, &.{ 0x83, 'd', 'o', 'g' }, out);
}

test "encodeBytes: long string (> 55 bytes) uses a length-of-length prefix" {
    const long = [_]u8{'x'} ** 56;
    const out = try encodeBytes(std.testing.allocator, &long);
    defer std.testing.allocator.free(out);
    // 0xb7 + 1 length-of-length byte, then the length (56 = 0x38) itself.
    try std.testing.expectEqual(@as(u8, 0xb8), out[0]);
    try std.testing.expectEqual(@as(u8, 56), out[1]);
    try std.testing.expectEqualSlices(u8, &long, out[2..]);
}

test "encodeInt: zero is the empty string, not a zero byte" {
    const out = try encodeInt(std.testing.allocator, 0);
    defer std.testing.allocator.free(out);
    try std.testing.expectEqualSlices(u8, &.{0x80}, out);
}

test "encodeInt: small values below 0x80 have no prefix" {
    const out = try encodeInt(std.testing.allocator, 1);
    defer std.testing.allocator.free(out);
    try std.testing.expectEqualSlices(u8, &.{0x01}, out);
}

test "encodeInt: 128 needs a length prefix since it doesn't fit as a bare byte" {
    const out = try encodeInt(std.testing.allocator, 128);
    defer std.testing.allocator.free(out);
    try std.testing.expectEqualSlices(u8, &.{ 0x81, 0x80 }, out);
}

test "encodeInt: no leading zero bytes" {
    const out = try encodeInt(std.testing.allocator, 1024);
    defer std.testing.allocator.free(out);
    try std.testing.expectEqualSlices(u8, &.{ 0x82, 0x04, 0x00 }, out);
}

test "encodeList: [\"cat\", \"dog\"] matches the canonical RLP test vector" {
    const cat = try encodeBytes(std.testing.allocator, "cat");
    defer std.testing.allocator.free(cat);
    const dog = try encodeBytes(std.testing.allocator, "dog");
    defer std.testing.allocator.free(dog);

    const out = try encodeList(std.testing.allocator, &.{ cat, dog });
    defer std.testing.allocator.free(out);

    try std.testing.expectEqualSlices(u8, &.{
        0xc8, 0x83, 'c', 'a', 't', 0x83, 'd', 'o', 'g',
    }, out);
}

test "encodeList: empty list" {
    const out = try encodeList(std.testing.allocator, &.{});
    defer std.testing.allocator.free(out);
    try std.testing.expectEqualSlices(u8, &.{0xc0}, out);
}

test "decode: empty string" {
    const item = try decode(std.testing.allocator, &.{0x80});
    defer item.deinit(std.testing.allocator);
    try std.testing.expectEqualSlices(u8, "", item.string);
}

test "decode: single byte below 0x80 decodes as itself" {
    const item = try decode(std.testing.allocator, &.{0x61});
    defer item.deinit(std.testing.allocator);
    try std.testing.expectEqualSlices(u8, "a", item.string);
}

test "decode: single byte at or above 0x80 needs its length prefix" {
    const item = try decode(std.testing.allocator, &.{ 0x81, 0x80 });
    defer item.deinit(std.testing.allocator);
    try std.testing.expectEqualSlices(u8, &.{0x80}, item.string);
}

test "decode: short string" {
    const item = try decode(std.testing.allocator, &.{ 0x83, 'd', 'o', 'g' });
    defer item.deinit(std.testing.allocator);
    try std.testing.expectEqualSlices(u8, "dog", item.string);
}

test "decode: long string (> 55 bytes) uses a length-of-length prefix" {
    const long = [_]u8{'x'} ** 56;
    const encoded = try encodeBytes(std.testing.allocator, &long);
    defer std.testing.allocator.free(encoded);

    const item = try decode(std.testing.allocator, encoded);
    defer item.deinit(std.testing.allocator);
    try std.testing.expectEqualSlices(u8, &long, item.string);
}

test "decode: string payload borrows from the input rather than copying" {
    const encoded = [_]u8{ 0x83, 'd', 'o', 'g' };
    const item = try decode(std.testing.allocator, &encoded);
    defer item.deinit(std.testing.allocator);
    try std.testing.expectEqual(@intFromPtr(encoded[1..].ptr), @intFromPtr(item.string.ptr));
}

test "decode: [\"cat\", \"dog\"] matches the canonical RLP test vector" {
    const encoded = [_]u8{ 0xc8, 0x83, 'c', 'a', 't', 0x83, 'd', 'o', 'g' };
    const item = try decode(std.testing.allocator, &encoded);
    defer item.deinit(std.testing.allocator);

    try std.testing.expectEqual(@as(usize, 2), item.list.len);
    try std.testing.expectEqualSlices(u8, "cat", item.list[0].string);
    try std.testing.expectEqualSlices(u8, "dog", item.list[1].string);
}

test "decode: empty list" {
    const item = try decode(std.testing.allocator, &.{0xc0});
    defer item.deinit(std.testing.allocator);
    try std.testing.expectEqual(@as(usize, 0), item.list.len);
}

test "decode: a list longer than 55 bytes of payload uses a length-of-length prefix" {
    const cat = try encodeBytes(std.testing.allocator, "cat");
    defer std.testing.allocator.free(cat);
    var items: [20][]const u8 = undefined;
    for (&items) |*i| i.* = cat;
    const encoded = try encodeList(std.testing.allocator, &items);
    defer std.testing.allocator.free(encoded);
    try std.testing.expect(encoded.len > 55); // sanity: this test exercises the long form

    const item = try decode(std.testing.allocator, encoded);
    defer item.deinit(std.testing.allocator);
    try std.testing.expectEqual(@as(usize, 20), item.list.len);
    for (item.list) |sub| try std.testing.expectEqualSlices(u8, "cat", sub.string);
}

test "decode: a list can nest other lists" {
    const dog = try encodeBytes(std.testing.allocator, "dog");
    defer std.testing.allocator.free(dog);
    const inner = try encodeList(std.testing.allocator, &.{dog});
    defer std.testing.allocator.free(inner);
    const outer = try encodeList(std.testing.allocator, &.{ inner, inner });
    defer std.testing.allocator.free(outer);

    const item = try decode(std.testing.allocator, outer);
    defer item.deinit(std.testing.allocator);

    try std.testing.expectEqual(@as(usize, 2), item.list.len);
    try std.testing.expectEqual(@as(usize, 1), item.list[0].list.len);
    try std.testing.expectEqualSlices(u8, "dog", item.list[0].list[0].string);
    try std.testing.expectEqualSlices(u8, "dog", item.list[1].list[0].string);
}

test "decode: encodeInt round-trips through decode" {
    const encoded = try encodeInt(std.testing.allocator, 1024);
    defer std.testing.allocator.free(encoded);
    const item = try decode(std.testing.allocator, encoded);
    defer item.deinit(std.testing.allocator);
    try std.testing.expectEqualSlices(u8, &.{ 0x04, 0x00 }, item.string);
}

test "decode: truncated input errors instead of reading out of bounds" {
    try std.testing.expectError(error.UnexpectedEndOfInput, decode(std.testing.allocator, &.{0x83, 'd', 'o'}));
}

test "decode: a length prefix promising more than the input has errors" {
    try std.testing.expectError(error.UnexpectedEndOfInput, decode(std.testing.allocator, &.{0xc4, 0x83, 'd', 'o'}));
}

test "decode: trailing bytes after one complete item error" {
    try std.testing.expectError(error.TrailingBytes, decode(std.testing.allocator, &.{ 0x80, 0x80 }));
}

test "decode: a truncated list frees the items it already decoded before erroring" {
    // 0xc6 promises 6 bytes of payload: a valid "dog", then a second string
    // prefix promising 3 more bytes with only one present. "dog" decodes
    // first (landing in `items`), exercising decodeListPayload's errdefer.
    try std.testing.expectError(error.UnexpectedEndOfInput, decode(std.testing.allocator, &.{ 0xc6, 0x83, 'd', 'o', 'g', 0x83, 'x' }));
}
