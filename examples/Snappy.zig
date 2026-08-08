//! A Snappy decompressor: Zig's stdlib has no Snappy support,
//! and era1 files (`sync_era1.zig`'s input) are Snappy-compressed. Only
//! decompression is implemented.
//!
//! Two layers, per the real format:
//!   - The *framing format* (https://github.com/google/snappy/blob/main/framing_format.txt):
//!     a stream identifier chunk ("sNaPpY") followed by typed,
//!     length-prefixed chunks (compressed-data, uncompressed-data, or
//!     skippable padding/reserved). `frameDecompress` handles this layer.
//!   - The *block format* (https://github.com/google/snappy/blob/main/format_description.txt):
//!     what a compressed-data chunk's payload contains, a varint
//!     uncompressed-length prefix followed by literal and copy elements.
//!     `blockDecompress` handles this layer, exposed separately since it's
//!     also useful standalone.

const std = @import("std");

const stream_identifier = "sNaPpY";

const ChunkType = enum(u8) {
    compressed_data = 0x00,
    uncompressed_data = 0x01,
    padding = 0xfe,
    stream_identifier = 0xff,
    _,
};

pub const Error = error{
    InvalidStreamIdentifier,
    TruncatedChunk,
    UnskippableReservedChunk,
    ChecksumMismatch,
    TruncatedVarint,
    VarintTooLong,
    InvalidCopyOffset,
    TruncatedBlock,
} || std.mem.Allocator.Error;

/// Decompresses a full Snappy-framed stream (the format `.era1` records
/// hold their header/body/receipts payloads in).
pub fn frameDecompress(allocator: std.mem.Allocator, compressed: []const u8) Error![]u8 {
    var out: std.ArrayList(u8) = .empty;
    errdefer out.deinit(allocator);

    var pos: usize = 0;
    var seen_identifier = false;
    while (pos < compressed.len) {
        if (pos + 4 > compressed.len) return error.TruncatedChunk;
        const chunk_type: ChunkType = @enumFromInt(compressed[pos]);
        const len = compressed[pos + 1] |
            (@as(u32, compressed[pos + 2]) << 8) |
            (@as(u32, compressed[pos + 3]) << 16);
        pos += 4;
        if (pos + len > compressed.len) return error.TruncatedChunk;
        const chunk_data = compressed[pos .. pos + len];
        pos += len;

        switch (chunk_type) {
            .stream_identifier => {
                if (!std.mem.eql(u8, chunk_data, stream_identifier)) {
                    return error.InvalidStreamIdentifier;
                }
                seen_identifier = true;
            },
            .compressed_data => {
                if (!seen_identifier) return error.InvalidStreamIdentifier;
                if (chunk_data.len < 4) return error.TruncatedChunk;
                const expected_checksum = std.mem.readInt(u32, chunk_data[0..4], .little);
                const block = try blockDecompress(allocator, chunk_data[4..]);
                defer allocator.free(block);
                if (maskedCrc32c(block) != expected_checksum) return error.ChecksumMismatch;
                try out.appendSlice(allocator, block);
            },
            .uncompressed_data => {
                if (!seen_identifier) return error.InvalidStreamIdentifier;
                if (chunk_data.len < 4) return error.TruncatedChunk;
                const expected_checksum = std.mem.readInt(u32, chunk_data[0..4], .little);
                const payload = chunk_data[4..];
                if (maskedCrc32c(payload) != expected_checksum) return error.ChecksumMismatch;
                try out.appendSlice(allocator, payload);
            },
            .padding => {},
            _ => {
                // Chunk types 0x02..0x7f are reserved *unskippable*:
                // encountering one means corruption or an unknown framing
                // extension. 0x80..0xfd are reserved *skippable*, already
                // skipped above via `pos += len`.
                if (@intFromEnum(chunk_type) < 0x80) return error.UnskippableReservedChunk;
            },
        }
    }

    return out.toOwnedSlice(allocator);
}

/// CRC-32C (Castagnoli) with Snappy's own masking:
/// `((crc >> 15) | (crc << 17)) +% 0xa282ead8`, deliberately not a plain
/// CRC so a stream of literal zero bytes doesn't checksum to all-zero.
fn maskedCrc32c(data: []const u8) u32 {
    const crc = std.hash.crc.Crc32Iscsi.hash(data);
    return (crc >> 15 | crc << 17) +% 0xa282ead8;
}

fn readVarint(data: []const u8, pos: *usize) Error!u64 {
    var result: u64 = 0;
    var shift: u6 = 0;
    while (true) {
        if (pos.* >= data.len) return error.TruncatedVarint;
        const byte = data[pos.*];
        pos.* += 1;
        result |= @as(u64, byte & 0x7f) << shift;
        if (byte & 0x80 == 0) return result;
        if (shift >= 63) return error.VarintTooLong;
        shift += 7;
    }
}

/// Decompresses one Snappy *block* (a compressed-data chunk's payload,
/// stripped of its framing checksum): a varint uncompressed-length prefix
/// followed by literal/copy elements, per
/// https://github.com/google/snappy/blob/main/format_description.txt.
pub fn blockDecompress(allocator: std.mem.Allocator, block: []const u8) Error![]u8 {
    var pos: usize = 0;
    const uncompressed_len = try readVarint(block, &pos);

    var out = try std.ArrayList(u8).initCapacity(allocator, uncompressed_len);
    errdefer out.deinit(allocator);

    while (pos < block.len) {
        const tag = block[pos];
        pos += 1;
        switch (tag & 0x3) {
            0x0 => {
                // Literal: top 6 bits encode length-1 directly if < 60,
                // otherwise they say how many following little-endian
                // bytes hold length-1 instead.
                const tag_hi: u64 = tag >> 2;
                const len: u64 = if (tag_hi < 60) tag_hi + 1 else blk: {
                    const extra_bytes: usize = tag_hi - 59;
                    if (pos + extra_bytes > block.len) return error.TruncatedBlock;
                    var len_minus_1: u64 = 0;
                    for (0..extra_bytes) |i| len_minus_1 |= @as(u64, block[pos + i]) << @intCast(8 * i);
                    pos += extra_bytes;
                    break :blk len_minus_1 + 1;
                };
                if (pos + len > block.len) return error.TruncatedBlock;
                try out.appendSlice(allocator, block[pos .. pos + len]);
                pos += len;
            },
            0x1 => {
                // Copy, 1-byte offset: 3-bit length (bits 2-4, +4 → 4-11),
                // 11-bit offset (top 3 bits of the tag as its high bits,
                // then one more byte).
                if (pos >= block.len) return error.TruncatedBlock;
                const length: usize = ((tag >> 2) & 0x7) + 4;
                const offset: usize = (@as(usize, tag >> 5) << 8) | block[pos];
                pos += 1;
                try emitCopy(allocator, &out, offset, length);
            },
            0x2 => {
                // Copy, 2-byte offset: 6-bit length (bits 2-7, +1 → 1-64).
                if (pos + 2 > block.len) return error.TruncatedBlock;
                const length: usize = (tag >> 2) + 1;
                const offset: usize = std.mem.readInt(u16, block[pos..][0..2], .little);
                pos += 2;
                try emitCopy(allocator, &out, offset, length);
            },
            0x3 => {
                // Copy, 4-byte offset: 6-bit length (bits 2-7, +1 → 1-64).
                if (pos + 4 > block.len) return error.TruncatedBlock;
                const length: usize = (tag >> 2) + 1;
                const offset: usize = std.mem.readInt(u32, block[pos..][0..4], .little);
                pos += 4;
                try emitCopy(allocator, &out, offset, length);
            },
            else => unreachable,
        }
    }

    if (out.items.len != uncompressed_len) return error.TruncatedBlock;
    return out.toOwnedSlice(allocator);
}

/// A copy's source and destination ranges can overlap (`offset < length`
/// is how runs of a single repeated byte compress to almost nothing), so
/// this copies byte-by-byte: each byte must see the already-copied bytes
/// ahead of it in the output.
fn emitCopy(allocator: std.mem.Allocator, out: *std.ArrayList(u8), offset: usize, length: usize) Error!void {
    if (offset == 0 or offset > out.items.len) return error.InvalidCopyOffset;
    try out.ensureUnusedCapacity(allocator, length);
    for (0..length) |_| {
        out.appendAssumeCapacity(out.items[out.items.len - offset]);
    }
}

fn frameEncodeForTest(allocator: std.mem.Allocator, chunks: []const struct { kind: ChunkType, data: []const u8 }) ![]u8 {
    var out: std.ArrayList(u8) = .empty;
    defer out.deinit(allocator);
    try out.appendSlice(allocator, stream_identifier);
    // Wrap the identifier in its own chunk header.
    var framed: std.ArrayList(u8) = .empty;
    defer framed.deinit(allocator);
    try appendChunk(allocator, &framed, .stream_identifier, stream_identifier);
    for (chunks) |c| {
        if (c.kind == .compressed_data or c.kind == .uncompressed_data) {
            // The checksum always covers the *uncompressed* bytes, so
            // decompress first if needed rather than hashing the raw block.
            const uncompressed = if (c.kind == .compressed_data)
                try blockDecompress(allocator, c.data)
            else
                try allocator.dupe(u8, c.data);
            defer allocator.free(uncompressed);

            var payload: std.ArrayList(u8) = .empty;
            defer payload.deinit(allocator);
            var checksum_buf: [4]u8 = undefined;
            std.mem.writeInt(u32, &checksum_buf, maskedCrc32c(uncompressed), .little);
            try payload.appendSlice(allocator, &checksum_buf);
            try payload.appendSlice(allocator, c.data);
            try appendChunk(allocator, &framed, c.kind, payload.items);
        } else {
            try appendChunk(allocator, &framed, c.kind, c.data);
        }
    }
    return framed.toOwnedSlice(allocator);
}

fn appendChunk(allocator: std.mem.Allocator, out: *std.ArrayList(u8), kind: ChunkType, data: []const u8) !void {
    try out.append(allocator, @intFromEnum(kind));
    try out.append(allocator, @intCast(data.len & 0xff));
    try out.append(allocator, @intCast((data.len >> 8) & 0xff));
    try out.append(allocator, @intCast((data.len >> 16) & 0xff));
    try out.appendSlice(allocator, data);
}

test "blockDecompress: literal-only block" {
    // varint(5) + literal tag (len-1=4 -> 4<<2|00=0x10) + "hello"
    const block = [_]u8{ 5, 0x10 } ++ "hello".*;
    const out = try blockDecompress(std.testing.allocator, &block);
    defer std.testing.allocator.free(out);
    try std.testing.expectEqualStrings("hello", out);
}

test "blockDecompress: a copy repeats earlier output, including overlapping runs" {
    // "aaaa": varint(4) + literal 'a' (len-1=0 -> tag 0x00) + 'a', then a
    // 1-byte-offset copy of length 3 at offset 1 (tag: len_bits=(3-4)... use
    // 2-byte-offset form instead for clarity: tag = ((length-1)<<2)|0x2).
    const block = [_]u8{ 4, 0x00, 'a', ((3 - 1) << 2) | 0x2, 1, 0 };
    const out = try blockDecompress(std.testing.allocator, &block);
    defer std.testing.allocator.free(out);
    try std.testing.expectEqualStrings("aaaa", out);
}

test "blockDecompress: long literal uses the extra-length-bytes form" {
    const data = [_]u8{'x'} ** 61;
    // tag_hi = 60 means "1 extra byte holds length-1" -> tag = 60<<2|0x0 = 0xf0
    const block = [_]u8{ 61, 0xf0, 60 } ++ data;
    const out = try blockDecompress(std.testing.allocator, &block);
    defer std.testing.allocator.free(out);
    try std.testing.expectEqualSlices(u8, &data, out);
}

test "blockDecompress: truncated varint errors" {
    const block = [_]u8{0x80};
    try std.testing.expectError(error.TruncatedVarint, blockDecompress(std.testing.allocator, &block));
}

test "blockDecompress: copy offset pointing before the start of output errors" {
    const block = [_]u8{ 1, ((4 - 1) << 2) | 0x2, 5, 0 };
    try std.testing.expectError(error.InvalidCopyOffset, blockDecompress(std.testing.allocator, &block));
}

test "frameDecompress: a stream with only uncompressed-data chunks round-trips" {
    const framed = try frameEncodeForTest(std.testing.allocator, &.{
        .{ .kind = .uncompressed_data, .data = "hello, world" },
    });
    defer std.testing.allocator.free(framed);

    const out = try frameDecompress(std.testing.allocator, framed);
    defer std.testing.allocator.free(out);
    try std.testing.expectEqualStrings("hello, world", out);
}

test "frameDecompress: a compressed-data chunk decompresses and concatenates with others" {
    // The compressed-data chunk's payload is itself a valid Snappy block
    // (literal "hi" here; any valid block exercises the dispatch layer).
    const block = [_]u8{ 2, 0x04 } ++ "hi".*;
    const framed = try frameEncodeForTest(std.testing.allocator, &.{
        .{ .kind = .compressed_data, .data = &block },
        .{ .kind = .uncompressed_data, .data = " there" },
    });
    defer std.testing.allocator.free(framed);

    const out = try frameDecompress(std.testing.allocator, framed);
    defer std.testing.allocator.free(out);
    try std.testing.expectEqualStrings("hi there", out);
}

test "frameDecompress: padding chunks are skipped" {
    const framed = try frameEncodeForTest(std.testing.allocator, &.{
        .{ .kind = .padding, .data = &.{ 1, 2, 3 } },
        .{ .kind = .uncompressed_data, .data = "ok" },
    });
    defer std.testing.allocator.free(framed);

    const out = try frameDecompress(std.testing.allocator, framed);
    defer std.testing.allocator.free(out);
    try std.testing.expectEqualStrings("ok", out);
}

test "frameDecompress: a corrupted checksum is rejected" {
    var framed = try frameEncodeForTest(std.testing.allocator, &.{
        .{ .kind = .uncompressed_data, .data = "hello" },
    });
    defer std.testing.allocator.free(framed);
    // Flip a byte inside the checksum (right after the 4-byte chunk header
    // + stream-identifier chunk).
    framed[framed.len - "hello".len - 1] ^= 0xff;
    try std.testing.expectError(error.ChecksumMismatch, frameDecompress(std.testing.allocator, framed));
}

test "frameDecompress: missing stream identifier is rejected" {
    var out: std.ArrayList(u8) = .empty;
    defer out.deinit(std.testing.allocator);
    try appendChunk(std.testing.allocator, &out, .uncompressed_data, &.{ 0, 0, 0, 0 });
    try std.testing.expectError(error.InvalidStreamIdentifier, frameDecompress(std.testing.allocator, out.items));
}
