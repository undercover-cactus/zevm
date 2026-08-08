//! The EVM's byte-addressable, word-expanding memory space, scoped to a
//! single call frame. Owns the growable byte buffer and word-level
//! read/write primitives; gas accounting is the interpreter's job.

const std = @import("std");

allocator: std.mem.Allocator,
bytes: std.ArrayListUnmanaged(u8) = .empty,

const Memory = @This();

pub fn init(allocator: std.mem.Allocator) Memory {
    return .{ .allocator = allocator };
}

pub fn deinit(self: *Memory) void {
    self.bytes.deinit(self.allocator);
}

pub fn len(self: *const Memory) usize {
    return self.bytes.items.len;
}

/// Grows the buffer (zero-filled) so that bytes `[offset, offset + size)` are
/// addressable, rounding up to the next 32-byte word. A no-op if already large enough.
pub fn expand(self: *Memory, offset: usize, size: usize) !void {
    if (size == 0) return;
    const needed = offset + size;
    if (needed <= self.bytes.items.len) return;
    const word_aligned = std.mem.alignForward(usize, needed, 32);
    const old_len = self.bytes.items.len;
    try self.bytes.resize(self.allocator, word_aligned);
    @memset(self.bytes.items[old_len..], 0);
}

/// Returns a slice into the buffer, expanding first if needed.
pub fn read(self: *Memory, offset: usize, size: usize) ![]const u8 {
    try self.expand(offset, size);
    return self.bytes.items[offset .. offset + size];
}

pub fn write(self: *Memory, offset: usize, data: []const u8) !void {
    try self.expand(offset, data.len);
    @memcpy(self.bytes.items[offset .. offset + data.len], data);
}

pub fn readWord(self: *Memory, offset: usize) !u256 {
    const slice = try self.read(offset, 32);
    return std.mem.readInt(u256, slice[0..32], .big);
}

pub fn writeWord(self: *Memory, offset: usize, value: u256) !void {
    var buf: [32]u8 = undefined;
    std.mem.writeInt(u256, &buf, value, .big);
    try self.write(offset, &buf);
}

test "read before any write returns zero-filled bytes" {
    var memory = Memory.init(std.testing.allocator);
    defer memory.deinit();

    const slice = try memory.read(0, 4);
    try std.testing.expectEqualSlices(u8, &.{ 0, 0, 0, 0 }, slice);
}

test "write then read round-trips" {
    var memory = Memory.init(std.testing.allocator);
    defer memory.deinit();

    try memory.write(0, "hi");
    const slice = try memory.read(0, 2);
    try std.testing.expectEqualStrings("hi", slice);
}

test "expansion rounds up to the next 32-byte word" {
    var memory = Memory.init(std.testing.allocator);
    defer memory.deinit();

    try memory.expand(0, 1);
    try std.testing.expectEqual(@as(usize, 32), memory.len());

    try memory.expand(32, 1);
    try std.testing.expectEqual(@as(usize, 64), memory.len());
}

test "writeWord then readWord round-trips" {
    var memory = Memory.init(std.testing.allocator);
    defer memory.deinit();

    try memory.writeWord(0, 0x1234);
    try std.testing.expectEqual(@as(u256, 0x1234), try memory.readWord(0));
}

test "writeWord at an offset does not disturb other words" {
    var memory = Memory.init(std.testing.allocator);
    defer memory.deinit();

    try memory.writeWord(0, std.math.maxInt(u256));
    try memory.writeWord(32, 7);
    try std.testing.expectEqual(@as(u256, std.math.maxInt(u256)), try memory.readWord(0));
    try std.testing.expectEqual(@as(u256, 7), try memory.readWord(32));
}
