//! The EVM operand stack: a fixed-capacity LIFO of 256-bit words.
//!
//! `items` is a heap-allocated slice, not an inline `[capacity]u256` array.
//! At 32KB, embedding it in `Interpreter` (constructed fresh per call/create)
//! made every construction pay for stack-probing that frame size, measured
//! at ~4.3us fixed cost regardless of whether the call pushed a single word.
//! Heap-allocating trades that for one allocation, the same choice revm's
//! own `Stack` makes (`Vec::with_capacity`, not an inline array).

const std = @import("std");

pub const capacity = 1024;

pub const Error = error{
    StackOverflow,
    StackUnderflow,
};

allocator: std.mem.Allocator,
items: []u256,
len: usize = 0,

const Stack = @This();

pub fn init(allocator: std.mem.Allocator) !Stack {
    return .{ .allocator = allocator, .items = try allocator.alloc(u256, capacity) };
}

pub fn deinit(self: *Stack) void {
    self.allocator.free(self.items);
}

pub fn push(self: *Stack, value: u256) Error!void {
    if (self.len == capacity) return Error.StackOverflow;
    self.items[self.len] = value;
    self.len += 1;
}

pub fn pop(self: *Stack) Error!u256 {
    if (self.len == 0) return Error.StackUnderflow;
    self.len -= 1;
    return self.items[self.len];
}

/// `depth` is 0-based from the top: `peek(0)` is the top of the stack.
pub fn peek(self: *const Stack, depth: usize) Error!u256 {
    if (depth >= self.len) return Error.StackUnderflow;
    return self.items[self.len - 1 - depth];
}

/// `n` is 1-based, matching DUP1..DUP16: duplicates the nth item from the top.
pub fn dup(self: *Stack, n: usize) Error!void {
    const value = try self.peek(n - 1);
    try self.push(value);
}

/// `n` is 1-based, matching SWAP1..SWAP16: swaps the top with the (n+1)th item.
pub fn swap(self: *Stack, n: usize) Error!void {
    if (n >= self.len) return Error.StackUnderflow;
    const top = self.len - 1;
    const other = top - n;
    std.mem.swap(u256, &self.items[top], &self.items[other]);
}

test "push then pop returns the same value" {
    var stack = try Stack.init(std.testing.allocator);
    defer stack.deinit();
    try stack.push(42);
    try std.testing.expectEqual(@as(u256, 42), try stack.pop());
}

test "pop is LIFO" {
    var stack = try Stack.init(std.testing.allocator);
    defer stack.deinit();
    try stack.push(1);
    try stack.push(2);
    try stack.push(3);
    try std.testing.expectEqual(@as(u256, 3), try stack.pop());
    try std.testing.expectEqual(@as(u256, 2), try stack.pop());
    try std.testing.expectEqual(@as(u256, 1), try stack.pop());
}

test "pop on empty stack returns StackUnderflow" {
    var stack = try Stack.init(std.testing.allocator);
    defer stack.deinit();
    try std.testing.expectError(Error.StackUnderflow, stack.pop());
}

test "push past capacity returns StackOverflow" {
    var stack = try Stack.init(std.testing.allocator);
    defer stack.deinit();
    var i: usize = 0;
    while (i < capacity) : (i += 1) {
        try stack.push(0);
    }
    try std.testing.expectError(Error.StackOverflow, stack.push(0));
}

test "peek does not consume the item" {
    var stack = try Stack.init(std.testing.allocator);
    defer stack.deinit();
    try stack.push(10);
    try stack.push(20);
    try std.testing.expectEqual(@as(u256, 20), try stack.peek(0));
    try std.testing.expectEqual(@as(u256, 10), try stack.peek(1));
    try std.testing.expectEqual(@as(usize, 2), stack.len);
}

test "dup1 duplicates the top item" {
    var stack = try Stack.init(std.testing.allocator);
    defer stack.deinit();
    try stack.push(7);
    try stack.dup(1);
    try std.testing.expectEqual(@as(usize, 2), stack.len);
    try std.testing.expectEqual(@as(u256, 7), try stack.pop());
    try std.testing.expectEqual(@as(u256, 7), try stack.pop());
}

test "dup2 duplicates the second item from the top" {
    var stack = try Stack.init(std.testing.allocator);
    defer stack.deinit();
    try stack.push(1);
    try stack.push(2);
    try stack.dup(2);
    try std.testing.expectEqual(@as(u256, 1), try stack.pop());
    try std.testing.expectEqual(@as(u256, 2), try stack.pop());
    try std.testing.expectEqual(@as(u256, 1), try stack.pop());
}

test "swap1 swaps the top two items" {
    var stack = try Stack.init(std.testing.allocator);
    defer stack.deinit();
    try stack.push(1);
    try stack.push(2);
    try stack.swap(1);
    try std.testing.expectEqual(@as(u256, 1), try stack.pop());
    try std.testing.expectEqual(@as(u256, 2), try stack.pop());
}

test "swap on too-shallow stack returns StackUnderflow" {
    var stack = try Stack.init(std.testing.allocator);
    defer stack.deinit();
    try stack.push(1);
    try std.testing.expectError(Error.StackUnderflow, stack.swap(1));
}
