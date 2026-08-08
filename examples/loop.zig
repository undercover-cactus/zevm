const std = @import("std");
const zevm = @import("zevm");

const OpCode = zevm.OpCode;

pub fn main(io: std.Io) anyerror!void {
    _ = io;

    // Sums 1..5 with a JUMP/JUMPI loop, keeping [acc, counter] on the stack
    // (counter on top).
    const code = [_]u8{
        @intFromEnum(OpCode.PUSH1), 0, // 0,1:   acc = 0
        @intFromEnum(OpCode.PUSH1), 5, // 2,3:   counter = 5
        @intFromEnum(OpCode.JUMPDEST), // 4:     loop:
        @intFromEnum(OpCode.DUP1), // 5
        @intFromEnum(OpCode.ISZERO), // 6
        @intFromEnum(OpCode.PUSH1), 21, // 7,8:   push end
        @intFromEnum(OpCode.JUMPI), // 9:     if counter == 0, goto end
        @intFromEnum(OpCode.DUP1), // 10
        @intFromEnum(OpCode.SWAP2), // 11
        @intFromEnum(OpCode.ADD), // 12:    acc += counter (leaves acc on top)
        @intFromEnum(OpCode.SWAP1), // 13:    bring counter back to the top
        @intFromEnum(OpCode.PUSH1), 1, // 14,15
        @intFromEnum(OpCode.SWAP1), // 16
        @intFromEnum(OpCode.SUB), // 17:    counter -= 1
        @intFromEnum(OpCode.PUSH1), 4, // 18,19: push loop
        @intFromEnum(OpCode.JUMP), // 20:    goto loop
        @intFromEnum(OpCode.JUMPDEST), // 21:    end:
        @intFromEnum(OpCode.POP), // 22:    discard counter (0)
        @intFromEnum(OpCode.STOP), // 23
    };

    var gpa = std.heap.DebugAllocator(.{}){};
    defer std.debug.assert(gpa.deinit() == .ok);

    var interp = try zevm.Interpreter.init(gpa.allocator(), &code, 1_000_000);
    defer interp.deinit();
    try interp.run();

    std.debug.print("status: {s}\n", .{@tagName(interp.status)});
    std.debug.print("sum(1..5) = {d}\n", .{try interp.stack.pop()});
}
