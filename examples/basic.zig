const std = @import("std");
const zevm = @import("zevm");

pub fn main(io: std.Io, args: []const []const u8) anyerror!void {
    _ = io;
    _ = args;
    var gpa = std.heap.DebugAllocator(.{}){};
    defer std.debug.assert(gpa.deinit() == .ok);
    const allocator = gpa.allocator();

    var state = zevm.State.init(allocator);
    defer state.deinit();
    try state.setBalance(0x1, 1000);

    var evm = zevm.Evm{ .allocator = allocator, .state = &state };
    const result = try evm.executeTransaction(.{
        .nonce = 0,
        .gas_price = 0,
        .gas_limit = 21000,
        .to = 0xdd,
        .value = 100,
        .data = &.{},
        .v = 0,
        .r = 0,
        .s = 0,
    }, 0x1);
    defer allocator.free(result.return_data);

    std.debug.print("status: {s}\n", .{@tagName(result.status)});
    std.debug.print("sender balance: {d}\n", .{state.getBalance(0x1)});
    std.debug.print("recipient balance: {d}\n", .{state.getBalance(0xdd)});
}
