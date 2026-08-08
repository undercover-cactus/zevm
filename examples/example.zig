const std = @import("std");
const basic = @import("./basic.zig");
const loop = @import("./loop.zig");
const sync = @import("./sync.zig");
const sync_era1 = @import("./sync_era1.zig");
const eq = std.mem.eql;

const ExampleProgram = *const fn (std.Io) anyerror!void;

fn getExample(example_name: []const u8) ?ExampleProgram {
    if (eq(u8, "basic", example_name)) return basic.main;
    if (eq(u8, "loop", example_name)) return loop.main;
    if (eq(u8, "sync", example_name)) return sync.main;
    if (eq(u8, "sync_era1", example_name)) return sync_era1.main;
    return null;
}

fn runExample(io: std.Io, example_name: []const u8) !void {
    const example = getExample(example_name);
    if (example) |program| {
        try program(io);
    } else {
        std.debug.print("Unknown example {s}\n", .{example_name});
    }
}

pub fn main(init: std.process.Init) !void {
    var args = init.minimal.args.iterate();
    _ = args.skip();

    const arg = args.next();
    if (arg) |example_name| {
        try runExample(init.io, example_name);
    } else {
        std.debug.print("Usage: zig build example -- <example-name>\n\n", .{});
        std.debug.print("Available examples:\n", .{});
        std.debug.print("  - basic\n", .{});
        std.debug.print("  - loop\n", .{});
        std.debug.print("  - sync\n", .{});
        std.debug.print("  - sync_era1\n\n", .{});
    }
}
