const std = @import("std");
const zevm = @import("zevm");

fn millisSince(io: std.Io, start: std.Io.Clock.Timestamp) f64 {
    const elapsed = start.durationTo(std.Io.Clock.Timestamp.now(io, .awake));
    return @as(f64, @floatFromInt(elapsed.raw.nanoseconds)) / 1_000_000.0;
}

pub fn main(io: std.Io, args: []const []const u8) anyerror!void {
    _ = args;
    var gpa = std.heap.DebugAllocator(.{}){};
    defer std.debug.assert(gpa.deinit() == .ok);
    const allocator = gpa.allocator();

    var state = zevm.State.init(allocator);
    defer state.deinit();

    // Load genesis: reth's copy of Ethereum mainnet's fixed genesis
    // allocation, embedded at compile time since it's fixed protocol data.
    // https://github.com/paradigmxyz/reth/blob/main/crates/chainspec/res/genesis/mainnet.json
    const genesis_json = @embedFile("data/mainnet_genesis.json");
    const parsed = try std.json.parseFromSlice(std.json.Value, allocator, genesis_json, .{});
    defer parsed.deinit();

    var accounts = parsed.value.object.get("alloc").?.object.iterator();
    while (accounts.next()) |entry| {
        var address_bytes: [20]u8 = undefined;
        _ = try std.fmt.hexToBytes(&address_bytes, entry.key_ptr.*);
        const address: zevm.Address = std.mem.readInt(u160, &address_bytes, .big);

        const balance_hex = entry.value_ptr.object.get("balance").?.string;
        const balance = try std.fmt.parseInt(u256, balance_hex[2..], 16); // strip "0x"

        try state.setBalance(address, balance);
    }
    std.debug.print("loaded {d} genesis accounts\n", .{state.accounts.count()});

    // Replay real mainnet blocks 0..46299, continuously from genesis (a
    // discontinuous window would misreport senders as insolvent). Read from
    // disk rather than @embedFile: this fixture is tens of MB.
    const blocks_json = try std.Io.Dir.cwd().readFileAlloc(
        io,
        "examples/data/mainnet_blocks_0_46299.json",
        allocator,
        .unlimited,
    );
    defer allocator.free(blocks_json);

    const blocks_parsed = try std.json.parseFromSlice(std.json.Value, allocator, blocks_json, .{});
    defer blocks_parsed.deinit();

    // .awake is the monotonic clock, immune to wall-clock adjustments.
    // Started here, after loading/parsing, so this measures EVM processing
    // time only, not I/O + JSON parsing.
    const start = std.Io.Clock.Timestamp.now(io, .awake);

    var evm = zevm.Evm{ .allocator = allocator, .state = &state };

    for (blocks_parsed.value.array.items) |block_json| {
        const block = block_json.object;

        var miner_bytes: [20]u8 = undefined;
        _ = try std.fmt.hexToBytes(&miner_bytes, block.get("miner").?.string[2..]);

        var uncles: std.ArrayList(zevm.Block.Uncle) = .empty;
        defer uncles.deinit(allocator);
        for (block.get("uncles").?.array.items) |uncle_json| {
            // Uncles fetched but not yet enriched are still a raw hash
            // string rather than a {hash, number, miner} object; skip those
            // instead of failing the whole replay over incomplete data.
            const uncle = switch (uncle_json) {
                .object => |o| o,
                .string => continue,
                else => unreachable,
            };
            var uncle_miner_bytes: [20]u8 = undefined;
            _ = try std.fmt.hexToBytes(&uncle_miner_bytes, uncle.get("miner").?.string[2..]);
            try uncles.append(allocator, .{
                .number = try std.fmt.parseInt(u64, uncle.get("number").?.string[2..], 16),
                .miner = std.mem.readInt(u160, &uncle_miner_bytes, .big),
            });
        }

        var entries: std.ArrayList(zevm.Block.Entry) = .empty;
        defer entries.deinit(allocator);
        var tx_data: std.ArrayList([]u8) = .empty;
        defer {
            for (tx_data.items) |d| allocator.free(d);
            tx_data.deinit(allocator);
        }

        for (block.get("transactions").?.array.items) |tx_json| {
            const tx = tx_json.object;

            var from_bytes: [20]u8 = undefined;
            _ = try std.fmt.hexToBytes(&from_bytes, tx.get("from").?.string[2..]);

            const to: ?zevm.Address = switch (tx.get("to").?) {
                .null => null,
                .string => |s| blk: {
                    var to_bytes: [20]u8 = undefined;
                    _ = try std.fmt.hexToBytes(&to_bytes, s[2..]);
                    break :blk std.mem.readInt(u160, &to_bytes, .big);
                },
                else => unreachable,
            };

            const input_hex = tx.get("input").?.string[2..];
            const data = try allocator.alloc(u8, input_hex.len / 2);
            _ = try std.fmt.hexToBytes(data, input_hex);
            try tx_data.append(allocator, data);

            try entries.append(allocator, .{
                .from = std.mem.readInt(u160, &from_bytes, .big),
                .tx = .{
                    .nonce = try std.fmt.parseInt(u64, tx.get("nonce").?.string[2..], 16),
                    .gas_price = try std.fmt.parseInt(u256, tx.get("gasPrice").?.string[2..], 16),
                    .gas_limit = try std.fmt.parseInt(u64, tx.get("gas").?.string[2..], 16),
                    .to = to,
                    .value = try std.fmt.parseInt(u256, tx.get("value").?.string[2..], 16),
                    .data = data,
                    .v = try std.fmt.parseInt(u64, tx.get("v").?.string[2..], 16),
                    .r = try std.fmt.parseInt(u256, tx.get("r").?.string[2..], 16),
                    .s = try std.fmt.parseInt(u256, tx.get("s").?.string[2..], 16),
                },
            });
        }

        const number = try std.fmt.parseInt(u64, block.get("number").?.string[2..], 16);

        try evm.processBlock(.{
            .number = number,
            .miner = std.mem.readInt(u160, &miner_bytes, .big),
            .transactions = entries.items,
            .uncles = uncles.items,
            .timestamp = try std.fmt.parseInt(u64, block.get("timestamp").?.string[2..], 16),
            .gas_limit = try std.fmt.parseInt(u64, block.get("gasLimit").?.string[2..], 16),
            .difficulty = try std.fmt.parseInt(u256, block.get("difficulty").?.string[2..], 16),
        });

        if (entries.items.len != 0 or number % 5000 == 0) {
            std.debug.print("processed block {d} ({d} txs, {d} uncles)\n", .{ number, entries.items.len, uncles.items.len });
        }
    }

    std.debug.print("done: {d} accounts touched in {d:.2}ms\n", .{ state.accounts.count(), millisSince(io, start) });
}
