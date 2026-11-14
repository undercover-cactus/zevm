//! Ethereum's protocol upgrades, in chronological order. A closed,
//! protocol-defined set, hence a plain enum rather than something
//! extensible.
//!
//! Only `frontier` through `petersburg` have any actual behavior modeled
//! (see `Evm.processBlock`'s guard); the rest exists so the block-to-fork
//! mapping is complete.
//!
//! `constantinople` and `petersburg` share block 7,280,000 on mainnet:
//! Constantinople shipped, but its EIP-1283 SSTORE repricing was withdrawn
//! by Petersburg in the same upgrade, so no mainnet block ever ran under
//! Constantinople's rules alone.

const std = @import("std");

pub const Fork = enum {
    frontier,
    homestead,
    dao,
    tangerine_whistle,
    spurious_dragon,
    byzantium,
    constantinople,
    petersburg,
    istanbul,
    muir_glacier,
    berlin,
    london,
    arrow_glacier,
    gray_glacier,
    merge,
    shanghai,
    cancun,
    prague,
    osaka,

    /// Mainnet activation block for each fork, oldest first. `at` walks
    /// this looking for the last entry at or before a given block number.
    const activations = [_]struct { fork: Fork, block: u64 }{
        .{ .fork = .frontier, .block = 0 },
        .{ .fork = .homestead, .block = 1_150_000 },
        .{ .fork = .dao, .block = 1_920_000 },
        .{ .fork = .tangerine_whistle, .block = 2_463_000 },
        .{ .fork = .spurious_dragon, .block = 2_675_000 },
        .{ .fork = .byzantium, .block = 4_370_000 },
        .{ .fork = .constantinople, .block = 7_280_000 },
        .{ .fork = .petersburg, .block = 7_280_000 }, // same block: Constantinople was repriced same-day
        .{ .fork = .istanbul, .block = 9_069_000 },
        .{ .fork = .muir_glacier, .block = 9_200_000 },
        .{ .fork = .berlin, .block = 12_244_000 },
        .{ .fork = .london, .block = 12_965_000 },
        .{ .fork = .arrow_glacier, .block = 13_773_000 },
        .{ .fork = .gray_glacier, .block = 15_050_000 },
        .{ .fork = .merge, .block = 15_537_394 },
        .{ .fork = .shanghai, .block = 17_034_870 },
        .{ .fork = .cancun, .block = 19_426_587 },
        .{ .fork = .prague, .block = 22_431_084 },
        .{ .fork = .osaka, .block = 23_935_694 },
    };

    pub fn at(block_number: u64) Fork {
        var result: Fork = .frontier;
        for (activations) |entry| {
            if (entry.block > block_number) break;
            result = entry.fork;
        }
        return result;
    }

    /// Whether this fork activated at or before `other` (forks are declared
    /// in chronological order above, so enum ordinal order matches
    /// activation order).
    pub fn atLeast(self: Fork, other: Fork) bool {
        return @intFromEnum(self) >= @intFromEnum(other);
    }
};

test "before Homestead is Frontier" {
    try std.testing.expectEqual(Fork.frontier, Fork.at(1_149_999));
}

test "Homestead's own activation block is already Homestead" {
    try std.testing.expectEqual(Fork.homestead, Fork.at(1_150_000));
}

test "far in the future resolves to the latest known fork" {
    try std.testing.expectEqual(Fork.osaka, Fork.at(30_000_000));
}

test "atLeast compares chronological order, inclusive of equal forks" {
    try std.testing.expect(Fork.tangerine_whistle.atLeast(.homestead));
    try std.testing.expect(Fork.tangerine_whistle.atLeast(.tangerine_whistle));
    try std.testing.expect(!Fork.homestead.atLeast(.tangerine_whistle));
}
