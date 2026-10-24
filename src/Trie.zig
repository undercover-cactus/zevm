//! Merkle Patricia Trie root computation.
//!
//! Only the *root hash* is produced — there's no persistent trie here, no
//! node store, and no proofs. That's deliberate: this exists so a replay can
//! check its state against the `stateRoot` every real block header already
//! carries, and for that the root is the whole answer. Building the trie
//! fresh from a sorted entry list is far simpler than maintaining one
//! incrementally, at the cost of being O(entries) per call rather than
//! O(changed) — see `State.stateRoot`'s doc comment for what that means in
//! practice.
//!
//! Keys are the *already-hashed* keys of Ethereum's "secure" trie
//! (`keccak256(address)` for accounts, `keccak256(slot)` for storage), but
//! nothing here requires that: keys are plain byte strings, which keeps the
//! standard variable-length-key test vectors usable as tests.

const std = @import("std");
const Rlp = @import("Rlp.zig");
const Hash = @import("Hash.zig").Hash;
const keccak256 = @import("Hash.zig").keccak256;

pub const Entry = struct {
    key: []const u8,
    value: []const u8,
};

/// `keccak256(rlp(""))`: the root of a trie with nothing in it. Every empty
/// storage trie hashes to this, so it's worth naming rather than recomputing.
pub const empty_root: Hash = 0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421;

fn lessThanKey(_: void, a: Entry, b: Entry) bool {
    return std.mem.lessThan(u8, a.key, b.key);
}

/// Nibbles are half-bytes, high nibble first — the unit trie paths are
/// measured in, so a 32-byte hashed key is a 64-step path.
fn nibbleAt(key: []const u8, i: usize) u8 {
    const byte = key[i / 2];
    return if (i % 2 == 0) byte >> 4 else byte & 0x0f;
}

fn nibbleCount(key: []const u8) usize {
    return key.len * 2;
}

/// "Hex prefix" encoding: packs a nibble path back into bytes, with a
/// leading flag nibble carrying whether this is a leaf and whether the path
/// has odd length (which is what makes an odd path representable at all).
fn compactEncode(
    allocator: std.mem.Allocator,
    key: []const u8,
    start: usize,
    end: usize,
    is_leaf: bool,
) ![]u8 {
    const count = end - start;
    const out = try allocator.alloc(u8, count / 2 + 1);
    var flag: u8 = if (is_leaf) 0x20 else 0x00;
    var i = start;
    if (count % 2 == 1) {
        flag |= 0x10 | nibbleAt(key, start);
        i += 1;
    }
    out[0] = flag;
    var o: usize = 1;
    while (i < end) : (i += 2) {
        out[o] = (nibbleAt(key, i) << 4) | nibbleAt(key, i + 1);
        o += 1;
    }
    return out;
}

/// How a parent refers to a child: by hash once the child's encoding reaches
/// 32 bytes, otherwise by embedding the child's RLP verbatim. The embedded
/// form is spliced in as an already-encoded item, *not* wrapped as a byte
/// string — getting that backwards is the classic way to produce roots that
/// look plausible and match nothing.
fn nodeReference(allocator: std.mem.Allocator, node_rlp: []const u8) ![]const u8 {
    if (node_rlp.len < 32) return allocator.dupe(u8, node_rlp);
    var buf: [32]u8 = undefined;
    std.mem.writeInt(u256, &buf, keccak256(node_rlp), .big);
    return Rlp.encodeBytes(allocator, &buf);
}

/// Builds the node covering `entries` (sorted, unique) at nibble depth
/// `depth`, returning its RLP encoding. The caller owns the result.
///
/// Every intermediate — a child's full encoding, the references to it, the
/// packed path — is freed before returning, so peak memory stays proportional
/// to the trie's *depth* rather than its size. That matters: a mainnet state
/// trie has tens of millions of nodes, and holding them all would cost more
/// than the state they describe.
fn buildNode(allocator: std.mem.Allocator, entries: []const Entry, depth: usize) ![]const u8 {
    if (entries.len == 0) return Rlp.encodeBytes(allocator, &.{});

    if (entries.len == 1) {
        const entry = entries[0];
        const path = try compactEncode(allocator, entry.key, depth, nibbleCount(entry.key), true);
        defer allocator.free(path);
        const encoded_path = try Rlp.encodeBytes(allocator, path);
        defer allocator.free(encoded_path);
        const encoded_value = try Rlp.encodeBytes(allocator, entry.value);
        defer allocator.free(encoded_value);
        return Rlp.encodeList(allocator, &.{ encoded_path, encoded_value });
    }

    // Entries are sorted, so whatever prefix the first and last share is
    // shared by everything between them too.
    const first = entries[0].key;
    const last = entries[entries.len - 1].key;
    const limit = @min(nibbleCount(first), nibbleCount(last));
    var prefix_end = depth;
    while (prefix_end < limit and nibbleAt(first, prefix_end) == nibbleAt(last, prefix_end)) {
        prefix_end += 1;
    }

    if (prefix_end > depth) {
        const child = try buildNode(allocator, entries, prefix_end);
        defer allocator.free(child);
        const reference = try nodeReference(allocator, child);
        defer allocator.free(reference);
        const path = try compactEncode(allocator, first, depth, prefix_end, false);
        defer allocator.free(path);
        const encoded_path = try Rlp.encodeBytes(allocator, path);
        defer allocator.free(encoded_path);
        return Rlp.encodeList(allocator, &.{ encoded_path, reference });
    }

    // No shared prefix left: branch on the nibble at `depth`. A key that
    // ends exactly here has no branch to take, so its value rides in the
    // node's 17th slot. Sorting puts such a key first, since a prefix always
    // compares less than what extends it.
    var items: [17][]const u8 = undefined;
    var filled: usize = 0;
    defer for (items[0..filled]) |item| allocator.free(item);

    var index: usize = 0;
    const has_own_value = nibbleCount(entries[0].key) == depth;
    if (has_own_value) index = 1;

    var nibble: u8 = 0;
    while (nibble < 16) : (nibble += 1) {
        const start = index;
        while (index < entries.len and nibbleAt(entries[index].key, depth) == nibble) index += 1;
        if (index == start) {
            items[nibble] = try Rlp.encodeBytes(allocator, &.{});
        } else {
            const child = try buildNode(allocator, entries[start..index], depth + 1);
            defer allocator.free(child);
            items[nibble] = try nodeReference(allocator, child);
        }
        filled += 1;
    }
    items[16] = if (has_own_value)
        try Rlp.encodeBytes(allocator, entries[0].value)
    else
        try Rlp.encodeBytes(allocator, &.{});
    filled += 1;

    return Rlp.encodeList(allocator, &items);
}

/// Root hash of a trie holding `entries`. Sorts `entries` in place; keys
/// must be unique. Every allocation made along the way is released before
/// returning, so only the 32-byte result survives.
///
/// The root is hashed even when the whole trie encodes to under 32 bytes —
/// the embed-if-short rule applies to a node's *reference from its parent*,
/// and the root has no parent.
pub fn hashRoot(allocator: std.mem.Allocator, entries: []Entry) !Hash {
    if (entries.len == 0) return empty_root;
    std.mem.sort(Entry, entries, {}, lessThanKey);

    const root_node = try buildNode(allocator, entries, 0);
    defer allocator.free(root_node);
    return keccak256(root_node);
}

/// The same root as `hashRoot`, with the 16 subtries under the root sorted
/// and built on separate threads. `allocator` must be thread-safe.
///
/// Keys sharing a first nibble form one of the root's 16 children and never
/// interact with any other, so for a large set of hashed keys (which always
/// spread over all 16) the root is a branch whose children can be computed
/// independently. Entries are partitioned by first nibble in place, so no
/// copy of a 181M-entry set is needed; each part is then sorted and built
/// exactly as `buildNode` would build it at depth 1. Anything that would not
/// make the root a branch of that shape (a small set, an empty key, every
/// key under one nibble) takes the serial path instead.
pub fn hashRootParallel(allocator: std.mem.Allocator, entries: []Entry) !Hash {
    if (entries.len < 4096) return hashRoot(allocator, entries);

    var counts = [_]usize{0} ** 16;
    for (entries) |e| {
        if (e.key.len == 0) return hashRoot(allocator, entries);
        counts[nibbleAt(e.key, 0)] += 1;
    }
    var nonempty: usize = 0;
    for (counts) |c| nonempty += @intFromBool(c != 0);
    if (nonempty < 2) return hashRoot(allocator, entries);

    // In-place partition by first nibble: `next[n]` is where bucket n's next
    // entry goes; every entry is swapped straight into its own bucket.
    var starts: [17]usize = undefined;
    starts[0] = 0;
    for (0..16) |n| starts[n + 1] = starts[n] + counts[n];
    var next: [16]usize = undefined;
    @memcpy(&next, starts[0..16]);
    for (0..16) |n| {
        while (next[n] < starts[n + 1]) {
            const target = nibbleAt(entries[next[n]].key, 0);
            if (target == n) {
                next[n] += 1;
            } else {
                std.mem.swap(Entry, &entries[next[n]], &entries[next[target]]);
                next[target] += 1;
            }
        }
    }

    var refs: [16][]const u8 = undefined;
    var failures: [16]?anyerror = @splat(null);
    var threads: [16]?std.Thread = @splat(null);
    defer for (threads) |t| if (t) |thread| thread.join();
    for (0..16) |n| {
        const part = entries[starts[n]..starts[n + 1]];
        if (part.len == 0) {
            refs[n] = try Rlp.encodeBytes(allocator, &.{});
            continue;
        }
        threads[n] = try std.Thread.spawn(.{}, buildChild, .{ allocator, part, &refs[n], &failures[n] });
    }
    for (&threads) |*t| if (t.*) |thread| {
        thread.join();
        t.* = null;
    };
    // Freed on every path: a failed child leaves an empty slice, which is a
    // no-op to free, so one failure cannot leak the others' references.
    defer for (refs) |r| allocator.free(r);
    for (failures) |failure| if (failure) |err| return err;

    // The root branch: the 16 child references, then an empty value slot
    // (no key ends at depth 0, every one is at least a byte long).
    var items: [17][]const u8 = undefined;
    @memcpy(items[0..16], &refs);
    items[16] = try Rlp.encodeBytes(allocator, &.{});
    defer allocator.free(items[16]);
    const root_node = try Rlp.encodeList(allocator, &items);
    defer allocator.free(root_node);
    return keccak256(root_node);
}

fn buildChild(allocator: std.mem.Allocator, part: []Entry, ref: *[]const u8, failure: *?anyerror) void {
    std.mem.sort(Entry, part, {}, lessThanKey);
    const child = buildNode(allocator, part, 1) catch |err| {
        failure.* = err;
        ref.* = &.{};
        return;
    };
    defer allocator.free(child);
    ref.* = nodeReference(allocator, child) catch |err| {
        failure.* = err;
        ref.* = &.{};
        return;
    };
}

test "an empty trie hashes to keccak256 of the empty RLP string" {
    var none: [0]Entry = .{};
    try std.testing.expectEqual(empty_root, try hashRoot(std.testing.allocator, &none));
    // The named constant should be exactly that, not a transcribed literal.
    try std.testing.expectEqual(empty_root, keccak256(&[_]u8{0x80}));
}

test "a single short entry embeds nothing and still hashes its root" {
    var entries = [_]Entry{.{ .key = "a", .value = "b" }};
    const root = try hashRoot(std.testing.allocator, &entries);
    // Built by hand: leaf path "a" is nibbles 6,1 — even length, not odd —
    // so the compact encoding is 0x20 0x61, and the node is a two-item list.
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const expected = try Rlp.encodeList(a, &.{
        try Rlp.encodeBytes(a, &[_]u8{ 0x20, 0x61 }),
        try Rlp.encodeBytes(a, "b"),
    });
    try std.testing.expectEqual(keccak256(expected), root);
}

test "the classic three-key trie matches its published root" {
    // From the Merkle Patricia trie specification's own worked example.
    var entries = [_]Entry{
        .{ .key = "doe", .value = "reindeer" },
        .{ .key = "dog", .value = "puppy" },
        .{ .key = "dogglesworth", .value = "cat" },
    };
    try std.testing.expectEqual(
        @as(Hash, 0x8aad789dff2f538bca5d8ea56e8abe10f4c7ba3a5dea95fea4cd6e7c3a1168d3),
        try hashRoot(std.testing.allocator, &entries),
    );
}

test "a trie with a key that is a prefix of another uses the branch value slot" {
    // "do" ends exactly where "dog"/"doge" branch, exercising the 17th slot.
    var entries = [_]Entry{
        .{ .key = "do", .value = "verb" },
        .{ .key = "dog", .value = "puppy" },
        .{ .key = "doge", .value = "coin" },
        .{ .key = "horse", .value = "stallion" },
    };
    try std.testing.expectEqual(
        @as(Hash, 0x5991bb8c6514148a29db676a14ac506cd2cd5775ace63c30a4fe457715e9ac84),
        try hashRoot(std.testing.allocator, &entries),
    );
}

test "insertion order does not affect the root" {
    var forward = [_]Entry{
        .{ .key = "doe", .value = "reindeer" },
        .{ .key = "dog", .value = "puppy" },
        .{ .key = "dogglesworth", .value = "cat" },
    };
    var backward = [_]Entry{
        .{ .key = "dogglesworth", .value = "cat" },
        .{ .key = "dog", .value = "puppy" },
        .{ .key = "doe", .value = "reindeer" },
    };
    try std.testing.expectEqual(
        try hashRoot(std.testing.allocator, &forward),
        try hashRoot(std.testing.allocator, &backward),
    );
}

test "long values force hashed child references rather than embedding" {
    // Values well over 32 bytes make every node too big to embed, so this
    // exercises the hash-reference path throughout.
    const long = "0123456789abcdef0123456789abcdef0123456789abcdef";
    var entries = [_]Entry{
        .{ .key = "aaa", .value = long },
        .{ .key = "aab", .value = long },
        .{ .key = "abb", .value = long },
    };
    const root = try hashRoot(std.testing.allocator, &entries);
    try std.testing.expect(root != empty_root);
    // Same keys, one value changed, must move the root.
    var changed = [_]Entry{
        .{ .key = "aaa", .value = long },
        .{ .key = "aab", .value = long },
        .{ .key = "abb", .value = "different" },
    };
    try std.testing.expect(try hashRoot(std.testing.allocator, &changed) != root);
}

test "the parallel root matches the serial root" {
    var prng: std.Random.DefaultPrng = .init(0x74726965);
    const rand = prng.random();
    const allocator = std.testing.allocator;
    // Hashed-style 32-byte keys at sizes on both sides of the serial cutoff,
    // plus a set whose keys all share a first nibble (serial fallback).
    for ([_]usize{ 10, 4095, 4096, 20_000 }) |count| for ([_]bool{ false, true }) |one_nibble| {
        const keys = try allocator.alloc([32]u8, count);
        defer allocator.free(keys);
        const values = try allocator.alloc([8]u8, count);
        defer allocator.free(values);
        const a = try allocator.alloc(Entry, count);
        defer allocator.free(a);
        const b = try allocator.alloc(Entry, count);
        defer allocator.free(b);
        for (keys, values, 0..) |*k, *v, i| {
            rand.bytes(k);
            if (one_nibble) k[0] = 0x30 | (k[0] & 0x0f);
            std.mem.writeInt(u64, k[24..32], i, .big); // unique
            std.mem.writeInt(u64, v, i * 7 + 1, .big);
            a[i] = .{ .key = k, .value = v };
            b[i] = a[i];
        }
        try std.testing.expectEqual(try hashRoot(allocator, a), try hashRootParallel(allocator, b));
    };
}
