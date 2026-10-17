//! The pure-Zig counterpart to `rzevm/examples/sync_era1.rs`: reads the
//! same `.era1` files (`data/era1/`, populated by `make download-era1`) and
//! replays them through zevm natively, no FFI or Rust process involved.
//!
//! era1's record layout and the legacy-transaction signing-hash
//! reconstruction mirror `sync_era1.rs`'s own doc comments (e2store's
//! four-record-per-block layout, EIP-155's chain_id/0/0 padding for `v > 28`).

const std = @import("std");
const zevm = @import("zevm");
const Snappy = @import("Snappy.zig");
const secp256k1 = zevm.Secp256k1;
const Secp256k1 = secp256k1.Secp256k1;

// DEBUG: era1-replay divergence hunt scaffolding, same spirit as
// `State.debug_enabled`. Gated by an explicit boolean rather than a
// sentinel block number, so block 0 is not accidentally special.
const debug_dump_block_enabled = false;
const debug_dump_block: u64 = 6831202;

fn millisSince(io: std.Io, start: std.Io.Clock.Timestamp) f64 {
    const elapsed = start.durationTo(std.Io.Clock.Timestamp.now(io, .awake));
    return @as(f64, @floatFromInt(elapsed.raw.nanoseconds)) / 1_000_000.0;
}

const blocks_per_file: u64 = 8192;

fn bytesToU256(bytes: []const u8) u256 {
    var out: u256 = 0;
    for (bytes) |b| out = (out << 8) | b;
    return out;
}

fn bytesToU64(bytes: []const u8) u64 {
    return @intCast(bytesToU256(bytes));
}

fn bytesToAddress(bytes: []const u8) zevm.Address {
    var buf: [20]u8 = [_]u8{0} ** 20;
    @memcpy(buf[20 - bytes.len ..], bytes);
    return std.mem.readInt(u160, &buf, .big);
}

fn padTo32(bytes: []const u8) [32]u8 {
    var out: [32]u8 = [_]u8{0} ** 32;
    @memcpy(out[32 - bytes.len ..], bytes);
    return out;
}

const DecodedHeader = struct {
    number: u64,
    /// EIP-1559 (London) appended `baseFeePerGas` as the header's 16th
    /// field. Zero before that.
    base_fee: u256,
    miner: zevm.Address,
    timestamp: u64,
    gas_limit: u64,
    difficulty: u256,
    /// What this block commits its whole world state to. Free ground truth
    /// for validating a replay: no RPC, no trusted third party, just the
    /// era1 files already on disk.
    state_root: zevm.Hash,
    /// Total gas the block's transactions used, also committed to by the
    /// header. Far weaker than `state_root` (it says nothing about *values*
    /// written) but free to check and, unlike the root, cheap enough to
    /// check on every single block.
    gas_used: u64,
};

/// Frontier-era headers RLP-encode as a 15-field list (`parentHash,
/// unclesHash, coinbase, stateRoot, transactionsRoot, receiptsRoot,
/// logsBloom, difficulty, number, gasLimit, gasUsed, timestamp, extraData,
/// mixHash, nonce`); everything except coinbase/difficulty/number/
/// gasLimit/timestamp is decoded and discarded.
fn decodeHeader(header: zevm.Rlp.Item) DecodedHeader {
    return .{
        .number = bytesToU64(header.list[8].string),
        .base_fee = if (header.list.len > 15) bytesToU256(header.list[15].string) else 0,
        .miner = bytesToAddress(header.list[2].string),
        .timestamp = bytesToU64(header.list[11].string),
        .gas_limit = bytesToU64(header.list[9].string),
        .difficulty = bytesToU256(header.list[7].string),
        .state_root = bytesToU256(header.list[3].string),
        .gas_used = bytesToU64(header.list[10].string),
    };
}

/// An uncle is encoded as a full header; only coinbase/number matter here.
fn decodeUncle(uncle: zevm.Rlp.Item) zevm.Block.Uncle {
    return .{
        .number = bytesToU64(uncle.list[8].string),
        .miner = bytesToAddress(uncle.list[2].string),
    };
}

/// Derives a legacy transaction's sender via ECDSA signature recovery over
/// the RLP encoding of its first 6 fields, plus chain_id/0/0 for EIP-155
/// transactions (`v > 28`), which shouldn't occur in this block range but
/// is kept for correctness rather than assumed away.
///
/// Uses `zevm.Secp256k1` directly rather than going through a full
/// `ECRECOVER` precompile call: this is driver-side sender derivation, a
/// different concern from the EVM's own `Precompiles.ecrecover`.
fn deriveSender(allocator: std.mem.Allocator, secp: Secp256k1, fields: []const zevm.Rlp.Item) !zevm.Address {
    var parts: std.ArrayList([]const u8) = .empty;
    defer {
        for (parts.items) |p| allocator.free(p);
        parts.deinit(allocator);
    }
    for (fields[0..6]) |f| try parts.append(allocator, try zevm.Rlp.encodeBytes(allocator, f.string));

    const v = bytesToU64(fields[6].string);
    if (v > 28) {
        const chain_id = (v - 35) / 2;
        try parts.append(allocator, try zevm.Rlp.encodeInt(allocator, chain_id));
        try parts.append(allocator, try zevm.Rlp.encodeInt(allocator, 0));
        try parts.append(allocator, try zevm.Rlp.encodeInt(allocator, 0));
    }

    const signed_payload = try zevm.Rlp.encodeList(allocator, parts.items);
    defer allocator.free(signed_payload);

    var hash: secp256k1.Message = undefined;
    std.mem.writeInt(u256, &hash, zevm.keccak256(signed_payload), .big);

    const recid: u8 = switch (v) {
        0, 1 => @intCast(v),
        27, 28 => @intCast(v - 27),
        else => @intCast((v - 35) % 2),
    };
    return recoverAddress(secp, hash, fields[7].string, fields[8].string, recid);
}

/// The address that signed `hash`, given the signature's `r`, `s` and
/// recovery id.
fn recoverAddress(secp: Secp256k1, hash: secp256k1.Message, r: []const u8, s: []const u8, recid: u8) !zevm.Address {
    var sig: secp256k1.Signature = undefined;
    sig[0..32].* = padTo32(r);
    sig[32..64].* = padTo32(s);
    sig[64] = recid;

    const pubkey = try secp.recoverPubkey(hash, sig);
    // Skip `pubkey[0]`, the uncompressed-key format byte (0x04). An
    // Ethereum address is the low 160 bits of Keccak256 over the raw
    // 64-byte (x, y) coordinates alone.
    return @truncate(zevm.keccak256(pubkey[1..65]));
}

/// Re-encodes a decoded item. Only used to rebuild a typed transaction's
/// signing payload, whose access list is a nested list; a valid
/// transaction's encoding is canonical, so this reproduces it exactly.
fn encodeItem(allocator: std.mem.Allocator, item: zevm.Rlp.Item) ![]u8 {
    switch (item) {
        .string => |bytes| return zevm.Rlp.encodeBytes(allocator, bytes),
        .list => |items| {
            var parts: std.ArrayList([]const u8) = .empty;
            defer {
                for (parts.items) |part| allocator.free(part);
                parts.deinit(allocator);
            }
            for (items) |sub| try parts.append(allocator, try encodeItem(allocator, sub));
            return zevm.Rlp.encodeList(allocator, parts.items);
        },
    }
}

/// The address that signed `tx_item`. This is the expensive half of reading
/// a transaction (an ECDSA public-key recovery, ~30us), and it depends on
/// nothing but the transaction's own bytes, which is what lets
/// `recoverSenders` run it for a whole file at once across every core.
/// `allocator` only holds scratch that is freed before returning.
fn txSender(allocator: std.mem.Allocator, secp: Secp256k1, tx_item: zevm.Rlp.Item) !zevm.Address {
    // EIP-2718: a typed transaction sits in the body as a byte string,
    // `type || payload`, where a Legacy one is a bare list.
    if (tx_item == .string) return typedSender(allocator, secp, tx_item.string);
    return deriveSender(allocator, secp, tx_item.list);
}

/// How many fields a typed transaction carries before its signature
/// (`y_parity, r, s`), or null for a type this decoder does not know.
/// EIP-1559 (type 2) splits EIP-2930's single `gas_price` into a tip cap and
/// a fee cap, so everything after `nonce` sits one field later.
fn signedFieldCount(tx_type: u8) ?usize {
    return switch (tx_type) {
        0x01 => 8,
        0x02 => 9,
        else => null,
    };
}

/// A typed transaction signs `keccak(type || rlp(every field before the
/// signature))`.
fn typedSender(allocator: std.mem.Allocator, secp: Secp256k1, bytes: []const u8) !zevm.Address {
    if (bytes.len == 0) return error.UnsupportedTransactionType;
    const signed_count = signedFieldCount(bytes[0]) orelse return error.UnsupportedTransactionType;
    const payload = try zevm.Rlp.decode(allocator, bytes[1..]);
    defer payload.deinit(allocator);
    const fields = payload.list;
    if (fields.len != signed_count + 3) return error.MalformedTransaction;

    const signed = try encodeItem(allocator, .{ .list = fields[0..signed_count] });
    defer allocator.free(signed);
    const preimage = try allocator.alloc(u8, signed.len + 1);
    defer allocator.free(preimage);
    preimage[0] = bytes[0];
    @memcpy(preimage[1..], signed);
    var hash: secp256k1.Message = undefined;
    std.mem.writeInt(u256, &hash, zevm.keccak256(preimage), .big);

    const y_parity = bytesToU64(fields[signed_count].string);
    if (y_parity > 1) return error.MalformedTransaction;
    return recoverAddress(secp, hash, fields[signed_count + 1].string, fields[signed_count + 2].string, @intCast(y_parity));
}

/// `tx_item`'s string fields borrow directly from the decompressed body
/// buffer the caller owns, kept alive as long as one block's entries are in use.
/// A typed transaction's decoded payload and access list are allocated in
/// `arena`, which must live as long too. `from` comes from `txSender`.
fn parseTransaction(arena: std.mem.Allocator, tx_item: zevm.Rlp.Item, from: zevm.Address) !zevm.Block.Entry {
    if (tx_item == .string) return parseTypedTransaction(arena, tx_item.string, from);
    const fields = tx_item.list;
    const to_bytes = fields[3].string;
    return .{
        .from = from,
        .tx = .{
            .nonce = bytesToU64(fields[0].string),
            .gas_price = bytesToU256(fields[1].string),
            .gas_limit = bytesToU64(fields[2].string),
            .to = if (to_bytes.len == 0) null else bytesToAddress(to_bytes),
            .value = bytesToU256(fields[4].string),
            .data = fields[5].string,
            .v = bytesToU64(fields[6].string),
            .r = bytesToU256(fields[7].string),
            .s = bytesToU256(fields[8].string),
        },
    };
}

/// EIP-2930 (type 1, Berlin):
/// `rlp([chain_id, nonce, gas_price, gas_limit, to, value, data, access_list,
/// y_parity, r, s])`.
/// EIP-1559 (type 2, London):
/// `rlp([chain_id, nonce, max_priority_fee, max_fee, gas_limit, to, value,
/// data, access_list, y_parity, r, s])`, the same shape with `gas_price`
/// split in two, so the fields after it are read one position later.
fn parseTypedTransaction(arena: std.mem.Allocator, bytes: []const u8, from: zevm.Address) !zevm.Block.Entry {
    if (bytes.len == 0) return error.UnsupportedTransactionType;
    const signed_count = signedFieldCount(bytes[0]) orelse return error.UnsupportedTransactionType;
    const payload = try zevm.Rlp.decode(arena, bytes[1..]);
    const fields = payload.list;
    if (fields.len != signed_count + 3) return error.MalformedTransaction;
    const fee_market = bytes[0] == 0x02;
    const shift: usize = if (fee_market) 1 else 0;

    const access_list = fields[7 + shift].list;
    const entries = try arena.alloc(zevm.AccessListEntry, access_list.len);
    for (access_list, entries) |item, *entry| {
        const keys = try arena.alloc(u256, item.list[1].list.len);
        for (item.list[1].list, keys) |key, *out| out.* = bytesToU256(key.string);
        entry.* = .{ .address = bytesToAddress(item.list[0].string), .storage_keys = keys };
    }

    const to_bytes = fields[4 + shift].string;
    return .{
        .from = from,
        .tx = .{
            .nonce = bytesToU64(fields[1].string),
            // For type 2 this is `max_fee`; see `Transaction.gas_price`.
            .gas_price = bytesToU256(fields[2 + shift].string),
            .gas_limit = bytesToU64(fields[3 + shift].string),
            .to = if (to_bytes.len == 0) null else bytesToAddress(to_bytes),
            .value = bytesToU256(fields[5 + shift].string),
            .data = fields[6 + shift].string,
            .v = bytesToU64(fields[signed_count].string),
            .r = bytesToU256(fields[signed_count + 1].string),
            .s = bytesToU256(fields[signed_count + 2].string),
            .chain_id = bytesToU256(fields[0].string),
            .access_list = entries,
            .max_priority_fee = if (fee_market) bytesToU256(fields[2].string) else null,
        },
    };
}

/// Recovers `senders[i]` for every `items[i]`, split across one thread per
/// core. Each worker owns a contiguous slice and its own scratch arena, and
/// libsecp256k1 only ever reads the shared context, so the workers share
/// nothing mutable. The result cannot depend on how the work is split.
fn recoverSenders(secp: Secp256k1, items: []const zevm.Rlp.Item, senders: []zevm.Address) !void {
    const max_threads = 64;
    const cpus = std.Thread.getCpuCount() catch 1;
    // Below a few hundred transactions a thread costs more than it saves.
    const thread_count = @max(1, @min(max_threads, @min(cpus, items.len / 256)));

    var threads: [max_threads]std.Thread = undefined;
    var failures: [max_threads]?anyerror = @splat(null);
    const per_thread = (items.len + thread_count - 1) / thread_count;
    var spawned: usize = 0;
    while (spawned < thread_count) : (spawned += 1) {
        const lo = @min(items.len, spawned * per_thread);
        const hi = @min(items.len, lo + per_thread);
        threads[spawned] = std.Thread.spawn(.{}, recoverSendersWorker, .{ secp, items[lo..hi], senders[lo..hi], &failures[spawned] }) catch |err| {
            for (threads[0..spawned]) |t| t.join();
            return err;
        };
    }
    for (threads[0..spawned]) |t| t.join();
    for (failures[0..spawned]) |failure| if (failure) |err| return err;
}

fn recoverSendersWorker(secp: Secp256k1, items: []const zevm.Rlp.Item, senders: []zevm.Address, failure: *?anyerror) void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    for (items, senders) |item, *sender| {
        sender.* = txSender(arena.allocator(), secp, item) catch |err| {
            failure.* = err;
            return;
        };
        _ = arena.reset(.retain_capacity);
    }
}

const record_type = struct {
    const version = [2]u8{ 0x65, 0x32 }; // "e2"
    const compressed_header = [2]u8{ 0x03, 0x00 };
    const compressed_body = [2]u8{ 0x04, 0x00 };
    const compressed_receipts = [2]u8{ 0x05, 0x00 };
};

/// One e2store record: an 8-byte header (2-byte type, 4-byte little-endian
/// length, 2 reserved bytes) followed by `length` bytes of data.
const Record = struct {
    kind: [2]u8,
    data: []const u8,
};

fn readRecords(allocator: std.mem.Allocator, bytes: []const u8) ![]Record {
    var records: std.ArrayList(Record) = .empty;
    errdefer records.deinit(allocator);
    var pos: usize = 0;
    while (pos + 8 <= bytes.len) {
        const kind = bytes[pos..][0..2].*;
        const length = std.mem.readInt(u32, bytes[pos + 2 ..][0..4], .little);
        const data = bytes[pos + 8 .. pos + 8 + length];
        try records.append(allocator, .{ .kind = kind, .data = data });
        pos += 8 + length;
    }
    return records.toOwnedSlice(allocator);
}

fn lessThanStr(_: void, a: []const u8, b: []const u8) bool {
    return std.mem.lessThan(u8, a, b);
}

/// The `stateRoot` a given block's real header commits to, read straight out
/// of the era1 files. Ground truth with no network and no trusted third
/// party — the same bytes the replay is being checked against.
fn era1StateRoot(allocator: std.mem.Allocator, io: std.Io, block: u64) !zevm.Hash {
    var dir = try std.Io.Dir.cwd().openDir(io, "data/era1", .{ .iterate = true });
    defer dir.close(io);
    const names = try era1FileNames(allocator, io, dir);
    defer {
        for (names) |n| allocator.free(n);
        allocator.free(names);
    }

    const file_index = block / blocks_per_file;
    if (file_index >= names.len) return error.BlockNotInEra1Files;
    const raw = try dir.readFileAlloc(io, names[file_index], allocator, .unlimited);
    defer allocator.free(raw);
    const records = try readRecords(allocator, raw);
    defer allocator.free(records);

    // One version record, then four per block (header, body, receipts,
    // total difficulty) — same layout the replay loop walks.
    const index = 1 + (block % blocks_per_file) * 4;
    if (index >= records.len) return error.BlockNotInEra1Files;
    const header_rlp = try Snappy.frameDecompress(allocator, records[index].data);
    defer allocator.free(header_rlp);
    const item = try zevm.Rlp.decode(allocator, header_rlp);
    defer item.deinit(allocator);

    const header = decodeHeader(item);
    if (header.number != block) return error.Era1BlockIndexMismatch;
    return header.state_root;
}

fn era1FileNames(allocator: std.mem.Allocator, io: std.Io, dir: std.Io.Dir) ![][]u8 {
    var files: std.ArrayList([]u8) = .empty;
    errdefer {
        for (files.items) |f| allocator.free(f);
        files.deinit(allocator);
    }

    var it = dir.iterate();
    while (try it.next(io)) |entry| {
        if (!std.mem.endsWith(u8, entry.name, ".era1")) continue;
        try files.append(allocator, try allocator.dupe(u8, entry.name));
    }

    std.mem.sort([]u8, files.items, {}, lessThanStr);
    return files.toOwnedSlice(allocator);
}

pub fn main(io: std.Io, args: []const []const u8) anyerror!void {
    // Not `DebugAllocator` (unlike `sync.zig`'s smaller benchmark): this
    // driver's era1 decoding does a huge number of small allocations, and
    // `DebugAllocator`'s per-allocation bookkeeping dominates runtime at
    // that volume, same reasoning `ffi.zig` uses `smp_allocator` for.
    const allocator = std.heap.smp_allocator;

    // Debugging aids for iterating on a divergence/hang found deep into a
    // multi-million-block replay without re-running from genesis each time:
    //   --dump-at <block> <path>   dump full state right after that block,
    //                              then exit (block must be a file's last
    //                              block, i.e. (block+1) % 8192 == 0).
    //   --resume-from <path>       load state from a dump instead of
    //                              genesis, skip straight to the block
    //                              after it. The dump also carries
    //                              BLOCKHASH's 256-block window, so a
    //                              resumed run's BLOCKHASH results match a
    //                              from-genesis run from the very next
    //                              block on.
    var dump_at_block: ?u64 = null;
    // Checks the state root after *every* block rather than only at the
    // dump point, stopping at the first mismatch. Rebuilding the whole trie
    // per block is far too slow to leave on for a full replay, but early
    // state is small enough that it costs little — and it names the exact
    // block a divergence begins, which a chunk-boundary check can only
    // narrow to 65,536 candidates.
    var verify_roots = false;
    // Checks the root at exactly one block, then stops. Rebuilding the trie
    // per block (`--verify-roots`) costs ~0.4s once the account count reaches
    // the hundreds of thousands, which is hours across a whole chunk; one
    // check per run makes a binary search over a chunk far cheaper than
    // walking it — ~log2(65536) = 16 runs instead of 65,536 rebuilds.
    var root_at_block: ?u64 = null;
    // Compares each block's total gas against its header, stopping at the
    // first block that disagrees. Catches any gas divergence at the exact
    // block for the cost of one addition per transaction, where a state root
    // bisect over the same range costs ~16 full trie builds. Blind to a
    // divergence that spends the right gas and stores the wrong value, so it
    // narrows rather than replaces the root check.
    var check_gas = false;
    // Computes the state root of an existing snapshot in a fresh process. A
    // replay process still holds its journal and allocator churn when it
    // reaches a chunk boundary; loading the same state cold costs far less,
    // which is what makes the very largest checkpoints verifiable at all.
    var snapshot_root_path: ?[]const u8 = null;
    // Computes a snapshot's root through `loadSnapshot` and `State.stateRoot`
    // rather than the streaming `snapshotStateRoot`. The two must agree:
    // `--snapshot-root` reads the file directly, while this exercises the
    // lazy read-through state and the merged base/overlay scan that the
    // replay itself depends on. Disagreement means the lazy path is wrong.
    var lazy_root_path: ?[]const u8 = null;
    // Reads a snapshot and writes it back out. Exists to migrate checkpoints
    // written before `writeSnapshot` sorted each account's storage slots:
    // the read-in-place `State.Base` binary-searches those slots, so an
    // unsorted file would silently answer wrongly. One-off, and it loads the
    // old way, so it needs the memory the lazy path exists to avoid.
    var rewrite_in: ?[]const u8 = null;
    var rewrite_out: ?[]const u8 = null;
    var dump_path: []const u8 = "";
    var resume_path: ?[]const u8 = null;
    // --scan-miner <address> <end_block>   header-only scan (no state, no
    //                                      tx parsing, no EVM execution) for
    //                                      every block/uncle up to
    //                                      end_block whose miner is
    //                                      `address`, printing each match's
    //                                      block number and whether it was
    //                                      an uncle. Existed only to test
    //                                      the "under-credited block
    //                                      reward" hypothesis during a real
    //                                      divergence hunt, cheaply — skips
    //                                      the two most expensive parts of
    //                                      a normal replay (ECDSA
    //                                      sender-recovery and EVM
    //                                      interpretation) entirely.
    var scan_miner: ?zevm.Address = null;
    var scan_end_block: u64 = 0;
    var scan_start_block: u64 = 0;
    var check_balance_addr: ?[]const u8 = null;
    var check_balance_dump: []const u8 = "";
    var check_storage_addr: ?[]const u8 = null;
    var check_storage_slot: []const u8 = "";
    var check_storage_dump: []const u8 = "";
    {
        var i: usize = 0;
        while (i < args.len) : (i += 1) {
            if (std.mem.eql(u8, args[i], "--check-gas")) {
                check_gas = true;
            } else if (std.mem.eql(u8, args[i], "--root-at") and i + 1 < args.len) {
                root_at_block = try std.fmt.parseInt(u64, args[i + 1], 10);
                i += 1;
            } else if (std.mem.eql(u8, args[i], "--verify-roots")) {
                verify_roots = true;
            } else if (std.mem.eql(u8, args[i], "--dump-at") and i + 2 < args.len) {
                dump_at_block = try std.fmt.parseInt(u64, args[i + 1], 10);
                dump_path = args[i + 2];
                i += 2;
                // Any block may be dumped. Only *resuming* from a mid-file
                // dump is unsafe, and `--resume-from` refuses that below.
                // The final era1 file ends at the Merge, mid-file, and its
                // last block is exactly where this replay has to stop.
            } else if (std.mem.eql(u8, args[i], "--resume-from") and i + 1 < args.len) {
                resume_path = args[i + 1];
                i += 1;
            } else if (std.mem.eql(u8, args[i], "--scan-miner") and i + 2 < args.len) {
                var addr_bytes: [20]u8 = undefined;
                const hex = if (std.mem.startsWith(u8, args[i + 1], "0x")) args[i + 1][2..] else args[i + 1];
                _ = try std.fmt.hexToBytes(&addr_bytes, hex);
                scan_miner = std.mem.readInt(u160, &addr_bytes, .big);
                scan_end_block = try std.fmt.parseInt(u64, args[i + 2], 10);
                i += 2;
                // Optional 3rd arg: a starting block to skip ahead to
                // (rounded down to its file's first block), so a scan can
                // target a narrow known-relevant range instead of always
                // paying full genesis-to-end_block sender-recovery cost.
                if (i + 1 < args.len and args[i + 1].len > 0 and args[i + 1][0] != '-') {
                    scan_start_block = try std.fmt.parseInt(u64, args[i + 1], 10);
                    i += 1;
                }
            } else if (std.mem.eql(u8, args[i], "--rewrite-snapshot") and i + 2 < args.len) {
                rewrite_in = args[i + 1];
                rewrite_out = args[i + 2];
                i += 2;
            } else if (std.mem.eql(u8, args[i], "--lazy-root") and i + 1 < args.len) {
                lazy_root_path = args[i + 1];
                i += 1;
            } else if (std.mem.eql(u8, args[i], "--snapshot-root") and i + 1 < args.len) {
                snapshot_root_path = args[i + 1];
                i += 1;
            } else if (std.mem.eql(u8, args[i], "--check-balance") and i + 2 < args.len) {
                check_balance_addr = args[i + 1];
                check_balance_dump = args[i + 2];
                i += 2;
            } else if (std.mem.eql(u8, args[i], "--check-storage") and i + 3 < args.len) {
                check_storage_addr = args[i + 1];
                check_storage_slot = args[i + 2];
                check_storage_dump = args[i + 3];
                i += 3;
            }
        }
    }

    // --check-balance <address> <dump-path>   loads a snapshot and prints
    // one address's balance/nonce/existence, then exits. A quick way to
    // ask "did zevm's own replay ever correctly credit this account by
    // this checkpoint?" without needing @embedFile (which chokes badly at
    // compile time on a multi-hundred-MB dump — confirmed during a real
    // divergence hunt: hours of CPU time for what should be a few seconds).
    if (rewrite_in) |in_path| {
        const out_path = rewrite_out.?;
        var file = try std.Io.Dir.cwd().openFile(io, in_path, .{});
        defer file.close(io);
        const bytes = try std.posix.mmap(
            null,
            (try file.stat(io)).size,
            .{ .READ = true },
            .{ .TYPE = .PRIVATE },
            file.handle,
            0,
        );
        defer std.posix.munmap(bytes);
        const snapshot = try zevm.State.loadSnapshot(allocator, bytes);
        var loaded = snapshot.state;
        defer loaded.deinit();
        std.debug.print("loaded block {d} ({d} accounts), rewriting...\n", .{ snapshot.block, loaded.accountCount() });

        var out_file = try std.Io.Dir.cwd().createFile(io, out_path, .{});
        defer out_file.close(io);
        const out_buf = try allocator.alloc(u8, 1 << 20);
        defer allocator.free(out_buf);
        var out_writer = out_file.writer(io, out_buf);
        try loaded.writeSnapshot(&out_writer.interface, snapshot.block, snapshot.recent_hashes);
        try out_writer.interface.flush();
        allocator.free(snapshot.recent_hashes);
        std.debug.print("wrote {s}\n", .{out_path});
        return;
    }

    if (lazy_root_path) |path| {
        var file = try std.Io.Dir.cwd().openFile(io, path, .{});
        defer file.close(io);
        const bytes = try std.posix.mmap(
            null,
            (try file.stat(io)).size,
            .{ .READ = true },
            .{ .TYPE = .PRIVATE },
            file.handle,
            0,
        );
        defer std.posix.munmap(bytes);
        const snapshot = try zevm.State.loadSnapshot(allocator, bytes);
        var loaded = snapshot.state;
        defer loaded.deinit();
        allocator.free(snapshot.recent_hashes);
        std.debug.print("indexed block {d} ({d} accounts), computing root through the lazy state...\n", .{ snapshot.block, loaded.accountCount() });
        const root = try loaded.stateRoot(allocator);
        const expected = try era1StateRoot(allocator, io, snapshot.block);
        if (root != expected) {
            std.debug.print(
                "LAZY ROOT MISMATCH at block {d}\n  computed 0x{x:0>64}\n  header   0x{x:0>64}\n",
                .{ snapshot.block, root, expected },
            );
            return error.StateRootMismatch;
        }
        std.debug.print("lazy state root OK at block {d} (0x{x:0>64})\n", .{ snapshot.block, root });
        return;
    }

    if (snapshot_root_path) |path| {
        var file = try std.Io.Dir.cwd().openFile(io, path, .{});
        defer file.close(io);
        const bytes = try std.posix.mmap(
            null,
            (try file.stat(io)).size,
            .{ .READ = true },
            .{ .TYPE = .PRIVATE },
            file.handle,
            0,
        );
        defer std.posix.munmap(bytes);
        std.posix.madvise(bytes.ptr, bytes.len, std.posix.MADV.SEQUENTIAL) catch {};

        const computed = try zevm.State.snapshotStateRoot(allocator, bytes);
        const expected = try era1StateRoot(allocator, io, computed.block);
        if (computed.root != expected) {
            std.debug.print(
                "STATE ROOT MISMATCH at block {d}\n  computed 0x{x:0>64}\n  header   0x{x:0>64}\n",
                .{ computed.block, computed.root, expected },
            );
            return error.StateRootMismatch;
        }
        std.debug.print("state root OK at block {d} (0x{x:0>64})\n", .{ computed.block, computed.root });
        return;
    }

    if (check_balance_addr) |addr_hex| {
        var addr_bytes: [20]u8 = undefined;
        const hex = if (std.mem.startsWith(u8, addr_hex, "0x")) addr_hex[2..] else addr_hex;
        _ = try std.fmt.hexToBytes(&addr_bytes, hex);
        const target: zevm.Address = std.mem.readInt(u160, &addr_bytes, .big);

        const dump = try std.Io.Dir.cwd().readFileAlloc(io, check_balance_dump, allocator, .unlimited);
        defer allocator.free(dump);
        const snapshot = try zevm.State.loadSnapshot(allocator, dump);
        std.debug.print("block {d}: balance={d} nonce={d} exists={}\n", .{
            snapshot.block,
            snapshot.state.getBalance(target),
            snapshot.state.get(target).nonce,
            snapshot.state.exists(target),
        });
        return;
    }

    // --check-storage <address> <slot> <dump-path>   same idea as
    // --check-balance, but for a single storage slot.
    if (check_storage_addr) |addr_hex| {
        var addr_bytes: [20]u8 = undefined;
        const hex = if (std.mem.startsWith(u8, addr_hex, "0x")) addr_hex[2..] else addr_hex;
        _ = try std.fmt.hexToBytes(&addr_bytes, hex);
        const target: zevm.Address = std.mem.readInt(u160, &addr_bytes, .big);
        const slot: u256 = try std.fmt.parseInt(u256, check_storage_slot, 0);

        const dump = try std.Io.Dir.cwd().readFileAlloc(io, check_storage_dump, allocator, .unlimited);
        defer allocator.free(dump);
        const snapshot = try zevm.State.loadSnapshot(allocator, dump);

        // A slot of 0 means "dump the whole account instead": balance,
        // nonce, code length, and every storage slot it has. Loading a
        // multi-GB snapshot takes minutes, so checking a contract's whole
        // storage one `--check-storage` call per slot is impractical —
        // this gets all of it from a single load.
        if (slot == 0) {
            const account = snapshot.state.get(target);
            // `get` returns a zeroed account for an address that isn't there,
            // so an absent account and an existing-but-empty one print
            // identically without this — and telling those two apart is
            // exactly what a `SELFDESTRUCT` or EIP-161 sweep question needs.
            std.debug.print("block {d}: exists={} balance={d} nonce={d} code_len={d} slots={d}\n", .{
                snapshot.block,
                snapshot.state.exists(target),
                account.balance,
                account.nonce,
                account.code.len,
                account.storage.count(),
            });
            var it = account.storage.iterator();
            while (it.next()) |kv| {
                std.debug.print("  slot {d} = {d}\n", .{ kv.key_ptr.*, kv.value_ptr.* });
            }
            return;
        }

        var loaded_state = snapshot.state;
        std.debug.print("block {d}: storage[{d}]={d}\n", .{
            snapshot.block,
            slot,
            loaded_state.getStorage(target, slot),
        });
        return;
    }

    if (scan_miner) |target| {
        var era1_dir = try std.Io.Dir.cwd().openDir(io, "data/era1", .{ .iterate = true });
        defer era1_dir.close(io);
        const all_files = try era1FileNames(allocator, io, era1_dir);
        defer {
            for (all_files) |f| allocator.free(f);
            allocator.free(all_files);
        }
        const secp = try Secp256k1.init();
        const start_file_index = scan_start_block / blocks_per_file;
        const scan_files = all_files[@min(start_file_index, all_files.len)..];

        var matches: u64 = 0;
        var in_total: u256 = 0;
        var out_total: u256 = 0;
        var out_gas_total: u256 = 0;
        outer: for (scan_files) |file_name| {
            const raw = try era1_dir.readFileAlloc(io, file_name, allocator, .unlimited);
            defer allocator.free(raw);
            const records = try readRecords(allocator, raw);
            defer allocator.free(records);

            var idx: usize = 1; // skip version record
            while (idx < records.len and std.mem.eql(u8, &records[idx].kind, &record_type.compressed_header)) {
                const header_record = records[idx];
                const body_record = records[idx + 1];
                idx += 4;

                const header_rlp = try Snappy.frameDecompress(allocator, header_record.data);
                defer allocator.free(header_rlp);
                const header_item = try zevm.Rlp.decode(allocator, header_rlp);
                defer header_item.deinit(allocator);
                const header = decodeHeader(header_item);
                if (header.number > scan_end_block) break :outer;

                if (header.miner == target) {
                    matches += 1;
                    std.debug.print("MATCH: block {d} miner\n", .{header.number});
                }

                const body_rlp = try Snappy.frameDecompress(allocator, body_record.data);
                defer allocator.free(body_rlp);
                const body_item = try zevm.Rlp.decode(allocator, body_rlp);
                defer body_item.deinit(allocator);
                for (body_item.list[1].list) |uncle_item| {
                    const uncle = decodeUncle(uncle_item);
                    if (uncle.miner == target) {
                        matches += 1;
                        std.debug.print("MATCH: block {d} UNCLE (included in block {d})\n", .{ uncle.number, header.number });
                    }
                }

                var tx_arena = std.heap.ArenaAllocator.init(allocator);
                defer tx_arena.deinit();
                for (body_item.list[0].list) |tx_item| {
                    const entry = try parseTransaction(tx_arena.allocator(), tx_item, try txSender(allocator, secp, tx_item));
                    if (entry.tx.to == target and entry.tx.value > 0) {
                        in_total += entry.tx.value;
                        std.debug.print("IN:  block {d} from {x} value {d} (running in_total {d})\n", .{ header.number, entry.from, entry.tx.value, in_total });
                    }
                    if (entry.from == target) {
                        out_total += entry.tx.value;
                        const gas_cost = @as(u256, entry.tx.gas_limit) * entry.tx.gas_price;
                        out_gas_total += gas_cost;
                        const selector = if (entry.tx.data.len >= 4) entry.tx.data[0..4] else entry.tx.data;
                        std.debug.print("OUT: block {d} nonce {d} value {d} gas_limit {d} gas_price {d} upfront_gas {d} to {?x} selector {x} datalen {d} (running out_total {d} out_gas_total {d})\n", .{ header.number, entry.tx.nonce, entry.tx.value, entry.tx.gas_limit, entry.tx.gas_price, gas_cost, entry.tx.to, selector, entry.tx.data.len, out_total, out_gas_total });
                    }
                }
            }
        }
        std.debug.print("scan done: {d} miner matches, in_total={d} out_total={d} out_gas_total={d} (upfront, not actual gas used) through block {d}\n", .{ matches, in_total, out_total, out_gas_total, scan_end_block });
        return;
    }

    var state: zevm.State = undefined;
    var starting_block: u64 = 0;
    // Populated from the dump when resuming; otherwise `recent_hashes`
    // below just starts empty, same as a from-genesis run.
    var resumed_hashes: []zevm.Hash = &.{};
    if (resume_path) |path| {
        // Mapped rather than read into a heap buffer: the snapshot runs
        // ~20GB at this depth, and `readFileAlloc` would hold all of it as
        // anonymous memory for the whole load, on top of the ~44GB of state
        // being built from it. A mapping's pages are file-backed and clean,
        // so the kernel can evict them under pressure instead of OOM-killing
        // the replay (which it did, twice). `loadSnapshot` copies out every
        // byte it keeps (code included), so nothing points into the mapping
        // once it returns.
        var file = try std.Io.Dir.cwd().openFile(io, path, .{});
        defer file.close(io);
        const dump = try std.posix.mmap(
            null,
            (try file.stat(io)).size,
            .{ .READ = true },
            .{ .TYPE = .PRIVATE },
            file.handle,
            0,
        );
        // Deliberately NOT unmapped: the loaded state's accounts, code and
        // storage are all read out of this mapping rather than copied to the
        // heap (see `State.Base`), so it has to outlive the state. It is
        // released when the process exits, which is the same moment the
        // state is discarded anyway.
        //
        // `MADV_WILLNEED` rather than `MADV_SEQUENTIAL`. Both the indexing
        // pass and the replay read this file, but in opposite patterns: the
        // index walk is strictly front to back, while account and storage
        // reads afterwards are scattered. `SEQUENTIAL` serves the first and
        // actively hurts the second, since it tells the kernel to drop pages
        // once passed and every later read then faults them back one 4KB
        // page at a time. Leaving no advice at all was worse still: a chunk
        // that had been taking ~13 minutes spent 98 minutes at 20% CPU,
        // waiting on single-page faults against a file too big for what was
        // left of the page cache. `WILLNEED` asks for the whole thing up
        // front, which is affordable precisely because these are file-backed
        // pages the kernel may evict under pressure, unlike the anonymous
        // copy this design replaced.
        std.posix.madvise(dump.ptr, dump.len, std.posix.MADV.WILLNEED) catch {};
        const snapshot = try zevm.State.loadSnapshot(allocator, dump);
        // Resuming restarts at the dumped block's *file*, not the block
        // itself, so a snapshot taken mid-file would have that file's earlier
        // blocks replayed a second time, silently double-applying their
        // transactions. Only a file's last block is a safe place to resume.
        if ((snapshot.block + 1) % blocks_per_file != 0) {
            std.debug.print("cannot resume from block {d}: not a file's last block ((block+1) % {d} must be 0)\n", .{ snapshot.block, blocks_per_file });
            return error.UnalignedResumeBlock;
        }
        state = snapshot.state;
        starting_block = snapshot.block + 1;
        resumed_hashes = snapshot.recent_hashes;
        std.debug.print("resumed from block {d}, starting at {d} ({d} accounts)\n", .{ snapshot.block, starting_block, state.accountCount() });
    } else {
        state = zevm.State.init(allocator);

        const genesis_json = @embedFile("data/mainnet_genesis.json");
        const parsed = try std.json.parseFromSlice(std.json.Value, allocator, genesis_json, .{});
        defer parsed.deinit();

        var accounts = parsed.value.object.get("alloc").?.object.iterator();
        while (accounts.next()) |entry| {
            var address_bytes: [20]u8 = undefined;
            _ = try std.fmt.hexToBytes(&address_bytes, entry.key_ptr.*);
            const address: zevm.Address = std.mem.readInt(u160, &address_bytes, .big);

            const balance_hex = entry.value_ptr.object.get("balance").?.string;
            const balance = try std.fmt.parseInt(u256, balance_hex[2..], 16);

            try state.setBalance(address, balance);
        }
        std.debug.print("loaded {d} genesis accounts\n", .{state.accountCount()});

        // Mainnet's genesis state root is a published constant, and the
        // genesis allocation is small enough to hash in well under a second.
        // Checking it here means a broken trie is caught before a single
        // block is replayed, rather than looking like a consensus bug later.
        const genesis_root = try state.stateRoot(allocator);
        const expected_genesis_root: zevm.Hash = 0xd7f8974fb5ac78d9ac099b9ad5018bedc2ce0a72dad1827a1709da30580f0544;
        if (genesis_root != expected_genesis_root) {
            std.debug.print(
                "genesis state root MISMATCH\n  computed 0x{x:0>64}\n  expected 0x{x:0>64}\n",
                .{ genesis_root, expected_genesis_root },
            );
            return error.GenesisStateRootMismatch;
        }
        std.debug.print("genesis state root OK (0x{x:0>64})\n", .{genesis_root});
    }
    defer state.deinit();

    var era1_dir = try std.Io.Dir.cwd().openDir(io, "data/era1", .{ .iterate = true });
    defer era1_dir.close(io);

    const all_files = try era1FileNames(allocator, io, era1_dir);
    defer {
        for (all_files) |f| allocator.free(f);
        allocator.free(all_files);
    }
    const start_file_index = starting_block / blocks_per_file;
    const files = all_files[@min(start_file_index, all_files.len)..];
    std.debug.print("found {d} era1 files ({d} remaining after skip)\n", .{ all_files.len, files.len });

    var evm = zevm.Evm{ .allocator = allocator, .state = &state };
    const secp = try Secp256k1.init();

    // Started here, after genesis is loaded, so this measures block
    // processing only, matching `sync_era1.rs`'s methodology so the two
    // totals are comparable.
    const start = std.Io.Clock.Timestamp.now(io, .awake);

    var blocks_processed: u64 = 0;
    var transactions_processed: u64 = 0;

    // Separately accumulated so the final summary can break down how much
    // of the total is spent *executing* (`Evm.processBlock`, comparable to
    // revm's own EVM-execution time) versus *decoding* (Snappy + RLP +
    // ECDSA sender-recovery); the two are easy to conflate otherwise.
    var decode_ns: u64 = 0;
    var execute_ns: u64 = 0;
    // Sub-split of `decode_ns`, to find which of the three actually
    // dominates rather than guessing.
    var snappy_ns: u64 = 0;
    var rlp_ns: u64 = 0;
    var tx_parse_ns: u64 = 0;

    // BLOCKHASH's lookup window, most recent first (index 0 is the
    // previous block's hash), capped at the 256 blocks real Ethereum keeps.
    // Seeded from the dump on resume (`resumed_hashes`), empty otherwise —
    // either way, ownership transfers straight into the list, no copy.
    var recent_hashes: std.ArrayList(zevm.Hash) = if (resumed_hashes.len != 0) .fromOwnedSlice(resumed_hashes) else .empty;
    defer recent_hashes.deinit(allocator);

    for (files, start_file_index..) |file_name, file_index| {
        const raw = try era1_dir.readFileAlloc(io, file_name, allocator, .unlimited);
        defer allocator.free(raw);

        const records = try readRecords(allocator, raw);
        defer allocator.free(records);

        var idx: usize = 0;
        if (records.len == 0 or !std.mem.eql(u8, &records[0].kind, &record_type.version)) {
            return error.MissingVersionRecord;
        }
        idx += 1;

        // Every sender in this file, recovered up front across all cores.
        // Recovery reads nothing but each transaction's own bytes, so it can
        // run ahead of execution, and the block loop below just takes the
        // results in order. That loop decompresses and decodes each body a
        // second time, which costs a fraction of a percent; restructuring it
        // around a pre-decoded file would touch the dump/resume/root paths.
        const recover_start = std.Io.Clock.Timestamp.now(io, .awake);
        var senders: std.ArrayList(zevm.Address) = .empty;
        defer senders.deinit(allocator);
        {
            var bodies: std.ArrayList([]u8) = .empty;
            defer {
                for (bodies.items) |body| allocator.free(body);
                bodies.deinit(allocator);
            }
            var decoded: std.ArrayList(zevm.Rlp.Item) = .empty;
            defer {
                for (decoded.items) |item| item.deinit(allocator);
                decoded.deinit(allocator);
            }
            var tx_items: std.ArrayList(zevm.Rlp.Item) = .empty;
            defer tx_items.deinit(allocator);

            var r = idx;
            while (r < records.len and std.mem.eql(u8, &records[r].kind, &record_type.compressed_header)) : (r += 4) {
                try bodies.ensureUnusedCapacity(allocator, 1);
                try decoded.ensureUnusedCapacity(allocator, 1);
                const body = try Snappy.frameDecompress(allocator, records[r + 1].data);
                bodies.appendAssumeCapacity(body);
                const item = try zevm.Rlp.decode(allocator, body);
                decoded.appendAssumeCapacity(item);
                try tx_items.appendSlice(allocator, item.list[0].list);
            }
            try senders.resize(allocator, tx_items.items.len);
            try recoverSenders(secp, tx_items.items, senders.items);
        }
        var next_sender: usize = 0;
        const recover_ns: u64 = @intCast(recover_start.durationTo(std.Io.Clock.Timestamp.now(io, .awake)).raw.nanoseconds);
        tx_parse_ns += recover_ns;
        decode_ns += recover_ns;

        var blocks_in_file: u64 = 0;
        var transactions_in_file: u64 = 0;
        while (idx < records.len and std.mem.eql(u8, &records[idx].kind, &record_type.compressed_header)) {
            const header_record = records[idx];
            const body_record = records[idx + 1];
            const receipts_record = records[idx + 2];
            // records[idx + 3] is the total-difficulty record (stored raw,
            // not Snappy-compressed), unused here.
            std.debug.assert(std.mem.eql(u8, &body_record.kind, &record_type.compressed_body));
            std.debug.assert(std.mem.eql(u8, &receipts_record.kind, &record_type.compressed_receipts));
            idx += 4;

            const decode_start = std.Io.Clock.Timestamp.now(io, .awake);

            const snappy_start = std.Io.Clock.Timestamp.now(io, .awake);
            const header_rlp = try Snappy.frameDecompress(allocator, header_record.data);
            defer allocator.free(header_rlp);
            const body_rlp = try Snappy.frameDecompress(allocator, body_record.data);
            defer allocator.free(body_rlp);
            snappy_ns += @intCast(snappy_start.durationTo(std.Io.Clock.Timestamp.now(io, .awake)).raw.nanoseconds);

            const rlp_start = std.Io.Clock.Timestamp.now(io, .awake);
            const header_item = try zevm.Rlp.decode(allocator, header_rlp);
            defer header_item.deinit(allocator);
            const header = decodeHeader(header_item);

            const body_item = try zevm.Rlp.decode(allocator, body_rlp);
            defer body_item.deinit(allocator);
            const transactions_rlp = body_item.list[0].list;
            const uncles_rlp = body_item.list[1].list;
            rlp_ns += @intCast(rlp_start.durationTo(std.Io.Clock.Timestamp.now(io, .awake)).raw.nanoseconds);

            const tx_parse_start = std.Io.Clock.Timestamp.now(io, .awake);
            var entries: std.ArrayList(zevm.Block.Entry) = .empty;
            defer entries.deinit(allocator);
            // Typed transactions' access lists live here until the block
            // has executed.
            var tx_arena = std.heap.ArenaAllocator.init(allocator);
            defer tx_arena.deinit();
            for (transactions_rlp) |tx_item| {
                // The pre-pass walked exactly these records in this order, so
                // running past its results means the two loops disagree.
                if (next_sender >= senders.items.len) return error.SenderCountMismatch;
                try entries.append(allocator, try parseTransaction(tx_arena.allocator(), tx_item, senders.items[next_sender]));
                next_sender += 1;
            }
            transactions_in_file += entries.items.len;

            // DEBUG: era1-replay divergence hunt. Dumps every transaction of
            // one specific block exactly as zevm parsed it, to compare
            // against the real chain's block body. Gated by an explicit
            // boolean, not a sentinel block number.
            if (debug_dump_block_enabled and header.number == debug_dump_block) {
                std.debug.print("DEBUG block {d}: zevm parsed {d} transactions\n", .{ header.number, entries.items.len });
                for (entries.items, 0..) |e, ti| {
                    std.debug.print("DEBUG   tx[{d}] from={x} to={?x} nonce={d} value={d} gas_limit={d} gas_price={d}\n", .{ ti, e.from, e.tx.to, e.tx.nonce, e.tx.value, e.tx.gas_limit, e.tx.gas_price });
                }
            }

            var uncles: std.ArrayList(zevm.Block.Uncle) = .empty;
            defer uncles.deinit(allocator);
            for (uncles_rlp) |uncle_item| {
                try uncles.append(allocator, decodeUncle(uncle_item));
            }
            tx_parse_ns += @intCast(tx_parse_start.durationTo(std.Io.Clock.Timestamp.now(io, .awake)).raw.nanoseconds);

            decode_ns += @intCast(decode_start.durationTo(std.Io.Clock.Timestamp.now(io, .awake)).raw.nanoseconds);
            const execute_start = std.Io.Clock.Timestamp.now(io, .awake);

            // Block 0 is genesis itself: its state *is* the allocation loaded
            // above, not something produced by executing it. Replaying it
            // credits a block reward for a block that never had a miner,
            // inventing an account at the zero address — holding 5 ETH — that
            // real chain has never had. Its hash is still recorded below,
            // since block 1's `BLOCKHASH` can legitimately ask for it.
            if (header.number != 0) {
                evm.processBlock(.{
                    .number = header.number,
                    .miner = header.miner,
                    .transactions = entries.items,
                    .uncles = uncles.items,
                    .timestamp = header.timestamp,
                    .gas_limit = header.gas_limit,
                    .difficulty = header.difficulty,
                    .base_fee = header.base_fee,
                    .recent_hashes = recent_hashes.items,
                }) catch |err| {
                    std.debug.print("block {d} failed: {s}\n", .{ header.number, @errorName(err) });
                    return err;
                };
            }

            execute_ns += @intCast(execute_start.durationTo(std.Io.Clock.Timestamp.now(io, .awake)).raw.nanoseconds);

            if (check_gas and evm.block_gas_used != header.gas_used) {
                std.debug.print(
                    "BLOCK GAS MISMATCH at block {d}\n  zevm   {d}\n  header {d}\n  (difference {d}, {d} transactions)\n",
                    .{ header.number, evm.block_gas_used, header.gas_used, @as(i128, evm.block_gas_used) - @as(i128, header.gas_used), entries.items.len },
                );
                return error.BlockGasMismatch;
            }

            if (root_at_block == header.number) {
                state.releaseJournal();
                const computed_root = try state.stateRoot(allocator);
                if (computed_root == header.state_root) {
                    std.debug.print("ROOT OK at block {d} ({d} accounts)\n", .{ header.number, state.accountCount() });
                    return;
                }
                std.debug.print(
                    "ROOT MISMATCH at block {d}\n  computed 0x{x:0>64}\n  header   0x{x:0>64}\n  ({d} accounts)\n",
                    .{ header.number, computed_root, header.state_root, state.accountCount() },
                );
                return error.StateRootMismatch;
            }

            if (verify_roots) {
                // Non-consuming, and the journal stays: unlike every other
                // root check here, this one runs *mid-replay* and the state
                // has to survive it intact for the next block.
                const computed_root = try state.stateRoot(allocator);
                if (computed_root != header.state_root) {
                    std.debug.print(
                        "STATE ROOT MISMATCH at block {d}\n  computed 0x{x:0>64}\n  header   0x{x:0>64}\n  ({d} accounts, {d} transactions in this block)\n",
                        .{ header.number, computed_root, header.state_root, state.accountCount(), entries.items.len },
                    );
                    return error.StateRootMismatch;
                }
            }

            // This block's own hash becomes available for BLOCKHASH lookups
            // starting with the *next* block, pushed after the call so
            // `recent_hashes` here only ever covers strictly earlier blocks.
            try recent_hashes.insert(allocator, 0, zevm.keccak256(header_rlp));
            if (recent_hashes.items.len > 256) recent_hashes.shrinkRetainingCapacity(256);

            blocks_in_file += 1;

            if (dump_at_block == header.number) {

                // Streamed straight to the file rather than built up in a
                // `Writer.Allocating`: past block ~6M the snapshot runs
                // ~20GB, and buffering it whole (with a doubling realloc
                // briefly holding two copies) on top of the ~44GB of live
                // state peaked over this machine's 62GB and got the replay
                // OOM-killed mid-run.
                var dump_file = try std.Io.Dir.cwd().createFile(io, dump_path, .{});
                defer dump_file.close(io);
                const dump_buf = try allocator.alloc(u8, 1 << 20);
                defer allocator.free(dump_buf);
                var dump_writer = dump_file.writer(io, dump_buf);
                try state.writeSnapshot(&dump_writer.interface, header.number, recent_hashes.items);
                try dump_writer.interface.flush();
                std.debug.print("dumped snapshot at block {d} to {s} ({d} accounts)\n", .{ header.number, dump_path, state.accountCount() });

                // Same breakdown the end-of-run summary prints. Without it
                // here, a chunked run (which always leaves through this
                // `return`) throws its timings away, which is how we ended
                // up guessing at where the time goes instead of reading it.
                std.debug.print("  decode (snappy+RLP+ecrecover): {d:.2}ms\n", .{
                    @as(f64, @floatFromInt(decode_ns)) / 1_000_000.0,
                });
                std.debug.print("    snappy:    {d:.2}ms\n", .{@as(f64, @floatFromInt(snappy_ns)) / 1_000_000.0});
                std.debug.print("    rlp:       {d:.2}ms\n", .{@as(f64, @floatFromInt(rlp_ns)) / 1_000_000.0});
                std.debug.print("    tx_parse:  {d:.2}ms\n", .{@as(f64, @floatFromInt(tx_parse_ns)) / 1_000_000.0});
                std.debug.print("  execute (Evm.processBlock):    {d:.2}ms\n", .{
                    @as(f64, @floatFromInt(execute_ns)) / 1_000_000.0,
                });

                // The root is deliberately NOT checked here. Doing it in
                // this process means holding the entire live state — hashmap
                // table, every Account, every storage map — while the trie's
                // entries are built alongside it, which past ~52M accounts
                // peaked near 58GB and was killed three times running.
                // `--snapshot-root` recomputes the same root from this file
                // by streaming it, at roughly a third of the memory, and
                // checks it against the era1 header itself. The driver runs
                // that as its own step before accepting the chunk.
                return;
            }
        }
        blocks_processed += blocks_in_file;
        transactions_processed += transactions_in_file;

        std.debug.print("[{d}/{d}] {s}: {d} blocks, {d} transactions processed\n", .{
            file_index + 1,
            all_files.len,
            file_name,
            blocks_in_file,
            transactions_in_file,
        });
    }

    std.debug.print("done: {d} blocks, {d} transactions, {d} accounts touched in {d:.2}ms (expected ~{d} blocks)\n", .{
        blocks_processed,
        transactions_processed,
        state.accountCount(),
        millisSince(io, start),
        files.len * blocks_per_file,
    });
    std.debug.print("  decode (snappy+RLP+ecrecover): {d:.2}ms\n", .{
        @as(f64, @floatFromInt(decode_ns)) / 1_000_000.0,
    });
    std.debug.print("    snappy:    {d:.2}ms\n", .{@as(f64, @floatFromInt(snappy_ns)) / 1_000_000.0});
    std.debug.print("    rlp:       {d:.2}ms\n", .{@as(f64, @floatFromInt(rlp_ns)) / 1_000_000.0});
    std.debug.print("    tx_parse:  {d:.2}ms\n", .{@as(f64, @floatFromInt(tx_parse_ns)) / 1_000_000.0});
    std.debug.print("  execute (Evm.processBlock):    {d:.2}ms\n", .{
        @as(f64, @floatFromInt(execute_ns)) / 1_000_000.0,
    });
}
