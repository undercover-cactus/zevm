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
    miner: zevm.Address,
    timestamp: u64,
    gas_limit: u64,
    difficulty: u256,
};

/// Frontier-era headers RLP-encode as a 15-field list (`parentHash,
/// unclesHash, coinbase, stateRoot, transactionsRoot, receiptsRoot,
/// logsBloom, difficulty, number, gasLimit, gasUsed, timestamp, extraData,
/// mixHash, nonce`); everything except coinbase/difficulty/number/
/// gasLimit/timestamp is decoded and discarded.
fn decodeHeader(header: zevm.Rlp.Item) DecodedHeader {
    return .{
        .number = bytesToU64(header.list[8].string),
        .miner = bytesToAddress(header.list[2].string),
        .timestamp = bytesToU64(header.list[11].string),
        .gas_limit = bytesToU64(header.list[9].string),
        .difficulty = bytesToU256(header.list[7].string),
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
    var sig: secp256k1.Signature = undefined;
    sig[0..32].* = padTo32(fields[7].string);
    sig[32..64].* = padTo32(fields[8].string);
    sig[64] = recid;

    const pubkey = try secp.recoverPubkey(hash, sig);
    // Skip `pubkey[0]`, the uncompressed-key format byte (0x04). An
    // Ethereum address is the low 160 bits of Keccak256 over the raw
    // 64-byte (x, y) coordinates alone.
    return @truncate(zevm.keccak256(pubkey[1..65]));
}

/// `tx_item`'s string fields borrow directly from the decompressed body
/// buffer the caller owns, kept alive as long as one block's entries are in use.
fn parseTransaction(allocator: std.mem.Allocator, secp: Secp256k1, tx_item: zevm.Rlp.Item) !zevm.Block.Entry {
    const fields = tx_item.list;
    const to_bytes = fields[3].string;
    return .{
        .from = try deriveSender(allocator, secp, fields),
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

pub fn main(io: std.Io) anyerror!void {
    // Not `DebugAllocator` (unlike `sync.zig`'s smaller benchmark): this
    // driver's era1 decoding does a huge number of small allocations, and
    // `DebugAllocator`'s per-allocation bookkeeping dominates runtime at
    // that volume, same reasoning `ffi.zig` uses `smp_allocator` for.
    const allocator = std.heap.smp_allocator;

    var state = zevm.State.init(allocator);
    defer state.deinit();

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
    std.debug.print("loaded {d} genesis accounts\n", .{state.accounts.count()});

    var era1_dir = try std.Io.Dir.cwd().openDir(io, "data/era1", .{ .iterate = true });
    defer era1_dir.close(io);

    const files = try era1FileNames(allocator, io, era1_dir);
    defer {
        for (files) |f| allocator.free(f);
        allocator.free(files);
    }
    std.debug.print("found {d} era1 files\n", .{files.len});

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
    var recent_hashes: std.ArrayList(zevm.Hash) = .empty;
    defer recent_hashes.deinit(allocator);

    for (files, 0..) |file_name, file_index| {
        const raw = try era1_dir.readFileAlloc(io, file_name, allocator, .unlimited);
        defer allocator.free(raw);

        const records = try readRecords(allocator, raw);
        defer allocator.free(records);

        var idx: usize = 0;
        if (records.len == 0 or !std.mem.eql(u8, &records[0].kind, &record_type.version)) {
            return error.MissingVersionRecord;
        }
        idx += 1;

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
            for (transactions_rlp) |tx_item| {
                try entries.append(allocator, try parseTransaction(allocator, secp, tx_item));
            }
            transactions_in_file += entries.items.len;

            var uncles: std.ArrayList(zevm.Block.Uncle) = .empty;
            defer uncles.deinit(allocator);
            for (uncles_rlp) |uncle_item| {
                try uncles.append(allocator, decodeUncle(uncle_item));
            }
            tx_parse_ns += @intCast(tx_parse_start.durationTo(std.Io.Clock.Timestamp.now(io, .awake)).raw.nanoseconds);

            decode_ns += @intCast(decode_start.durationTo(std.Io.Clock.Timestamp.now(io, .awake)).raw.nanoseconds);
            const execute_start = std.Io.Clock.Timestamp.now(io, .awake);

            evm.processBlock(.{
                .number = header.number,
                .miner = header.miner,
                .transactions = entries.items,
                .uncles = uncles.items,
                .timestamp = header.timestamp,
                .gas_limit = header.gas_limit,
                .difficulty = header.difficulty,
                .recent_hashes = recent_hashes.items,
            }) catch |err| {
                std.debug.print("block {d} failed: {s}\n", .{ header.number, @errorName(err) });
                return err;
            };

            execute_ns += @intCast(execute_start.durationTo(std.Io.Clock.Timestamp.now(io, .awake)).raw.nanoseconds);

            // This block's own hash becomes available for BLOCKHASH lookups
            // starting with the *next* block, pushed after the call so
            // `recent_hashes` here only ever covers strictly earlier blocks.
            try recent_hashes.insert(allocator, 0, zevm.keccak256(header_rlp));
            if (recent_hashes.items.len > 256) recent_hashes.shrinkRetainingCapacity(256);

            blocks_in_file += 1;
        }
        blocks_processed += blocks_in_file;
        transactions_processed += transactions_in_file;

        std.debug.print("[{d}/{d}] {s}: {d} blocks, {d} transactions processed\n", .{
            file_index + 1,
            files.len,
            file_name,
            blocks_in_file,
            transactions_in_file,
        });
    }

    std.debug.print("done: {d} blocks, {d} transactions, {d} accounts touched in {d:.2}ms (expected ~{d} blocks)\n", .{
        blocks_processed,
        transactions_processed,
        state.accounts.count(),
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
