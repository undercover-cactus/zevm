//! A minimal in-memory account store: balances, nonces, and code, keyed by
//! address. Deliberately concrete rather than abstracted behind a `Host`
//! interface, since the shape a swappable backend needs isn't known yet.
//!
//! Mutations are journaled rather than snapshotted: `checkpoint()` records
//! the journal's current length (O(1)), and `revertTo()` walks it backward
//! undoing entries until that length is reached again. Mirrors how real EVM
//! implementations (e.g. revm) do it: state mutates immediately, and undo
//! cost is proportional to the actual changes made, not the whole state.
//!
//! Code is immutable once set (`setCode`, called only by `CREATE`),
//! matching the real EVM. That keeps the journal simple: an account either
//! never existed (undone by removing it) or only its balance/nonce change.
//!
//! Storage lives per account (`Account.storage`), not in one shared map:
//! two lookups instead of one, but each lands in a small, warm table
//! instead of one giant shared one (measured ~4.7x faster for
//! storage-heavy execution; matches how real chains structure it too).

const std = @import("std");
const AddressModule = @import("Address.zig");
const Address = AddressModule.Address;
const Interpreter = @import("Interpreter.zig");
const Hash = @import("Hash.zig").Hash;
const keccak256 = @import("Hash.zig").keccak256;
const Rlp = @import("Rlp.zig");
const Trie = @import("Trie.zig");

pub const Account = struct {
    balance: u256 = 0,
    nonce: u64 = 0,
    code: []const u8 = &.{},
    /// Only the slots this account has *written* while loaded from a `base`
    /// snapshot. Unwritten slots still live in the snapshot and are read
    /// through, so this is the account's whole storage only when
    /// `base_storage_void` says so.
    storage: std.HashMapUnmanaged(u256, u256, KeyContext(u256), 80) = .empty,
    /// Overlay bookkeeping, not consensus state. False once the account has
    /// been erased, which is how a deletion overrides a `base` that still
    /// holds the account.
    present: bool = true,
    /// Whether `base`'s slots for this address must be ignored. True for an
    /// account that never existed in `base`, and true again after a
    /// destruction: a `SELFDESTRUCT`ed account recreated at the same address
    /// by `CREATE2` must not see the storage its predecessor was carrying.
    base_storage_void: bool = true,
};

pub const SlotKey = struct { address: Address, slot: u256 };

/// The hash map context every map in this file uses, in place of
/// `std.hash_map.AutoContext`. That one feeds the key's bytes through
/// wyhash's general byte-stream path (seeding, round loop, tail handling,
/// finalisation), which was ~5% of block execution for keys that are just
/// two to seven 64-bit words. This keeps wyhash's core step, a 64x64->128
/// multiply folded back to 64 bits, applied once per pair of words.
///
/// The fold puts every input bit into both the low bits (the bucket index)
/// and the top 7 (the probe fingerprint), which matters because storage
/// slots are often small integers (0, 1, 2 for plain variables) rather than
/// keccak outputs.
pub fn KeyContext(comptime K: type) type {
    return struct {
        pub fn hash(_: @This(), key: K) u64 {
            return switch (K) {
                Address => hashWords(0, @truncate(key), @truncate(key >> 64), @truncate(key >> 128), 0),
                u256 => hashWords(0, @truncate(key), @truncate(key >> 64), @truncate(key >> 128), @truncate(key >> 192)),
                SlotKey => hashWords(
                    hashWords(0, @truncate(key.address), @truncate(key.address >> 64), @truncate(key.address >> 128), 0),
                    @truncate(key.slot),
                    @truncate(key.slot >> 64),
                    @truncate(key.slot >> 128),
                    @truncate(key.slot >> 192),
                ),
                else => @compileError("no KeyContext hash for " ++ @typeName(K)),
            };
        }
        pub fn eql(_: @This(), a: K, b: K) bool {
            return std.meta.eql(a, b);
        }
    };
}

fn hashWords(seed: u64, w0: u64, w1: u64, w2: u64, w3: u64) u64 {
    const h = foldMul(seed ^ w0 ^ 0xa0761d6478bd642f, w1 ^ 0xe7037ed1a0b428db);
    const r = foldMul(h ^ w2 ^ 0x8ebc6af09c88c6e3, w3 ^ 0x589965cc75374cc3);
    // When only `w3` varies, and by a little, the product's low bits follow
    // the low bits of `w3` alone (and repeat if the other factor is even),
    // so the bucket index would clump; its middle bits are well mixed.
    return r ^ (r >> 32);
}

fn foldMul(a: u64, b: u64) u64 {
    const p = @as(u128, a) * b;
    return @as(u64, @truncate(p)) ^ @as(u64, @truncate(p >> 64));
}

const Change = union(enum) {
    created: Address,
    balance: struct { address: Address, old: u256 },
    nonce: struct { address: Address, old: u64 },
    storage: struct { address: Address, slot: u256, old: u256 },
    /// Code was deployed to `address`, which had none before (`setCode`
    /// asserts that), so undoing it means clearing it, not restoring an
    /// older value.
    code: Address,
    marked_for_destruction: Address,
    touched: Address,
    /// A tombstoned account was written to again, reviving it. Undoing that
    /// restores the tombstone rather than removing the overlay entry, which
    /// would let `base` answer for the address and resurrect the account
    /// a `SELFDESTRUCT` had erased.
    revived: Address,
    /// EIP-2929: an address or slot was accessed for the first time in this
    /// transaction. Undone like any other change, because a reverted frame's
    /// accesses never happened as far as later pricing is concerned.
    warmed_address: Address,
    warmed_slot: SlotKey,
    /// EIP-1153: a transient slot held `old` before a `TSTORE` in a frame
    /// that may still revert.
    transient: struct { key: SlotKey, old: u256 },
};

pub const Checkpoint = usize;

allocator: std.mem.Allocator,
/// Accounts that have been written since `base` was loaded, plus any read
/// that had to be materialised. Everything else is read straight out of
/// `base`, so this holds a chunk's working set rather than the whole chain.
accounts: std.HashMapUnmanaged(Address, Account, KeyContext(Address), 80) = .empty,
/// The snapshot this state was resumed from, read in place. Null for a state
/// built from genesis, in which case `accounts` is the whole story.
base: ?Base = null,
/// The snapshot mapping a resumed state was built from, if any. Contract
/// code loaded from it points *into* it rather than being copied onto the
/// heap: at 10.3M contracts that copy costs 6.8GB of anonymous memory, and
/// borrowing instead leaves those pages file-backed and evictable. The
/// caller must keep the mapping alive for the state's lifetime, and code
/// deployed later during execution is still heap-owned as usual, so every
/// free goes through `ownsCode` to tell the two apart.
snapshot_bytes: ?[]const u8 = null,
/// `JUMPDEST` analyses, computed on first execution of an account's code
/// rather than for every contract at load. Kept beside the accounts rather
/// than inside them: as an `Account` field it cost 16 bytes in all 134M
/// hashmap slots whether or not the account had code at all, and eagerly
/// analysing 10.3M contracts built 0.85GB of bitsets the vast majority of
/// which no chunk ever executes. A derived cache, so `setCode` and account
/// removal invalidate rather than update it.
jumpdest_cache: std.HashMapUnmanaged(Address, std.DynamicBitSetUnmanaged, KeyContext(Address), 80) = .empty,
/// Each slot's value as of the start of the current transaction, recorded
/// the first time that transaction writes it. EIP-2200 prices an `SSTORE`
/// on how *original*, current and new relate, so "what was this before
/// anything in this transaction touched it" has to be answerable even after
/// several writes. Cleared by `finalizeTransaction`, which is exactly the
/// boundary the word "original" refers to.
originals: std.HashMapUnmanaged(SlotKey, u256, KeyContext(SlotKey), 80) = .empty,
/// Slots already looked up in `base`, remembered so a hot one is searched
/// for once rather than on every access. Finding a slot in the snapshot
/// means a binary search over its account's region, and `SLOAD` is the
/// hottest opcode there is: without this, a chunk at depth took over two
/// hours at 99% CPU against the ~13 minutes the fully materialised state
/// managed, because a slot read a thousand times was searched for a
/// thousand times.
///
/// Needs no invalidation. A written slot lives in the overlay, which
/// `getStorage` consults first, and a destroyed or recreated account returns
/// before the cache is reached. Entries are therefore only ever the
/// snapshot's own unchanged values.
slot_cache: std.HashMapUnmanaged(SlotKey, u256, KeyContext(SlotKey), 80) = .empty,
/// EIP-2929's accessed addresses and storage keys for the transaction in
/// progress: whatever is in here is "warm" and pays the small price. Seeded
/// per transaction by `Evm.executeTransaction` and cleared by
/// `finalizeTransaction`. Kept here rather than in the interpreter so the
/// journal can undo a reverted frame's additions with everything else.
warm_addresses: std.HashMapUnmanaged(Address, void, KeyContext(Address), 80) = .empty,
warm_slots: std.HashMapUnmanaged(SlotKey, void, KeyContext(SlotKey), 80) = .empty,
journal: std.ArrayListUnmanaged(Change) = .empty,
/// EIP-1153 (Cancun): `TSTORE`/`TLOAD`'s storage, which lasts for one
/// transaction. Journaled like persistent storage, so a reverted frame's
/// writes are undone, and emptied by `finalizeTransaction`.
transient: std.HashMapUnmanaged(SlotKey, u256, KeyContext(SlotKey), 80) = .empty,
/// EIP-6780 (Cancun): contracts created during the transaction in progress,
/// the only ones `SELFDESTRUCT` still deletes. Not journaled: an address
/// whose creation reverted holds no code, so nothing can run there to
/// self-destruct unless a later creation in the same transaction puts code
/// back, which marks it again anyway. Emptied by `finalizeTransaction`.
created_this_transaction: std.HashMapUnmanaged(Address, void, KeyContext(Address), 80) = .empty,
/// Addresses `SELFDESTRUCT`ed during the transaction currently in
/// progress, appended by `destroyAccount` in lockstep with its
/// `.marked_for_destruction` journal entry (so a `revertTo` that undoes one
/// also undoes the other). Real Ethereum only deletes a self-destructed
/// account once its transaction fully commits, not immediately — code,
/// storage, balance, all of it stay exactly as they were until then, so a
/// later call to the same address *within the same transaction* still runs
/// its code normally (this is why `destroyAccount` doesn't touch the
/// account itself at all, unlike an earlier version of this fix that wiped
/// code immediately: that broke exactly this "call it again before the
/// transaction ends" case). `finalizeTransaction` does the real removal,
/// called once per transaction by `Evm.executeTransaction`.
pending_destructions: std.ArrayListUnmanaged(Address) = .empty,
/// From Spurious Dragon on (EIP-161): every message-call target whose call
/// succeeded and, at that moment, `existsAndIsEmpty` — reset each
/// transaction by `finalizeTransaction`, which sweeps this list and
/// deletes any address still empty by the time the transaction ends. This
/// is what actually cleared the DoS-attack dust accounts off real mainnet.
touched: std.ArrayListUnmanaged(Address) = .empty,
/// Counts deletions since `accounts` was last `rehash`ed, so
/// `removeAccount` can periodically clear accumulated tombstones (see its
/// own comment) instead of letting them build up for the rest of the run.
deletions_since_rehash: u32 = 0,

const State = @This();

pub fn init(allocator: std.mem.Allocator) State {
    return .{ .allocator = allocator };
}

/// Whether `code` is this state's to free, or borrowed from the snapshot
/// mapping it was loaded from.
fn ownsCode(self: *const State, code: []const u8) bool {
    if (code.len == 0) return false;
    const snapshot = self.snapshot_bytes orelse return true;
    const start = @intFromPtr(snapshot.ptr);
    const at = @intFromPtr(code.ptr);
    return at < start or at >= start + snapshot.len;
}

pub fn deinit(self: *State) void {
    var it = self.accounts.valueIterator();
    while (it.next()) |account| {
        if (self.ownsCode(account.code)) self.allocator.free(account.code);
        account.storage.deinit(self.allocator);
    }
    self.originals.deinit(self.allocator);
    self.slot_cache.deinit(self.allocator);
    self.warm_addresses.deinit(self.allocator);
    self.warm_slots.deinit(self.allocator);
    self.transient.deinit(self.allocator);
    self.created_this_transaction.deinit(self.allocator);
    if (self.base) |*base| base.deinit(self.allocator);

    var jd = self.jumpdest_cache.valueIterator();
    while (jd.next()) |bits| bits.deinit(self.allocator);
    self.jumpdest_cache.deinit(self.allocator);

    self.accounts.deinit(self.allocator);
    self.journal.deinit(self.allocator);
    self.pending_destructions.deinit(self.allocator);
    self.touched.deinit(self.allocator);
}

/// Deletions in `accounts` (a `std.HashMapUnmanaged`) are tombstones, not
/// true removals — real Ethereum's account count only ever grows overall,
/// but from Spurious Dragon on, EIP-161 makes *touching* an empty account
/// (any zero-value `CALL` to one) a short-lived insert-then-delete within
/// the same transaction. That's exactly the "long-lived HashMap with
/// repeated inserts and deletes" pattern Zig's own `rehash` doc comment
/// warns fragments a table into excessive probing: measured 99%+ of total
/// wall time in a single `getOrPut` call once tombstones built up over a
/// few hundred thousand deletions. Rehashing periodically (not on every
/// deletion — `rehash` itself is `O(capacity)`) keeps the tombstone ratio
/// bounded without paying for it on every touch.
const rehash_after_deletions: u32 = 100_000;

/// Fully erases `address` (code, balance, nonce, and storage all at once),
/// if still present. Shared by `finalizeTransaction`'s two sweeps
/// (`pending_destructions` and `touched`) so a later call to that address
/// is indistinguishable from one that was never used.
fn removeAccount(self: *State, address: Address) void {
    self.invalidateJumpdest(address);
    const in_base = if (self.base) |*b| b.contains(address) else false;

    if (self.accounts.getPtr(address)) |overlaid| {
        if (self.ownsCode(overlaid.code)) self.allocator.free(overlaid.code);
        overlaid.storage.deinit(self.allocator);
        if (in_base) {
            // A tombstone, not a removal: dropping the entry would let
            // `base` answer for this address again and resurrect the
            // account. `base_storage_void` also stops a later recreation at
            // the same address (a `CREATE2` after `SELFDESTRUCT`) from
            // seeing its predecessor's slots.
            overlaid.* = .{ .present = false, .base_storage_void = true };
            return;
        }
        _ = self.accounts.remove(address);
    } else if (in_base) {
        // Never materialised, so the tombstone is all there is to write.
        self.accounts.put(self.allocator, address, .{ .present = false, .base_storage_void = true }) catch return;
        return;
    } else return;

    self.deletions_since_rehash += 1;
    if (self.deletions_since_rehash >= rehash_after_deletions) {
        self.accounts.rehash(KeyContext(Address){});
        self.deletions_since_rehash = 0;
    }
}

/// Removes every account queued by `destroyAccount` since the last call,
/// matching real Ethereum's "gone at the end of the transaction" deletion,
/// then (from Spurious Dragon on) sweeps `touched` for any address that's
/// still empty and removes those too (EIP-161). Call once per transaction,
/// after it's done reverting (a reverted `SELFDESTRUCT` never reaches here:
/// `revertTo` already dropped it from `pending_destructions`, and a
/// reverted call's touches were never added to `touched` in the first
/// place — see `markTouchedIfEmpty`'s call sites).
pub fn finalizeTransaction(self: *State) void {
    for (self.pending_destructions.items) |address| self.removeAccount(address);
    self.pending_destructions.clearRetainingCapacity();

    for (self.touched.items) |address| {
        if (self.existsAndIsEmpty(address)) self.removeAccount(address);
    }
    self.touched.clearRetainingCapacity();

    // Every `checkpoint` a transaction takes is consumed by a `revertTo`
    // within that same transaction (see `Evm.call`/`create` and
    // `Interpreter.call`/`createOp`), so once one ends none of its journal
    // entries can ever be undone again. Dropping them here bounds the
    // journal to a single transaction instead of letting it accumulate for
    // a whole replay: at ~55M accounts a 65,536-block chunk grew it to
    // several GB on top of an already ~50GB state, which is what pushed the
    // process past this machine's 62GB and got it OOM-killed. Capacity is
    // retained, so the next transaction reuses the same buffer.
    self.journal.clearRetainingCapacity();
    // A new transaction means a new notion of "original", and everything is
    // cold again.
    //
    // Unlike the lists above, clearing a hash map while retaining capacity
    // zero-fills its *whole* table, not just what this transaction used. One
    // heavy transaction touching tens of thousands of slots grew these once,
    // and every transaction after it, a plain transfer included, then paid to
    // zero-fill the lot: 6.4% of all replay time on late-2022 blocks. A table
    // far bigger than what it just held is given back instead; one sized
    // about right is kept, as before.
    if (self.originals.capacity() > 4 * @max(self.originals.count(), 256)) self.originals.clearAndFree(self.allocator) else self.originals.clearRetainingCapacity();
    if (self.warm_addresses.capacity() > 4 * @max(self.warm_addresses.count(), 256)) self.warm_addresses.clearAndFree(self.allocator) else self.warm_addresses.clearRetainingCapacity();
    if (self.warm_slots.capacity() > 4 * @max(self.warm_slots.count(), 256)) self.warm_slots.clearAndFree(self.allocator) else self.warm_slots.clearRetainingCapacity();
    // Nearly always empty, and clearing an empty table still zero-fills it.
    if (self.transient.count() != 0) self.transient.clearRetainingCapacity();
    if (self.created_this_transaction.count() != 0) self.created_this_transaction.clearRetainingCapacity();
}

/// EIP-1153: `address`'s transient `slot`, 0 if this transaction never set it.
pub fn getTransient(self: *const State, address: Address, slot: u256) u256 {
    return self.transient.get(.{ .address = address, .slot = slot }) orelse 0;
}

/// EIP-1153: sets `address`'s transient `slot` until the transaction ends,
/// or until the frame that set it reverts.
pub fn setTransient(self: *State, address: Address, slot: u256, value: u256) !void {
    const key: SlotKey = .{ .address = address, .slot = slot };
    const entry = try self.transient.getOrPut(self.allocator, key);
    const old = if (entry.found_existing) entry.value_ptr.* else 0;
    entry.value_ptr.* = value;
    try self.journal.append(self.allocator, .{ .transient = .{ .key = key, .old = old } });
}

/// EIP-6780: records that a contract is being created at `address` in this
/// transaction.
pub fn markCreated(self: *State, address: Address) !void {
    try self.created_this_transaction.put(self.allocator, address, {});
}

/// EIP-6780: whether a contract was created at `address` in this transaction.
pub fn createdThisTransaction(self: *const State, address: Address) bool {
    return self.created_this_transaction.contains(address);
}

/// Marks `address` warm (EIP-2929), returning whether it already was. The
/// caller prices the access from the answer: warm costs
/// `gas.warm_storage_read_2929`, cold costs `gas.cold_account_access_2929`.
pub fn warmAddress(self: *State, address: Address) !bool {
    const entry = try self.warm_addresses.getOrPut(self.allocator, address);
    if (entry.found_existing) return true;
    try self.journal.append(self.allocator, .{ .warmed_address = address });
    return false;
}

/// `warmAddress` for one storage slot of `address`.
pub fn warmSlot(self: *State, address: Address, slot: u256) !bool {
    const key: SlotKey = .{ .address = address, .slot = slot };
    const entry = try self.warm_slots.getOrPut(self.allocator, key);
    if (entry.found_existing) return true;
    try self.journal.append(self.allocator, .{ .warmed_slot = key });
    return false;
}

/// `slot`'s value as of the start of the current transaction, which is the
/// current value when this transaction has not written it yet.
pub fn originalStorage(self: *State, address: Address, slot: u256) u256 {
    if (self.originals.get(.{ .address = address, .slot = slot })) |original| return original;
    return self.getStorage(address, slot);
}

/// `address`'s balance, nonce and code, from the overlay if it has been
/// written and from `base` otherwise.
///
/// The returned `storage` is NOT the account's storage: a base-backed
/// account's unwritten slots stay in the snapshot. Read slots through
/// `getStorage`, which knows how to look there. Nothing outside this file
/// reads `.storage` off a `get`, and nothing should start.
pub fn get(self: *const State, address: Address) Account {
    if (self.accounts.get(address)) |overlaid| {
        return if (overlaid.present) overlaid else .{};
    }
    if (self.base) |*base| {
        if (base.get(address)) |record| return .{
            .balance = record.balance,
            .nonce = record.nonce,
            .code = record.code,
            .base_storage_void = false,
        };
    }
    return .{};
}

pub fn exists(self: *const State, address: Address) bool {
    if (self.accounts.get(address)) |overlaid| return overlaid.present;
    if (self.base) |*base| return base.contains(address);
    return false;
}

/// How many accounts the state holds, overlay and `base` merged. O(overlay),
/// since the only corrections needed are for overlay entries that either
/// shadow a base account or erase one.
pub fn accountCount(self: *const State) usize {
    const base = if (self.base) |*b| b else return self.accounts.count();
    var total = base.count();
    var it = self.accounts.iterator();
    while (it.next()) |entry| {
        const in_base = base.contains(entry.key_ptr.*);
        if (entry.value_ptr.present and !in_base) total += 1;
        if (!entry.value_ptr.present and in_base) total -= 1;
    }
    return total;
}

/// The overlay entry for `address`, materialising it from `base` on first
/// write. Every mutation goes through this, which is what keeps the overlay
/// holding only a chunk's working set.
/// `journal_creation` false for the callers whose write a revert must not
/// undo (block rewards, gas fees). Those materialise the entry but leave no
/// `.created` behind, so `revertTo` has nothing to remove and the credit
/// stands, matching the unjournaled behaviour `creditBalance` has always had.
fn materialiseMaybeJournaled(self: *State, address: Address, journal_creation: bool) !*Account {
    const entry = try self.accounts.getOrPut(self.allocator, address);
    if (entry.found_existing) {
        if (entry.value_ptr.present) return entry.value_ptr;
        // Writing to a tombstoned address brings it back as a brand-new
        // account. `base_storage_void` stays set, so none of the erased
        // account's slots come with it.
        entry.value_ptr.* = .{ .present = true, .base_storage_void = true };
        if (journal_creation) try self.journal.append(self.allocator, .{ .revived = address });
        return entry.value_ptr;
    }

    // Copied out of `base` if it is there, so later writes layer onto the
    // real values; `base_storage_void` stays false so unwritten slots are
    // still read through to the snapshot.
    if (self.base) |*base| {
        if (base.get(address)) |record| {
            entry.value_ptr.* = .{
                .balance = record.balance,
                .nonce = record.nonce,
                .code = record.code,
                .base_storage_void = false,
            };
            if (journal_creation) try self.journal.append(self.allocator, .{ .created = address });
            return entry.value_ptr;
        }
    }

    entry.value_ptr.* = .{};
    if (debugOn(address)) {
        std.debug.print("DEBUG block={d} touch({x}): created\n", .{ debug_block_number, address });
    }
    if (journal_creation) try self.journal.append(self.allocator, .{ .created = address });
    return entry.value_ptr;
}

fn materialise(self: *State, address: Address) !*Account {
    return self.materialiseMaybeJournaled(address, true);
}

fn isEmptyAccount(account: Account) bool {
    return account.nonce == 0 and account.code.len == 0 and account.balance == 0;
}

/// EIP-161's "alive" check: exists AND has some nonce, code, or balance.
/// An existing-but-empty account (leftover from a zero-value touch, say)
/// counts as *not* alive — it's slated for cleanup just like one that was
/// never there at all.
pub fn isAlive(self: *const State, address: Address) bool {
    return self.exists(address) and !isEmptyAccount(self.get(address));
}

/// Whether `address` exists and has zero nonce, empty code, and zero
/// balance — the condition `finalizeTransaction`'s EIP-161 sweep uses to
/// decide what to delete.
pub fn existsAndIsEmpty(self: *const State, address: Address) bool {
    return self.exists(address) and isEmptyAccount(self.get(address));
}

/// Records `address` as touched this transaction, from Spurious Dragon on
/// (EIP-161), but only if it's currently `existsAndIsEmpty` — the only
/// state `finalizeTransaction`'s sweep would ever act on, so touching an
/// address that already has balance/nonce/code is a no-op. Journaled just
/// like everything else here, so it's safe to call unconditionally
/// (including right before a call that might still fail): a later
/// `revertTo` automatically discards it along with the rest of that call's
/// effects, matching real Ethereum's "a reverted call's touches never
/// happened" rule without callers needing to gate on success themselves.
pub fn markTouchedIfEmpty(self: *State, address: Address) !void {
    if (self.existsAndIsEmpty(address)) {
        try self.journal.append(self.allocator, .{ .touched = address });
        try self.touched.append(self.allocator, address);
    }
}

/// Whether `address` was already `destroyAccount`d earlier in the current
/// transaction. `SELFDESTRUCT` uses this to only earn its gas refund the
/// first time an address is destroyed, matching real Ethereum's
/// `accounts_to_delete` set semantics rather than paying out again on
/// every repeat call to an already-self-destructed contract.
pub fn isPendingDestruction(self: *const State, address: Address) bool {
    for (self.pending_destructions.items) |a| {
        if (a == address) return true;
    }
    return false;
}

pub fn getBalance(self: *const State, address: Address) u256 {
    return self.get(address).balance;
}

pub fn getCode(self: *const State, address: Address) []const u8 {
    return self.get(address).code;
}

/// Materialises `address` in state if it isn't there yet, journaling the
/// creation so `revertTo` can remove it entirely rather than merely
/// resetting its fields, keeping `exists()` accurate after a rollback.
///
/// Public because contract creation needs it directly: execution-specs'
/// `process_message` touches the new contract's address *before* running
/// its init code, and a constructor that `SELFDESTRUCT`s relies on the
/// account already existing for the destruction to register at all.
pub fn touch(self: *State, address: Address) !void {
    self.debugRecord(address);
    _ = try self.materialise(address);
}

// DEBUG: era1-replay divergence hunt scaffolding. Edit `debug_target` and
// flip `debug_enabled` to `true`, then rebuild, to trace a specific
// address's full balance history (set `debug_block_number` from
// `Evm.processBlock`). Left in place across sessions per user request; not
// meant to ship, but useful enough to keep. `debug_enabled` gates every
// check below, so it's always a hard no-op when off — no address value
// (including `0x0`) is a safe "definitely inactive" sentinel on real
// mainnet: burns, failed CREATEs, and SELFDESTRUCTs all pile up activity
// on `0x0` specifically, and it silently reintroduces the exact per-line
// slowdown this comment warns about if relied on as "disabled".
const debug_enabled = false;
const debug_target: Address = 0x0;
pub var debug_block_number: u64 = 0;
// DEBUG: the other axis of the same hunt. `debug_target` traces one address
// through every block; this traces every address through one block, for
// finding which account a state-root mismatch is about when every
// transaction's gas and status already agree with the receipts.
const debug_block_enabled = false;
const debug_block: u64 = 7_398_462;

fn debugOn(address: Address) bool {
    return (debug_enabled and address == debug_target) or
        (debug_block_enabled and debug_block_number == debug_block);
}

/// Every address any mutation touched during `debug_block`, so its final
/// state can be dumped at block end and diffed against the real chain.
pub var debug_block_addresses: std.AutoHashMapUnmanaged(Address, void) = .empty;

fn debugRecord(self: *State, address: Address) void {
    if (debug_block_enabled and debug_block_number == debug_block) {
        debug_block_addresses.put(self.allocator, address, {}) catch {};
    }
}

/// Final state of every address recorded during `debug_block`.
pub fn debugDumpBlockAccounts(self: *const State) void {
    if (!(debug_block_enabled and debug_block_number == debug_block)) return;
    var it = debug_block_addresses.iterator();
    while (it.next()) |e| {
        const address = e.key_ptr.*;
        const account = self.get(address);
        std.debug.print("DEBUG acct {x:0>40} exists={} balance={d} nonce={d} code_len={d} code_hash={x:0>64}\n", .{
            address, self.exists(address), account.balance, account.nonce, account.code.len,
            if (account.code.len == 0) empty_code_hash else keccak256(account.code),
        });
    }
}

pub fn setBalance(self: *State, address: Address, balance: u256) !void {
    self.debugRecord(address);
    const account = try self.materialise(address);
    if (debugOn(address)) {
        std.debug.print("DEBUG block={d} setBalance({x}): {d} -> {d}\n", .{ debug_block_number, address, account.balance, balance });
    }
    if (account.balance == balance) return;
    try self.journal.append(self.allocator, .{ .balance = .{ .address = address, .old = account.balance } });
    account.balance = balance;
}

/// Adds `amount` to `address`'s balance without journaling, for callers
/// that will never revert this specific change (e.g. block/uncle rewards).
pub fn creditBalance(self: *State, address: Address, amount: u256) !void {
    self.debugRecord(address);
    // Materialised so a base-backed account is credited on top of the
    // balance it actually has rather than from zero, but without journaling
    // the creation: these credits survive reverts by design.
    const account = try self.materialiseMaybeJournaled(address, false);
    if (debugOn(address)) {
        std.debug.print("DEBUG block={d} creditBalance({x}): {d} + {d} = {d}\n", .{ debug_block_number, address, account.balance, amount, account.balance + amount });
    }
    account.balance += amount;
}

pub fn setNonce(self: *State, address: Address, nonce: u64) !void {
    self.debugRecord(address);
    const account = try self.materialise(address);
    if (account.nonce == nonce) return;
    try self.journal.append(self.allocator, .{ .nonce = .{ .address = address, .old = account.nonce } });
    account.nonce = nonce;
}

/// Sets `address`'s code, `CREATE`'s job only. Code is write-once: this
/// asserts the account doesn't already have code, rather than journaling a
/// code change. Holds even for an address `destroyAccount`d earlier: a
/// self-destructed account keeps its old code until `finalizeTransaction`
/// actually removes it (see there), and `CREATE` can only ever target a
/// fresh nonce anyway, never that same still-live account.
pub fn setCode(self: *State, address: Address, code: []const u8) !void {
    self.debugRecord(address);
    const account = try self.materialise(address);
    std.debug.assert(account.code.len == 0);
    if (code.len == 0) return;
    account.code = try self.allocator.dupe(u8, code);
    // Journaled like every other mutation, so an enclosing frame that
    // reverts after a nested creation *succeeded* takes the deployed code
    // with it. Without this, `revertTo` restored the account's balance,
    // nonce, and storage and left the code in place. That stayed invisible
    // for 7.27M blocks because a plain `CREATE` always lands on a fresh
    // address, whose `.created` entry makes the revert delete the whole
    // account, code included. `CREATE2` deploys to a precomputed address
    // that is routinely pre-funded and so already exists; the first such
    // revert on mainnet (block 7,306,818) left 357 bytes of code behind.
    try self.journal.append(self.allocator, .{ .code = address });
}

/// EIP-7702 (Prague): replaces `address`'s code with a delegation indicator,
/// or clears it when `code` is empty. Unlike `setCode` this overwrites, and
/// like `creditBalance` it is not journaled: authorizations are applied
/// before a transaction's checkpoint and survive any revert, so nothing
/// ever rolls back past them.
pub fn setDelegation(self: *State, address: Address, code: []const u8) !void {
    self.debugRecord(address);
    const account = try self.materialiseMaybeJournaled(address, false);
    if (self.ownsCode(account.code)) self.allocator.free(account.code);
    account.code = if (code.len == 0) &.{} else try self.allocator.dupe(u8, code);
    self.invalidateJumpdest(address);
}

/// `address`'s cached `JUMPDEST` analysis (see `Account.jumpdest`), for a
/// `CALL`'s target to hand `Interpreter.initCall` instead of re-scanning
/// its bytecode. Only meaningful once `getCode(address).len != 0` is
/// already known — callers skip straight past an empty-code target before
/// ever needing this (see `Interpreter.call`'s own "no code" shortcut).
/// `address`'s `JUMPDEST` analysis, computed on first use and cached. The
/// returned pointer is owned by the cache and stays valid until that entry
/// is invalidated, which only `setCode` and account removal do.
pub fn getJumpdest(self: *State, address: Address) !*const std.DynamicBitSetUnmanaged {
    const entry = try self.jumpdest_cache.getOrPut(self.allocator, address);
    if (!entry.found_existing) {
        entry.value_ptr.* = try Interpreter.analyzeJumpdests(self.allocator, self.getCode(address));
    }
    return entry.value_ptr;
}

/// Drops `address`'s cached analysis, because its code changed or the whole
/// account went away.
fn invalidateJumpdest(self: *State, address: Address) void {
    if (self.jumpdest_cache.fetchRemove(address)) |kv| {
        var bits = kv.value;
        bits.deinit(self.allocator);
    }
}

/// Queues `address` for full removal (code, storage, nonce — all of it)
/// once its transaction commits, via `pending_destructions` (see
/// `finalizeTransaction`). Doesn't touch the account itself: real Ethereum
/// only deletes a self-destructed account at the true end of its
/// transaction, so a later call to this same address *within the same
/// transaction* must still run its code exactly as before — including
/// calling `SELFDESTRUCT` again, which is why this doesn't guard against
/// being called more than once for the same address.
pub fn destroyAccount(self: *State, address: Address) !void {
    self.debugRecord(address);
    if (!self.exists(address)) return;
    try self.journal.append(self.allocator, .{ .marked_for_destruction = address });
    try self.pending_destructions.append(self.allocator, address);
}

pub fn getStorage(self: *State, address: Address, slot: u256) u256 {
    if (self.accounts.getPtr(address)) |overlaid| {
        if (!overlaid.present) return 0;
        // A written slot is authoritative, including when it was written to
        // zero, which is why presence in the map decides rather than value.
        if (overlaid.storage.get(slot)) |written| return written;
        if (overlaid.base_storage_void) return 0;
    }
    const base = if (self.base) |*b| b else return 0;

    const key: SlotKey = .{ .address = address, .slot = slot };
    if (self.slot_cache.get(key)) |cached| return cached;

    const record = base.get(address) orelse return 0;
    const value = record.storage(slot);
    // Cached even when zero: "this account has no such slot" is just as
    // expensive to establish, and just as worth remembering.
    self.slot_cache.put(self.allocator, key, value) catch return value;
    return value;
}

pub fn setStorage(self: *State, address: Address, slot: u256, value: u256) !void {
    self.debugRecord(address);
    // Read the effective old value before materialising anything: for a
    // base-backed account an unwritten slot's previous value is in the
    // snapshot, not in the overlay, and the journal has to record that one
    // or a revert would restore a zero that was never there.
    const old = self.getStorage(address, slot);
    const account = try self.materialise(address);
    // `getOrPut` does one probe for the check-and-set instead of a separate
    // `get` + `put`. SSTORE is by far the hottest caller of this.
    // Recorded before the write, and only once per transaction, so repeated
    // writes to the same slot keep pointing at the value it had on entry.
    const original_entry = try self.originals.getOrPut(self.allocator, .{ .address = address, .slot = slot });
    if (!original_entry.found_existing) original_entry.value_ptr.* = old;

    const entry = try account.storage.getOrPut(self.allocator, slot);
    if (!entry.found_existing) entry.value_ptr.* = old;
    if (debugOn(address)) {
        std.debug.print("DEBUG block={d} setStorage({x}, slot={d}): {d} -> {d}\n", .{ debug_block_number, address, slot, old, value });
    }
    if (old == value) return;
    try self.journal.append(self.allocator, .{ .storage = .{ .address = address, .slot = slot, .old = old } });
    entry.value_ptr.* = value;
}

/// Moves `value` from `from` to `to`. Returns `false` (no-op) if `from`
/// doesn't have enough balance, matching the EVM's "call fails, nothing
/// moves" behavior rather than a partial transfer.
///
/// A zero-value transfer still touches `to`: real pre-EIP-161 Ethereum
/// materializes an account merely by calling it, even with no value moved.
pub fn transfer(self: *State, from: Address, to: Address, value: u256) !bool {
    if (value == 0) {
        try self.touch(to);
        return true;
    }
    const sender_balance = self.getBalance(from);
    if (sender_balance < value) return false;
    try self.setBalance(from, sender_balance - value);
    try self.setBalance(to, self.getBalance(to) + value);
    return true;
}

pub fn checkpoint(self: *const State) Checkpoint {
    return self.journal.items.len;
}

/// Undoes every change made since `cp`, in reverse order.
pub fn revertTo(self: *State, cp: Checkpoint) void {
    while (self.journal.items.len > cp) {
        switch (self.journal.pop().?) {
            .balance => |c| {
                // Logged like `setBalance`/`setStorage` below: undoing a
                // change here writes the field directly rather than going
                // back through those, so without this a trace shows every
                // forward write but none of the rollbacks — which reads as
                // "this value persisted" when it didn't. That cost real
                // time during an era1 divergence hunt: a trace-based bisect
                // fingered a block whose writes had in fact been correctly
                // reverted.
                if (debugOn(c.address)) {
                    std.debug.print("DEBUG block={d} REVERT balance({x}): -> {d}\n", .{ debug_block_number, c.address, c.old });
                }
                self.accounts.getPtr(c.address).?.balance = c.old;
            },
            .nonce => |c| self.accounts.getPtr(c.address).?.nonce = c.old,
            .storage => |c| {
                // `setStorage` always `touch`es the account and `put`s the
                // slot before this entry could exist, so both are
                // guaranteed present: direct pointer writes avoid a
                // fallible re-insertion here.
                if (debugOn(c.address)) {
                    std.debug.print("DEBUG block={d} REVERT setStorage({x}, slot={d}): -> {d}\n", .{ debug_block_number, c.address, c.slot, c.old });
                }
                self.accounts.getPtr(c.address).?.storage.getPtr(c.slot).?.* = c.old;
            },
            .code => |address| {
                // Popped before any `.created` for the same account (it was
                // appended after), so by the time that entry frees the
                // account these fields are already empty and it frees nothing.
                const account = self.accounts.getPtr(address).?;
                if (self.ownsCode(account.code)) self.allocator.free(account.code);
                account.code = &.{};
                self.invalidateJumpdest(address);
            },
            .created => |address| {
                var kv = self.accounts.fetchRemove(address).?;
                if (self.ownsCode(kv.value.code)) self.allocator.free(kv.value.code);
                kv.value.storage.deinit(self.allocator);
            },
            .marked_for_destruction => |address| {
                // Appended in lockstep with this journal entry in
                // `destroyAccount`, so it's always the list's last item here.
                std.debug.assert(self.pending_destructions.pop().? == address);
            },
            .revived => |address| {
                const account = self.accounts.getPtr(address).?;
                if (self.ownsCode(account.code)) self.allocator.free(account.code);
                account.storage.deinit(self.allocator);
                account.* = .{ .present = false, .base_storage_void = true };
            },
            .touched => |address| {
                // Appended in lockstep with this journal entry in
                // `markTouchedIfEmpty`, so it's always the list's last item
                // here.
                std.debug.assert(self.touched.pop().? == address);
            },
            .warmed_address => |address| _ = self.warm_addresses.remove(address),
            .warmed_slot => |key| _ = self.warm_slots.remove(key),
            .transient => |c| self.transient.getPtr(c.key).?.* = c.old,
        }
    }
}

/// Drops the journal and the per-transaction bookkeeping lists, keeping the
/// accounts themselves. Only for a caller that is finished mutating this
/// state: `revertTo` cannot see past this point, so any checkpoint taken
/// earlier becomes meaningless. Exists because a long replay accumulates
/// millions of journal entries, and a caller about to do something
/// memory-hungry (building the state trie, say) would rather have that space.
pub fn releaseJournal(self: *State) void {
    self.journal.clearAndFree(self.allocator);
    self.touched.clearAndFree(self.allocator);
    self.pending_destructions.clearAndFree(self.allocator);
}

/// One account's complete state with `base` and the overlay merged, as the
/// full scans that write a snapshot or compute a state root need it.
pub const Merged = struct {
    address: Address,
    balance: u256,
    nonce: u64,
    code: []const u8,
    /// `base`'s slot region for this account, ascending, empty when the
    /// account is overlay-only or its base storage has been voided.
    base_slots: []const u8,
    /// The overlay's written slots, or null when the account is base-only.
    written: ?*const std.HashMapUnmanaged(u256, u256, KeyContext(u256), 80),

    /// Yields every slot this account holds, ascending, with written values
    /// overriding `base`. Two passes are cheaper than buffering the union:
    /// the largest contract on this chain carries 11.95M slots.
    pub const Slots = struct {
        base_slots: []const u8,
        sorted_written: []const SlotPair,
        base_at: usize = 0,
        written_at: usize = 0,

        pub fn next(self: *Slots) ?SlotPair {
            const base_left = self.base_at * 64 < self.base_slots.len;
            const written_left = self.written_at < self.sorted_written.len;
            if (!base_left and !written_left) return null;
            if (!base_left) {
                defer self.written_at += 1;
                return self.sorted_written[self.written_at];
            }
            const entry = self.base_slots[self.base_at * 64 ..];
            const base_slot = std.mem.readInt(u256, entry[0..32], .little);
            if (!written_left) {
                defer self.base_at += 1;
                return .{ .slot = base_slot, .value = std.mem.readInt(u256, entry[32..64], .little) };
            }
            const written = self.sorted_written[self.written_at];
            if (written.slot < base_slot) {
                self.written_at += 1;
                return written;
            }
            if (written.slot == base_slot) {
                // The written value wins, and the base entry is consumed so
                // the slot is not emitted twice.
                self.base_at += 1;
                self.written_at += 1;
                return written;
            }
            self.base_at += 1;
            return .{ .slot = base_slot, .value = std.mem.readInt(u256, entry[32..64], .little) };
        }
    };

    /// `scratch` is filled with this account's written slots, sorted, and
    /// borrowed by the returned iterator.
    pub fn slots(self: Merged, allocator: std.mem.Allocator, scratch: *std.ArrayListUnmanaged(SlotPair)) !Slots {
        scratch.clearRetainingCapacity();
        if (self.written) |map| {
            try scratch.ensureTotalCapacity(allocator, map.count());
            var it = map.iterator();
            while (it.next()) |e| scratch.appendAssumeCapacity(.{ .slot = e.key_ptr.*, .value = e.value_ptr.* });
            std.mem.sort(SlotPair, scratch.items, {}, lessThanSlot);
        }
        return .{ .base_slots = self.base_slots, .sorted_written = scratch.items };
    }
};

/// Every account in the state, exactly once: first a front-to-back walk of
/// `base` (skipping what the overlay has erased, merging what it has
/// changed), then the overlay entries `base` never held.
pub const Scan = struct {
    state: *const State,
    base_walk: ?Base.Walk,
    overlay: std.HashMapUnmanaged(Address, Account, KeyContext(Address), 80).Iterator,

    pub fn next(self: *Scan) ?Merged {
        if (self.base_walk) |*walk| {
            while (walk.next()) |item| {
                if (self.state.accounts.getPtr(item.address)) |overlaid| {
                    if (!overlaid.present) continue; // erased
                    return .{
                        .address = item.address,
                        .balance = overlaid.balance,
                        .nonce = overlaid.nonce,
                        .code = overlaid.code,
                        .base_slots = if (overlaid.base_storage_void) &.{} else item.record.slots,
                        .written = &overlaid.storage,
                    };
                }
                return .{
                    .address = item.address,
                    .balance = item.record.balance,
                    .nonce = item.record.nonce,
                    .code = item.record.code,
                    .base_slots = item.record.slots,
                    .written = null,
                };
            }
            self.base_walk = null;
        }
        while (self.overlay.next()) |entry| {
            if (!entry.value_ptr.present) continue;
            // Already emitted during the base walk.
            if (self.state.base) |*base| if (base.contains(entry.key_ptr.*)) continue;
            return .{
                .address = entry.key_ptr.*,
                .balance = entry.value_ptr.balance,
                .nonce = entry.value_ptr.nonce,
                .code = entry.value_ptr.code,
                .base_slots = &.{},
                .written = &entry.value_ptr.storage,
            };
        }
        return null;
    }
};

pub fn scan(self: *const State) Scan {
    return .{
        .state = self,
        .base_walk = if (self.base) |*b| b.walk() else null,
        .overlay = self.accounts.iterator(),
    };
}

/// `keccak256("")` — the code hash every account without code carries in/// `keccak256("")` — the code hash every account without code carries in
/// the state trie. Not zero: an account with no code still commits to the
/// hash of empty code.
pub const empty_code_hash: Hash = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;

/// The state root: the Merkle Patricia Trie root over every account, keyed
/// by `keccak256(address)`, each holding `rlp([nonce, balance, storageRoot,
/// codeHash])`.
///
/// This is exactly what a real block header commits to, so comparing it
/// against a header's own `stateRoot` detects *any* divergence — including
/// the quiet ones that never raise an error and would otherwise only surface
/// hundreds of thousands of blocks later, as somebody else's failure.
///
/// Rebuilt from scratch on every call, which is O(accounts + storage slots)
/// and takes minutes at mainnet scale. That's the deliberate trade for not
/// maintaining a persistent trie: call it at checkpoints, never per block.
pub fn stateRoot(self: *State, allocator: std.mem.Allocator) !Hash {
    return self.computeStateRoot(allocator);
}

fn computeStateRoot(self: *State, allocator: std.mem.Allocator) !Hash {
    // Account keys and values must all stay alive until the final hash, so
    // they share one arena. Storage tries don't: each is consumed as soon as
    // its root is folded into an account, so they reuse a second arena that
    // resets per account rather than growing across millions of them.
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const account_allocator = arena.allocator();

    var storage_arena = std.heap.ArenaAllocator.init(allocator);
    defer storage_arena.deinit();

    var entries: std.ArrayListUnmanaged(Trie.Entry) = .empty;
    try entries.ensureTotalCapacity(account_allocator, self.accountCount());

    var slot_scratch: std.ArrayListUnmanaged(SlotPair) = .empty;
    defer slot_scratch.deinit(allocator);

    var accounts = self.scan();
    while (accounts.next()) |account| {
        _ = storage_arena.reset(.retain_capacity);
        const storage_allocator = storage_arena.allocator();
        var slots: std.ArrayListUnmanaged(Trie.Entry) = .empty;
        var stored = try account.slots(allocator, &slot_scratch);
        while (stored.next()) |pair| {
            // A slot set back to zero is *absent* from the trie, not present
            // holding zero — the state keeps the entry, the trie must not.
            if (pair.value == 0) continue;
            var slot_bytes: [32]u8 = undefined;
            std.mem.writeInt(u256, &slot_bytes, pair.slot, .big);
            const key = try storage_allocator.alloc(u8, 32);
            std.mem.writeInt(u256, key[0..32], keccak256(&slot_bytes), .big);
            try slots.append(storage_allocator, .{
                .key = key,
                .value = try Rlp.encodeInt(storage_allocator, pair.value),
            });
        }
        // `hashRoot` frees as it goes, so it gets the real allocator rather
        // than the arena, whose frees are no-ops.
        const storage_root = try Trie.hashRoot(allocator, slots.items);

        var storage_root_bytes: [32]u8 = undefined;
        std.mem.writeInt(u256, &storage_root_bytes, storage_root, .big);
        var code_hash_bytes: [32]u8 = undefined;
        std.mem.writeInt(u256, &code_hash_bytes, if (account.code.len == 0)
            empty_code_hash
        else
            keccak256(account.code), .big);

        var address_bytes: [20]u8 = undefined;
        std.mem.writeInt(u160, &address_bytes, account.address, .big);
        const key = try account_allocator.alloc(u8, 32);
        std.mem.writeInt(u256, key[0..32], keccak256(&address_bytes), .big);

        entries.appendAssumeCapacity(.{
            .key = key,
            .value = try Rlp.encodeList(account_allocator, &.{
                try Rlp.encodeInt(account_allocator, account.nonce),
                try Rlp.encodeInt(account_allocator, account.balance),
                try Rlp.encodeBytes(account_allocator, &storage_root_bytes),
                try Rlp.encodeBytes(account_allocator, &code_hash_bytes),
            }),
        });

    }

    return Trie.hashRoot(allocator, entries.items);
}

test "an empty state hashes to the empty trie root" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try std.testing.expectEqual(Trie.empty_root, try state.stateRoot(std.testing.allocator));
}

test "every part of an account is committed to by the state root" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0xaa, 100);
    const base = try state.stateRoot(std.testing.allocator);

    try state.setNonce(0xaa, 1);
    const with_nonce = try state.stateRoot(std.testing.allocator);
    try std.testing.expect(with_nonce != base);

    try state.setStorage(0xaa, 1, 42);
    const with_storage = try state.stateRoot(std.testing.allocator);
    try std.testing.expect(with_storage != with_nonce);

    try state.setCode(0xaa, &.{ 0x60, 0x00 });
    try std.testing.expect(try state.stateRoot(std.testing.allocator) != with_storage);
}

test "a storage slot cleared back to zero leaves no trace in the state root" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0xaa, 100);
    const before = try state.stateRoot(std.testing.allocator);

    try state.setStorage(0xaa, 7, 1234);
    try std.testing.expect(try state.stateRoot(std.testing.allocator) != before);

    // The map still holds slot 7, now zero; the trie must not.
    try state.setStorage(0xaa, 7, 0);
    try std.testing.expectEqual(before, try state.stateRoot(std.testing.allocator));
}

test "the state root does not depend on account insertion order" {
    var one = State.init(std.testing.allocator);
    defer one.deinit();
    try one.setBalance(0xaa, 1);
    try one.setBalance(0xbb, 2);
    try one.setBalance(0xcc, 3);

    var two = State.init(std.testing.allocator);
    defer two.deinit();
    try two.setBalance(0xcc, 3);
    try two.setBalance(0xaa, 1);
    try two.setBalance(0xbb, 2);

    try std.testing.expectEqual(
        try one.stateRoot(std.testing.allocator),
        try two.stateRoot(std.testing.allocator),
    );
}

/// A snapshot's block number alongside the state root computed from it.
pub const SnapshotRoot = struct { block: u64, root: Hash };

/// Computes a snapshot's state root by streaming its bytes, without ever
/// building a `State`.
///
/// This is the difference between verification being routine and being
/// impossible at mainnet scale. Going through `loadSnapshot` first
/// materialises ~53M `Account` structs in a 134M-slot hashmap — about 17GB of
/// table before a single trie entry exists, plus a separate allocation for
/// every contract's code and storage map — and only then starts building the
/// entries the root actually needs. Reading the file in order instead touches
/// each account once, keeps only its finished trie leaf, and lets the storage
/// scratch space be reused for the next one. Peak memory becomes the entry
/// set alone.
///
/// `bytes` is best supplied as a read-only mapping: the pages are then
/// file-backed and evictable rather than anonymous, so they cost the process
/// nothing it can't give back.
pub fn snapshotStateRoot(allocator: std.mem.Allocator, bytes: []const u8) !SnapshotRoot {
    var pos: usize = 0;
    const block = std.mem.readInt(u64, bytes[pos..][0..8], .little);
    pos += 8;
    const account_count = std.mem.readInt(u64, bytes[pos..][0..8], .little);
    pos += 8;

    // Accounts are independent of each other, so their leaves are computed
    // on every core. A sequential pass first marks out batches, reading only
    // the lengths needed to skip from one record to the next; workers then
    // take batches from a shared counter, so a batch of large contracts and
    // a batch of plain accounts balance out. Single-threaded, this pass was
    // ~20 minutes of every checkpoint at the Merge, 29% of a full replay.
    var batches: std.ArrayListUnmanaged(RootBatch) = .empty;
    defer batches.deinit(allocator);
    {
        var batch: RootBatch = .{ .pos = pos, .first = 0, .count = 0 };
        var i: u64 = 0;
        while (i < account_count) : (i += 1) {
            const code_len = std.mem.readInt(u32, bytes[pos + 60 ..][0..4], .little);
            const storage_count = std.mem.readInt(u64, bytes[pos + 64 + code_len ..][0..8], .little);
            pos += 72 + code_len + storage_count * 64;
            batch.count += 1;
            if (batch.count == 4096 or pos - batch.pos >= 64 << 20) {
                try batches.append(allocator, batch);
                batch = .{ .pos = pos, .first = i + 1, .count = 0 };
            }
        }
        if (batch.count != 0) try batches.append(allocator, batch);
    }

    const entries = try allocator.alloc(Trie.Entry, @intCast(account_count));
    defer allocator.free(entries);

    const max_threads = 32;
    const cpus = std.Thread.getCpuCount() catch 1;
    const thread_count = @max(1, @min(max_threads, @min(cpus, batches.items.len)));

    // Each worker's leaves live in its own arena until the trie is built.
    var leaf_arenas: [max_threads]std.heap.ArenaAllocator = undefined;
    for (leaf_arenas[0..thread_count]) |*a| a.* = std.heap.ArenaAllocator.init(allocator);
    defer for (leaf_arenas[0..thread_count]) |*a| a.deinit();

    var job: RootJob = .{ .allocator = allocator, .bytes = bytes, .batches = batches.items, .entries = entries };
    var threads: [max_threads]std.Thread = undefined;
    var failures: [max_threads]?anyerror = @splat(null);
    var spawned: usize = 0;
    while (spawned < thread_count) : (spawned += 1) {
        threads[spawned] = std.Thread.spawn(.{}, rootWorker, .{ &job, &leaf_arenas[spawned], &failures[spawned] }) catch |err| {
            job.next.store(batches.items.len, .monotonic);
            for (threads[0..spawned]) |t| t.join();
            return err;
        };
    }
    for (threads[0..spawned]) |t| t.join();
    for (failures[0..spawned]) |failure| if (failure) |err| return err;

    return .{ .block = block, .root = try Trie.hashRootParallel(allocator, entries) };
}

/// A run of consecutive account records: `count` accounts, starting at byte
/// `pos` of the snapshot with account number `first`.
const RootBatch = struct { pos: usize, first: u64, count: u64 };

const RootJob = struct {
    allocator: std.mem.Allocator,
    bytes: []const u8,
    batches: []const RootBatch,
    entries: []Trie.Entry,
    next: std.atomic.Value(usize) = .init(0),
};

fn rootWorker(job: *RootJob, leaf_arena: *std.heap.ArenaAllocator, failure: *?anyerror) void {
    // Storage tries are folded into their account straight away, so their
    // scratch is reset per account rather than kept.
    var storage_arena = std.heap.ArenaAllocator.init(job.allocator);
    defer storage_arena.deinit();
    while (true) {
        const b = job.next.fetchAdd(1, .monotonic);
        if (b >= job.batches.len) return;
        const batch = job.batches[b];
        var pos = batch.pos;
        for (0..batch.count) |k| {
            _ = storage_arena.reset(.retain_capacity);
            job.entries[batch.first + k] = accountLeaf(job.allocator, leaf_arena.allocator(), storage_arena.allocator(), job.bytes, &pos) catch |err| {
                failure.* = err;
                job.next.store(job.batches.len, .monotonic);
                return;
            };
        }
    }
}

/// The account trie leaf for the record at `pos.*`, advancing `pos` past it.
/// Its key and value are allocated in `leaf_allocator`; `storage_allocator`
/// only holds scratch for the storage trie, and `allocator` serves
/// `Trie.hashRoot`, which frees as it goes.
fn accountLeaf(allocator: std.mem.Allocator, leaf_allocator: std.mem.Allocator, storage_allocator: std.mem.Allocator, bytes: []const u8, pos: *usize) !Trie.Entry {
    const address = std.mem.readInt(u160, bytes[pos.*..][0..20], .big);
    pos.* += 20;
    const balance = std.mem.readInt(u256, bytes[pos.*..][0..32], .little);
    pos.* += 32;
    const nonce = std.mem.readInt(u64, bytes[pos.*..][0..8], .little);
    pos.* += 8;
    const code_len = std.mem.readInt(u32, bytes[pos.*..][0..4], .little);
    pos.* += 4;
    const code = bytes[pos.*..][0..code_len];
    pos.* += code_len;

    const storage_count = std.mem.readInt(u64, bytes[pos.*..][0..8], .little);
    pos.* += 8;

    var slots: std.ArrayListUnmanaged(Trie.Entry) = .empty;
    try slots.ensureTotalCapacity(storage_allocator, @intCast(storage_count));
    var s: u64 = 0;
    while (s < storage_count) : (s += 1) {
        const slot = std.mem.readInt(u256, bytes[pos.*..][0..32], .little);
        pos.* += 32;
        const value = std.mem.readInt(u256, bytes[pos.*..][0..32], .little);
        pos.* += 32;
        // A slot holding zero is absent from the trie, not present as zero.
        if (value == 0) continue;
        var slot_bytes: [32]u8 = undefined;
        std.mem.writeInt(u256, &slot_bytes, slot, .big);
        const slot_key = try storage_allocator.alloc(u8, 32);
        std.mem.writeInt(u256, slot_key[0..32], keccak256(&slot_bytes), .big);
        slots.appendAssumeCapacity(.{
            .key = slot_key,
            .value = try Rlp.encodeInt(storage_allocator, value),
        });
    }
    // `hashRoot` frees as it goes, so it gets the real allocator rather
    // than the arena, whose frees are no-ops.
    const storage_root = try Trie.hashRoot(allocator, slots.items);

    var storage_root_bytes: [32]u8 = undefined;
    std.mem.writeInt(u256, &storage_root_bytes, storage_root, .big);
    var code_hash_bytes: [32]u8 = undefined;
    std.mem.writeInt(u256, &code_hash_bytes, if (code_len == 0)
        empty_code_hash
    else
        keccak256(code), .big);

    var address_bytes: [20]u8 = undefined;
    std.mem.writeInt(u160, &address_bytes, address, .big);
    const key = try leaf_allocator.alloc(u8, 32);
    std.mem.writeInt(u256, key[0..32], keccak256(&address_bytes), .big);

    // The four field encodings and `encodeList`'s payload copy are scratch:
    // an arena never frees them, so built in `leaf_allocator` they would
    // outlive the run at roughly twice the size of the value kept. Only the
    // finished list is copied out. At 219M accounts (block 18,079,743) the
    // difference is ~30GB, and without it verification ran out of memory.
    const value = try Rlp.encodeList(storage_allocator, &.{
        try Rlp.encodeInt(storage_allocator, nonce),
        try Rlp.encodeInt(storage_allocator, balance),
        try Rlp.encodeBytes(storage_allocator, &storage_root_bytes),
        try Rlp.encodeBytes(storage_allocator, &code_hash_bytes),
    });
    return .{ .key = key, .value = try leaf_allocator.dupe(u8, value) };
}

test "a snapshot writes each account's storage slots in ascending order" {
    // A reader locates one slot inside an account's region by binary search,
    // with no index, so the ordering is load-bearing rather than cosmetic.
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    // Inserted deliberately out of order, and spread far enough apart that
    // hash-map iteration order is very unlikely to be ascending by accident.
    try state.setStorage(0xaa, 500, 1);
    try state.setStorage(0xaa, 3, 2);
    try state.setStorage(0xaa, std.math.maxInt(u256), 3);
    try state.setStorage(0xaa, 77, 4);
    try state.setStorage(0xaa, 0, 5);

    var out = std.Io.Writer.Allocating.init(std.testing.allocator);
    defer out.deinit();
    try state.writeSnapshot(&out.writer, 1, &.{});
    const bytes = out.writer.buffered();

    // Walk to this account's slot region: header, then address, balance,
    // nonce, code length (no code here), then the slot count.
    var pos: usize = 8 + 8 + 20 + 32 + 8;
    const code_len = std.mem.readInt(u32, bytes[pos..][0..4], .little);
    try std.testing.expectEqual(@as(u32, 0), code_len);
    pos += 4;
    const count = std.mem.readInt(u64, bytes[pos..][0..8], .little);
    pos += 8;
    try std.testing.expectEqual(@as(u64, 5), count);

    var previous: u256 = 0;
    var i: u64 = 0;
    while (i < count) : (i += 1) {
        const slot = std.mem.readInt(u256, bytes[pos..][0..32], .little);
        pos += 64; // slot and its value
        if (i != 0) try std.testing.expect(slot > previous);
        previous = slot;
    }
    try std.testing.expectEqual(@as(u256, std.math.maxInt(u256)), previous);
}

test "a cached base slot still loses to a later write, and to erasure" {
    // The read cache must never outrank the overlay. Reading first (which
    // caches) and writing after is the ordering that would expose a cache
    // consulted too early.
    var origin = State.init(std.testing.allocator);
    defer origin.deinit();
    try origin.setStorage(0xaa, 1, 11);
    try origin.setStorage(0xaa, 2, 22);

    var out = std.Io.Writer.Allocating.init(std.testing.allocator);
    defer out.deinit();
    try origin.writeSnapshot(&out.writer, 1, &.{});

    var loaded = (try loadSnapshot(std.testing.allocator, out.writer.buffered())).state;
    defer loaded.deinit();

    // Populate the cache, including the "no such slot" answer.
    try std.testing.expectEqual(@as(u256, 11), loaded.getStorage(0xaa, 1));
    try std.testing.expectEqual(@as(u256, 0), loaded.getStorage(0xaa, 99));
    try std.testing.expectEqual(@as(u256, 11), loaded.getStorage(0xaa, 1)); // served from cache

    // A write wins over the cached value.
    try loaded.setStorage(0xaa, 1, 111);
    try std.testing.expectEqual(@as(u256, 111), loaded.getStorage(0xaa, 1));
    // Including a write to zero.
    try loaded.setStorage(0xaa, 2, 0);
    try std.testing.expectEqual(@as(u256, 0), loaded.getStorage(0xaa, 2));
    // And a slot the snapshot never had.
    try loaded.setStorage(0xaa, 99, 9);
    try std.testing.expectEqual(@as(u256, 9), loaded.getStorage(0xaa, 99));

    // Erasure beats the cache too: these slots were cached from base, and
    // must not come back once the account is gone.
    try loaded.destroyAccount(0xaa);
    loaded.finalizeTransaction();
    try std.testing.expectEqual(@as(u256, 0), loaded.getStorage(0xaa, 1));
    try std.testing.expectEqual(@as(u256, 0), loaded.getStorage(0xaa, 2));

    // And a recreation at the same address sees none of them.
    try loaded.setBalance(0xaa, 1);
    try std.testing.expectEqual(@as(u256, 0), loaded.getStorage(0xaa, 1));
}

test "the read cache does not disturb the state root" {
    var origin = State.init(std.testing.allocator);
    defer origin.deinit();
    try origin.setStorage(0xaa, 1, 11);
    try origin.setStorage(0xaa, 2, 22);
    try origin.setBalance(0xbb, 5);
    const expected = try origin.stateRoot(std.testing.allocator);

    var out = std.Io.Writer.Allocating.init(std.testing.allocator);
    defer out.deinit();
    try origin.writeSnapshot(&out.writer, 1, &.{});

    var loaded = (try loadSnapshot(std.testing.allocator, out.writer.buffered())).state;
    defer loaded.deinit();
    // Read everything, so the cache is fully populated before the root is
    // computed. A cache that leaked into the overlay would show up here as
    // duplicated or shadowed slots.
    _ = loaded.getStorage(0xaa, 1);
    _ = loaded.getStorage(0xaa, 2);
    _ = loaded.getStorage(0xaa, 3);
    _ = loaded.getStorage(0xbb, 1);
    try std.testing.expectEqual(expected, try loaded.stateRoot(std.testing.allocator));
}

test "a state resumed from a snapshot reads through to it, and writes layer on top" {
    var origin = State.init(std.testing.allocator);
    defer origin.deinit();
    try origin.setBalance(0xaa, 100);
    try origin.setNonce(0xaa, 7);
    try origin.setCode(0xaa, &.{ 0x60, 0x01 });
    try origin.setStorage(0xaa, 1, 11);
    try origin.setStorage(0xaa, 2, 22);
    try origin.setBalance(0xbb, 5);

    var out = std.Io.Writer.Allocating.init(std.testing.allocator);
    defer out.deinit();
    try origin.writeSnapshot(&out.writer, 77, &.{});

    var loaded = (try loadSnapshot(std.testing.allocator, out.writer.buffered())).state;
    defer loaded.deinit();

    // Nothing materialised yet: every one of these is answered from the file.
    try std.testing.expectEqual(@as(usize, 0), loaded.accounts.count());
    try std.testing.expectEqual(@as(usize, 2), loaded.accountCount());
    try std.testing.expect(loaded.exists(0xaa));
    try std.testing.expect(!loaded.exists(0xcc));
    try std.testing.expectEqual(@as(u256, 100), loaded.getBalance(0xaa));
    try std.testing.expectEqual(@as(u64, 7), loaded.get(0xaa).nonce);
    try std.testing.expectEqualSlices(u8, &.{ 0x60, 0x01 }, loaded.getCode(0xaa));
    try std.testing.expectEqual(@as(u256, 11), loaded.getStorage(0xaa, 1));
    try std.testing.expectEqual(@as(u256, 0), loaded.getStorage(0xaa, 99));

    // A write materialises just that account, and unwritten slots keep
    // reading through.
    try loaded.setStorage(0xaa, 2, 222);
    try std.testing.expectEqual(@as(usize, 1), loaded.accounts.count());
    try std.testing.expectEqual(@as(u256, 222), loaded.getStorage(0xaa, 2));
    try std.testing.expectEqual(@as(u256, 11), loaded.getStorage(0xaa, 1));
    try std.testing.expectEqual(@as(u256, 100), loaded.getBalance(0xaa));

    // A slot written to zero is authoritative, not a fall-through.
    try loaded.setStorage(0xaa, 1, 0);
    try std.testing.expectEqual(@as(u256, 0), loaded.getStorage(0xaa, 1));

    // An account the snapshot never held.
    try loaded.setBalance(0xcc, 9);
    try std.testing.expect(loaded.exists(0xcc));
    try std.testing.expectEqual(@as(usize, 3), loaded.accountCount());
}

test "a resumed state's root is unchanged by what it has or has not materialised" {
    var origin = State.init(std.testing.allocator);
    defer origin.deinit();
    try origin.setBalance(0xaa, 100);
    try origin.setStorage(0xaa, 1, 11);
    try origin.setStorage(0xaa, 2, 22);
    try origin.setCode(0xbb, &.{0x00});
    try origin.setBalance(0xcc, 1);
    const expected = try origin.stateRoot(std.testing.allocator);

    var out = std.Io.Writer.Allocating.init(std.testing.allocator);
    defer out.deinit();
    try origin.writeSnapshot(&out.writer, 1, &.{});

    // Untouched: entirely read through.
    var cold = (try loadSnapshot(std.testing.allocator, out.writer.buffered())).state;
    defer cold.deinit();
    try std.testing.expectEqual(expected, try cold.stateRoot(std.testing.allocator));

    // Materialised by a write-then-revert, which must leave the root alone.
    var warm = (try loadSnapshot(std.testing.allocator, out.writer.buffered())).state;
    defer warm.deinit();
    const cp = warm.checkpoint();
    try warm.setStorage(0xaa, 1, 999);
    try warm.setBalance(0xaa, 12345);
    warm.revertTo(cp);
    try std.testing.expectEqual(expected, try warm.stateRoot(std.testing.allocator));
}

test "a resumed snapshot round-trips through writeSnapshot unchanged" {
    var origin = State.init(std.testing.allocator);
    defer origin.deinit();
    try origin.setBalance(0xaa, 100);
    try origin.setStorage(0xaa, 5, 55);
    try origin.setStorage(0xaa, 3, 33);
    try origin.setBalance(0xbb, 7);

    var first = std.Io.Writer.Allocating.init(std.testing.allocator);
    defer first.deinit();
    try origin.writeSnapshot(&first.writer, 42, &.{});

    var loaded = (try loadSnapshot(std.testing.allocator, first.writer.buffered())).state;
    defer loaded.deinit();
    // One written slot, one new account, so the dump has to merge.
    try loaded.setStorage(0xaa, 4, 44);
    try loaded.setBalance(0xcc, 3);

    var second = std.Io.Writer.Allocating.init(std.testing.allocator);
    defer second.deinit();
    try loaded.writeSnapshot(&second.writer, 43, &.{});

    const expected = try loaded.stateRoot(std.testing.allocator);
    const reloaded = try snapshotStateRoot(std.testing.allocator, second.writer.buffered());
    try std.testing.expectEqual(@as(u64, 43), reloaded.block);
    try std.testing.expectEqual(expected, reloaded.root);
}

test "an account erased from a resumed state stays erased, storage included" {
    var origin = State.init(std.testing.allocator);
    defer origin.deinit();
    try origin.setBalance(0xaa, 100);
    try origin.setStorage(0xaa, 1, 11);

    var out = std.Io.Writer.Allocating.init(std.testing.allocator);
    defer out.deinit();
    try origin.writeSnapshot(&out.writer, 1, &.{});

    var loaded = (try loadSnapshot(std.testing.allocator, out.writer.buffered())).state;
    defer loaded.deinit();
    try loaded.destroyAccount(0xaa);
    loaded.finalizeTransaction();

    // The snapshot still holds it; the tombstone must win, and its storage
    // must not come back when the address is reused.
    try std.testing.expect(!loaded.exists(0xaa));
    try std.testing.expectEqual(@as(u256, 0), loaded.getBalance(0xaa));
    try std.testing.expectEqual(@as(u256, 0), loaded.getStorage(0xaa, 1));
    try std.testing.expectEqual(@as(usize, 0), loaded.accountCount());

    // Recreated at the same address, as CREATE2 after SELFDESTRUCT does.
    try loaded.setBalance(0xaa, 5);
    try std.testing.expect(loaded.exists(0xaa));
    try std.testing.expectEqual(@as(u256, 0), loaded.getStorage(0xaa, 1));
    try std.testing.expectEqual(Trie.empty_root, try storageRootOf(&loaded, 0xaa));
}

/// Just this account's storage trie root, for asserting a recreated account
/// carries none of its predecessor's slots.
fn storageRootOf(state: *State, address: Address) !Hash {
    var scratch: std.ArrayListUnmanaged(SlotPair) = .empty;
    defer scratch.deinit(state.allocator);
    var it = state.scan();
    while (it.next()) |account| {
        if (account.address != address) continue;
        var slots: std.ArrayListUnmanaged(Trie.Entry) = .empty;
        defer {
            for (slots.items) |e| {
                state.allocator.free(e.key);
                state.allocator.free(e.value);
            }
            slots.deinit(state.allocator);
        }
        var stored = try account.slots(state.allocator, &scratch);
        while (stored.next()) |pair| {
            if (pair.value == 0) continue;
            var slot_bytes: [32]u8 = undefined;
            std.mem.writeInt(u256, &slot_bytes, pair.slot, .big);
            const key = try state.allocator.alloc(u8, 32);
            std.mem.writeInt(u256, key[0..32], keccak256(&slot_bytes), .big);
            try slots.append(state.allocator, .{ .key = key, .value = try Rlp.encodeInt(state.allocator, pair.value) });
        }
        return Trie.hashRoot(state.allocator, slots.items);
    }
    return Trie.empty_root;
}

test "a snapshot's streamed state root matches the state it came from" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0xaa, 12345);
    try state.setNonce(0xaa, 7);
    try state.setCode(0xaa, &.{ 0x60, 0x01, 0x60, 0x02 });
    try state.setStorage(0xaa, 1, 999);
    try state.setStorage(0xaa, 2, 0xdeadbeef);
    // A slot cleared back to zero must be absent from both paths alike.
    try state.setStorage(0xaa, 3, 42);
    try state.setStorage(0xaa, 3, 0);
    try state.setBalance(0xbb, 42);
    try state.setNonce(0xcc, 1);

    const expected = try state.stateRoot(std.testing.allocator);

    var out = std.Io.Writer.Allocating.init(std.testing.allocator);
    defer out.deinit();
    try state.writeSnapshot(&out.writer, 4242, &.{});

    const streamed = try snapshotStateRoot(std.testing.allocator, out.writer.buffered());
    try std.testing.expectEqual(@as(u64, 4242), streamed.block);
    try std.testing.expectEqual(expected, streamed.root);
}

test "an empty snapshot streams to the empty trie root" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    var out = std.Io.Writer.Allocating.init(std.testing.allocator);
    defer out.deinit();
    try state.writeSnapshot(&out.writer, 0, &.{});

    const streamed = try snapshotStateRoot(std.testing.allocator, out.writer.buffered());
    try std.testing.expectEqual(Trie.empty_root, streamed.root);
}

/// Serializes every account's balance, nonce, code, and storage as a flat
/// binary blob, tagged with `block` (whatever block this snapshot
/// represents), so a later run can start from here instead of replaying
/// from genesis. `jumpdest` isn't included: a derived cache, `setCode`
/// (or `loadSnapshot`'s own equivalent) recomputes it. Not a stable or
/// portable format — no version tag, native-width ints, no endianness
/// negotiation — meant purely for fast local debugging iteration on top of
/// a multi-million-block replay (`sync_era1`'s `--dump-at`/`--resume-from`).
///
/// Binary rather than the JSON this replaced: JSON's per-field
/// tokenizing/hex-encoding and `std.json.Value`'s per-leaf heap allocation
/// made loading a multi-GB, multi-million-account dump take longer than a
/// single debugging iteration could tolerate (measured: loading a 3.2GB/
/// 4.8M-account dump didn't finish in 10 minutes). This format is a flat
/// sequence of fixed-width fields — writing and reading are both a linear
/// scan with no parsing and at most one allocation per account (for its
/// code), not one per JSON token.
///
/// `recent_hashes` is `BLOCKHASH`'s 256-block lookup window (most recent
/// first, same order `Interpreter.BlockContext.recent_hashes` expects) —
/// carried through so a resumed run's first 256 blocks get correct
/// `BLOCKHASH` results too, not just its own state. Without this, a
/// contract that reads `BLOCKHASH` in exactly that window (a faucet or
/// game using it as a pseudo-random seed, say) diverges from a from-genesis
/// run right after resuming, and that divergence can silently propagate
/// into balances far past the 256-block window itself before it's ever
/// noticed — this was chased down as a real false-positive `InsufficientBalance`
/// failure during era1 validation before landing here.
const SlotPair = struct { slot: u256, value: u256 };

fn lessThanSlot(_: void, a: SlotPair, b: SlotPair) bool {
    return a.slot < b.slot;
}

/// Writes the snapshot. Each account's storage slots are emitted in
/// ascending slot order, which costs a per-account sort here and buys a
/// binary search later: a reader can find one slot inside an account's
/// region of the file without an index and without scanning, which matters
/// because the largest contract on this chain holds 11.95M slots. Accounts
/// themselves stay in hash-map order; they are found through an in-memory
/// offset index instead, so sorting 74M of them would buy nothing.
pub fn writeSnapshot(self: *const State, writer: *std.Io.Writer, block: u64, recent_hashes: []const Hash) !void {
    var buf8: [8]u8 = undefined;
    std.mem.writeInt(u64, &buf8, block, .little);
    try writer.writeAll(&buf8);
    std.mem.writeInt(u64, &buf8, self.accountCount(), .little);
    try writer.writeAll(&buf8);

    var sorted_slots: std.ArrayListUnmanaged(SlotPair) = .empty;
    defer sorted_slots.deinit(self.allocator);

    var it = self.scan();
    while (it.next()) |account| {
        var addr_buf: [20]u8 = undefined;
        std.mem.writeInt(u160, &addr_buf, account.address, .big);
        try writer.writeAll(&addr_buf);

        var buf32: [32]u8 = undefined;
        std.mem.writeInt(u256, &buf32, account.balance, .little);
        try writer.writeAll(&buf32);

        std.mem.writeInt(u64, &buf8, account.nonce, .little);
        try writer.writeAll(&buf8);

        var buf4: [4]u8 = undefined;
        std.mem.writeInt(u32, &buf4, @intCast(account.code.len), .little);
        try writer.writeAll(&buf4);
        try writer.writeAll(account.code);

        // Counted with one pass and written with a second, rather than
        // buffering the merged union: the largest contract here holds
        // 11.95M slots, which would be a 768MB scratch buffer.
        //
        // Both passes skip slots holding zero. A zero slot reads exactly like
        // an absent one, and the state root leaves it out, but the merge
        // yields one for every slot ever written back to zero, and each
        // snapshot used to carry those forward: at the Merge they were 258M
        // of 1,045M stored slots, ~16.5GB of every 100GB checkpoint.
        var counting = try account.slots(self.allocator, &sorted_slots);
        var total: u64 = 0;
        while (counting.next()) |pair| total += @intFromBool(pair.value != 0);
        std.mem.writeInt(u64, &buf8, total, .little);
        try writer.writeAll(&buf8);

        var writing = try account.slots(self.allocator, &sorted_slots);
        while (writing.next()) |pair| {
            if (pair.value == 0) continue;
            std.mem.writeInt(u256, &buf32, pair.slot, .little);
            try writer.writeAll(&buf32);
            std.mem.writeInt(u256, &buf32, pair.value, .little);
            try writer.writeAll(&buf32);
        }
    }

    std.mem.writeInt(u64, &buf8, recent_hashes.len, .little);
    try writer.writeAll(&buf8);
    var buf32: [32]u8 = undefined;
    for (recent_hashes) |hash| {
        std.mem.writeInt(u256, &buf32, hash, .little);
        try writer.writeAll(&buf32);
    }
}

/// `recent_hashes` is allocator-owned (same allocator as `loadSnapshot` was
/// given) — the caller frees it once done, same as `state`.
/// A loaded snapshot, read in place rather than materialised.
///
/// Accounts are located through `index` (address to the byte offset of its
/// record); an account's storage slots are then found by binary search
/// inside that account's own region of the file, which is what
/// `writeSnapshot`'s per-account slot ordering exists for.
///
/// The point is memory. Materialising the state costs ~105 bytes for every
/// one of the hash map's power-of-two slots plus ~100 bytes per storage
/// slot; indexing it costs ~41 bytes per account and leaves the data itself
/// in file-backed pages the kernel can evict. At 74M accounts and 321M
/// slots that is roughly 6GB against 48GB, and it stops growing with the
/// chain the way the materialised form does.
pub const Base = struct {
    /// The snapshot's bytes, owned by the caller and outliving this.
    bytes: []const u8,
    index: std.HashMapUnmanaged(Address, u64, KeyContext(Address), 80) = .empty,
    block: u64 = 0,

    /// One account, pointing into `bytes`.
    pub const Record = struct {
        balance: u256,
        nonce: u64,
        code: []const u8,
        /// The account's slots, 64 bytes each (slot then value, both
        /// little-endian), in ascending slot order.
        slots: []const u8,

        pub fn slotCount(self: Record) usize {
            return self.slots.len / 64;
        }

        /// `slot`'s value, or 0 if this account has no entry for it.
        /// Binary search, so the 11.95M-slot contract on this chain costs
        /// 24 probes rather than a scan.
        pub fn storage(self: Record, slot: u256) u256 {
            var low: usize = 0;
            var high: usize = self.slotCount();
            while (low < high) {
                const mid = low + (high - low) / 2;
                const entry = self.slots[mid * 64 ..];
                const key = std.mem.readInt(u256, entry[0..32], .little);
                if (key == slot) return std.mem.readInt(u256, entry[32..64], .little);
                if (key < slot) low = mid + 1 else high = mid;
            }
            return 0;
        }
    };

    /// Indexes `bytes` in a single pass, the same pass `loadSnapshot` makes
    /// to materialise it, so this is no more expensive to produce.
    pub fn init(allocator: std.mem.Allocator, bytes: []const u8) !Base {
        var self: Base = .{ .bytes = bytes };
        errdefer self.index.deinit(allocator);

        var pos: usize = 0;
        self.block = std.mem.readInt(u64, bytes[pos..][0..8], .little);
        pos += 8;
        const total = std.mem.readInt(u64, bytes[pos..][0..8], .little);
        pos += 8;
        try self.index.ensureTotalCapacity(allocator, @intCast(total));

        var i: u64 = 0;
        while (i < total) : (i += 1) {
            const start = pos;
            const address = std.mem.readInt(u160, bytes[pos..][0..20], .big);
            pos += 20 + 32 + 8;
            const code_len = std.mem.readInt(u32, bytes[pos..][0..4], .little);
            pos += 4 + code_len;
            const slot_count = std.mem.readInt(u64, bytes[pos..][0..8], .little);
            pos += 8 + slot_count * 64;
            self.index.putAssumeCapacityNoClobber(address, start);
        }
        return self;
    }

    pub fn deinit(self: *Base, allocator: std.mem.Allocator) void {
        self.index.deinit(allocator);
    }

    pub fn count(self: *const Base) usize {
        return self.index.count();
    }

    pub fn contains(self: *const Base, address: Address) bool {
        return self.index.contains(address);
    }

    /// `address`'s record, or null if the snapshot has no such account.
    pub fn get(self: *const Base, address: Address) ?Record {
        const offset = self.index.get(address) orelse return null;
        return self.at(offset);
    }

    /// Walks the file front to back, which is both how it was written and
    /// the cheapest order to read it: sequential pages, and the address
    /// comes out of the record rather than needing the index.
    pub const Walk = struct {
        base: *const Base,
        pos: usize = 16, // past block and count
        left: u64,

        pub fn next(self: *Walk) ?struct { address: Address, record: Record } {
            if (self.left == 0) return null;
            self.left -= 1;
            const start = self.pos;
            const address = std.mem.readInt(u160, self.base.bytes[start..][0..20], .big);
            const record = self.base.at(start);
            self.pos = start + 20 + 32 + 8 + 4 + record.code.len + 8 + record.slots.len;
            return .{ .address = address, .record = record };
        }
    };

    pub fn walk(self: *const Base) Walk {
        return .{ .base = self, .left = @intCast(self.index.count()) };
    }

    /// The record starting at `offset`. Used both by `get` and by the
    /// sequential walks that produce a state root or a new snapshot.
    pub fn at(self: *const Base, offset: u64) Record {
        var pos: usize = @intCast(offset);
        pos += 20; // address, already known by whoever has the offset
        const balance = std.mem.readInt(u256, self.bytes[pos..][0..32], .little);
        pos += 32;
        const nonce = std.mem.readInt(u64, self.bytes[pos..][0..8], .little);
        pos += 8;
        const code_len = std.mem.readInt(u32, self.bytes[pos..][0..4], .little);
        pos += 4;
        const code = self.bytes[pos..][0..code_len];
        pos += code_len;
        const slot_count = std.mem.readInt(u64, self.bytes[pos..][0..8], .little);
        pos += 8;
        return .{
            .balance = balance,
            .nonce = nonce,
            .code = code,
            .slots = self.bytes[pos..][0 .. slot_count * 64],
        };
    }
};

test "a Base finds every account the snapshot it indexed contains" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0xaa, 100);
    try state.setNonce(0xaa, 7);
    try state.setCode(0xaa, &.{ 0x60, 0x01 });
    try state.setBalance(0xbb, 0);
    try state.setNonce(0xcc, 3);

    var out = std.Io.Writer.Allocating.init(std.testing.allocator);
    defer out.deinit();
    try state.writeSnapshot(&out.writer, 4242, &.{});

    var base = try Base.init(std.testing.allocator, out.writer.buffered());
    defer base.deinit(std.testing.allocator);

    try std.testing.expectEqual(@as(u64, 4242), base.block);
    try std.testing.expectEqual(@as(usize, 3), base.count());
    try std.testing.expect(base.contains(0xaa));
    try std.testing.expect(!base.contains(0xdd));
    try std.testing.expectEqual(@as(?Base.Record, null), base.get(0xdd));

    const a = base.get(0xaa).?;
    try std.testing.expectEqual(@as(u256, 100), a.balance);
    try std.testing.expectEqual(@as(u64, 7), a.nonce);
    try std.testing.expectEqualSlices(u8, &.{ 0x60, 0x01 }, a.code);

    const c = base.get(0xcc).?;
    try std.testing.expectEqual(@as(u64, 3), c.nonce);
    try std.testing.expectEqual(@as(usize, 0), c.code.len);
}

test "a Base binary-searches an account's storage slots" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    // Deliberately inserted out of order and spread wide, so a search that
    // assumed ordering wrongly, or scanned, would show up.
    const slots = [_]u256{ 500, 3, std.math.maxInt(u256), 77, 0, 1 << 200, 42 };
    for (slots, 0..) |slot, i| try state.setStorage(0xaa, slot, @as(u256, i) + 1);

    var out = std.Io.Writer.Allocating.init(std.testing.allocator);
    defer out.deinit();
    try state.writeSnapshot(&out.writer, 1, &.{});

    var base = try Base.init(std.testing.allocator, out.writer.buffered());
    defer base.deinit(std.testing.allocator);

    const record = base.get(0xaa).?;
    try std.testing.expectEqual(@as(usize, slots.len), record.slotCount());
    for (slots, 0..) |slot, i| {
        try std.testing.expectEqual(@as(u256, @as(u256, i) + 1), record.storage(slot));
    }
    // Absent slots read as zero, including ones bracketed by present ones.
    try std.testing.expectEqual(@as(u256, 0), record.storage(4));
    try std.testing.expectEqual(@as(u256, 0), record.storage(499));
    try std.testing.expectEqual(@as(u256, 0), record.storage(std.math.maxInt(u256) - 1));
}

test "a Base over an empty snapshot holds nothing" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    var out = std.Io.Writer.Allocating.init(std.testing.allocator);
    defer out.deinit();
    try state.writeSnapshot(&out.writer, 9, &.{});

    var base = try Base.init(std.testing.allocator, out.writer.buffered());
    defer base.deinit(std.testing.allocator);
    try std.testing.expectEqual(@as(usize, 0), base.count());
    try std.testing.expectEqual(@as(u64, 9), base.block);
    try std.testing.expect(!base.contains(0xaa));
}

pub const Snapshot = struct { state: State, block: u64, recent_hashes: []Hash };

/// The inverse of `writeSnapshot`. Builds a fresh `State` from scratch (the
/// caller owns it, same as `State.init`) rather than populating an
/// existing one, since a snapshot is always meant to replace genesis
/// loading entirely, not merge with other state. Inserts accounts directly
/// rather than through `setBalance`/`setNonce`/`setStorage` — those exist
/// to journal changes for `revertTo`, which a fresh load has no use for and
/// would only pay allocations for.
pub fn loadSnapshot(allocator: std.mem.Allocator, bytes: []const u8) !Snapshot {
    var state = State.init(allocator);
    state.snapshot_bytes = bytes;
    errdefer state.deinit();

    // Indexed, not materialised. The accounts stay in `bytes` and are read
    // through `base`; the overlay starts empty and fills with whatever this
    // chunk actually touches. At 74M accounts and 321M storage slots that is
    // the difference between ~6GB of anonymous memory and ~48GB, and unlike
    // the materialised form it does not grow with the chain.
    state.base = try Base.init(allocator, bytes);
    const block = state.base.?.block;

    // The recent block hashes trail the accounts, so their offset is wherever
    // the last account's record ends.
    var pos: usize = 16;
    var walk = state.base.?.walk();
    while (walk.next()) |_| {}
    pos = walk.pos;

    const hash_count = std.mem.readInt(u64, bytes[pos..][0..8], .little);
    pos += 8;
    const recent_hashes = try allocator.alloc(Hash, hash_count);
    for (recent_hashes) |*hash| {
        hash.* = std.mem.readInt(u256, bytes[pos..][0..32], .little);
        pos += 32;
    }

    return .{ .state = state, .block = block, .recent_hashes = recent_hashes };
}

test "a snapshot round-trips balance, nonce, code, and storage" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0xaa, 12345);
    try state.setNonce(0xaa, 7);
    try state.setCode(0xaa, &.{ 0x60, 0x01, 0x60, 0x02 });
    try state.setStorage(0xaa, 1, 999);
    try state.setStorage(0xaa, 2, 0xdeadbeef);
    // A plain EOA: balance only, no code/storage — exercises the
    // empty-code, empty-storage path through the same round-trip.
    try state.setBalance(0xbb, 42);

    const hashes = [_]Hash{ 0xaaaa, 0xbbbb, 0xcccc };

    var out = std.Io.Writer.Allocating.init(std.testing.allocator);
    defer out.deinit();
    try state.writeSnapshot(&out.writer, 123, &hashes);

    const snapshot = try loadSnapshot(std.testing.allocator, out.writer.buffered());
    var loaded = snapshot.state;
    defer loaded.deinit();
    defer std.testing.allocator.free(snapshot.recent_hashes);

    try std.testing.expectEqual(@as(u64, 123), snapshot.block);
    try std.testing.expectEqual(@as(u256, 12345), loaded.getBalance(0xaa));
    try std.testing.expectEqual(@as(u64, 7), loaded.get(0xaa).nonce);
    try std.testing.expectEqualSlices(u8, &.{ 0x60, 0x01, 0x60, 0x02 }, loaded.getCode(0xaa));
    try std.testing.expectEqual(@as(u256, 999), loaded.getStorage(0xaa, 1));
    try std.testing.expectEqual(@as(u256, 0xdeadbeef), loaded.getStorage(0xaa, 2));
    try std.testing.expectEqual(@as(u256, 42), loaded.getBalance(0xbb));
    try std.testing.expectEqualSlices(u8, &.{}, loaded.getCode(0xbb));
    try std.testing.expectEqualSlices(Hash, &hashes, snapshot.recent_hashes);
}

test "unknown account reads as zero balance and empty code" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try std.testing.expectEqual(@as(u256, 0), state.getBalance(0x1));
    try std.testing.expectEqualSlices(u8, &.{}, state.getCode(0x1));
}

test "setCode copies code in, so a stack-lifetime literal doesn't need to outlive it" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    {
        const code = [_]u8{ 1, 2, 3 };
        try state.setCode(0x1, &code);
    }
    try std.testing.expectEqualSlices(u8, &.{ 1, 2, 3 }, state.getCode(0x1));
}

test "setCode precomputes getJumpdest, matching a direct analysis of the same code" {
    const OpCode = @import("OpCode.zig").OpCode;
    const code = [_]u8{
        @intFromEnum(OpCode.JUMPDEST), // 0: valid
        @intFromEnum(OpCode.PUSH2), 0x5b, 0x5b, // 1-3: PUSH data, NOT jumpdests even though it's 0x5b
        @intFromEnum(OpCode.JUMPDEST), // 4: valid
        @intFromEnum(OpCode.STOP), // 5
    };
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0x1, &code);

    const jumpdest = try state.getJumpdest(0x1);
    try std.testing.expect(jumpdest.isSet(0));
    try std.testing.expect(!jumpdest.isSet(1));
    try std.testing.expect(!jumpdest.isSet(2));
    try std.testing.expect(!jumpdest.isSet(3));
    try std.testing.expect(jumpdest.isSet(4));
    try std.testing.expect(!jumpdest.isSet(5));
}

test "transfer moves balance between accounts" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 100);

    try std.testing.expect(try state.transfer(0x1, 0x2, 40));
    try std.testing.expectEqual(@as(u256, 60), state.getBalance(0x1));
    try std.testing.expectEqual(@as(u256, 40), state.getBalance(0x2));
}

test "transfer fails without touching balances when sender is short" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 10);

    try std.testing.expect(!(try state.transfer(0x1, 0x2, 40)));
    try std.testing.expectEqual(@as(u256, 10), state.getBalance(0x1));
    try std.testing.expectEqual(@as(u256, 0), state.getBalance(0x2));
}

test "creditBalance adds to an existing balance and creates a new account starting from zero" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 100);

    try state.creditBalance(0x1, 50);
    try state.creditBalance(0x2, 50);

    try std.testing.expectEqual(@as(u256, 150), state.getBalance(0x1));
    try std.testing.expectEqual(@as(u256, 50), state.getBalance(0x2));
}

test "creditBalance is not undone by revertTo, unlike setBalance" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    const cp = state.checkpoint();
    try state.creditBalance(0x1, 100);
    state.revertTo(cp);

    try std.testing.expectEqual(@as(u256, 100), state.getBalance(0x1));
}

test "exists distinguishes an untouched address from a stored one" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try std.testing.expect(!state.exists(0x1));
    try state.setBalance(0x1, 0);
    try std.testing.expect(state.exists(0x1));
}

test "finalizeTransaction fully erases a destroyed account, unlike destroyAccount alone" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0x1, &.{ 1, 2, 3 });
    try state.setNonce(0x1, 1);
    try state.setStorage(0x1, 5, 99);

    try state.destroyAccount(0x1);
    // Not finalized yet: real Ethereum only deletes a self-destructed
    // account once its transaction fully commits, so code, nonce, and
    // storage all still read exactly as they did before the destroy — a
    // later call within the same transaction sees this same account,
    // fully intact, and can even destroy it again (see `destroyAccount`'s
    // own doc comment).
    try std.testing.expect(state.exists(0x1));
    try std.testing.expectEqualSlices(u8, &.{ 1, 2, 3 }, state.getCode(0x1));
    try std.testing.expectEqual(@as(u64, 1), state.get(0x1).nonce);
    try std.testing.expectEqual(@as(u256, 99), state.getStorage(0x1, 5));
    try state.destroyAccount(0x1);

    state.finalizeTransaction();
    try std.testing.expect(!state.exists(0x1));
    try std.testing.expectEqual(@as(u64, 0), state.get(0x1).nonce);
    try std.testing.expectEqual(@as(u256, 0), state.getStorage(0x1, 5));
}

test "a reverted destroyAccount is never finalized away" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0x1, &.{ 1, 2, 3 });

    const cp = state.checkpoint();
    try state.destroyAccount(0x1);
    state.revertTo(cp);
    state.finalizeTransaction();

    try std.testing.expect(state.exists(0x1));
    try std.testing.expectEqualSlices(u8, &.{ 1, 2, 3 }, state.getCode(0x1));
}

test "isPendingDestruction tracks destroyAccount across repeats, reverts, and finalization" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setCode(0x1, &.{1});
    try std.testing.expect(!state.isPendingDestruction(0x1));

    try state.destroyAccount(0x1);
    try std.testing.expect(state.isPendingDestruction(0x1));
    // Calling it again (SELFDESTRUCT re-triggered by a later CALL, say)
    // leaves it just as pending, not doubly so.
    try state.destroyAccount(0x1);
    try std.testing.expect(state.isPendingDestruction(0x1));

    const cp = state.checkpoint();
    try state.destroyAccount(0x1);
    state.revertTo(cp);
    // The reverted call's own destroyAccount is undone, but the earlier,
    // un-reverted one still stands.
    try std.testing.expect(state.isPendingDestruction(0x1));

    state.finalizeTransaction();
    try std.testing.expect(!state.isPendingDestruction(0x1));
}

test "revertTo undoes balance changes made after the checkpoint" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 100);

    const cp = state.checkpoint();
    _ = try state.transfer(0x1, 0x2, 100);
    try std.testing.expectEqual(@as(u256, 0), state.getBalance(0x1));

    state.revertTo(cp);
    try std.testing.expectEqual(@as(u256, 100), state.getBalance(0x1));
    try std.testing.expectEqual(@as(u256, 0), state.getBalance(0x2));
}

test "revertTo removes an account created after the checkpoint entirely" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    const cp = state.checkpoint();
    try state.setBalance(0x1, 50);
    try state.setCode(0x1, &.{ 1, 2, 3 });
    try std.testing.expect(state.exists(0x1));

    state.revertTo(cp);
    try std.testing.expect(!state.exists(0x1));
}

test "revertTo undoes only changes after the checkpoint, keeping earlier ones" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setBalance(0x1, 100);

    const cp = state.checkpoint();
    try state.setBalance(0x1, 50);
    state.revertTo(cp);

    try std.testing.expectEqual(@as(u256, 100), state.getBalance(0x1));
}

test "an unwritten storage slot reads as zero" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try std.testing.expectEqual(@as(u256, 0), state.getStorage(0x1, 42));
}

test "setStorage then getStorage round-trips, independently per slot" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setStorage(0x1, 1, 100);
    try state.setStorage(0x1, 2, 200);

    try std.testing.expectEqual(@as(u256, 100), state.getStorage(0x1, 1));
    try std.testing.expectEqual(@as(u256, 200), state.getStorage(0x1, 2));
}

test "the same slot is independent across different addresses" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setStorage(0x1, 1, 100);
    try state.setStorage(0x2, 1, 200);

    try std.testing.expectEqual(@as(u256, 100), state.getStorage(0x1, 1));
    try std.testing.expectEqual(@as(u256, 200), state.getStorage(0x2, 1));
}

test "revertTo undoes a storage write, including back to an untouched slot" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    const cp = state.checkpoint();
    try state.setStorage(0x1, 1, 100);
    try std.testing.expectEqual(@as(u256, 100), state.getStorage(0x1, 1));

    state.revertTo(cp);
    try std.testing.expectEqual(@as(u256, 0), state.getStorage(0x1, 1));
}

test "revertTo restores a slot's prior value, not just zero" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();
    try state.setStorage(0x1, 1, 100);

    const cp = state.checkpoint();
    try state.setStorage(0x1, 1, 999);
    state.revertTo(cp);

    try std.testing.expectEqual(@as(u256, 100), state.getStorage(0x1, 1));
}

test "a reverted frame's warm accesses go cold again, earlier ones stay warm" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    try std.testing.expect(!try state.warmAddress(0xaa));
    const cp = state.checkpoint();
    try std.testing.expect(!try state.warmAddress(0xbb));
    try std.testing.expect(!try state.warmSlot(0xaa, 7));
    // Already warm: no new journal entry, so nothing for the revert to undo.
    try std.testing.expect(try state.warmAddress(0xaa));
    state.revertTo(cp);

    try std.testing.expect(try state.warmAddress(0xaa));
    try std.testing.expect(!try state.warmAddress(0xbb));
    try std.testing.expect(!try state.warmSlot(0xaa, 7));

    // And a new transaction starts with everything cold.
    state.finalizeTransaction();
    try std.testing.expect(!try state.warmAddress(0xaa));
}

test "a per-transaction map grown by one heavy transaction is given back after a light one" {
    var state = State.init(std.testing.allocator);
    defer state.deinit();

    // A heavy transaction warms 10,000 slots.
    for (0..10_000) |i| _ = try state.warmSlot(0xaa, i);
    state.finalizeTransaction();
    const grown = state.warm_slots.capacity();
    try std.testing.expect(grown >= 10_000);

    // A light one touches a single slot; its clear releases the big table.
    _ = try state.warmSlot(0xaa, 1);
    state.finalizeTransaction();
    try std.testing.expect(state.warm_slots.capacity() < grown);

    // Correctness is unaffected either way: everything starts cold again.
    try std.testing.expect(!try state.warmSlot(0xaa, 1));
    try std.testing.expect(!try state.warmAddress(0xbb));
}

test "the parallel snapshot root matches the root of the state it was written from" {
    // Enough accounts for several batches and threads, with code and storage
    // spread across them, so the parallel paths are really exercised.
    var origin = State.init(std.testing.allocator);
    defer origin.deinit();
    for (1..9001) |i| {
        const a: Address = @intCast(0x5000 + i * 7919);
        try origin.setBalance(a, i);
        try origin.setNonce(a, i % 13);
        if (i % 50 == 0) try origin.setCode(a, &.{ 0x60, @intCast(i % 256), 0x00 });
        for (0..(i % 4)) |k| try origin.setStorage(a, k * 3 + i, i * 10 + k + 1);
    }
    const expected = try origin.stateRoot(std.testing.allocator);
    var out = std.Io.Writer.Allocating.init(std.testing.allocator);
    defer out.deinit();
    try origin.writeSnapshot(&out.writer, 5, &.{});
    const computed = try snapshotStateRoot(std.testing.allocator, out.writer.buffered());
    try std.testing.expectEqual(@as(u64, 5), computed.block);
    try std.testing.expectEqual(expected, computed.root);
}

test "a snapshot stores no zero-valued slots, and reads are unchanged by their absence" {
    var origin = State.init(std.testing.allocator);
    defer origin.deinit();
    try origin.setStorage(0xaa, 1, 11);
    try origin.setStorage(0xaa, 2, 22);
    try origin.setStorage(0xaa, 3, 0); // written to zero, never anything else
    try origin.setStorage(0xbb, 9, 99);
    var first = std.Io.Writer.Allocating.init(std.testing.allocator);
    defer first.deinit();
    try origin.writeSnapshot(&first.writer, 1, &.{});

    var loaded = (try loadSnapshot(std.testing.allocator, first.writer.buffered())).state;
    defer loaded.deinit();
    try std.testing.expectEqual(@as(usize, 2), loaded.base.?.get(0xaa).?.slotCount());
    // A base slot cleared in the overlay drops out of the next snapshot too.
    try loaded.setStorage(0xaa, 2, 0);
    var second = std.Io.Writer.Allocating.init(std.testing.allocator);
    defer second.deinit();
    try loaded.writeSnapshot(&second.writer, 2, &.{});

    var reloaded = (try loadSnapshot(std.testing.allocator, second.writer.buffered())).state;
    defer reloaded.deinit();
    try std.testing.expectEqual(@as(usize, 1), reloaded.base.?.get(0xaa).?.slotCount());
    try std.testing.expectEqual(@as(u256, 11), reloaded.getStorage(0xaa, 1));
    try std.testing.expectEqual(@as(u256, 0), reloaded.getStorage(0xaa, 2));
    try std.testing.expectEqual(@as(u256, 0), reloaded.getStorage(0xaa, 3));
    try std.testing.expectEqual(@as(u256, 99), reloaded.getStorage(0xbb, 9));
    // And the root, which never counted zeros, is the same either way.
    try std.testing.expectEqual(try loaded.stateRoot(std.testing.allocator), try reloaded.stateRoot(std.testing.allocator));
}

test "KeyContext spreads structured keys evenly over buckets" {
    // The keys real state is full of: small slot numbers, consecutive
    // addresses, and slots or addresses that differ only in a high limb.
    // Each set of 65536 keys goes into 4096 buckets by the low 12 bits (how
    // the map picks a bucket), where a fair hash averages 16 per bucket.
    // The fullest bucket of a fair hash stays well under 40.
    const sets = [_][]const u8{ "small slots", "high-limb slots", "addresses", "high addresses", "slot keys" };
    for (sets) |name| {
        var buckets = [_]u16{0} ** 4096;
        for (0..65536) |i| {
            const n: u64 = @intCast(i);
            const h = if (std.mem.eql(u8, name, "small slots"))
                KeyContext(u256).hash(.{}, n)
            else if (std.mem.eql(u8, name, "high-limb slots"))
                KeyContext(u256).hash(.{}, @as(u256, n) << 192)
            else if (std.mem.eql(u8, name, "addresses"))
                KeyContext(Address).hash(.{}, n)
            else if (std.mem.eql(u8, name, "high addresses"))
                KeyContext(Address).hash(.{}, @as(Address, n) << 128)
            else
                KeyContext(SlotKey).hash(.{}, .{ .address = @as(Address, n % 256) << 100, .slot = n / 256 });
            buckets[h & 4095] += 1;
        }
        var fullest: u16 = 0;
        for (buckets) |b| fullest = @max(fullest, b);
        std.testing.expect(fullest < 40) catch |err| {
            std.debug.print("{s}: fullest bucket {d}\n", .{ name, fullest });
            return err;
        };
    }
}
