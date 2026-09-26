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
    storage: std.AutoHashMapUnmanaged(u256, u256) = .empty,
};

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
};

pub const Checkpoint = usize;

allocator: std.mem.Allocator,
accounts: std.AutoHashMapUnmanaged(Address, Account) = .empty,
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
jumpdest_cache: std.AutoHashMapUnmanaged(Address, std.DynamicBitSetUnmanaged) = .empty,
journal: std.ArrayListUnmanaged(Change) = .empty,
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
    var kv = self.accounts.fetchRemove(address) orelse return;
    if (self.ownsCode(kv.value.code)) self.allocator.free(kv.value.code);
    kv.value.storage.deinit(self.allocator);
    self.invalidateJumpdest(address);

    self.deletions_since_rehash += 1;
    if (self.deletions_since_rehash >= rehash_after_deletions) {
        self.accounts.rehash(std.hash_map.AutoContext(Address){});
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
}

pub fn get(self: *const State, address: Address) Account {
    return self.accounts.get(address) orelse .{};
}

pub fn exists(self: *const State, address: Address) bool {
    return self.accounts.contains(address);
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
    // `getOrPut` does one probe for the check-and-set instead of a separate
    // `contains` + `put` — this is by far the hottest path in a real
    // multi-million-block replay (every zero-value CALL touches its
    // target), so the redundant second lookup shows up as roughly half of
    // total wall time once the account count reaches the millions. Mirrors
    // `setStorage`'s identical fix.
    const entry = try self.accounts.getOrPut(self.allocator, address);
    if (entry.found_existing) return;
    entry.value_ptr.* = .{}; // must initialize a freshly created slot regardless
    if (debugOn(address)) {
        std.debug.print("DEBUG block={d} touch({x}): created\n", .{ debug_block_number, address });
    }
    try self.journal.append(self.allocator, .{ .created = address });
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
    try self.touch(address);
    const account = self.accounts.getPtr(address).?;
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
    const entry = try self.accounts.getOrPutValue(self.allocator, address, .{});
    if (debugOn(address)) {
        std.debug.print("DEBUG block={d} creditBalance({x}): {d} + {d} = {d}\n", .{ debug_block_number, address, entry.value_ptr.balance, amount, entry.value_ptr.balance + amount });
    }
    entry.value_ptr.balance += amount;
}

pub fn setNonce(self: *State, address: Address, nonce: u64) !void {
    self.debugRecord(address);
    try self.touch(address);
    const account = self.accounts.getPtr(address).?;
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
    try self.touch(address);
    const account = self.accounts.getPtr(address).?;
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
    if (!self.accounts.contains(address)) return;
    try self.journal.append(self.allocator, .{ .marked_for_destruction = address });
    try self.pending_destructions.append(self.allocator, address);
}

pub fn getStorage(self: *const State, address: Address, slot: u256) u256 {
    const account = self.accounts.get(address) orelse return 0;
    return account.storage.get(slot) orelse 0;
}

pub fn setStorage(self: *State, address: Address, slot: u256, value: u256) !void {
    self.debugRecord(address);
    try self.touch(address);
    const account = self.accounts.getPtr(address).?;
    // `getOrPut` does one probe for the check-and-set instead of a separate
    // `get` + `put`. SSTORE is by far the hottest caller of this.
    const entry = try account.storage.getOrPut(self.allocator, slot);
    const old: u256 = if (entry.found_existing) entry.value_ptr.* else 0;
    if (!entry.found_existing) entry.value_ptr.* = 0; // must initialize a freshly created slot regardless
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
            .touched => |address| {
                // Appended in lockstep with this journal entry in
                // `markTouchedIfEmpty`, so it's always the list's last item
                // here.
                std.debug.assert(self.touched.pop().? == address);
            },
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

/// `keccak256("")` — the code hash every account without code carries in
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
    return self.computeStateRoot(allocator, false);
}

/// The same root as `stateRoot`, but dismantles the state while computing it:
/// each account's storage map and code are freed the moment they have been
/// folded into that account's trie leaf. The state is left unusable — only
/// call this when the process is about to exit or the state is about to be
/// discarded.
///
/// This exists because the non-consuming version needs the whole state *and*
/// the whole entry set live at once, which at ~52M accounts came to roughly
/// 58GB and got the replay killed one chunk from the end. Freeing as it goes
/// means the entries grow into space the accounts are vacating.
pub fn stateRootConsuming(self: *State, allocator: std.mem.Allocator) !Hash {
    return self.computeStateRoot(allocator, true);
}

fn computeStateRoot(self: *State, allocator: std.mem.Allocator, consume: bool) !Hash {
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
    try entries.ensureTotalCapacity(account_allocator, self.accounts.count());

    var accounts = self.accounts.iterator();
    while (accounts.next()) |account_entry| {
        const account = account_entry.value_ptr;

        _ = storage_arena.reset(.retain_capacity);
        const storage_allocator = storage_arena.allocator();
        var slots: std.ArrayListUnmanaged(Trie.Entry) = .empty;
        var stored = account.storage.iterator();
        while (stored.next()) |slot| {
            // A slot set back to zero is *absent* from the trie, not present
            // holding zero — the map keeps the entry, the trie must not.
            if (slot.value_ptr.* == 0) continue;
            var slot_bytes: [32]u8 = undefined;
            std.mem.writeInt(u256, &slot_bytes, slot.key_ptr.*, .big);
            const key = try storage_allocator.alloc(u8, 32);
            std.mem.writeInt(u256, key[0..32], keccak256(&slot_bytes), .big);
            try slots.append(storage_allocator, .{
                .key = key,
                .value = try Rlp.encodeInt(storage_allocator, slot.value_ptr.*),
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
        std.mem.writeInt(u160, &address_bytes, account_entry.key_ptr.*, .big);
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

        if (consume) {
            // Everything this account contributes is now captured in the
            // entry above. Freed with `self.allocator`, which is what
            // allocated them — not the caller's `allocator`, which may
            // differ. The emptied fields keep `deinit` safe to call after.
            account.storage.deinit(self.allocator);
            account.storage = .empty;
            if (self.ownsCode(account.code)) self.allocator.free(account.code);
            account.code = &.{};
        }
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

    // Account leaves must all be live at once — the trie needs them sorted —
    // so they share one arena. Storage tries do not: each is folded into its
    // account immediately, so they reuse a second arena reset per account.
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const account_allocator = arena.allocator();

    var storage_arena = std.heap.ArenaAllocator.init(allocator);
    defer storage_arena.deinit();

    var entries: std.ArrayListUnmanaged(Trie.Entry) = .empty;
    try entries.ensureTotalCapacity(account_allocator, @intCast(account_count));

    var i: u64 = 0;
    while (i < account_count) : (i += 1) {
        const address = std.mem.readInt(u160, bytes[pos..][0..20], .big);
        pos += 20;
        const balance = std.mem.readInt(u256, bytes[pos..][0..32], .little);
        pos += 32;
        const nonce = std.mem.readInt(u64, bytes[pos..][0..8], .little);
        pos += 8;
        const code_len = std.mem.readInt(u32, bytes[pos..][0..4], .little);
        pos += 4;
        const code = bytes[pos..][0..code_len];
        pos += code_len;

        const storage_count = std.mem.readInt(u64, bytes[pos..][0..8], .little);
        pos += 8;

        _ = storage_arena.reset(.retain_capacity);
        const storage_allocator = storage_arena.allocator();
        var slots: std.ArrayListUnmanaged(Trie.Entry) = .empty;
        try slots.ensureTotalCapacity(storage_allocator, @intCast(storage_count));
        var s: u64 = 0;
        while (s < storage_count) : (s += 1) {
            const slot = std.mem.readInt(u256, bytes[pos..][0..32], .little);
            pos += 32;
            const value = std.mem.readInt(u256, bytes[pos..][0..32], .little);
            pos += 32;
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
        const key = try account_allocator.alloc(u8, 32);
        std.mem.writeInt(u256, key[0..32], keccak256(&address_bytes), .big);

        entries.appendAssumeCapacity(.{
            .key = key,
            .value = try Rlp.encodeList(account_allocator, &.{
                try Rlp.encodeInt(account_allocator, nonce),
                try Rlp.encodeInt(account_allocator, balance),
                try Rlp.encodeBytes(account_allocator, &storage_root_bytes),
                try Rlp.encodeBytes(account_allocator, &code_hash_bytes),
            }),
        });
    }

    return .{ .block = block, .root = try Trie.hashRoot(allocator, entries.items) };
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
pub fn writeSnapshot(self: *const State, writer: *std.Io.Writer, block: u64, recent_hashes: []const Hash) !void {
    var buf8: [8]u8 = undefined;
    std.mem.writeInt(u64, &buf8, block, .little);
    try writer.writeAll(&buf8);
    std.mem.writeInt(u64, &buf8, self.accounts.count(), .little);
    try writer.writeAll(&buf8);

    var it = self.accounts.iterator();
    while (it.next()) |entry| {
        const account = entry.value_ptr;

        var addr_buf: [20]u8 = undefined;
        std.mem.writeInt(u160, &addr_buf, entry.key_ptr.*, .big);
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

        std.mem.writeInt(u64, &buf8, account.storage.count(), .little);
        try writer.writeAll(&buf8);
        var storage_it = account.storage.iterator();
        while (storage_it.next()) |slot| {
            std.mem.writeInt(u256, &buf32, slot.key_ptr.*, .little);
            try writer.writeAll(&buf32);
            std.mem.writeInt(u256, &buf32, slot.value_ptr.*, .little);
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

    var pos: usize = 0;
    const block = std.mem.readInt(u64, bytes[pos..][0..8], .little);
    pos += 8;
    const account_count = std.mem.readInt(u64, bytes[pos..][0..8], .little);
    pos += 8;

    try state.accounts.ensureTotalCapacity(allocator, @intCast(account_count));

    var i: u64 = 0;
    while (i < account_count) : (i += 1) {
        const address: Address = std.mem.readInt(u160, bytes[pos..][0..20], .big);
        pos += 20;
        const balance = std.mem.readInt(u256, bytes[pos..][0..32], .little);
        pos += 32;
        const nonce = std.mem.readInt(u64, bytes[pos..][0..8], .little);
        pos += 8;
        const code_len = std.mem.readInt(u32, bytes[pos..][0..4], .little);
        pos += 4;
        const code_bytes = bytes[pos..][0..code_len];
        pos += code_len;

        var account: Account = .{ .balance = balance, .nonce = nonce };
        if (code_bytes.len != 0) {
            // Borrowed from `bytes`, not copied (see `snapshot_bytes`).
            account.code = code_bytes;
        }

        const storage_count = std.mem.readInt(u64, bytes[pos..][0..8], .little);
        pos += 8;
        try account.storage.ensureTotalCapacity(allocator, @intCast(storage_count));
        var s: u64 = 0;
        while (s < storage_count) : (s += 1) {
            const slot = std.mem.readInt(u256, bytes[pos..][0..32], .little);
            pos += 32;
            const value = std.mem.readInt(u256, bytes[pos..][0..32], .little);
            pos += 32;
            account.storage.putAssumeCapacityNoClobber(slot, value);
        }

        try state.accounts.putNoClobber(allocator, address, account);
    }

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
