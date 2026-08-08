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
const Address = @import("Address.zig").Address;

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
    destroyed: struct { address: Address, code: []const u8 },
};

pub const Checkpoint = usize;

allocator: std.mem.Allocator,
accounts: std.AutoHashMapUnmanaged(Address, Account) = .empty,
journal: std.ArrayListUnmanaged(Change) = .empty,

const State = @This();

pub fn init(allocator: std.mem.Allocator) State {
    return .{ .allocator = allocator };
}

pub fn deinit(self: *State) void {
    var it = self.accounts.valueIterator();
    while (it.next()) |account| {
        if (account.code.len != 0) self.allocator.free(account.code);
        account.storage.deinit(self.allocator);
    }
    // A `.destroyed` entry left in the journal (never undone by a
    // `revertTo`) is the only remaining reference to that code buffer,
    // since `destroyAccount` cleared the account's own pointer to it.
    for (self.journal.items) |change| {
        if (change == .destroyed) self.allocator.free(change.destroyed.code);
    }
    self.accounts.deinit(self.allocator);
    self.journal.deinit(self.allocator);
}

pub fn get(self: *const State, address: Address) Account {
    return self.accounts.get(address) orelse .{};
}

pub fn exists(self: *const State, address: Address) bool {
    return self.accounts.contains(address);
}

pub fn getBalance(self: *const State, address: Address) u256 {
    return self.get(address).balance;
}

pub fn getCode(self: *const State, address: Address) []const u8 {
    return self.get(address).code;
}

/// Records that `address` is about to be touched for the first time, if it
/// is, so `revertTo` can remove it entirely rather than merely resetting
/// its fields, keeping `exists()` accurate after a rollback.
fn touch(self: *State, address: Address) !void {
    if (self.accounts.contains(address)) return;
    try self.journal.append(self.allocator, .{ .created = address });
    try self.accounts.put(self.allocator, address, .{});
}

pub fn setBalance(self: *State, address: Address, balance: u256) !void {
    try self.touch(address);
    const account = self.accounts.getPtr(address).?;
    if (account.balance == balance) return;
    try self.journal.append(self.allocator, .{ .balance = .{ .address = address, .old = account.balance } });
    account.balance = balance;
}

/// Adds `amount` to `address`'s balance without journaling, for callers
/// that will never revert this specific change (e.g. block/uncle rewards).
pub fn creditBalance(self: *State, address: Address, amount: u256) !void {
    const entry = try self.accounts.getOrPutValue(self.allocator, address, .{});
    entry.value_ptr.balance += amount;
}

pub fn setNonce(self: *State, address: Address, nonce: u64) !void {
    try self.touch(address);
    const account = self.accounts.getPtr(address).?;
    if (account.nonce == nonce) return;
    try self.journal.append(self.allocator, .{ .nonce = .{ .address = address, .old = account.nonce } });
    account.nonce = nonce;
}

/// Sets `address`'s code, `CREATE`'s job only. Code is write-once: this
/// asserts the account doesn't already have code, rather than journaling a
/// code change. The invariant holds even across a `destroyAccount`, since
/// it clears code back to empty first.
pub fn setCode(self: *State, address: Address, code: []const u8) !void {
    try self.touch(address);
    const account = self.accounts.getPtr(address).?;
    std.debug.assert(account.code.len == 0);
    if (code.len != 0) account.code = try self.allocator.dupe(u8, code);
}

/// Wipes `address`'s code, `SELFDESTRUCT`'s job: the one exception to code
/// otherwise being immutable once set. Balance isn't handled here;
/// `SELFDESTRUCT` moves it out via `transfer`/`setBalance` first. The code
/// buffer is freed in `deinit` either way, via the account or the journal.
pub fn destroyAccount(self: *State, address: Address) !void {
    const account = self.accounts.getPtr(address) orelse return;
    if (account.code.len == 0) return;
    try self.journal.append(self.allocator, .{ .destroyed = .{ .address = address, .code = account.code } });
    account.code = &.{};
}

pub fn getStorage(self: *const State, address: Address, slot: u256) u256 {
    const account = self.accounts.get(address) orelse return 0;
    return account.storage.get(slot) orelse 0;
}

pub fn setStorage(self: *State, address: Address, slot: u256, value: u256) !void {
    try self.touch(address);
    const account = self.accounts.getPtr(address).?;
    // `getOrPut` does one probe for the check-and-set instead of a separate
    // `get` + `put`. SSTORE is by far the hottest caller of this.
    const entry = try account.storage.getOrPut(self.allocator, slot);
    const old: u256 = if (entry.found_existing) entry.value_ptr.* else 0;
    if (!entry.found_existing) entry.value_ptr.* = 0; // must initialize a freshly created slot regardless
    if (old == value) return;
    try self.journal.append(self.allocator, .{ .storage = .{ .address = address, .slot = slot, .old = old } });
    entry.value_ptr.* = value;
}

/// Moves `value` from `from` to `to`. Returns `false` (no-op) if `from`
/// doesn't have enough balance, matching the EVM's "call fails, nothing
/// moves" behavior rather than a partial transfer.
pub fn transfer(self: *State, from: Address, to: Address, value: u256) !bool {
    if (value == 0) return true;
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
            .balance => |c| self.accounts.getPtr(c.address).?.balance = c.old,
            .nonce => |c| self.accounts.getPtr(c.address).?.nonce = c.old,
            .storage => |c| {
                // `setStorage` always `touch`es the account and `put`s the
                // slot before this entry could exist, so both are
                // guaranteed present: direct pointer writes avoid a
                // fallible re-insertion here.
                self.accounts.getPtr(c.address).?.storage.getPtr(c.slot).?.* = c.old;
            },
            .created => |address| {
                var kv = self.accounts.fetchRemove(address).?;
                if (kv.value.code.len != 0) self.allocator.free(kv.value.code);
                kv.value.storage.deinit(self.allocator);
            },
            .destroyed => |c| self.accounts.getPtr(c.address).?.code = c.code,
        }
    }
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
