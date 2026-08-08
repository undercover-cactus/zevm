//! A Block struct.

const Address = @import("Address.zig").Address;
const Transaction = @import("Transaction.zig").Transaction;
const Hash = @import("Hash.zig").Hash;

pub const Block = struct {
    number: u64,
    miner: Address,
    transactions: []const Entry,
    uncles: []const Uncle = &.{},

    timestamp: u64 = 0,
    gas_limit: u64 = 0,
    /// DIFFICULTY pre-merge, PREVRANDAO post-merge.
    difficulty: u256 = 0,
    /// 0 pre-London (EIP-1559).
    base_fee: u256 = 0,
    chain_id: u256 = 1,
    recent_hashes: []const Hash = &.{},

    pub const Entry = struct {
        tx: Transaction,
        from: Address,
    };

    /// An uncle (ommer) block, reduced to what its reward calculation needs.
    pub const Uncle = struct {
        number: u64,
        miner: Address,
    };
};
