//! A Block struct.

const Address = @import("Address.zig").Address;
const Transaction = @import("Transaction.zig").Transaction;
const Hash = @import("Hash.zig").Hash;

pub const Block = struct {
    number: u64,
    miner: Address,
    transactions: []const Entry,
    uncles: []const Uncle = &.{},
    /// EIP-4895 (Shanghai): beacon chain withdrawals, credited after the
    /// block's transactions.
    withdrawals: []const Withdrawal = &.{},

    timestamp: u64 = 0,
    gas_limit: u64 = 0,
    /// DIFFICULTY pre-merge, PREVRANDAO post-merge.
    difficulty: u256 = 0,
    /// 0 pre-London (EIP-1559).
    base_fee: u256 = 0,
    chain_id: u256 = 1,
    recent_hashes: []const Hash = &.{},
    /// EIP-2935 (Prague): the parent's hash, written into the history
    /// storage contract before the block's transactions.
    parent_hash: Hash = 0,
    /// EIP-4844 (Cancun): the header's `excess_blob_gas`, which sets the
    /// block's blob base fee. 0 before Cancun.
    excess_blob_gas: u64 = 0,
    /// EIP-4788 (Cancun): the header's `parent_beacon_block_root`, written
    /// into the beacon roots contract before the block's transactions.
    parent_beacon_block_root: Hash = 0,

    pub const Entry = struct {
        tx: Transaction,
        from: Address,
    };

    /// A withdrawal, reduced to what its balance credit needs.
    pub const Withdrawal = struct {
        address: Address,
        /// In gwei, as the beacon chain counts it.
        amount: u64,
    };

    /// An uncle (ommer) block, reduced to what its reward calculation needs.
    pub const Uncle = struct {
        number: u64,
        miner: Address,
    };
};
