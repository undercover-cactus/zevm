//! A decoded Ethereum transaction: Legacy, EIP-2930's access-list type
//! (type 1, Berlin), EIP-1559's fee-market type (type 2, London) or
//! EIP-4844's blob type (type 3, Cancun). EIP-7702 authorizations are not
//! supported.

const Address = @import("Address.zig").Address;

/// One EIP-2930 access-list entry: an account to start warm, and slots of
/// it to start warm too.
pub const AccessListEntry = struct {
    address: Address,
    storage_keys: []const u256,
};

pub const Transaction = struct {
    nonce: u64,
    /// For an EIP-1559 transaction this is `max_fee_per_gas`, the most it
    /// will pay per gas in total; what it actually pays depends on the
    /// block's base fee (see `Evm.executeTransaction`).
    gas_price: u256,
    gas_limit: u64,
    /// `null` means this transaction creates a contract, and `data` is its init code.
    to: ?Address,
    value: u256,
    /// Calldata for a call, init code for a contract creation.
    data: []const u8,

    /// For a Legacy transaction, 27/28 or an EIP-155 `chain_id * 2 + 35/36`.
    /// For a typed one, just the signature's y parity (0 or 1).
    v: u64,
    r: u256,
    s: u256,

    /// The chain id a typed transaction states outright. Null for Legacy,
    /// whose chain id (if any) is folded into `v` instead.
    chain_id: ?u256 = null,
    /// EIP-2930. Empty for Legacy transactions.
    access_list: []const AccessListEntry = &.{},
    /// EIP-1559's `max_priority_fee_per_gas`, the most the miner may get
    /// per gas on top of the base fee. Null for every other type, which
    /// pays `gas_price` outright.
    max_priority_fee: ?u256 = null,
    /// EIP-4844 (type 3): the most it will pay per unit of blob gas. Null
    /// for every other type.
    max_fee_per_blob_gas: ?u256 = null,
    /// EIP-4844: one versioned hash per blob the transaction carries, what
    /// `BLOBHASH` reads. The blobs themselves never reach execution.
    blob_versioned_hashes: []const u256 = &.{},
};
