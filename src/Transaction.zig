//! A decoded Ethereum transaction. Only the Legacy (pre-EIP-2718) format is
//! supported, predating EIP-1559 fee markets, EIP-2930 access lists,
//! EIP-4844 blobs, and EIP-7702 authorizations.

const Address = @import("Address.zig").Address;

pub const Transaction = struct {
    nonce: u64,
    gas_price: u256,
    gas_limit: u64,
    /// `null` means this transaction creates a contract, and `data` is its init code.
    to: ?Address,
    value: u256,
    /// Calldata for a call, init code for a contract creation.
    data: []const u8,

    v: u64,
    r: u256,
    s: u256,
};
