const std = @import("std");

pub const Stack = @import("Stack.zig");
pub const Memory = @import("Memory.zig");
pub const Interpreter = @import("Interpreter.zig");
pub const State = @import("State.zig");
pub const Rlp = @import("Rlp.zig");
pub const Trie = @import("Trie.zig");
pub const Transaction = @import("Transaction.zig").Transaction;
pub const AccessListEntry = @import("Transaction.zig").AccessListEntry;
pub const Block = @import("Block.zig").Block;
pub const Fork = @import("Fork.zig").Fork;
pub const Evm = @import("Evm.zig");
pub const Address = @import("Address.zig").Address;
pub const addressToHex = @import("Address.zig").toHex;
pub const Hash = @import("Hash.zig").Hash;
pub const keccak256 = @import("Hash.zig").keccak256;
pub const OpCode = @import("OpCode.zig").OpCode;
pub const Precompiles = @import("Precompiles.zig");
pub const Secp256k1 = @import("Secp256k1.zig");
pub const Bn128 = @import("Bn128.zig");
pub const gas = @import("gas.zig");

// Not `pub`: ffi.zig isn't meant to be used from Zig code, but its
// `export fn`s only make it into the compiled library if reachable here.
comptime {
    _ = @import("ffi.zig");
}

test {
    std.testing.refAllDecls(@This());
    // `Address` and `Hash` are plain integer aliases, so refAllDecls above
    // has nothing to recurse into; reference their files directly.
    std.testing.refAllDecls(@import("Address.zig"));
    std.testing.refAllDecls(@import("Hash.zig"));
    std.testing.refAllDecls(@import("Fork.zig"));
    // `Ripemd160.zig` isn't re-exported (internal detail of Precompiles.zig).
    std.testing.refAllDecls(@import("Ripemd160.zig"));
}
