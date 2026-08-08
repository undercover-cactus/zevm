//! A minimal, direct FFI binding to real libsecp256k1 (vendored under
//! `third_party/secp256k1/`, see `build.zig`'s doc comment). Just enough
//! for ECDSA public-key recovery: `Precompiles.zig`'s `ECRECOVER` and
//! `examples/sync_era1.zig`'s sender derivation. No custom C shim needed,
//! since modern libsecp256k1's public API is complete enough to call
//! directly.
//!
//! Struct layouts and flag values below are copied from
//! `third_party/secp256k1/include/secp256k1.h` and
//! `include/secp256k1_recovery.h`.

const std = @import("std");

const Context = opaque {};

/// `SECP256K1_CONTEXT_NONE`: the only context flag with any effect since
/// upstream deprecated `..._SIGN`/`..._VERIFY` (every context now supports both).
const context_none: c_uint = 1;
/// `SECP256K1_EC_UNCOMPRESSED`.
const ec_uncompressed: c_uint = 2;

const PubkeyRaw = extern struct { data: [64]u8 };
const RecoverableSigRaw = extern struct { data: [65]u8 };

extern fn secp256k1_context_create(flags: c_uint) ?*Context;
extern fn secp256k1_ecdsa_recoverable_signature_parse_compact(
    ctx: *const Context,
    sig: *RecoverableSigRaw,
    input64: *const [64]u8,
    recid: c_int,
) c_int;
extern fn secp256k1_ecdsa_recover(
    ctx: *const Context,
    pubkey: *PubkeyRaw,
    sig: *const RecoverableSigRaw,
    msghash32: *const [32]u8,
) c_int;
extern fn secp256k1_ec_pubkey_serialize(
    ctx: *const Context,
    output: [*]u8,
    outputlen: *usize,
    pubkey: *const PubkeyRaw,
    flags: c_uint,
) c_int;

pub const Message = [32]u8;
/// Compact recoverable signature: `r[32] || s[32] || recovery_id[1]`,
/// recovery_id in `0..3`.
pub const Signature = [65]u8;
/// Uncompressed public key: `0x04 || x[32] || y[32]`.
pub const PublicKey = [65]u8;

pub const Secp256k1 = struct {
    context: *Context,

    pub fn init() !Secp256k1 {
        const ctx = secp256k1_context_create(context_none) orelse return error.FailedInitialize;
        return .{ .context = ctx };
    }

    pub fn recoverPubkey(self: Secp256k1, msg: Message, sig: Signature) !PublicKey {
        if (sig[64] >= 4) return error.InvalidRecoveryID;

        var raw_sig: RecoverableSigRaw = undefined;
        if (secp256k1_ecdsa_recoverable_signature_parse_compact(
            self.context,
            &raw_sig,
            sig[0..64],
            @intCast(sig[64]),
        ) == 0) return error.RecoverFailed;

        var raw_pubkey: PubkeyRaw = undefined;
        if (secp256k1_ecdsa_recover(self.context, &raw_pubkey, &raw_sig, &msg) == 0) {
            return error.RecoverFailed;
        }

        var out: PublicKey = undefined;
        var out_len: usize = out.len;
        if (secp256k1_ec_pubkey_serialize(self.context, &out, &out_len, &raw_pubkey, ec_uncompressed) == 0) {
            return error.RecoverFailed;
        }
        return out;
    }
};

test "recover pubkey" {
    var msg: Message = undefined;
    _ = try std.fmt.hexToBytes(&msg, "ce0677bb30baa8cf067c88db9811f4333d131bf8bcf12fe7065d211dce971008");
    var sig: Signature = undefined;
    _ = try std.fmt.hexToBytes(&sig, "90f27b8b488db00b00606796d2987f6a5f59ae62ea05effe84fef5b8b0e549984a691139ad57a3f0b906637673aa2f63d1f55cb1a69199d4009eea23ceaddc9301");

    const secp = try Secp256k1.init();
    const pubkey = try secp.recoverPubkey(msg, sig);

    var expected: PublicKey = undefined;
    _ = try std.fmt.hexToBytes(&expected, "04e32df42865e97135acfb65f3bae71bdc86f4d49150ad6a440b6f15878109880a0a2b2667f7e725ceea70c673093bf67663e0312623c8e091b13cf2c0f11ef652");
    try std.testing.expectEqualSlices(u8, &expected, &pubkey);
}

test "invalid recovery id is rejected" {
    const secp = try Secp256k1.init();
    var sig: Signature = [_]u8{0} ** 65;
    sig[63] = 1; // nonzero s
    sig[64] = 4; // only 0-3 are valid
    try std.testing.expectError(error.InvalidRecoveryID, secp.recoverPubkey([_]u8{0} ** 32, sig));
}
