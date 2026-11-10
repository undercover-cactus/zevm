//! KZG proof verification over BLS12-381, for Cancun's point evaluation
//! precompile (EIP-4844). A thin binding to vendored c-kzg-4844 (see
//! `build.zig`), the same library revm and reth use.

const std = @import("std");

const c = @cImport({
    @cInclude("ckzg.h");
});

/// The Ethereum KZG ceremony's output, as c-kzg ships it: a count of G1
/// points, a count of G2 points, then the G1 points in Lagrange form, the G2
/// points in monomial form and the G1 points in monomial form, one hex
/// string each.
const trusted_setup_text = @embedFile("kzg_trusted_setup");

var settings: c.KZGSettings = undefined;
var loaded = false;

/// Loads the trusted setup now rather than on first use. Loading is not
/// thread-safe, so anything that runs precompiles on several threads at once
/// calls this first; after it, verification only reads the settings.
pub fn init() void {
    if (loaded) return;
    load() catch |err| std.debug.panic("loading the KZG trusted setup failed: {s}", .{@errorName(err)});
    loaded = true;
}

fn load() !void {
    var it = std.mem.tokenizeAny(u8, trusted_setup_text, " \t\r\n");
    const g1_count = try std.fmt.parseUnsigned(usize, it.next() orelse return error.TruncatedSetup, 10);
    const g2_count = try std.fmt.parseUnsigned(usize, it.next() orelse return error.TruncatedSetup, 10);

    // c-kzg converts these into its own point representation, so the bytes
    // are only needed for the duration of the call.
    const allocator = std.heap.page_allocator;
    const g1_lagrange = try allocator.alloc(u8, g1_count * 48);
    defer allocator.free(g1_lagrange);
    const g2_monomial = try allocator.alloc(u8, g2_count * 96);
    defer allocator.free(g2_monomial);
    const g1_monomial = try allocator.alloc(u8, g1_count * 48);
    defer allocator.free(g1_monomial);
    try readPoints(&it, g1_lagrange, 48);
    try readPoints(&it, g2_monomial, 96);
    try readPoints(&it, g1_monomial, 48);

    // The last argument is precomputation for EIP-7594's cell proofs, which
    // proof verification never uses.
    if (c.load_trusted_setup(&settings, g1_monomial.ptr, g1_monomial.len, g1_lagrange.ptr, g1_lagrange.len, g2_monomial.ptr, g2_monomial.len, 0) != c.C_KZG_OK) {
        return error.InvalidSetup;
    }
}

fn readPoints(it: *std.mem.TokenIterator(u8, .any), out: []u8, point_size: usize) !void {
    var i: usize = 0;
    while (i < out.len) : (i += point_size) {
        const hex = it.next() orelse return error.TruncatedSetup;
        if (hex.len != point_size * 2) return error.InvalidSetup;
        _ = try std.fmt.hexToBytes(out[i..][0..point_size], hex);
    }
}

/// Whether `proof` shows that the polynomial committed to by `commitment`
/// evaluates to `y` at `z`. False for any malformed input as well (a point
/// not on the curve or not in the subgroup, a field element not below the
/// BLS12-381 scalar modulus), which the precompile treats the same as a
/// proof that does not verify.
pub fn verifyProof(commitment: *const [48]u8, z: *const [32]u8, y: *const [32]u8, proof: *const [48]u8) bool {
    init();
    var ok = false;
    if (c.verify_kzg_proof(&ok, @ptrCast(commitment), @ptrCast(z), @ptrCast(y), @ptrCast(proof), &settings) != c.C_KZG_OK) return false;
    return ok;
}
