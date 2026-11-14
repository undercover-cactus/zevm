//! EIP-2537 (Prague): the BLS12-381 precompiles (0x0b to 0x11), as a thin
//! layer over blst, which is already vendored for c-kzg-4844 (see
//! `build.zig`). revm and reth use the same library for these.
//!
//! Encodings, from the EIP: a base field element is 64 big-endian bytes whose
//! top 16 are zero and whose value is below the modulus; an Fp2 element is
//! `c0 || c1`; a point is `x || y`, with all zeros meaning the point at
//! infinity (which blst represents the same way in affine form). Scalars are
//! 32 big-endian bytes and need not be reduced. Every malformed input is
//! `error.InvalidInput`, which the caller turns into a failure that forfeits
//! all gas.

const std = @import("std");

const c = @cImport({
    @cInclude("blst.h");
});

const g1_size = 128;
const g2_size = 256;
const scalar_size = 32;
const g1_msm_pair_size = g1_size + scalar_size;
const g2_msm_pair_size = g2_size + scalar_size;
const pairing_pair_size = g1_size + g2_size;

pub const g1_add_gas: u64 = 375;
pub const g2_add_gas: u64 = 600;
pub const map_fp_to_g1_gas: u64 = 5500;
pub const map_fp2_to_g2_gas: u64 = 23800;
const g1_mul_gas: u64 = 12000;
const g2_mul_gas: u64 = 22500;

/// Per-mille discount for an MSM of `k` pairs, `k` from 1 to 128, from the
/// EIP's tables. Larger MSMs get the last entry.
const g1_msm_discount = [128]u16{
    1000, 949, 848, 797, 764, 750, 738, 728, 719, 712, 705, 698, 692, 687, 682, 677,
    673,  669, 665, 661, 658, 654, 651, 648, 645, 642, 640, 637, 635, 632, 630, 627,
    625,  623, 621, 619, 617, 615, 613, 611, 609, 608, 606, 604, 603, 601, 599, 598,
    596,  595, 593, 592, 591, 589, 588, 586, 585, 584, 582, 581, 580, 579, 577, 576,
    575,  574, 573, 572, 570, 569, 568, 567, 566, 565, 564, 563, 562, 561, 560, 559,
    558,  557, 556, 555, 554, 553, 552, 551, 550, 549, 548, 547, 547, 546, 545, 544,
    543,  542, 541, 540, 540, 539, 538, 537, 536, 536, 535, 534, 533, 532, 532, 531,
    530,  529, 528, 528, 527, 526, 525, 525, 524, 523, 522, 522, 521, 520, 520, 519,
};
const g2_msm_discount = [128]u16{
    1000, 1000, 923, 884, 855, 832, 812, 796, 782, 770, 759, 749, 740, 732, 724, 717,
    711,  704,  699, 693, 688, 683, 679, 674, 670, 666, 663, 659, 655, 652, 649, 646,
    643,  640,  637, 634, 632, 629, 627, 624, 622, 620, 618, 615, 613, 611, 609, 607,
    606,  604,  602, 600, 598, 597, 595, 593, 592, 590, 589, 587, 586, 584, 583, 582,
    580,  579,  578, 576, 575, 574, 573, 571, 570, 569, 568, 567, 566, 565, 563, 562,
    561,  560,  559, 558, 557, 556, 555, 554, 553, 552, 552, 551, 550, 549, 548, 547,
    546,  545,  545, 544, 543, 542, 541, 541, 540, 539, 538, 537, 537, 536, 535, 535,
    534,  533,  532, 532, 531, 530, 530, 529, 528, 528, 527, 526, 526, 525, 524, 524,
};

/// `k * mul_gas * discount(k) / 1000`, with `k` the number of whole pairs.
/// A length that is not a whole number of pairs still gets a price; the
/// precompile then rejects it.
fn msmGas(input_len: usize, pair_size: usize, mul_gas: u64, discount: *const [128]u16) u64 {
    const k: u64 = input_len / pair_size;
    if (k == 0) return 0;
    const d: u64 = discount[@min(k, discount.len) - 1];
    return k * mul_gas * d / 1000;
}

pub fn g1MsmGas(input_len: usize) u64 {
    return msmGas(input_len, g1_msm_pair_size, g1_mul_gas, &g1_msm_discount);
}

pub fn g2MsmGas(input_len: usize) u64 {
    return msmGas(input_len, g2_msm_pair_size, g2_mul_gas, &g2_msm_discount);
}

pub fn pairingGas(input_len: usize) u64 {
    return 32600 * @as(u64, input_len / pairing_pair_size) + 37700;
}

// --- encoding ---

fn decodeFp(bytes: *const [64]u8) !c.blst_fp {
    for (bytes[0..16]) |b| if (b != 0) return error.InvalidInput;
    var fp: c.blst_fp = undefined;
    c.blst_fp_from_bendian(&fp, bytes[16..64]);
    // blst reduces modulo p on the way in, so a value at or above p comes
    // back out different.
    var back: [48]u8 = undefined;
    c.blst_bendian_from_fp(&back, &fp);
    if (!std.mem.eql(u8, &back, bytes[16..64])) return error.InvalidInput;
    return fp;
}

fn decodeFp2(bytes: *const [128]u8) !c.blst_fp2 {
    return .{ .fp = .{ try decodeFp(bytes[0..64]), try decodeFp(bytes[64..128]) } };
}

fn encodeFp(out: *[64]u8, fp: *const c.blst_fp) void {
    @memset(out[0..16], 0);
    c.blst_bendian_from_fp(out[16..64], fp);
}

/// A G1 point that is on the curve, and also in the prime-order subgroup if
/// `in_subgroup` (the additions skip that check, MSM and pairing do not).
fn decodeG1(bytes: *const [g1_size]u8, in_subgroup: bool) !c.blst_p1_affine {
    const p: c.blst_p1_affine = .{ .x = try decodeFp(bytes[0..64]), .y = try decodeFp(bytes[64..128]) };
    if (!c.blst_p1_affine_on_curve(&p)) return error.InvalidInput;
    if (in_subgroup and !c.blst_p1_affine_in_g1(&p)) return error.InvalidInput;
    return p;
}

fn decodeG2(bytes: *const [g2_size]u8, in_subgroup: bool) !c.blst_p2_affine {
    const p: c.blst_p2_affine = .{ .x = try decodeFp2(bytes[0..128]), .y = try decodeFp2(bytes[128..256]) };
    if (!c.blst_p2_affine_on_curve(&p)) return error.InvalidInput;
    if (in_subgroup and !c.blst_p2_affine_in_g2(&p)) return error.InvalidInput;
    return p;
}

fn encodeG1(allocator: std.mem.Allocator, p: *const c.blst_p1) ![]u8 {
    const out = try allocator.alloc(u8, g1_size);
    if (c.blst_p1_is_inf(p)) {
        @memset(out, 0);
        return out;
    }
    var a: c.blst_p1_affine = undefined;
    c.blst_p1_to_affine(&a, p);
    encodeFp(out[0..64], &a.x);
    encodeFp(out[64..128], &a.y);
    return out;
}

fn encodeG2(allocator: std.mem.Allocator, p: *const c.blst_p2) ![]u8 {
    const out = try allocator.alloc(u8, g2_size);
    if (c.blst_p2_is_inf(p)) {
        @memset(out, 0);
        return out;
    }
    var a: c.blst_p2_affine = undefined;
    c.blst_p2_to_affine(&a, p);
    encodeFp(out[0..64], &a.x.fp[0]);
    encodeFp(out[64..128], &a.x.fp[1]);
    encodeFp(out[128..192], &a.y.fp[0]);
    encodeFp(out[192..256], &a.y.fp[1]);
    return out;
}

/// blst takes scalars little-endian.
fn scalarLittleEndian(bytes: *const [scalar_size]u8) [scalar_size]u8 {
    var out: [scalar_size]u8 = undefined;
    for (bytes, 0..) |b, i| out[scalar_size - 1 - i] = b;
    return out;
}

// --- operations ---

/// BLS12_G1ADD (0x0b).
pub fn g1Add(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
    if (input.len != 2 * g1_size) return error.InvalidInput;
    const a = try decodeG1(input[0..g1_size], false);
    const b = try decodeG1(input[g1_size..][0..g1_size], false);
    var sum: c.blst_p1 = undefined;
    c.blst_p1_from_affine(&sum, &a);
    c.blst_p1_add_or_double_affine(&sum, &sum, &b);
    return encodeG1(allocator, &sum);
}

/// BLS12_G2ADD (0x0d).
pub fn g2Add(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
    if (input.len != 2 * g2_size) return error.InvalidInput;
    const a = try decodeG2(input[0..g2_size], false);
    const b = try decodeG2(input[g2_size..][0..g2_size], false);
    var sum: c.blst_p2 = undefined;
    c.blst_p2_from_affine(&sum, &a);
    c.blst_p2_add_or_double_affine(&sum, &sum, &b);
    return encodeG2(allocator, &sum);
}

/// BLS12_G1MSM (0x0c): the sum of `scalar_i * point_i`. Pairs whose point is
/// infinity or whose scalar is zero add nothing and are dropped before blst
/// sees them, as revm does.
pub fn g1Msm(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
    if (input.len == 0 or input.len % g1_msm_pair_size != 0) return error.InvalidInput;
    const k = input.len / g1_msm_pair_size;
    const points = try allocator.alloc(c.blst_p1_affine, k);
    defer allocator.free(points);
    const scalars = try allocator.alloc([scalar_size]u8, k);
    defer allocator.free(scalars);
    var n: usize = 0;
    for (0..k) |i| {
        const pair = input[i * g1_msm_pair_size ..][0..g1_msm_pair_size];
        const p = try decodeG1(pair[0..g1_size], true);
        const scalar = pair[g1_size..][0..scalar_size];
        if (c.blst_p1_affine_is_inf(&p) or std.mem.allEqual(u8, scalar, 0)) continue;
        points[n] = p;
        scalars[n] = scalarLittleEndian(scalar);
        n += 1;
    }

    var result = std.mem.zeroes(c.blst_p1);
    if (n == 1) {
        var p: c.blst_p1 = undefined;
        c.blst_p1_from_affine(&p, &points[0]);
        c.blst_p1_mult(&result, &p, &scalars[0], 8 * scalar_size);
    } else if (n > 1) {
        const point_ptrs = try allocator.alloc([*c]const c.blst_p1_affine, n);
        defer allocator.free(point_ptrs);
        const scalar_ptrs = try allocator.alloc([*c]const u8, n);
        defer allocator.free(scalar_ptrs);
        for (0..n) |i| {
            point_ptrs[i] = &points[i];
            scalar_ptrs[i] = &scalars[i];
        }
        const scratch = try allocator.alloc(c.limb_t, (c.blst_p1s_mult_pippenger_scratch_sizeof(n) + @sizeOf(c.limb_t) - 1) / @sizeOf(c.limb_t));
        defer allocator.free(scratch);
        c.blst_p1s_mult_pippenger(&result, point_ptrs.ptr, n, scalar_ptrs.ptr, 8 * scalar_size, scratch.ptr);
    }
    return encodeG1(allocator, &result);
}

/// BLS12_G2MSM (0x0e), as `g1Msm` over G2.
pub fn g2Msm(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
    if (input.len == 0 or input.len % g2_msm_pair_size != 0) return error.InvalidInput;
    const k = input.len / g2_msm_pair_size;
    const points = try allocator.alloc(c.blst_p2_affine, k);
    defer allocator.free(points);
    const scalars = try allocator.alloc([scalar_size]u8, k);
    defer allocator.free(scalars);
    var n: usize = 0;
    for (0..k) |i| {
        const pair = input[i * g2_msm_pair_size ..][0..g2_msm_pair_size];
        const p = try decodeG2(pair[0..g2_size], true);
        const scalar = pair[g2_size..][0..scalar_size];
        if (c.blst_p2_affine_is_inf(&p) or std.mem.allEqual(u8, scalar, 0)) continue;
        points[n] = p;
        scalars[n] = scalarLittleEndian(scalar);
        n += 1;
    }

    var result = std.mem.zeroes(c.blst_p2);
    if (n == 1) {
        var p: c.blst_p2 = undefined;
        c.blst_p2_from_affine(&p, &points[0]);
        c.blst_p2_mult(&result, &p, &scalars[0], 8 * scalar_size);
    } else if (n > 1) {
        const point_ptrs = try allocator.alloc([*c]const c.blst_p2_affine, n);
        defer allocator.free(point_ptrs);
        const scalar_ptrs = try allocator.alloc([*c]const u8, n);
        defer allocator.free(scalar_ptrs);
        for (0..n) |i| {
            point_ptrs[i] = &points[i];
            scalar_ptrs[i] = &scalars[i];
        }
        const scratch = try allocator.alloc(c.limb_t, (c.blst_p2s_mult_pippenger_scratch_sizeof(n) + @sizeOf(c.limb_t) - 1) / @sizeOf(c.limb_t));
        defer allocator.free(scratch);
        c.blst_p2s_mult_pippenger(&result, point_ptrs.ptr, n, scalar_ptrs.ptr, 8 * scalar_size, scratch.ptr);
    }
    return encodeG2(allocator, &result);
}

/// BLS12_PAIRING_CHECK (0x0f): whether the product of `e(P_i, Q_i)` is one,
/// as a 32-byte word. A pair with either point at infinity contributes one
/// and is skipped, but is still validated first.
pub fn pairing(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
    if (input.len == 0 or input.len % pairing_pair_size != 0) return error.InvalidInput;
    var product: c.blst_fp12 = undefined;
    var have_product = false;
    var i: usize = 0;
    while (i < input.len) : (i += pairing_pair_size) {
        const p = try decodeG1(input[i..][0..g1_size], true);
        const q = try decodeG2(input[i + g1_size ..][0..g2_size], true);
        if (c.blst_p1_affine_is_inf(&p) or c.blst_p2_affine_is_inf(&q)) continue;
        var loop: c.blst_fp12 = undefined;
        c.blst_miller_loop(&loop, &q, &p);
        if (have_product) {
            c.blst_fp12_mul(&product, &product, &loop);
        } else {
            product = loop;
            have_product = true;
        }
    }
    var is_one = true;
    if (have_product) {
        c.blst_final_exp(&product, &product);
        is_one = c.blst_fp12_is_one(&product);
    }
    const out = try allocator.alloc(u8, 32);
    @memset(out, 0);
    out[31] = @intFromBool(is_one);
    return out;
}

/// BLS12_MAP_FP_TO_G1 (0x10).
pub fn mapFpToG1(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
    if (input.len != 64) return error.InvalidInput;
    const u = try decodeFp(input[0..64]);
    var p: c.blst_p1 = undefined;
    c.blst_map_to_g1(&p, &u, null);
    return encodeG1(allocator, &p);
}

/// BLS12_MAP_FP2_TO_G2 (0x11).
pub fn mapFp2ToG2(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
    if (input.len != 128) return error.InvalidInput;
    const u = try decodeFp2(input[0..128]);
    var p: c.blst_p2 = undefined;
    c.blst_map_to_g2(&p, &u, null);
    return encodeG2(allocator, &p);
}

test "MSM and pairing gas follow EIP-2537's discount tables and formula" {
    try std.testing.expectEqual(@as(u64, 0), g1MsmGas(159));
    try std.testing.expectEqual(@as(u64, 12000), g1MsmGas(160));
    try std.testing.expectEqual(@as(u64, 2 * 12000 * 949 / 1000), g1MsmGas(2 * 160));
    // Past 128 pairs the discount stays at the last entry.
    try std.testing.expectEqual(@as(u64, 200 * 12000 * 519 / 1000), g1MsmGas(200 * 160));
    try std.testing.expectEqual(@as(u64, 2 * 22500), g2MsmGas(2 * 288));
    try std.testing.expectEqual(@as(u64, 200 * 22500 * 524 / 1000), g2MsmGas(200 * 288));
    try std.testing.expectEqual(@as(u64, 2 * 32600 + 37700), pairingGas(2 * 384 + 1));
}

fn fromHex(comptime hex: []const u8) [hex.len / 2]u8 {
    var out: [hex.len / 2]u8 = undefined;
    _ = std.fmt.hexToBytes(&out, hex) catch unreachable;
    return out;
}

test "G1ADD adds 2*G1 and 3*G1 to 5*G1 (geth's vector)" {
    const input = fromHex("000000000000000000000000000000000572cbea904d67468808c8eb50a9450c9721db309128012543902d0ac358a62ae28f75bb8f1c7c42c39a8c5529bf0f4e00000000000000000000000000000000166a9d8cabc673a322fda673779d8e3822ba3ecb8670e461f73bb9021d5fd76a4c56d9d4cd16bd1bba86881979749d280000000000000000000000000000000009ece308f9d1f0131765212deca99697b112d61f9be9a5f1f3780a51335b3ff981747a0b2ca2179b96d2c0c9024e522400000000000000000000000000000000032b80d3a6f5b09f8a84623389c5f80ca69a0cddabc3097f9d9c27310fd43be6e745256c634af45ca3473b0590ae30d1");
    const expected = fromHex("0000000000000000000000000000000010e7791fb972fe014159aa33a98622da3cdc98ff707965e536d8636b5fcc5ac7a91a8c46e59a00dca575af0f18fb13dc0000000000000000000000000000000016ba437edcc6551e30c10512367494bfb6b01cc6681e8a4c3cd2501832ab5c4abc40b4578b85cbaffbf0bcd70d67c6e2");
    const out = try g1Add(std.testing.allocator, &input);
    defer std.testing.allocator.free(out);
    try std.testing.expectEqualSlices(u8, &expected, out);

    // A coordinate at or above the modulus, or a nonzero top byte, is rejected.
    var bad = input;
    bad[0] = 1;
    try std.testing.expectError(error.InvalidInput, g1Add(std.testing.allocator, &bad));
    try std.testing.expectError(error.InvalidInput, g1Add(std.testing.allocator, input[0..255]));
}

const g1_generator = fromHex("0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb" ++
    "0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1");
const g2_generator = fromHex("00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8" ++
    "0000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e" ++
    "000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801" ++
    "000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be");

test "PAIRING_CHECK: e(G1, G2) * e(-G1, G2) is one, e(G1, G2) alone is not" {
    const p: u384 = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab;
    var neg_g1 = g1_generator;
    const y = std.mem.readInt(u384, g1_generator[80..128], .big);
    std.mem.writeInt(u384, neg_g1[80..128], p - y, .big);

    const one_pair = g1_generator ++ g2_generator;
    const out = try pairing(std.testing.allocator, &one_pair);
    defer std.testing.allocator.free(out);
    try std.testing.expectEqual(@as(u8, 0), out[31]);

    const two_pairs = one_pair ++ neg_g1 ++ g2_generator;
    const out2 = try pairing(std.testing.allocator, &two_pairs);
    defer std.testing.allocator.free(out2);
    try std.testing.expectEqual(@as(u8, 1), out2[31]);

    // A pair with a point at infinity contributes one.
    const with_infinity = one_pair ++ neg_g1 ++ g2_generator ++ [_]u8{0} ** g1_size ++ g2_generator;
    const out3 = try pairing(std.testing.allocator, &with_infinity);
    defer std.testing.allocator.free(out3);
    try std.testing.expectEqual(@as(u8, 1), out3[31]);

    try std.testing.expectError(error.InvalidInput, pairing(std.testing.allocator, &.{}));
}

test "G1MSM: 2*G1 + 3*G1 matches G1ADD's 5*G1, and a zero scalar drops its pair" {
    var input: [3 * g1_msm_pair_size]u8 = undefined;
    for (0..3) |i| {
        const pair = input[i * g1_msm_pair_size ..][0..g1_msm_pair_size];
        pair[0..g1_size].* = g1_generator;
        std.mem.writeInt(u256, pair[g1_size..][0..32], i + 2, .big);
    }
    // Third pair: scalar 4, then zeroed out.
    std.mem.writeInt(u256, input[2 * g1_msm_pair_size + g1_size ..][0..32], 0, .big);
    const out = try g1Msm(std.testing.allocator, &input);
    defer std.testing.allocator.free(out);
    const expected = fromHex("0000000000000000000000000000000010e7791fb972fe014159aa33a98622da3cdc98ff707965e536d8636b5fcc5ac7a91a8c46e59a00dca575af0f18fb13dc0000000000000000000000000000000016ba437edcc6551e30c10512367494bfb6b01cc6681e8a4c3cd2501832ab5c4abc40b4578b85cbaffbf0bcd70d67c6e2");
    try std.testing.expectEqualSlices(u8, &expected, out);
}
