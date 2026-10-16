//! BN128 (alt_bn128 / BN254) elliptic curve arithmetic and the optimal ate
//! pairing, for the `ECADD`/`ECMUL`/`ECPAIRING` precompiles (EIP-196,
//! EIP-197, Byzantium). Ported directly from `py_ecc`'s `bn128_curve.py`/
//! `bn128_pairing.py`/`bn128_field_elements.py` — the reference
//! implementation the EIPs themselves cite as "probably most self-contained
//! and best readable", and what `ethereum/execution-specs`' own Byzantium
//! fork package (`py_ecc.optimized_bn128`) is built on. Deliberately the
//! simple, non-Jacobian, non-tower-optimized formulation (affine
//! coordinates throughout, `Fq12` as one flat degree-12 extension rather
//! than the `Fq2 -> Fq6 -> Fq12` tower fast implementations use) — a
//! from-scratch cryptographic implementation prioritizes being checkable
//! against its source line-by-line over raw speed.
//!
//! No arbitrary-precision library needed: the field modulus is 254 bits,
//! comfortably within Zig's native `u256`/`u512` arbitrary-width integers
//! (multiply-then-reduce uses a `u512` intermediate for the pre-reduction
//! product). The one genuinely large constant, the final-exponentiation
//! exponent `(field_modulus^12 - 1) / curve_order`, is precomputed offline
//! (2790 bits) and embedded as a literal rather than computed at runtime.

const std = @import("std");

pub const field_modulus: u256 = 21888242871839275222246405745257275088696311157297823662689037894645226208583;
pub const curve_order: u256 = 21888242871839275222246405745257275088548364400416034343698204186575808495617;

/// `(field_modulus**12 - 1) // curve_order`, precomputed (Python, offline)
/// since computing it at runtime would need >3000-bit intermediates for a
/// single fixed constant used only as `Fq12`'s final-exponentiation exponent.
const final_exponent: u2790 = 552484233613224096312617126783173147097382103762957654188882734314196910839907541213974502761540629817009608548654680343627701153829446747810907373256841551006201639677726139946029199968412598804882391702273019083653272047566316584365559776493027495458238373902875937659943504873220554161550525926302303331747463515644711876653177129578303191095900909191624817826566688241804408081892785725967931714097716709526092261278071952560171111444072049229123565057483750161460024353346284167282452756217662335528813519139808291170539072125381230815729071544861602750936964829313608137325426383735122175229541155376346436093930287402089517426973178917569713384748081827255472576937471496195752727188261435633271238710131736096299798168852925540549342330775279877006784354801422249722573783561685179618816480037695005515426162362431072245638324744480;

const ate_loop_count: u256 = 29793968203157093288;
const log_ate_loop_count: u8 = 63;

/// The base field `Fq`, mod `field_modulus`.
pub const Fq = struct {
    n: u256,

    pub fn init(n: u256) Fq {
        return .{ .n = n % field_modulus };
    }

    pub const zero: Fq = .{ .n = 0 };
    pub const one: Fq = .{ .n = 1 };

    pub fn add(a: Fq, b: Fq) Fq {
        var s = a.n + b.n;
        if (s >= field_modulus) s -= field_modulus;
        return .{ .n = s };
    }

    pub fn sub(a: Fq, b: Fq) Fq {
        if (a.n >= b.n) return .{ .n = a.n - b.n };
        return .{ .n = field_modulus - (b.n - a.n) };
    }

    pub fn mul(a: Fq, b: Fq) Fq {
        const wide: u512 = @as(u512, a.n) * @as(u512, b.n);
        return .{ .n = @intCast(wide % field_modulus) };
    }

    pub fn neg(a: Fq) Fq {
        if (a.n == 0) return a;
        return .{ .n = field_modulus - a.n };
    }

    /// Same as `mul` — exists so `Fq` and `Fqp(...)` share a `mulScalar`
    /// interface, letting curve code (`double`, `linefunc`) stay generic
    /// over the coordinate field (`Fq` for G1, `Fq2`/`Fq12` for G2/G12).
    pub fn mulScalar(a: Fq, scalar: Fq) Fq {
        return a.mul(scalar);
    }

    /// Binary extended GCD. Same value as `bn128_field_elements.py`'s
    /// module-level `inv(a, n)` (the test below checks it against Fermat's
    /// `a^(p-2)`, an independent route), but every step is a shift, a
    /// comparison or a subtraction.
    ///
    /// The reference's division-based Euclid needs signed intermediates
    /// wider than the modulus, which meant `i512` and a 512-bit
    /// `@divFloor` on each of ~254 iterations. Inversions were 60% of a
    /// pairing's time once the exponentiations were gone, and nearly all of
    /// it was that division: `Fqp.inv`'s polynomial Euclid calls this
    /// several times per extension-field inversion.
    ///
    /// Everything stays in `[0, field_modulus)`, and `field_modulus` is 254
    /// bits, so the `+ field_modulus` halving steps cannot overflow `u256`.
    pub fn inv(a: Fq) Fq {
        if (a.n == 0) return a;
        var u: u256 = a.n;
        var v: u256 = field_modulus;
        var x1: u256 = 1;
        var x2: u256 = 0;
        while (u != 1 and v != 1) {
            while (u & 1 == 0) {
                u >>= 1;
                x1 = if (x1 & 1 == 0) x1 >> 1 else (x1 + field_modulus) >> 1;
            }
            while (v & 1 == 0) {
                v >>= 1;
                x2 = if (x2 & 1 == 0) x2 >> 1 else (x2 + field_modulus) >> 1;
            }
            if (u >= v) {
                u -= v;
                x1 = (Fq{ .n = x1 }).sub(.{ .n = x2 }).n;
            } else {
                v -= u;
                x2 = (Fq{ .n = x2 }).sub(.{ .n = x1 }).n;
            }
        }
        return .{ .n = if (u == 1) x1 else x2 };
    }

    pub fn div(a: Fq, b: Fq) Fq {
        return a.mul(b.inv());
    }

    pub fn eq(a: Fq, b: Fq) bool {
        return a.n == b.n;
    }

    pub fn pow(a: Fq, e: u256) Fq {
        var base = a;
        var exp = e;
        var result = Fq.one;
        while (exp > 0) : (exp >>= 1) {
            if (exp & 1 == 1) result = result.mul(base);
            base = base.mul(base);
        }
        return result;
    }
};

/// A degree-`degree` extension of `Fq`, `Fq[x] / (x^degree + sum(modulus_coeffs[i] * x^i))`.
/// Mirrors `bn128_field_elements.py`'s generic `FQP` class — one
/// implementation shared by both `Fq2` (`degree = 2`) and `Fq12`
/// (`degree = 12`), exactly like the Python reference.
pub fn Fqp(comptime degree: usize, comptime modulus_coeffs: [degree]i64) type {
    return struct {
        coeffs: [degree]Fq,

        const Self = @This();
        pub const mod_coeffs: [degree]Fq = blk: {
            var out: [degree]Fq = undefined;
            for (modulus_coeffs, 0..) |c, i| {
                out[i] = if (c >= 0) Fq.init(@intCast(c)) else Fq.init(field_modulus - @as(u256, @intCast(-c)));
            }
            break :blk out;
        };

        pub fn initInts(coeffs: [degree]i64) Self {
            var out: [degree]Fq = undefined;
            for (coeffs, 0..) |c, i| {
                out[i] = if (c >= 0) Fq.init(@intCast(c)) else Fq.init(field_modulus - @as(u256, @intCast(-c)));
            }
            return .{ .coeffs = out };
        }

        pub const zero: Self = blk: {
            var out: [degree]Fq = undefined;
            for (&out) |*c| c.* = Fq.zero;
            break :blk .{ .coeffs = out };
        };

        pub const one: Self = blk: {
            var out: [degree]Fq = undefined;
            out[0] = Fq.one;
            for (out[1..]) |*c| c.* = Fq.zero;
            break :blk .{ .coeffs = out };
        };

        pub fn add(a: Self, b: Self) Self {
            var out: [degree]Fq = undefined;
            for (0..degree) |i| out[i] = a.coeffs[i].add(b.coeffs[i]);
            return .{ .coeffs = out };
        }

        pub fn sub(a: Self, b: Self) Self {
            var out: [degree]Fq = undefined;
            for (0..degree) |i| out[i] = a.coeffs[i].sub(b.coeffs[i]);
            return .{ .coeffs = out };
        }

        pub fn neg(a: Self) Self {
            var out: [degree]Fq = undefined;
            for (0..degree) |i| out[i] = a.coeffs[i].neg();
            return .{ .coeffs = out };
        }

        pub fn mulScalar(a: Self, scalar: Fq) Self {
            var out: [degree]Fq = undefined;
            for (0..degree) |i| out[i] = a.coeffs[i].mul(scalar);
            return .{ .coeffs = out };
        }

        /// Full polynomial multiplication followed by reduction mod the
        /// extension's modulus polynomial, exactly mirroring `FQP.__mul__`'s
        /// `else` branch (the "other is also an FQP" case).
        pub fn mul(a: Self, b: Self) Self {
            var wide: [2 * degree - 1]Fq = undefined;
            for (&wide) |*c| c.* = Fq.zero;
            for (0..degree) |i| {
                for (0..degree) |j| {
                    wide[i + j] = wide[i + j].add(a.coeffs[i].mul(b.coeffs[j]));
                }
            }
            var len: usize = 2 * degree - 1;
            while (len > degree) {
                const top = wide[len - 1];
                const exp = len - degree - 1;
                for (0..degree) |i| {
                    wide[exp + i] = wide[exp + i].sub(top.mul(mod_coeffs[i]));
                }
                len -= 1;
            }
            var out: [degree]Fq = undefined;
            for (0..degree) |i| out[i] = wide[i];
            return .{ .coeffs = out };
        }

        pub fn eq(a: Self, b: Self) bool {
            for (0..degree) |i| {
                if (!a.coeffs[i].eq(b.coeffs[i])) return false;
            }
            return true;
        }

        pub fn isZero(a: Self) bool {
            return a.eq(Self.zero);
        }

        /// Degree of a coefficient list (as a plain array, one longer than
        /// `degree` — used only inside `inv`'s working polynomials), mirroring
        /// `deg(p)`: highest nonzero index, but never below 0.
        fn polyDeg(p: []const Fq) usize {
            var d = p.len - 1;
            while (d > 0 and p[d].eq(Fq.zero)) d -= 1;
            return d;
        }

        /// `poly_rounded_div(a, b)`: polynomial division, truncated (integer)
        /// division on each coefficient — safe here because every division
        /// this is used for happens to divide evenly, mirroring the Python
        /// reference exactly (which uses plain float `/` and gets away with
        /// the same fact).
        fn polyRoundedDiv(a: []const Fq, b: []const Fq, out: []Fq) void {
            const dega = polyDeg(a);
            const degb = polyDeg(b);
            var temp: [degree + 1]Fq = undefined;
            @memcpy(temp[0..a.len], a);
            for (out) |*o| o.* = Fq.zero;
            var i = dega - degb;
            while (true) : (i -= 1) {
                out[i] = out[i].add(temp[degb + i].div(b[degb]));
                for (0..degb + 1) |c| {
                    temp[c + i] = temp[c + i].sub(out[c]);
                }
                if (i == 0) break;
            }
        }

        /// Inverse. For a degree-2 extension with no linear term in its
        /// modulus (which is `Fq2`, whose modulus is `x^2 + 1`) this is one
        /// `Fq` inversion; otherwise it falls back to `invGeneric`.
        ///
        /// `x^2 == -modulus_coeffs[0]`, so `(a0 + a1 x)(a0 - a1 x)` lands
        /// back in `Fq` as `a0^2 + modulus_coeffs[0] * a1^2`, and dividing
        /// the conjugate by that norm inverts `a`. The generic polynomial
        /// Euclid below reaches the same answer via several `Fq` inversions
        /// and a pile of polynomial bookkeeping; `Fq2` inversions are hot
        /// enough in G2 arithmetic to be worth the special case.
        pub fn inv(a: Self) Self {
            if (comptime degree == 2 and modulus_coeffs[1] == 0) {
                const norm = a.coeffs[0].mul(a.coeffs[0])
                    .add(mod_coeffs[0].mul(a.coeffs[1].mul(a.coeffs[1])));
                const norm_inv = norm.inv();
                return .{ .coeffs = .{
                    a.coeffs[0].mul(norm_inv),
                    a.coeffs[1].neg().mul(norm_inv),
                } };
            }
            return a.invGeneric();
        }

        /// Extended Euclidean algorithm over polynomials, mirroring
        /// `FQP.inv()` exactly: `lm`/`hm`/`low`/`high` are all
        /// `degree + 1`-length coefficient arrays (the modulus polynomial's
        /// implied leading `1` makes `high` one longer than `coeffs`).
        pub fn invGeneric(a: Self) Self {
            var lm: [degree + 1]Fq = undefined;
            var hm: [degree + 1]Fq = undefined;
            var low: [degree + 1]Fq = undefined;
            var high: [degree + 1]Fq = undefined;
            for (&lm, 0..) |*c, i| c.* = if (i == 0) Fq.one else Fq.zero;
            for (&hm) |*c| c.* = Fq.zero;
            @memcpy(low[0..degree], &a.coeffs);
            low[degree] = Fq.zero;
            @memcpy(high[0..degree], &mod_coeffs);
            high[degree] = Fq.one;

            while (polyDeg(&low) != 0) {
                var r: [degree + 1]Fq = undefined;
                polyRoundedDiv(&high, &low, &r);
                var nm = hm;
                var new = high;
                for (0..degree + 1) |i| {
                    for (0..degree + 1 - i) |j| {
                        nm[i + j] = nm[i + j].sub(lm[i].mul(r[j]));
                        new[i + j] = new[i + j].sub(low[i].mul(r[j]));
                    }
                }
                hm = lm;
                high = low;
                lm = nm;
                low = new;
            }
            var result_coeffs: [degree]Fq = undefined;
            @memcpy(&result_coeffs, lm[0..degree]);
            const result: Self = .{ .coeffs = result_coeffs };
            return result.mulScalar(low[0].inv());
        }

        pub fn div(a: Self, b: Self) Self {
            return a.mul(b.inv());
        }

        /// Binary exponentiation by a native unsigned integer of any width
        /// (used both for small scalars and the 2790-bit final exponent).
        pub fn pow(a: Self, comptime T: type, e: T) Self {
            var base = a;
            var exp = e;
            var result = Self.one;
            while (exp > 0) : (exp >>= 1) {
                if (exp & 1 == 1) result = result.mul(base);
                base = base.mul(base);
            }
            return result;
        }
    };
}

pub const Fq2 = Fqp(2, .{ 1, 0 });
pub const Fq12 = Fqp(12, .{ 82, 0, 0, 0, 0, 0, -18, 0, 0, 0, 0, 0 });

/// `(x^p)^i` for `i` in `0..12`, generated offline from
/// `Fq12.initInts(x).pow(u256, field_modulus)` — the test below re-derives
/// them against that same reference and asserts they match.
///
/// Every coefficient of an `Fq12` element lives in `Fq`, where `a^p == a`,
/// so the p-power Frobenius is `Fq`-linear:
///
///     (sum a_i x^i)^p == sum a_i (x^p)^i == sum a_i gamma[i]
///
/// Each `gamma[i]` turns out to have only two nonzero coefficients, so the
/// whole map is 24 `Fq` multiplications. Reaching it by square-and-multiply
/// over `field_modulus` instead costs ~380 `Fq12` multiplications, and the
/// Miller loop does it four times per pairing: 26% of a pairing's time went
/// here before this existed.
const frobenius_gamma: [12][12]u256 = .{
    .{ 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, }, // gamma^0
    .{ 0x0, 0x1d8c8daef3eee1e81b2522ec5eb28ded6895e1cdfde6a43f5daa971f3fa65955, 0x0, 0x0, 0x0, 0x0, 0x0, 0x246996f3b4fae7e6a6327cfe12150b8e747992778eeec7e5ca5cf05f80f362ac, 0x0, 0x0, 0x0, 0x0, }, // gamma^1
    .{ 0x0, 0x0, 0x242b719062f6737b8481d22c6934ce844d72f250fd28d102c0d147b2f4d521a7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x16c9e55061ebae204ba4cc8bd75a079432ae2a1d0b7c9dce1665d51c640fcba2, 0x0, 0x0, 0x0, }, // gamma^2
    .{ 0x0, 0x0, 0x0, 0x21436d48fcb50cc60dd4ef1e69a0c1f0dd2949fa6df7b44cbb259ef7cb58d5ed, 0x0, 0x0, 0x0, 0x0, 0x0, 0x7c03cbcac41049a0704b5a7ec796f2b21807dc98fa25bd282d37f632623b0e3, 0x0, 0x0, }, // gamma^3
    .{ 0x0, 0x0, 0x0, 0x0, 0x2c84bbad27c3671562b7adefd44038ab3c0bbad96fc008e7d6998c82f7fc048b, 0x0, 0x0, 0x0, 0x0, 0x0, 0x2c145edbe7fd8aee9f3a80b03b0b1c923685d2ea1bdec763c13b4711cd2b8126, 0x0, }, // gamma^4
    .{ 0x0, 0x0, 0x0, 0x0, 0x0, 0x1b007294a55accce13fe08bea73305ff6bdac77c5371c546d428780a6e3dcfa8, 0x0, 0x0, 0x0, 0x0, 0x0, 0x12acf2ca76fd0675a27fb246c7729f7db080cb99678e2ac024c6b8ee6e0c2c4b, }, // gamma^5
    .{ 0x12, 0x0, 0x0, 0x0, 0x0, 0x0, 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd46, 0x0, 0x0, 0x0, 0x0, 0x0, }, // gamma^6
    .{ 0x0, 0x217e400dc9351e774e34e2ac06ead4000d14d1e242b29c567e9c385ce480a71a, 0x0, 0x0, 0x0, 0x0, 0x0, 0x12d7c0c3ed42be419d2b22ca22ceca702eeb88c36a8b264dde75f4f798d6a3f2, 0x0, 0x0, 0x0, 0x0, }, // gamma^7
    .{ 0x0, 0x0, 0x359809094bd5c8e1b9c22d81246ffc2e794e17643ac198484b8d9094aa82536, 0x0, 0x0, 0x0, 0x0, 0x0, 0xc38dce27e3b2cae33ce738a184c89d94a0e78406b48f98a7b4f4463e3a7dba0, 0x0, 0x0, 0x0, }, // gamma^8
    .{ 0x0, 0x0, 0x0, 0x18857a58f3b5bb3038a4311a86919d9c7c6c15f88a4f4f0831364cf35f78f771, 0x0, 0x0, 0x0, 0x0, 0x0, 0xf20e129e47c9363aa7b569817e0966cba582096fa7a164080faed1f0d24275a, 0x0, 0x0, }, // gamma^9
    .{ 0x0, 0x0, 0x0, 0x0, 0xc33b1c70e4fd11b6d1eab6fcd18b99ad4afd096a8697e0c9c36d8ca3339a7b5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x3df92c5b96e3914559897c6ad411fb25b75afb7f8b1c1a56586ff93e080f8bc, 0x0, }, // gamma^10
    .{ 0x0, 0x0, 0x0, 0x0, 0x0, 0x215d42e7ac7bd17cefe88dd8e6965b3adae92c974f501fe811493d72543a3977, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1563dbde3bd6d35ba4523cf7da4e525e2ba6a3151500054667f8140c6a3f2d9f, }, // gamma^11
};

/// `a^field_modulus`, the p-power Frobenius endomorphism of `Fq12`.
pub fn frobenius(a: Fq12) Fq12 {
    var out: [12]Fq = .{Fq.zero} ** 12;
    inline for (0..12) |i| {
        inline for (0..12) |j| {
            if (comptime frobenius_gamma[i][j] != 0) {
                out[j] = out[j].add(a.coeffs[i].mul(.{ .n = frobenius_gamma[i][j] }));
            }
        }
    }
    return .{ .coeffs = out };
}

/// `a^(field_modulus^n)`, by `n` applications of `frobenius`.
fn frobeniusPow(a: Fq12, comptime n: usize) Fq12 {
    var out = a;
    inline for (0..n) |_| out = frobenius(out);
    return out;
}

/// `(field_modulus^4 - field_modulus^2 + 1) / curve_order`, the only factor
/// of `final_exponent` that still needs a real exponentiation. 761 bits
/// against the whole exponent's 2790.
const hard_exponent: u761 = 10486551571378427818905133077457505975217533156541166536005452068033223782873764572151541189142778783267711471998854717549389605644966361077867290379973073897271417449614939788000730910148473503528371060814157528868116901618729649;

/// `f^((field_modulus^12 - 1) / curve_order)`, the pairing's final
/// exponentiation.
///
/// That exponent factors as `(p^6 - 1) * (p^2 + 1) * (p^4 - p^2 + 1)/r`
/// (asserted in the test below). The first two factors cost a Frobenius and
/// a single inversion each; only the third is exponentiated, and it is a
/// quarter the width. Square-and-multiply over the undecomposed 2790-bit
/// exponent was 71% of a pairing's time.
pub fn finalExponentiate(f: Fq12) Fq12 {
    // Matches what `pow` would do with a zero base; `inv` below would not.
    if (f.isZero()) return Fq12.zero;
    const easy = frobeniusPow(f, 6).mul(f.inv());
    const m = frobeniusPow(easy, 2).mul(easy);
    return m.pow(u761, hard_exponent);
}

/// An affine point over field `F`, or `null` for the point at infinity —
/// mirrors Python's `pt is None` convention directly.
pub fn AffinePoint(comptime F: type) type {
    return struct { x: F, y: F };
}

pub const G1Point = AffinePoint(Fq);
pub const G2Point = AffinePoint(Fq2);
const G12Point = AffinePoint(Fq12);

pub const b1: Fq = Fq.init(3);
/// `b2 = FQ2([3, 0]) / FQ2([9, 1])`.
pub const b2: Fq2 = Fq2.initInts(.{ 3, 0 }).div(Fq2.initInts(.{ 9, 1 }));
const b12: Fq12 = Fq12.initInts(.{3} ++ .{0} ** 11);

pub const g1: G1Point = .{ .x = Fq.init(1), .y = Fq.init(2) };
pub const g2: G2Point = .{
    .x = .{ .coeffs = .{ Fq.init(10857046999023057135944570762232829481370756359578518086990519993285655852781), Fq.init(11559732032986387107991004021392285783925812861821192530917403151452391805634) } },
    .y = .{ .coeffs = .{ Fq.init(8495653923123431417604973247489272438418190587263600148770280649306958101930), Fq.init(4082367875863433681332203403145435568316851327593401208105741076214120093531) } },
};

pub fn isOnCurve(comptime F: type, pt: ?AffinePoint(F), b: F) bool {
    const p = pt orelse return true;
    return p.y.mul(p.y).sub(p.x.mul(p.x).mul(p.x)).eq(b);
}

fn double(comptime F: type, pt: AffinePoint(F)) AffinePoint(F) {
    const x = pt.x;
    const y = pt.y;
    const l = x.mul(x).mulScalar(Fq.init(3)).div(y.mulScalar(Fq.init(2)));
    const newx = l.mul(l).sub(x).sub(x);
    const newy = l.neg().mul(newx).add(l.mul(x)).sub(y);
    return .{ .x = newx, .y = newy };
}

pub fn add(comptime F: type, p1: ?AffinePoint(F), p2: ?AffinePoint(F)) ?AffinePoint(F) {
    const a = p1 orelse return p2;
    const c = p2 orelse return p1;
    if (a.x.eq(c.x) and a.y.eq(c.y)) return double(F, a);
    if (a.x.eq(c.x)) return null;
    const l = c.y.sub(a.y).div(c.x.sub(a.x));
    const newx = l.mul(l).sub(a.x).sub(c.x);
    const newy = l.neg().mul(newx).add(l.mul(a.x)).sub(a.y);
    return .{ .x = newx, .y = newy };
}

/// `n` is reduced by nothing (matches Python: `multiply` recurses on the
/// literal integer `n`, which can be any non-negative value, not
/// necessarily `< curve_order` — a scalar `>= curve_order` is legal EVM
/// input for `ECMUL`, just wraps around group-theoretically).
pub fn multiply(comptime F: type, pt: ?AffinePoint(F), n: u256) ?AffinePoint(F) {
    if (n == 0) return null;
    const p = pt orelse return null;
    if (n == 1) return p;
    if (n % 2 == 0) return multiply(F, double(F, p), n / 2);
    return add(F, multiply(F, double(F, p), n / 2), p);
}

fn neg(comptime F: type, pt: ?AffinePoint(F)) ?AffinePoint(F) {
    const p = pt orelse return null;
    return .{ .x = p.x, .y = p.y.neg() };
}

const w: Fq12 = Fq12.initInts(.{0, 1} ++ .{0} ** 10);

/// Embeds a `G2` point into `G12` via the field isomorphism `Fq2 ->
/// Fq[w^6]`, mirroring `twist()` exactly.
fn twist(pt: ?G2Point) ?G12Point {
    const p = pt orelse return null;
    const x9 = p.x.coeffs[1].mul(Fq.init(9));
    const y9 = p.y.coeffs[1].mul(Fq.init(9));
    const xcoeffs = [2]Fq{ p.x.coeffs[0].sub(x9), p.x.coeffs[1] };
    const ycoeffs = [2]Fq{ p.y.coeffs[0].sub(y9), p.y.coeffs[1] };
    var nx_coeffs: [12]Fq = undefined;
    var ny_coeffs: [12]Fq = undefined;
    for (&nx_coeffs) |*c| c.* = Fq.zero;
    for (&ny_coeffs) |*c| c.* = Fq.zero;
    nx_coeffs[0] = xcoeffs[0];
    nx_coeffs[6] = xcoeffs[1];
    ny_coeffs[0] = ycoeffs[0];
    ny_coeffs[6] = ycoeffs[1];
    const nx: Fq12 = .{ .coeffs = nx_coeffs };
    const ny: Fq12 = .{ .coeffs = ny_coeffs };
    return .{ .x = nx.mul(w.mul(w)), .y = ny.mul(w.mul(w).mul(w)) };
}

fn castPointToFq12(pt: ?G1Point) ?G12Point {
    const p = pt orelse return null;
    var xc: [12]Fq = undefined;
    var yc: [12]Fq = undefined;
    for (&xc) |*c| c.* = Fq.zero;
    for (&yc) |*c| c.* = Fq.zero;
    xc[0] = p.x;
    yc[0] = p.y;
    return .{ .x = .{ .coeffs = xc }, .y = .{ .coeffs = yc } };
}

/// The line through `P1`/`P2`, evaluated at `T` — mirrors `linefunc`
/// exactly. All three points live in `G12` by the time this is called
/// (`Q` was already `twist`ed, `P` already `castPointToFq12`).
fn linefunc(p1: G12Point, p2: G12Point, t: G12Point) Fq12 {
    if (!p1.x.eq(p2.x)) {
        const m = p2.y.sub(p1.y).div(p2.x.sub(p1.x));
        return m.mul(t.x.sub(p1.x)).sub(t.y.sub(p1.y));
    } else if (p1.y.eq(p2.y)) {
        const m = p1.x.mul(p1.x).mulScalar(Fq.init(3)).div(p1.y.mulScalar(Fq.init(2)));
        return m.mul(t.x.sub(p1.x)).sub(t.y.sub(p1.y));
    } else {
        return t.x.sub(p1.x);
    }
}

/// The Miller loop, mirroring `miller_loop` exactly but for two
/// substitutions that leave its value unchanged: `frobenius` in place of
/// square-and-multiply by `field_modulus`, and the final exponentiation
/// lifted out to `finalExponentiate` so a caller checking a product of
/// pairings can apply it once rather than once per pair.
fn millerLoopRaw(q: ?G12Point, p: ?G12Point) Fq12 {
    const qq = q orelse return Fq12.one;
    const pp = p orelse return Fq12.one;
    var r = qq;
    var f = Fq12.one;
    var i: i16 = log_ate_loop_count;
    while (i >= 0) : (i -= 1) {
        f = f.mul(f).mul(linefunc(r, r, pp));
        r = double(Fq12, r);
        if (ate_loop_count & (@as(u256, 1) << @intCast(i)) != 0) {
            f = f.mul(linefunc(r, qq, pp));
            r = add(Fq12, r, qq).?;
        }
    }
    const q1: G12Point = .{ .x = frobenius(qq.x), .y = frobenius(qq.y) };
    const nq2: G12Point = .{ .x = frobenius(q1.x), .y = frobenius(q1.y).neg() };
    f = f.mul(linefunc(r, q1, pp));
    r = add(Fq12, r, q1).?;
    f = f.mul(linefunc(r, nq2, pp));
    return f;
}

/// The Miller loop alone, without the final exponentiation.
///
/// `ECPAIRING` asks whether a *product* of pairings is one, and since
/// `e(a,b) * e(c,d) == (ML(a,b) * ML(c,d))^exponent`, a caller can
/// accumulate these across pairs and exponentiate the product once.
pub fn millerLoop(q: ?G2Point, p: ?G1Point) Fq12 {
    return millerLoopRaw(twist(q), castPointToFq12(p));
}

/// `e(Q, P)`, the optimal ate pairing of a `G2` point and a `G1` point.
pub fn pairing(q: ?G2Point, p: ?G1Point) Fq12 {
    return finalExponentiate(millerLoop(q, p));
}

test "generators are on their respective curves" {
    try std.testing.expect(isOnCurve(Fq, g1, b1));
    try std.testing.expect(isOnCurve(Fq2, g2, b2));
}

test "the twisted G2 generator is on the G12 curve" {
    const g12 = twist(g2);
    try std.testing.expect(isOnCurve(Fq12, g12, b12));
}

test "point addition matches doubling" {
    const two_by_add = add(Fq, g1, g1).?;
    const two_by_double = double(Fq, g1);
    try std.testing.expect(two_by_add.x.eq(two_by_double.x));
    try std.testing.expect(two_by_add.y.eq(two_by_double.y));
}

test "multiply by curve_order gives the point at infinity" {
    const result = multiply(Fq, g1, curve_order);
    try std.testing.expectEqual(@as(?G1Point, null), result);
}

test "e(G1, G2)^curve_order == 1, and pairing is bilinear" {
    const e_g1_g2 = pairing(g2, g1);
    try std.testing.expect(e_g1_g2.pow(u256, curve_order).eq(Fq12.one));

    // e(2*G1, G2) == e(G1, G2)^2 == e(G1, 2*G2)
    const p2 = multiply(Fq, g1, 2).?;
    const q2 = multiply(Fq2, g2, 2).?;
    const e_2p_q = pairing(g2, p2);
    const e_p_2q = pairing(q2, g1);
    const e_squared = e_g1_g2.mul(e_g1_g2);
    try std.testing.expect(e_2p_q.eq(e_squared));
    try std.testing.expect(e_p_2q.eq(e_squared));
}

test "pairing with the point at infinity is 1" {
    try std.testing.expect(pairing(null, g1).eq(Fq12.one));
    try std.testing.expect(pairing(g2, null).eq(Fq12.one));
}

test "frobenius matches square-and-multiply by field_modulus" {
    // The reference the generated `frobenius_gamma` table replaced. Random
    // elements rather than structured ones, so a table entry that happens
    // to be right only on sparse input cannot pass.
    var prng: std.Random.DefaultPrng = .init(0x7a6b5c4d);
    const rand = prng.random();
    for (0..4) |_| {
        var coeffs: [12]Fq = undefined;
        for (&coeffs) |*c| c.* = Fq.init(rand.int(u256));
        const a: Fq12 = .{ .coeffs = coeffs };
        try std.testing.expect(frobenius(a).eq(a.pow(u256, field_modulus)));
    }
    // And on the structured values the Miller loop actually feeds it.
    try std.testing.expect(frobenius(Fq12.one).eq(Fq12.one));
    try std.testing.expect(frobenius(Fq12.zero).eq(Fq12.zero));
    const g = twist(g2).?;
    try std.testing.expect(frobenius(g.x).eq(g.x.pow(u256, field_modulus)));
    try std.testing.expect(frobenius(g.y).eq(g.y.pow(u256, field_modulus)));
}

test "the decomposed final exponentiation matches the undecomposed exponent" {
    // Proves `(p^6 - 1) * (p^2 + 1) * hard_exponent == final_exponent` in
    // the only way that matters here: both routes land on the same element.
    var prng: std.Random.DefaultPrng = .init(0x1f2e3d4c);
    const rand = prng.random();
    for (0..2) |_| {
        var coeffs: [12]Fq = undefined;
        for (&coeffs) |*c| c.* = Fq.init(rand.int(u256));
        const a: Fq12 = .{ .coeffs = coeffs };
        try std.testing.expect(finalExponentiate(a).eq(a.pow(u2790, final_exponent)));
    }
    // Zero has no inverse, so `finalExponentiate` special-cases it; check it
    // still agrees with what the plain exponentiation would have produced.
    try std.testing.expect(finalExponentiate(Fq12.zero).eq(Fq12.zero.pow(u2790, final_exponent)));
    // And the real article: a Miller loop output.
    const ml = millerLoop(g2, g1);
    try std.testing.expect(finalExponentiate(ml).eq(ml.pow(u2790, final_exponent)));
}

test "a product of Miller loops exponentiated once equals the product of pairings" {
    // The identity `ECPAIRING` relies on, which is what lets the precompile
    // pay for one final exponentiation rather than one per pair.
    const p1 = multiply(Fq, g1, 7).?;
    const q1 = multiply(Fq2, g2, 11).?;
    const p2 = multiply(Fq, g1, 13).?;
    const q2 = multiply(Fq2, g2, 17).?;

    const separate = pairing(q1, p1).mul(pairing(q2, p2));
    const combined = finalExponentiate(millerLoop(q1, p1).mul(millerLoop(q2, p2)));
    try std.testing.expect(separate.eq(combined));
}

test "Fq.inv agrees with Fermat's a^(p-2)" {
    // An independent route to the same inverse, so this checks the binary
    // GCD rather than just restating it.
    var prng: std.Random.DefaultPrng = .init(0x5e1f2a3b);
    const rand = prng.random();
    for (0..64) |_| {
        const a = Fq.init(rand.int(u256));
        if (a.n == 0) continue;
        try std.testing.expect(a.inv().eq(a.pow(field_modulus - 2)));
        try std.testing.expect(a.mul(a.inv()).eq(Fq.one));
    }
    // Edges: 1, p-1, and the smallest even and odd values, since the loop
    // branches on parity.
    for ([_]u256{ 1, 2, 3, 4, field_modulus - 1, field_modulus - 2 }) |n| {
        const a = Fq.init(n);
        try std.testing.expect(a.inv().eq(a.pow(field_modulus - 2)));
    }
    // Zero is returned unchanged, as the reference does.
    try std.testing.expect(Fq.zero.inv().eq(Fq.zero));
}

test "the direct Fq2 inverse agrees with the generic polynomial Euclid" {
    var prng: std.Random.DefaultPrng = .init(0x3c4d5e6f);
    const rand = prng.random();
    for (0..32) |_| {
        const a: Fq2 = .{ .coeffs = .{ Fq.init(rand.int(u256)), Fq.init(rand.int(u256)) } };
        if (a.isZero()) continue;
        try std.testing.expect(a.inv().eq(a.invGeneric()));
        try std.testing.expect(a.mul(a.inv()).eq(Fq2.one));
    }
    // A purely real and a purely imaginary element, where one coefficient
    // of the conjugate formula drops out.
    const real: Fq2 = .{ .coeffs = .{ Fq.init(7), Fq.zero } };
    const imag: Fq2 = .{ .coeffs = .{ Fq.zero, Fq.init(7) } };
    try std.testing.expect(real.inv().eq(real.invGeneric()));
    try std.testing.expect(imag.inv().eq(imag.invGeneric()));
    try std.testing.expect(Fq2.one.inv().eq(Fq2.one));
}
