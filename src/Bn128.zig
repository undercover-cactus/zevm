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

    /// `a * b mod p`, by two Montgomery reductions rather than a `%`.
    ///
    /// `%` on a 512-bit product has no hardware instruction behind it and
    /// compiles to a software long division, which was the floor under every
    /// operation in this file. `redc(t)` instead computes `t / R mod p`
    /// (`R = 2^256`) with multiplications and a shift. Applying it to `a * b`
    /// gives `a * b / R`; applying it again to that times `R^2 mod p` cancels
    /// the stray `1 / R`. So the result, and every `Fq` anywhere, stays in
    /// plain (non-Montgomery) form.
    pub fn mul(a: Fq, b: Fq) Fq {
        const x = redc(@as(u512, a.n) * b.n);
        return .{ .n = redc(@as(u512, x) * mont_r2) };
    }

    /// `-p^-1 mod 2^256`. Newton's iteration doubles the number of correct
    /// low bits each round, starting from 1 (correct mod 2, since `p` is
    /// odd), so eight rounds reach 256.
    const mont_n_prime: u256 = blk: {
        var x: u256 = 1;
        for (0..8) |_| x *%= 2 -% field_modulus *% x;
        break :blk 0 -% x;
    };
    /// `R^2 mod p`.
    const mont_r2: u256 = @intCast((@as(u1024, 1) << 512) % field_modulus);

    /// Montgomery reduction: `t * R^-1 mod p`, for any `t < p * R`. `m` is
    /// chosen so `t + m * p` is a multiple of `R`, which makes the division
    /// by `R` an exact shift. The sum stays under `2 * p * R < 2^511`, and
    /// the quotient under `2p`, so one conditional subtraction finishes it.
    fn redc(t: u512) u256 {
        const m: u256 = @as(u256, @truncate(t)) *% mont_n_prime;
        const sum = t + @as(u512, m) * field_modulus;
        var r: u256 = @intCast(sum >> 256);
        if (r >= field_modulus) r -= field_modulus;
        return r;
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

        pub fn mul(a: Self, b: Self) Self {
            if (comptime is_bn254_fq12) return .{ .coeffs = tower.mul12(a.coeffs, b.coeffs) };
            return a.mulSchoolbook(b);
        }

        /// This file's `Fq12`, whose modulus is what `tower` is built on.
        const is_bn254_fq12 = degree == 12 and std.mem.eql(i64, &modulus_coeffs, &.{ 82, 0, 0, 0, 0, 0, -18, 0, 0, 0, 0, 0 });

        /// Full polynomial multiplication followed by reduction mod the
        /// extension's modulus polynomial, exactly mirroring `FQP.__mul__`'s
        /// `else` branch (the "other is also an FQP" case). What `mul` does
        /// for `Fq2`, and the reference `tower.mul12` is tested against.
        pub fn mulSchoolbook(a: Self, b: Self) Self {
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
            // Python's `range(dega - degb, -1, -1)` is simply empty when the
            // divisor has the higher degree; here the subtraction would wrap.
            if (dega < degb) return;
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
            if (comptime is_bn254_fq12) return .{ .coeffs = tower.inv12(a.coeffs) };
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

/// `Fq12` arithmetic done as the tower `Fq2 -> Fq6 -> Fq12` it really is,
/// for `Fqp(12, ...)`'s `mul` and `inv`. The flat representation everything
/// else uses is converted in and out at the edges, which costs additions only.
///
/// The flat modulus `w^12 - 18w^6 + 82` hides the tower: put `u = w^6 - 9` and
/// it becomes `u^2 = -1`. So with `xi = 9 + u = w^6`:
///
///     Fq2  = Fq[u]  / (u^2 + 1)
///     Fq6  = Fq2[v] / (v^3 - xi)     where v = w^2
///     Fq12 = Fq6[w] / (w^2 - v)
///
/// and a flat element `sum c_k w^k` is `sum_{k<6} d_k w^k` with
/// `d_k = c_k + c_{k+6} * xi`, which in turn is `g + h w` for the `Fq6`
/// elements `g = (d0, d2, d4)` and `h = (d1, d3, d5)`.
///
/// Karatsuba at every level makes a multiplication 3 * 6 * 3 = 54 `Fq`
/// multiplications against the flat schoolbook's 144 plus reduction, and an
/// inversion becomes conjugate-and-norm down to a single `Fq` inversion
/// instead of a polynomial Euclid that performs several.
const tower = struct {
    const T2 = struct { a: Fq, b: Fq }; // a + b u
    const T6 = [3]T2; // c0 + c1 v + c2 v^2
    const T12 = struct { g: T6, h: T6 }; // g + h w

    fn add2(x: T2, y: T2) T2 {
        return .{ .a = x.a.add(y.a), .b = x.b.add(y.b) };
    }
    fn sub2(x: T2, y: T2) T2 {
        return .{ .a = x.a.sub(y.a), .b = x.b.sub(y.b) };
    }
    fn neg2(x: T2) T2 {
        return .{ .a = x.a.neg(), .b = x.b.neg() };
    }
    /// Karatsuba: three multiplications rather than four.
    fn mul2(x: T2, y: T2) T2 {
        const ac = x.a.mul(y.a);
        const bd = x.b.mul(y.b);
        const cross = x.a.add(x.b).mul(y.a.add(y.b));
        return .{ .a = ac.sub(bd), .b = cross.sub(ac).sub(bd) };
    }
    fn times9(x: Fq) Fq {
        const x2 = x.add(x);
        const x8 = x2.add(x2).add(x2.add(x2));
        return x8.add(x);
    }
    /// Multiplication by `xi = 9 + u`: `(a + bu)(9 + u) = (9a - b) + (a + 9b)u`.
    fn mulXi(x: T2) T2 {
        return .{ .a = times9(x.a).sub(x.b), .b = x.a.add(times9(x.b)) };
    }
    fn inv2(x: T2) T2 {
        const norm_inv = x.a.mul(x.a).add(x.b.mul(x.b)).inv();
        return .{ .a = x.a.mul(norm_inv), .b = x.b.neg().mul(norm_inv) };
    }

    fn add6(x: T6, y: T6) T6 {
        return .{ add2(x[0], y[0]), add2(x[1], y[1]), add2(x[2], y[2]) };
    }
    fn sub6(x: T6, y: T6) T6 {
        return .{ sub2(x[0], y[0]), sub2(x[1], y[1]), sub2(x[2], y[2]) };
    }
    /// Karatsuba over three terms: six `Fq2` multiplications rather than nine.
    fn mul6(x: T6, y: T6) T6 {
        const t0 = mul2(x[0], y[0]);
        const t1 = mul2(x[1], y[1]);
        const t2 = mul2(x[2], y[2]);
        const c0 = add2(t0, mulXi(sub2(sub2(mul2(add2(x[1], x[2]), add2(y[1], y[2])), t1), t2)));
        const c1 = add2(sub2(sub2(mul2(add2(x[0], x[1]), add2(y[0], y[1])), t0), t1), mulXi(t2));
        const c2 = add2(sub2(sub2(mul2(add2(x[0], x[2]), add2(y[0], y[2])), t0), t2), t1);
        return .{ c0, c1, c2 };
    }
    /// `x * v`, which only shifts coefficients (and wraps one through `xi`).
    fn mulV(x: T6) T6 {
        return .{ mulXi(x[2]), x[0], x[1] };
    }
    fn inv6(x: T6) T6 {
        const c0 = sub2(mul2(x[0], x[0]), mulXi(mul2(x[1], x[2])));
        const c1 = sub2(mulXi(mul2(x[2], x[2])), mul2(x[0], x[1]));
        const c2 = sub2(mul2(x[1], x[1]), mul2(x[0], x[2]));
        const norm = add2(mul2(x[0], c0), mulXi(add2(mul2(x[2], c1), mul2(x[1], c2))));
        const n = inv2(norm);
        return .{ mul2(c0, n), mul2(c1, n), mul2(c2, n) };
    }

    fn fromFlat(c: [12]Fq) T12 {
        var d: [6]T2 = undefined;
        // c_k + c_{k+6} (9 + u)
        for (0..6) |k| d[k] = .{ .a = c[k].add(times9(c[k + 6])), .b = c[k + 6] };
        return .{ .g = .{ d[0], d[2], d[4] }, .h = .{ d[1], d[3], d[5] } };
    }
    fn toFlat(x: T12) [12]Fq {
        const d = [6]T2{ x.g[0], x.h[0], x.g[1], x.h[1], x.g[2], x.h[2] };
        var c: [12]Fq = undefined;
        for (0..6) |k| {
            c[k + 6] = d[k].b;
            c[k] = d[k].a.sub(times9(d[k].b));
        }
        return c;
    }

    /// `(g0 + h0 w)(g1 + h1 w) = (g0 g1 + h0 h1 v) + ((g0 + h0)(g1 + h1) - g0 g1 - h0 h1) w`
    fn mul12(a: [12]Fq, b: [12]Fq) [12]Fq {
        const x = fromFlat(a);
        const y = fromFlat(b);
        const t0 = mul6(x.g, y.g);
        const t1 = mul6(x.h, y.h);
        const cross = sub6(sub6(mul6(add6(x.g, x.h), add6(y.g, y.h)), t0), t1);
        return toFlat(.{ .g = add6(t0, mulV(t1)), .h = cross });
    }
    /// `(g + h w)^-1 = (g - h w) / (g^2 - h^2 v)`.
    fn inv12(a: [12]Fq) [12]Fq {
        const x = fromFlat(a);
        const n = inv6(sub6(mul6(x.g, x.g), mulV(mul6(x.h, x.h))));
        const zero6: T6 = .{ .{ .a = Fq.zero, .b = Fq.zero }, .{ .a = Fq.zero, .b = Fq.zero }, .{ .a = Fq.zero, .b = Fq.zero } };
        return toFlat(.{ .g = mul6(x.g, n), .h = mul6(sub6(zero6, x.h), n) });
    }
};

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

/// `n * pt`, by double-and-add in Jacobian coordinates.
///
/// Affine doubling and addition each divide by a line's slope, so every one
/// of up to 256 steps paid a field inversion; for `Fq2` that was most of the
/// G2 subgroup check. A Jacobian point `(X, Y, Z)` stands for
/// `(X / Z^2, Y / Z^3)` and carries the denominator instead of dividing by
/// it, so the steps are multiplications only and the single inversion comes
/// at the end, to get back to affine. Infinity is `Z = 0`, so the subgroup
/// check (`n = curve_order`, expected infinity) never inverts at all.
///
/// `n` is reduced by nothing: a scalar `>= curve_order` is legal EVM input
/// for `ECMUL` and just wraps around group-theoretically, as in the Python
/// reference (`multiplyAffine`, which this is tested against).
pub fn multiply(comptime F: type, pt: ?AffinePoint(F), n: u256) ?AffinePoint(F) {
    const p = pt orelse return null;
    var acc: Jacobian(F) = .infinity;
    var bit: u9 = 256 - @as(u9, @clz(n));
    while (bit > 0) {
        bit -= 1;
        acc = jacobianDouble(F, acc);
        if ((n >> @intCast(bit)) & 1 == 1) acc = jacobianAddAffine(F, acc, p);
    }
    if (acc.z.eq(F.zero)) return null;
    const z_inv = acc.z.inv();
    const z_inv2 = z_inv.mul(z_inv);
    return .{ .x = acc.x.mul(z_inv2), .y = acc.y.mul(z_inv2).mul(z_inv) };
}

/// A point `(x / z^2, y / z^3)`; `z = 0` is the point at infinity.
fn Jacobian(comptime F: type) type {
    return struct {
        x: F,
        y: F,
        z: F,
        const infinity: @This() = .{ .x = F.one, .y = F.one, .z = F.zero };
    };
}

/// "dbl-2009-l" from the Explicit-Formulas Database, for curves with `a = 0`
/// (both of ours: `y^2 = x^3 + b`). Doubling infinity yields `z = 0` again,
/// and so does doubling a point with `y = 0`, which is correct for both.
fn jacobianDouble(comptime F: type, p: Jacobian(F)) Jacobian(F) {
    const a = p.x.mul(p.x);
    const b = p.y.mul(p.y);
    const c = b.mul(b);
    const xb = p.x.add(b);
    var d = xb.mul(xb).sub(a).sub(c);
    d = d.add(d);
    const e = a.add(a).add(a);
    const x3 = e.mul(e).sub(d).sub(d);
    const c2 = c.add(c);
    const c4 = c2.add(c2);
    const y3 = e.mul(d.sub(x3)).sub(c4.add(c4));
    const yz = p.y.mul(p.z);
    return .{ .x = x3, .y = y3, .z = yz.add(yz) };
}

/// "madd-2007-bl": Jacobian `p` plus affine `q`. The two degenerate cases
/// the formula cannot express, `q == p` and `q == -p`, are told apart by
/// whether the `y`s agree once the `x`s do, as the affine `add` does.
fn jacobianAddAffine(comptime F: type, p: Jacobian(F), q: AffinePoint(F)) Jacobian(F) {
    if (p.z.eq(F.zero)) return .{ .x = q.x, .y = q.y, .z = F.one };
    const z1z1 = p.z.mul(p.z);
    const qx_scaled = q.x.mul(z1z1);
    const s2 = q.y.mul(p.z).mul(z1z1);
    const h = qx_scaled.sub(p.x);
    var r = s2.sub(p.y);
    if (h.eq(F.zero)) {
        if (r.eq(F.zero)) return jacobianDouble(F, p);
        return .infinity;
    }
    r = r.add(r);
    const hh = h.mul(h);
    const hh2 = hh.add(hh);
    const i = hh2.add(hh2);
    const j = h.mul(i);
    const v = p.x.mul(i);
    const x3 = r.mul(r).sub(j).sub(v).sub(v);
    const y1j = p.y.mul(j);
    const y3 = r.mul(v.sub(x3)).sub(y1j).sub(y1j);
    const zh = p.z.add(h);
    return .{ .x = x3, .y = y3, .z = zh.mul(zh).sub(z1z1).sub(hh) };
}

/// The Python reference's recursive affine `multiply`, verbatim. Kept as
/// the oracle `multiply` is tested against.
fn multiplyAffine(comptime F: type, pt: ?AffinePoint(F), n: u256) ?AffinePoint(F) {
    if (n == 0) return null;
    const p = pt orelse return null;
    if (n == 1) return p;
    if (n % 2 == 0) return multiplyAffine(F, double(F, p), n / 2);
    return add(F, multiplyAffine(F, double(F, p), n / 2), p);
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
    const qq = q orelse return Fq12.one;
    const pp = p orelse return Fq12.one;
    return millerLoopFq2(qq, pp);
}

/// `millerLoopRaw`'s loop with `Q` kept in `G2` over `Fq2` rather than
/// twisted into `Fq12`, producing the very same `Fq12` value.
///
/// The twisted point is `(x w^2, y w^3)` for `Q = (x, y)`, so every slope the
/// reference divides out in `Fq12` is `lambda * w` for the `lambda` of the
/// same step over `Fq2`, and the twist commutes with doubling and adding.
/// Point arithmetic and slopes therefore stay in `Fq2`, where an inversion is
/// a single `Fq` inversion; the reference performed three `Fq12` inversions
/// per round (one each in `linefunc`, `double` and `add`), which were about
/// two thirds of a pairing once multiplication was cheap. Only squaring `f`
/// and multiplying in each line still happen in `Fq12`.
fn millerLoopFq2(q: G2Point, p: G1Point) Fq12 {
    var r = q;
    var f = Fq12.one;
    var i: i16 = log_ate_loop_count;
    while (i >= 0) : (i -= 1) {
        f = f.mul(f).mul(lineAt(r, r, p));
        r = double(Fq2, r);
        if (ate_loop_count & (@as(u256, 1) << @intCast(i)) != 0) {
            f = f.mul(lineAt(r, q, p));
            r = add(Fq2, r, q).?;
        }
    }
    const q1 = frobeniusG2(q);
    const nq2 = neg(Fq2, frobeniusG2(q1)).?;
    f = f.mul(lineAt(r, q1, p));
    r = add(Fq2, r, q1).?;
    f = f.mul(lineAt(r, nq2, p));
    return f;
}

/// `linefunc(twist(r), twist(s), castPointToFq12(p))`: the line through `r`
/// and `s` (the tangent if they are equal) evaluated at `p`, built directly.
/// With the twisted `x1 = xr w^2`, `y1 = yr w^3` and slope `lambda w`, the
/// reference's `m (xt - x1) - (yt - y1)` expands to
///
///     -yp + (lambda xp) w + (yr - lambda xr) w^3
///
/// and the vertical line `xt - x1` to `xp - xr w^2`.
fn lineAt(r: G2Point, s: G2Point, p: G1Point) Fq12 {
    var c: [12]Fq = .{Fq.zero} ** 12;
    if (r.x.eq(s.x) and !r.y.eq(s.y)) {
        c[0] = p.x;
        placeFq2(&c, 2, r.x.neg());
        return .{ .coeffs = c };
    }
    const lambda = if (r.x.eq(s.x))
        r.x.mul(r.x).mulScalar(Fq.init(3)).div(r.y.mulScalar(Fq.init(2)))
    else
        s.y.sub(r.y).div(s.x.sub(r.x));
    c[0] = p.y.neg();
    placeFq2(&c, 1, lambda.mulScalar(p.x));
    placeFq2(&c, 3, r.y.sub(lambda.mul(r.x)));
    return .{ .coeffs = c };
}

/// Adds `b * w^k` into the flat coefficients `c`, for `b` in `Fq2`. `twist`
/// embeds `Fq2` through `i = w^6 - 9`, so `(b0 + b1 i) w^k` is
/// `(b0 - 9 b1) w^k + b1 w^(k+6)`.
fn placeFq2(c: *[12]Fq, k: usize, b: Fq2) void {
    c[k] = c[k].add(b.coeffs[0].sub(tower.times9(b.coeffs[1])));
    c[k + 6] = c[k + 6].add(b.coeffs[1]);
}

/// The `G2` point whose twist is the Frobenius image of `twist(q)`, which is
/// what the reference's `q1`/`nq2` are. Computed by going through the twist
/// and back rather than with hand-derived constants, so it agrees with the
/// reference by construction; it runs twice per pairing, not per round.
fn frobeniusG2(q: G2Point) G2Point {
    const t = twist(q).?;
    const w2 = w.mul(w);
    return .{
        .x = fromSubfield(frobenius(t.x).mul(w2.inv())),
        .y = fromSubfield(frobenius(t.y).mul(w2.mul(w).inv())),
    };
}

/// The inverse of `twist`'s embedding of `Fq2`: an `Fq12` element that lies
/// in that subfield has only its `w^0` and `w^6` coefficients set, and
/// `c0 + c6 w^6 = (c0 + 9 c6) + c6 i`.
fn fromSubfield(e: Fq12) Fq2 {
    for (e.coeffs, 0..) |coeff, k| std.debug.assert(k == 0 or k == 6 or coeff.eq(Fq.zero));
    return .{ .coeffs = .{ e.coeffs[0].add(tower.times9(e.coeffs[6])), e.coeffs[6] } };
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

test "Montgomery Fq.mul agrees with a plain 512-bit remainder" {
    // The reference is the exact expression `mul` used to be.
    var prng: std.Random.DefaultPrng = .init(0x6d6f6e74);
    const rand = prng.random();
    for (0..2000) |_| {
        const a = Fq.init(rand.int(u256));
        const b = Fq.init(rand.int(u256));
        const expected: u256 = @intCast((@as(u512, a.n) * b.n) % field_modulus);
        try std.testing.expectEqual(expected, a.mul(b).n);
    }
    // Edges: zero, one, the largest element, and squaring it (the largest
    // possible product, which is what bounds `redc`'s input).
    const edges = [_]u256{ 0, 1, 2, field_modulus - 1, field_modulus - 2 };
    for (edges) |x| for (edges) |y| {
        const expected: u256 = @intCast((@as(u512, x) * y) % field_modulus);
        try std.testing.expectEqual(expected, (Fq{ .n = x }).mul(.{ .n = y }).n);
    };
}

test "the Fq12 tower multiplies and inverts exactly like the flat reference" {
    var prng: std.Random.DefaultPrng = .init(0x746f7765);
    const rand = prng.random();
    for (0..64) |_| {
        var ca: [12]Fq = undefined;
        var cb: [12]Fq = undefined;
        for (&ca, &cb) |*x, *y| {
            x.* = Fq.init(rand.int(u256));
            y.* = Fq.init(rand.int(u256));
        }
        const a: Fq12 = .{ .coeffs = ca };
        const b: Fq12 = .{ .coeffs = cb };
        try std.testing.expect(a.mul(b).eq(a.mulSchoolbook(b)));
        try std.testing.expect(a.inv().eq(a.invGeneric()));
        try std.testing.expect(a.mul(a.inv()).eq(Fq12.one));
    }
    // Structured values: the identity, and the tower's own generators
    // (w, and w^6 = xi) where the flat <-> tower conversion does real work.
    var w6_coeffs: [12]i64 = .{0} ** 12;
    w6_coeffs[6] = 1;
    const w6 = Fq12.initInts(w6_coeffs);
    for ([_]Fq12{ Fq12.one, w, w6, w.mulSchoolbook(w6) }) |x| {
        try std.testing.expect(x.mul(x).eq(x.mulSchoolbook(x)));
        try std.testing.expect(x.inv().eq(x.invGeneric()));
    }
    try std.testing.expect(Fq12.zero.inv().eq(Fq12.zero.invGeneric()));
}

test "Jacobian multiply agrees with the affine reference on G1 and G2" {
    var prng: std.Random.DefaultPrng = .init(0x6a61636f);
    const rand = prng.random();
    const fixed = [_]u256{ 0, 1, 2, 3, curve_order - 1, curve_order, curve_order + 1, std.math.maxInt(u256) };
    var scalars: [8 + 24]u256 = undefined;
    @memcpy(scalars[0..8], &fixed);
    for (scalars[8..]) |*n| n.* = rand.int(u256);
    for (scalars) |n| {
        try std.testing.expectEqual(multiplyAffine(Fq, g1, n), multiply(Fq, g1, n));
        const j2 = multiply(Fq2, g2, n);
        const a2 = multiplyAffine(Fq2, g2, n);
        try std.testing.expectEqual(a2 == null, j2 == null);
        if (a2) |a| try std.testing.expect(a.x.eq(j2.?.x) and a.y.eq(j2.?.y));
    }
    // A point plus its own negation lands on infinity mid-computation, the
    // case the addition formula has to special-case.
    const p = multiply(Fq, g1, 5).?;
    try std.testing.expectEqual(@as(?G1Point, null), add(Fq, p, neg(Fq, p)));
    try std.testing.expectEqual(@as(?G1Point, null), multiply(Fq, g1, curve_order));
}

test "the Fq2 Miller loop computes exactly the reference's Fq12 value" {
    // Exact equality before the final exponentiation, not just after it:
    // both loops are meant to produce the same field element.
    const ps = [_]u256{ 1, 2, 7, 1234567, curve_order - 1 };
    const qs = [_]u256{ 1, 3, 11, 7654321, curve_order - 2 };
    for (ps) |a| for (qs) |b| {
        const p = multiply(Fq, g1, a).?;
        const q = multiply(Fq2, g2, b).?;
        try std.testing.expect(millerLoop(q, p).eq(millerLoopRaw(twist(q), castPointToFq12(p))));
    };
    try std.testing.expect(millerLoop(null, g1).eq(Fq12.one));
    try std.testing.expect(millerLoop(g2, null).eq(Fq12.one));
}
