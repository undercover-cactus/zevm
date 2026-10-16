# The Frobenius endomorphism in `Bn128`

Why [`src/Bn128.zig`](../src/Bn128.zig) computes `a^p` with 23 field
multiplications instead of 100,000, and why that is the same value.

## The problem

The optimal ate pairing needs `a^p` (where `p` is the base field modulus)
in two places: the Miller loop's last two line functions, and the final
exponentiation's easy part. The original port of `py_ecc` reached it the
obvious way, by square-and-multiply:

```zig
const q1: G12Point = .{ .x = qq.x.pow(u256, field_modulus), .y = qq.y.pow(u256, field_modulus) };
```

`p` is 254 bits with a population count of 111, so each of those is 253
squarings plus 110 multiplications, 363 `Fq12` multiplications in all. One
`Fq12` multiplication is 144 `Fq` multiplications for the schoolbook
product plus 132 more for the reduction, so a single `a^p` costs roughly
**100,000 `Fq` multiplications**. The Miller loop does four of them per
pairing, which measured at **26% of total pairing time**.

It is also, mathematically, the wrong way to compute it. `a^p` in
characteristic `p` is not really an exponentiation.

## The Frobenius is linear

`Fq12` here is `Fq[x] / (x^12 - 18x^6 + 82)`, so an element is twelve `Fq`
coefficients. Write the map we want as

```
  pi(a) = a^p
```

Two standard facts make this `Fq`-linear.

**Addition is additive in characteristic `p`.** For any `u`, `v` in a
commutative ring of characteristic `p` prime,

```
  (u + v)^p = u^p + v^p
```

because every binomial coefficient `C(p, k)` for `0 < k < p` has `p` in its
numerator and nothing in its denominator to cancel it, so all the middle
terms vanish mod `p`.

**Scalars are fixed.** For `c` in `Fq`, Fermat's little theorem gives
`c^p = c`, since `Fq`'s multiplicative group has order `p - 1`.

Put them together for `a = sum a_i x^i` with every `a_i` in `Fq`:

```
  pi(a) = (sum a_i x^i)^p
        = sum (a_i x^i)^p        additivity
        = sum a_i^p (x^i)^p      multiplicativity
        = sum a_i (x^p)^i        Fermat on the coefficients
        = sum a_i gamma^i        where gamma = x^p
```

So `pi` is completely determined by the single element `gamma = x^p`, and
applying it is a fixed `Fq`-linear combination of the twelve constants
`gamma^0 ... gamma^11`. Those live in `frobenius_gamma`, generated offline
from the reference `pow`.

## Why the table is sparse

A dense `12 x 12` table would cost 144 multiplications. The real table
costs 23, because each `gamma^i` has only **two** nonzero coefficients:

```
  gamma^0   nonzero at [0]
  gamma^1   nonzero at [1, 7]
  gamma^2   nonzero at [2, 8]
  ...
  gamma^6   nonzero at [0, 6]
  gamma^7   nonzero at [1, 7]
  ...
  gamma^11  nonzero at [5, 11]
```

The pattern is `j` congruent to `i` mod 6, and it comes from a subfield.
Set `u = x^6`. The modulus says

```
  x^12 - 18x^6 + 82 = 0   so   u^2 = 18u - 82
```

That quadratic has discriminant `324 - 328 = -4`, so `u = 9 +- sqrt(-1)`.
Since `p = 3 mod 4`, `-1` is not a square in `Fq`, so `Fq[u]` really is a
degree-2 subfield of `Fq12`, and `{1, u}` is an `Fq`-basis for it.

Now `gamma` itself turns out to be `A*x + B*x^7`, which factors as
`x * (A + B*u)`. Therefore

```
  gamma^i = x^i * (A + B*u)^i
```

and `(A + B*u)^i` lies in `Fq[u]`, so it is `c + d*u` for some `c`, `d` in
`Fq`. That leaves

```
  gamma^i = c*x^i + d*x^(i + 6)
```

two terms, with the exponents reduced mod the modulus when `i >= 6`. The
sparsity is not a numerical coincidence; it is the `Fq12 / Fq[x^6] / Fq`
tower showing through the flat representation.

## The cost, before and after

| | `Fq` multiplications |
| --- | --- |
| `pow(u256, field_modulus)` | ~100,000 |
| `frobenius` | 23 |

The Miller loop calls it four times per pairing, and
`finalExponentiate` calls it eight more (six for `f^(p^6)`, two for
`^(p^2)`). Twelve calls at 23 multiplications each is 276, which is what a
single `Fq12` multiplication costs: the entire Frobenius budget of a
pairing now rounds to one multiplication.

## Where it is used

```zig
// Miller loop: the two Frobenius images of Q that the optimal ate
// pairing's final line functions need.
const q1: G12Point = .{ .x = frobenius(qq.x), .y = frobenius(qq.y) };
const nq2: G12Point = .{ .x = frobenius(q1.x), .y = frobenius(q1.y).neg() };

// Final exponentiation: the easy part, f^((p^6 - 1) * (p^2 + 1)).
const easy = frobeniusPow(f, 6).mul(f.inv());
const m = frobeniusPow(easy, 2).mul(easy);
```

`frobeniusPow(a, n)` is just `n` applications, which is how `p^2` and `p^6`
are reached. At 23 multiplications each that is cheaper than keeping
separate constant tables for them.

## Regenerating and checking the constants

The table is generated from the implementation it replaced, so it cannot
drift from it by transcription. To rebuild it, exponentiate `x` by
`field_modulus` with the reference `pow` and print the first twelve powers
of the result:

```zig
var x_coeffs: [12]i64 = .{0} ** 12;
x_coeffs[1] = 1;
const gamma = Fq12.initInts(x_coeffs).pow(u256, field_modulus);
// then print gamma^0 .. gamma^11
```

More importantly, the test suite re-derives it on every run. The test
`frobenius matches square-and-multiply by field_modulus` checks

```zig
frobenius(a).eq(a.pow(u256, field_modulus))
```

on random `Fq12` elements, not just structured ones, so a table entry that
happened to be correct only on sparse input could not pass. It also checks
the specific values the Miller loop feeds it: `one`, `zero`, and the
twisted `G2` generator's coordinates.

`pow` was deliberately left in place for this. It is the slow, auditable
reference the fast path is measured against.
