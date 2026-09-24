# Float error bounds: what is proven, how, and what is left

State as of 2026-09-25, `src/float/error.bend` (imported as `Err`).

## Proven

All values are compared as natural numbers on one scale: a mantissa `m`
at (offset) exponent `t` is `sh(m, t) = m * 2^t`. `Bound(Y, X, k)` is
`2|Y - X| <= 2^k`, written as two `Nat.LE` facts, so no subtraction.

| law | statement |
|---|---|
| `shr_ok` | `Bin.shr(k, a, r, s)` keeps `M = q * 2^N + T`, and its round and sticky bits say which of four cases `2T` is in against `2^N`: 0, below half, exactly half, above half (`Tail`) |
| `fin_near` | round to nearest, ties to even, on what `shr` left is within half of `2^k` |
| `round_near` | `Fmt.round(f, neg, m, e)` is `Near` `m * 2^e`: a finite result within half its own ulp (and with a non-zero mantissa), a zero within half of `2^lsb`, or infinity (no bound); never NaN |
| `adc_ok`, `add_ok`, `mul_ok`, `shl_ok` | `Bin.adc`, `Bin.add`, `Bin.mul`, `Bin.shl` are exact |
| `mul_near` | `spec_mul` of two finite values is `Near` `ma * mb * 2^(ea + eb - 300)` |
| `add_near` | `spec_add` of two finite values of the same sign is `Near` `ma * 2^ea + mb * 2^eb` |
| `canon_near` | `Fmt.canon` keeps `Near` (the value stays, the own ulp can only grow) |
| `hard_mul_near`, `hard_add_near` | under `SF32.HardOk`, the same for Base's `F32.mul` and `F32.add`, on the canonical form of the hardware result |
| `hard_step_near` | under `HardOk`, for positive finite `x`, `v`, `dt` with a positive finite product: `2 |x' - (x + v * dt)| <= ulp(x') + ulp(v * dt)`, where `x' = F32.add(x, F32.mul(v, dt))` |

`examples/drift.bend` attaches `hard_step_near` to its own Euler step
and measures the true error of 3000 hardware steps exactly (binary
integers): all within the bound, 237 of the random ones above half of
it. With only `ulp(x')` as the bound, 122 fall outside, so the second
term is needed.

Check time: `bend src/float/error.bend --check-only` about 0.8 s CPU
(Bend 2.0.27, M-series Mac). The proofs are symbolic, so a 24-bit
mantissa costs no more than a 3-bit one.

Each generic proof was broken once and rejected: rounding up whenever
any bit is set (rejected at `fin_near`'s below-half case), dropping the
round bit in `Bin.shr` (`shr_ok`), a carry bug in `Bin.adc` (`adc_ok`),
a two-ulp bound missing one ulp (`compose`), and the step law claiming a
zero product ulp (`hard_step_near`).

## Left, and why

- **`+` of opposite signs, and `-`.** `spec_add` then subtracts aligned
  mantissas with `Bin.sub` after `Bin.cmp`. Needs `Bin.sbb` exact and
  `Bin.cmp` agreeing with `Nat` order, then the same alignment proof as
  `add_near`. No checker obstacle; about the size of `adc_ok` plus
  `add_near`.
- **A constant epsilon from input ranges.** The bounds are in ulps of
  the results. Turning "x < 256" into "ulp(x') <= 2^-16" needs laws
  relating `Bin.len` and `Fmt.lsb` to the value's size. No obstacle
  found; not started.
- **Many steps.** One step's bound is proven. Over n steps the errors
  add, and a law needs the previous step's bound carried through the
  next step's inputs (the next `x` is the previous `x'`).
- **The product premise.** `hard_step_near` takes
  `{SF32.decode(F32.mul(v, dt)) == Fin{False, mp, tp}}`: the hardware
  product's bits. It could be derived from `HardOk` and the spec
  product being finite and positive, but that needs an existential
  (the hardware's `mp`, `tp`), which Bend expresses as a `Sigma` the
  caller then unpacks.
- **Metal and CUDA** are not checked against `HardOk`.

## Checker behaviours this hit

- `%e : P` needs the goal to be `P` with `e`'s right side in the holes,
  and leaves `P` with the left side. An error shows the goal as it was.
  Most failures here were a missing `Equal.sym`.
- `Equal.sym(A, a, b, e)` takes `e : {a == b}`.
- A pair `A & B` is a `Type`, so a proof pair cannot be copied with `+`.
  Where two branches need the same bound, pass it once plus a function
  that uses it (`over_near`'s `zf`).
- A function whose clauses overlap (`Bin.adc`: `case BZ{} b` then
  `case a BZ{}`) reduces only once every scrutinee's constructor is
  known, so `adc(BZ, b, c)` is stuck for a variable `b`; the proof
  splits `b` (`adc_ok`).
- Destructuring a triple with copies, `(+q, +r, +s) = res`, failed to
  infer; destructure plainly in a thin wrapper and take copies as the
  helper's parameters (`round_fin_near`).
- User files have no mutual recursion: an induction step helper takes
  the inductive result as an argument (`after_succ` in `shr_ok`).
