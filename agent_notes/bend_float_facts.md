# Bend facts that decide a float system

Verified on 2026-09-23 against Bend 2.0.25 (upstream `main`, run with
`bun bend2/main.ts`) and the installed 2.0.20. (probe) means a file was
checked; (source) cites upstream's code at `main`.

## How floats are defined

- `type F32 is Data: F32{data: Word(32n)}`: a float value is its 32 bits
  (`base.bend`). `U32` has the same representation.
- Every F32 operation is a law with no definition: `F32.add`, `sub`,
  `mul`, `div`, `mod`, `pow`, `sqrt`, `exp`, `log`, trig, `floor`,
  `ceil`, `trunc`, the comparisons, `F32.show`, `F32.bits`, `F32.read`,
  `U32.to_f32`, `F32.to_u32` (`base.bend`). `F32.min`, `max`, `clamp`,
  `lerp`, `round` are defined in terms of them.
- `{F32.add(1.0, 1.0) == 2.0 : F32}` does not check: the checker
  observes `2.0` and expects `F32.add(1.0, 1.0)` (probe).
- Functions of a literal's bits do compute: decoding `1.5` to sign
  `False`, mantissa `12582912` and biased exponent `127` as `U32` closes
  by `{==}` (probe).
- `-0.5` is not a literal (parse error, probe). Write `F32.sub(0.0, x)`
  or reorder the arithmetic.

## Who may assert what

- A law with no definition in a user file fails the check ("1 TODO
  found", probe). Only `base.bend` may leave laws unfilled.
- WONTFIX: "A user law of kind Type counts as open ... Opening this to
  user files touches consistency."
- A law may take `~` hypotheses and is checked once with them opaque; a
  law with `~` parameters needs no instance to pass the check (probe,
  and upstream `tests/proof/template_law.bend`). So "proven, given
  hypothesis H" is expressible now.

## How Base definitions become machine instructions

- Every definition loaded from `base.bend` gets `b = true`
  (`bend2/bend.ts` around line 1098).
- `intr_of` (`bend2/comp.ts` around line 863) gives a definition a native
  implementation from the `OPERATIONS` table when it is a Base
  definition, even one with a body, or an unfilled law. The key is the
  name lowercased with dots replaced by underscores: `F32.add` becomes
  `f32_add`.
- So Base's `U32.add` has a structural body (`Word.adc`) that the checker
  computes, and compiles to one machine add. Same for `Nat.add` (a
  native 48-bit add, `nat_add`) and `U32.from_nat` (measured: 200k calls
  in under a second).
- Consequence: if Base gave `F32.add` a body (a software IEEE addition),
  the checker would compute it and the compiled code would still be one
  float instruction. The change would be to `base.bend` only.
- User definitions never get a native implementation this way: module
  definitions carry their path in their name, and `b` is only set for
  Base.

## What the compiled float code is (source)

- C: `f32_rewrap(f32_unbox(a) op f32_unbox(b))`, with
  `#pragma clang fp contract(off)`; clang `-O3`. One binary32 operation
  per Bend operation, no fused multiply-add.
- CUDA: compiled with `--fmad=false`.
- Metal: `MTLMathModeSafe`; `sin`, `cos`, `tan` use `fast::`, the other
  library functions `precise::`.
- JS: `Math.fround(a op b)` and `Math.fround(Math.f(a))`. For `+ - × ÷`
  (and `sqrt`) on float32 inputs this equals correct binary32 rounding
  (Figueroa). NaN payloads differ from C (WONTFIX #797).
- Not verified: whether Apple GPUs flush subnormals to zero; how
  accurate `exp`, `log`, `pow` and fast trig are on each backend.
  Library functions are not correctly rounded on any backend.
- `apps/fluid.bend` printed identical results on JS and C (test, not
  proof).

## Checker costs that shape a model

- `Nat` is unary in the checker (`Zero`/`Succ`). A literal stays one
  `Lit` node until compared or matched (2.0.24), but arithmetic unfolds
  one successor at a time. Converting a 24-bit mantissa with
  `U32.to_nat` overflowed the checker's stack (probe).
- `U32`/`Word(n)` arithmetic is bit-by-bit: `Word.adc`, `Word.mul` and
  `Word.cmp` over `n` bits. Ground `U32` goals close in about 0.1 s. Base
  defines these generically in `n`, so `Word(64n)` or wider works.
- Exact arithmetic in the checker therefore needs binary numbers: fixed
  `Word(n)` where a bound on width is known, or a variable-length bit
  list (not in Base) where it is not.
- Universal laws over `Word` go by induction on the width with the carry
  generalized; `src/u32.bend` (`cmp_nat`, `sub_add`, `add_sub`) are
  worked examples, 16-64 lines each.

## Language constraints any float library meets

- A match inspects a parameter or pattern variable, not a computed
  value; scrutinees follow binder order; a `let` cannot precede a match
  on a parameter.
- A destructuring `let` works only on a parameter. Threading a linear
  value (an `Array`) through reads needs a helper per step, or a state
  monad (`apps/fluid.bend` defines `St`).
- A `+` or `-` binder is part of a law's type; a template argument's
  type must match exactly (hit in `examples/tour.bend` and
  `apps/fluid.bend`).
- Two template instances are equal only when their `~` arguments are the
  same terms (hit in `examples/tour.bend`). There is no function
  extensionality.
- Templates are the way to write a program once over a number dictionary
  and run it at several number types (`src/class.bend`).
- Dependent types: a type can be computed from values, so an error
  bound can be a type index.
- Quantities are `&0`, `&1`, `&2` (erased, affine, copyable). They
  prevent accidental duplication of `Type`-kinded values but do not
  count uses.

## Upstream constraints

- `bend2/bend.ts` is human-written; outside PRs are closed and
  re-implemented (PR #860 became 2.0.17's structural `Nat.max`).
- The repo gate caps `base.bend` at 32k tokens (`gates/repo.ts`); a
  software float in Base competes for that budget.
- Anything proposed upstream should come as an issue with a working
  library and probes as evidence.
