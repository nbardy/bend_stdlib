# float: laws about float code

Bend's Base leaves every `F32` operation as an unfilled law, so the
checker cannot compute `F32.add(0.1, 0.2)` or say anything about code
that uses floats. A float is also `F32{Word(32n)}`, its 32 bits, and
functions of the bits do compute. This folder (`import bend-lawful-stdlib@0.1.0.0/src/float/f32.bend as
F32`) uses that in two ways:

1. **Exact operations, specified on the bits.** Comparison and negation
   are exact in IEEE 754. `f32.bend` defines them on the bits and proves
   laws about Base's own `F32.clamp` and `F32.neg`. The hardware enters
   as one named assumption per operation (`LtOk`, `NegOk`), passed as a
   `~` argument, so each law says what it assumes. The game still runs
   on the machine's floats.
2. **Rounded operations, in software.** `sf32.bend` implements binary32
   `add`, `sub` and `mul` as IEEE 754 defines them: the exact result,
   then round to nearest even. The checker computes them, so a float
   fact closes by `{==}`.

## What it gives an app

From [`apps/breakout.bend`](../../apps/breakout.bend), a game whose
paddle and ball are `F32`. Every step ends by clamping the positions
with Base's `F32.clamp`, and the arena law holds for every input list,
including NaN and infinite mouse positions:

```python
law arena_run:
  for ~lt: F32.LtOk()
  for xs: List<&2, F32>
  Arena(M.run(~Game, ~F32, ~step, init(), xs))
```

The proof of one step is six calls, one per bound:

```python
(F32.lo_le_clamp(~lt, p, 0.0, 216.0, Unit{}), F32.clamp_le_hi(~lt, p, 0.0, 216.0, Unit{}),
 F32.lo_le_clamp(~lt, x, 0.0, 252.0, Unit{}), F32.clamp_le_hi(~lt, x, 0.0, 252.0, Unit{}),
 ...)
```

`Unit{}` is the proof that `0.0 <= 216.0`: the checker computes it from
the bits. With a NaN aim on every step, the paddle stays at 216, the
value the proof says `F32.clamp(NaN, 0, 216)` returns; `main` prints it.

In the same app, a bounce is `F32.neg(v)`. `F32.neg_mag` says negation
keeps the magnitude bits, so the ball's speed never changes, bit for
bit, over every input list (`speed_run`, assuming `NegOk`).

From [`apps/fluid.bend`](../../apps/fluid.bend): semi-Lagrangian
advection traces each cell back along the velocity and converts the
position to an array index with `F32.to_u32`. That conversion is
undefined in C for NaN, negative or huge values, and then the C and JS
lanes disagree. `cell` clamps the index and the interpolation weight,
and `cell_ok` proves both are in range for every float.

The same app shows the software floats earning their keep. Its
projection kernels take their float operations as a template argument
(`~o: Ops`): `hard()` is the machine's `F32`, `soft()` is `SF32`. The
app runs `project(~hard(), 31n, 20n, a)` on its 32x32 grid; the checker
runs the same `project` with `soft()` on a 4x4 fixture and closes

```python
law projection:
  {summary(checked(~soft())) == Summary{Bits3{1073741824, 1075419546, 907468800}, True{}} : Summary}
```

by `{==}`: 20 Jacobi sweeps take the total |divergence| from 2.4 to
1.1796875 * 2^-19, bit for bit (the `True{}` is "it went down").
`main` runs the fixture on `hard()` too and prints whether the bits
agree, which carries the law to the machine by test.

From [`examples/sf32.bend`](../../examples/sf32.bend): facts about
rounded arithmetic, closed by the checker:

```python
law add_rounds:
  {SF32.bits(SF32.add(0.1, 0.2)) == 1050253722 : U32}   # 0x3E99999A

def add_rounds():
  {==}
```

The same file compares the software operations, comparison and
negation with the hardware's on edge cases and 3000 random bit patterns,
on the interpreter (JS) and the native binary (C). It prints 0
mismatches. That test found that the JS lane does not keep a NaN's sign
bit, so `NegOk` leaves NaNs out.

## Modules

| module | import as | what |
|---|---|---|
| [`f32.bend`](f32.bend) | `F32` | `lt_bits`, `LE`, `neg_bits`, `mag`, `key` on the bits; `LtOk()`, `NegOk()`; laws `clamp_le_hi`, `lo_le_clamp`, `neg_mag`, `neg_key` |
| [`sf32.bend`](sf32.bend) | `SF32` | `add`, `sub`, `mul` in software; `decode`, `encode`; `soft()`, `hard()`; the assumption `HardOk()` that hardware `+` and `*` round correctly |
| [`format.bend`](format.bend) | `Fmt` | exact values `Val` (`Z`, `Inf`, `NaN`, `Fin`), `Format`, `round`, `spec_add`, `spec_sub`, `spec_mul` |
| [`num.bend`](num.bend) | `Num` | the contract an implementation meets: `Impl`, `AddOk`, `MulOk`, `Correct` |
| [`bin.bend`](bin.bend) | `Bin` | binary naturals: add, sub, mul, compare, shifts that keep round and sticky bits |

`f32.bend` stands alone and is the one most code needs. `format.bend`
works for any binary format: `binary32()` is `Format{24n, 151n, 404n}`,
and another `Format` gives another precision.

## Writing a float law

- Clamp a float before it becomes an index, or before it leaves the
  bounds a law is about. The clamp laws then hold for every input.
- Take the assumption as a `~` argument (`for ~lt: F32.LtOk()`), and
  pass it on. Don't hide it in a definition.
- Prefer exact operations for laws: comparison, negation, clamping.
  Their assumptions hold on every lane. Laws about rounded results need
  `HardOk`, which Metal and CUDA have not been checked against.
- Values the solver computes (a fluid's divergence, an integrator's
  drift) are still tested, not proven. Error-bound laws are not built
  yet.

## Limits

- Base's `F32.add` and friends stay opaque, so a law about them needs an
  assumption. bendlang/bend#1017 proposes giving them bodies in Base,
  as `U32.add` already has, so the assumptions go away.
- The software operations are slow at run time, since each is many
  integer operations. Use them in laws and tests; run on hardware.
- Transcendental functions (`sin`, `exp`, `pow`) have no model here.

Design notes and related work (Flocq, VCFloat, Numerical Fuzz):
[`docs/floats.md`](../../docs/floats.md).
