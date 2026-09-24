# Filed: bendlang/bend#1017

Opened 2026-09-24 as <https://github.com/bendlang/bend/issues/1017>.

---

**Title:** Laws about F32 code: make float operations computable in the checker

Body as edited 2026-09-25 (examples, hub import):

### What Bend should do

Let a law state and prove facts about float results:

```python
law sum_tenths:
  {F32.add(0.1, 0.2) == 0.3 : F32}   # true in binary32: both are 0x3E99999A
```

Today every `F32` operation in Base is an unfilled law, so this does not
check, and a user file cannot add axioms. Integer code has laws; float
code has none.

### What a library already gets

A float is `F32{Word(32n)}`, so functions of its bits compute in the
checker. A library uses that without any Base change:
<https://github.com/nbardy/bend_stdlib/tree/main/src/float>
(guide: [src/float/README.md](https://github.com/nbardy/bend_stdlib/blob/main/src/float/README.md)).
The hardware enters only as a named hypothesis, passed as a `~` argument.
It is on the hub, so trying it is one line:
`import bend-lawful-stdlib@0.1.0.0/src/float/f32.bend as F32`.

**Laws about game code.** [`apps/breakout.bend`](https://github.com/nbardy/bend_stdlib/blob/main/apps/breakout.bend)
keeps its paddle and ball in `F32` and moves them with Base's
`F32.add` and `F32.clamp`. Comparison and negation are specified on the
bits, and Base's `F32.clamp` is proven to stay in `[lo, hi]` for every
input, NaN and the infinities included. So, for every input list:

```python
law arena_run:
  for ~lt: F32.LtOk()          # the hardware's < is IEEE 754's
  for xs: List<&2, F32>        # mouse positions: any floats
  Arena(M.run(~Game, ~F32, ~step, init(), xs))
```

With NaN as the input on every step, the paddle sits at 216, the value
the proof says `F32.clamp(NaN, 0, 216)` returns. A second law,
`speed_run`, says the ball's speed never changes, bit for bit, because a
bounce is `F32.neg` (assuming `NegOk`).

**Laws that prevent backend divergence.** [`apps/fluid.bend`](https://github.com/nbardy/bend_stdlib/blob/main/apps/fluid.bend)
converts a back-traced position to an index with `F32.to_u32`, which is
undefined in C for NaN or out-of-range values, so the C and JS lanes
could disagree. A clamped `cell` step and its law `cell_ok` guarantee an
index in `[0, 95]` and a weight in `[0, 1]` for every float.

**Rounded arithmetic in the checker.** binary32 `add`, `sub`, `mul` in
software, as IEEE defines them (the exact result, then round to nearest
even), so a float fact closes by `{==}`:

```python
law add_rounds:
  {SF32.bits(SF32.add(0.1, 0.2)) == 1050253722 : U32}   # 0x3E99999A

def add_rounds():
  {==}
```

[`examples/sf32.bend`](https://github.com/nbardy/bend_stdlib/blob/main/examples/sf32.bend)
compares the software `add` and `mul`, and the bit-level comparison and
negation, with the hardware's on edge cases and 3000 random bit
patterns, on the C and JS lanes: 0 mismatches. It also found that the JS
lane does not keep a NaN's sign bit, so the negation hypothesis leaves
NaNs out.

### What only Base can do

Give the operations bodies while the compiler keeps the machine
instruction, as it already does for `U32.add` (`Word.adc` to the
checker, one instruction at run time). Then these laws need no
hypothesis. Two sizes:

1. **Exact operations first:** `F32.is_lt`, `is_le`, `is_eq`, `neg`,
   `abs`, whose results involve no rounding, so every backend agrees
   (NaN bits aside: #797, and the JS lane drops a NaN's sign). The bit-level definitions exist in
   [`src/float/f32.bend`](https://github.com/nbardy/bend_stdlib/blob/main/src/float/f32.bend).
   With these, `F32.min`, `max` and `clamp`, which Base already defines
   through `is_lt`, compute in the checker, and the breakout and fluid
   laws above need no assumption.
2. **Rounded operations:** `add`, `sub`, `mul`, `div`, `sqrt` as "exact,
   then round". They are correctly rounded on the C lane (contraction
   off) and the JS lane (`Math.fround` of a float64 result is the
   float32 result for these); Metal and CUDA would need checking.
   Transcendental functions would stay laws.

This is the step CompCert took in 1.12, replacing axiomatized floats with
Flocq's executable, proven IEEE model. Related work we drew on: VCFloat2
(Appel, Kellison), Numerical Fuzz (Kellison, Hsu), Bean. Design notes:
<https://github.com/nbardy/bend_stdlib/blob/main/notes/float_system.md>.

Is this something you want in Base, somewhere else, or left to
libraries? The library works as it is either way.

(Written with AI assistance; I read and approved it.)

