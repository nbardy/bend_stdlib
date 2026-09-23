# Floats and proofs in Bend

What can be proven about floating-point code in Bend, what has to be
assumed, and what a library can do without changing the language.
Facts marked (probe) were run on Bend 2.0.25 on 2026-09-23; facts marked
(source) were read in upstream's `bend2/comp.ts` at `main`.

## What Bend does with F32 today

- Every `F32` operation in Base (`F32.add`, `F32.mul`, `F32.sqrt`, ...)
  is a law with no definition, so the checker treats it as an opaque
  function. `{F32.add(1.0, 1.0) == 2.0 : F32}` does not check (probe).
- A float value is `F32{Word(32n)}`, its 32 bits, so functions over the
  bits compute on literals. Decoding `1.5` into sign, mantissa
  `12582912` and exponent `127` closes by `{==}` (probe).
- A user file cannot add an axiom: a law with no definition fails the
  check as an open TODO (probe). Only Base may leave laws unfilled.
- The compiled code is plain IEEE 754 binary32 for `+ - * /`, `sqrt`,
  `floor`:
  - C (CPU): `#pragma clang fp contract(off)`, so no fused multiply-add
    rewrites (source).
  - CUDA: `--fmad=false` (source).
  - Metal: `MTLMathModeSafe`, except `sin`, `cos`, `tan`, which use
    `fast::` (source).
  - JS: `Math.fround(a op b)`: the operation in float64, then rounded
    to float32 (source). For `+ - * /` (and `sqrt`) on float32 inputs
    this double rounding gives the correctly rounded float32 result
    (Figueroa 1995), so JS agrees with C bit for bit, except in NaN
    payloads (upstream WONTFIX #797).
  - Not checked: whether Apple GPUs flush subnormals to zero, and how
    far `exp`, `log`, `pow` and the fast trig functions are from
    correctly rounded on each backend.
- `apps/fluid.bend` prints identical F32 results on the interpreter
  (JS) and the native binary (C). That is a test, not a proof.

## Bit-field predicates

These are ordinary functions over a float's 32 bits: the sign (bit 31),
the exponent (bits 23-30), the mantissa (bits 0-22), and predicates such
as `is_nan` (exponent all ones, mantissa non-zero), `is_finite` and
`is_normal`. They compute in the checker.

On their own they are weak: they classify values but say nothing about
the result of `F32.add(x, y)`, whose bits the checker cannot see. A law
can take `is_finite(x) == True` as a premise, and a type can carry it,
but no arithmetic fact follows.

Their real use is as the decoder for an exact model: `decode(x)` turns
a float into the exact number `(-1)^s * m * 2^(e - 150)`, and every
statement about rounding error is a statement about decoded values.

Checker constraint (probe): keep the model in binary. Converting a
24-bit mantissa to `Nat` builds about 12 million unary successors and
overflows the checker's stack. `U32`/`Word` arithmetic computes fine.

## Layers, and which need upstream

| layer | what it gives | library or upstream |
|---|---|---|
| 1. exact model | dyadic numbers `m * 2^e` with exact `+`, `*`; a round-to-nearest-even function; the lemma `|round(z) - z| <= ulp(z)/2` | library |
| 2. software float | `SF32.add` etc. over `U32`, proven equal to `round(exact result)` | library |
| 3. hardware link | `F32.add(x, y) == encode(SF32.add(decode x, decode y))` | assumption or upstream (below) |
| 4. error bounds | types or laws bounding how far a float computation is from the exact one | library, on top of 1-3 |

Layers 1 and 2 are what Flocq provides in Coq: an executable model of
each IEEE operation plus the proof that it is "compute exactly, then
round". Nothing in them needs a language change; the cost is proof
effort over `Word`, like `U32.sub_add` in `src/u32.bend`.

Layer 2 alone already gives fully proven floats: run `SF32` instead of
hardware `F32`. Results are bit-exact on every backend, and nothing is
assumed. The price is speed, since each operation is many integer
operations instead of one float instruction.

Layer 3 is where hardware enters. `F32.add` is opaque, so the link
cannot be proven, and a user file cannot assert it. Three options:

1. **Assume it as a hypothesis (library, possible now).** A law takes
   the link as a `~` argument, a dictionary such as
   `~ieee: IEEE32Correct` holding one equation per operation, and is
   proven under it. The law checks without anyone supplying the
   dictionary. Every result is then "proven, given that the hardware
   rounds correctly", which is the same trust Flocq-based work places in
   hardware (CompCert assumes its target implements IEEE 754). The
   difference from Coq: Bend has no way to discharge it, so the
   hypothesis stays a parameter all the way to the top-level law.
2. **Structural F32 in Base (upstream).** Base defines `F32.add` etc. by
   the software model, so the checker computes it, while the compiler
   keeps the machine instruction. This is exactly how `U32.add` works
   today (`Word.adc` in the checker, one instruction at run time). It
   is sound on C and JS for `+ - * / sqrt` given the settings above; the
   GPU backends need the same check. Transcendental functions would stay
   axioms, since no backend rounds them correctly.
3. **Trusted axioms marked in the verdict (upstream).** A user law
   marked, say, `@axiom`, reported by the checker the way `@unsafe` is.
   Smaller change, weaker guarantee: a false axiom proves anything.
   WONTFIX notes that opening unfilled laws to user files "touches
   consistency", so upstream has already said no to this direction for
   now.

## Could the type system itself track error?

Research languages do this. Numerical Fuzz (Kellison and Hsu) combines
a linear type discipline with a graded monad that tracks accumulated
rounding error; Bean (Kellison, Zielinski, Bindel, Hsu, PLDI 2025) uses
a graded coeffect system with strict linearity for backward error.
Bend is already affine and graded, but its grades are the three
quantities `&0 &1 &2`, not real-valued error bounds, so adding error
grades would change the core type theory: an upstream research project,
and unlikely given how small upstream keeps the core.

It is not needed for a library. Bend has dependent types, so an error
bound can be a type index: a value of `Approx(ideal, bound)` holds a
float, the exact value it approximates, and a proof that they differ by
at most `bound`, with each operation's law composing the bounds. That
is the graded-monad idea written with types the checker already has.

## Where this fits game physics

- Gameplay laws that must hold exactly (momentum conservation, exact
  rewind, invariants) belong in integer or fixed-point arithmetic, where
  they compute and are proven outright (`src/sim.bend`).
- Float code can get "drift from the exact solution is below B after N
  steps" laws through layers 1-4. The closest published work is
  Kellison and Appel's verified leapfrog integration of the harmonic
  oscillator, a C program verified in Coq, with round-off analysis done
  by VCFloat.
- Rendering and visual-only simulation stay tested, not proven.

## Suggested order

1. `float/bits.bend`: decode, encode, classification. Small; grounds
   everything else.
2. `float/dyadic.bend` and `float/round.bend`: exact binary arithmetic
   on `U32`-backed mantissas, round-to-nearest-even, and the half-ulp
   error lemma. This is the Flocq core, and the largest proof effort.
3. `float/soft.bend`: `SF32.add`, `SF32.mul` proven against the model,
   and differential tests against hardware on every backend, including
   the GPU.
4. `float/ieee.bend`: the hardware hypothesis as a dictionary, and error
   bound laws for a leapfrog step.
5. With 1-3 as evidence, an upstream issue proposing structural F32 in
   Base for `+ - * / sqrt`.

## Related work

Checked while writing this:

- Flocq (Boldo, Melquiond): IEEE 754 in Coq; executable operations
  proven to be "exact, then rounded"; used for CompCert's float
  semantics. <https://rocq-prover.org/p/coq-flocq/4.2.1>,
  <https://xavierleroy.org/publi/floating-point-compcert.pdf>
- Gappa (Melquiond): interval and rewriting tool for round-off bounds
  that emits Coq-checkable proofs. <https://arxiv.org/pdf/0801.0523>
- VCFloat and VCFloat2 (Appel, Kellison): automatic round-off bounds for
  float expressions in Coq. <https://github.com/VeriNum/vcfloat>,
  <https://www.cs.princeton.edu/~appel/papers/vcfloat2.pdf>
- Verified Numerical Methods for ODEs (Kellison, Appel, NSV 2022):
  leapfrog for the harmonic oscillator, C program to real solution.
  <https://link.springer.com/chapter/10.1007/978-3-031-21222-2_9>,
  <https://github.com/VeriNum/VerifiedLeapfrog>
- Numerical Fuzz (Kellison, Hsu): linear types plus a graded monad for
  rounding error. <https://arxiv.org/abs/2405.04612>
- Bean (Kellison, Zielinski, Bindel, Hsu, PLDI 2025): graded coeffects
  with strict linearity for backward error.
  <https://arxiv.org/abs/2501.14550>
- Type-Based Approaches to Rounding Error Analysis (survey).
  <https://arxiv.org/pdf/2501.14598>
- Lean 4: FloatSpec (a Flocq port), <https://github.com/alok/FloatSpec>;
  lean-ieee754 (error bounds for binary32/64),
  <https://github.com/tunnellm/lean-ieee754>
- Verifying Numerical Methods with Isabelle/HOL (2025).
  <https://arxiv.org/pdf/2511.20550>
- Figueroa, When is double rounding innocuous? (1995).
  <https://dl.acm.org/doi/10.1145/221332.221334>

From memory, not re-checked here: FPTaylor, Daisy and Rosa (static
round-off analysis), Herbie (rewriting for accuracy), the SMT-LIB
FloatingPoint theory, Harrison's HOL Light float proofs, and Russinoff's
ACL2 proofs of AMD float hardware.
