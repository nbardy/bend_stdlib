# Float verification: what the literature does

Notes from reading the primary sources on 2026-09-23. For each work: the
core technical idea, then what it means for Bend. See
`bend_float_facts.md` for the Bend side and `float_system.md` for the
design these notes feed.

## Flocq and CompCert (Boldo, Jourdan, Leroy, Melquiond)

Source: "Verified Compilation of Floating-Point Computations", JAR,
sections 1-6 read. <https://xavierleroy.org/publi/floating-point-compcert.pdf>

- **The standard defines each operation as "compute exactly, then
  round"**: `x ⊕ y = ∘(x + y)` for a rounding operator `∘` fixed by
  format and mode (section 2). Every proof about float programs starts
  from this.
- **CompCert up to 1.11 axiomatized floats**: an abstract type whose
  operations were declared but not defined, and whose algebraic
  identities were asserted as axioms. The paper names the costs:
  conformance to IEEE 754 could not be guaranteed, the axioms could
  not be machine-checked, and constant folding ran on the host's
  floats (OCaml on x87, with double rounding) (section 4). **This is
  exactly Bend's Base today.**
- **The fix (1.12) was a constructive model**, not better axioms:
  - `binary_float` is a sum type: `B754_zero s | B754_infinity s |
    B754_nan s payload | B754_finite s m e (bounded m e = true)`. The
    finite case carries a proof that `m` and `e` fit the format and that
    `m` is normalized unless `e` is minimal, which makes each value's
    representation unique (5.1).
  - `B2R` maps a float to the real `(-1)^s × m × 2^e` (5.1).
  - Each operation is written twice (5.2): as the specification
    `round(m, B2R(a) op B2R(b))`, which uses reals and cannot run, and
    as an executable function on integers. A theorem ties them, e.g.
    `Bmult_correct`: `B2R(Bmult(m, x, y)) = round(m, B2R x × B2R y)` when
    that is below the overflow threshold, and `overflow(m, sign)`
    otherwise, with the sign given separately.
  - NaN results are under-specified by the standard and differ by
    architecture, so each operation takes a function that picks the NaN
    sign and payload; CompCert instantiates it per target (5.2).
  - `binary_float_of_bits` and `bits_of_binary_float` convert to and
    from the machine word and are proven inverse, which checks that the
    three bit fields cover the word without overlap (5.3).
  - Round-to-odd gives a first rounding that makes a second rounding
    innocuous: rounding to nearest in `p` bits equals rounding to
    nearest after first rounding to odd in `p + k` bits, `k >= 2`
    (5.4, Theorem 3). Used for integer-to-float conversions.
- **The hardware stays an assumption**: the assembly semantics "assume
  that the hardware implements IEEE-754 correctly" (section 6), for the
  scalar instructions CompCert emits (SSE2 on x86, not x87).

For Bend: the path from axioms to a constructive model is the one
CompCert took, and the design pieces transfer directly: a sum type with
a proof field for finite values, a value function, specification plus
executable operation plus a tying law, a NaN-choice parameter (Bend's
JS lane has different NaN payloads), and encode/decode proven inverse.
Bend has no real numbers; see `float_system.md` for why exact binary
rationals are enough.

## VCFloat2 (Appel, Kellison, CPP 2024)

Source: sections 1-5 read. <https://www.cs.princeton.edu/~appel/papers/vcfloat2.pdf>

- **Workflow in three proofs**: a floating-point *functional model* of
  the program; a proof that the C code implements it (via VST); a proof
  that it is within ε of a *real-valued* functional model; and a proof
  that the real model solves the mathematical problem (Coquelicot).
  VCFloat2 automates the middle proof.
- **Error model, including underflow** (section 2): for `op` in
  `+ - × ÷`, `R(x op y) = (R(x) op R(y))(1 + δ) + ε`, with
  `|δ| <= 2^-24` and `|ε| <= 2^-150` for binary32. Exact special cases
  are recognized: Sterbenz subtraction (`1/2 <= x/y < 2` gives
  `x - y` exactly) and multiplication by powers of two.
- **Reification**: a tactic turns a Coq formula into a deep-embedded
  expression tree (`expr` with `Const`, `Var`, `Binop`, `Unop`, `Cast`,
  `Func`), proven correct per instance by reflection. Identity functions
  `Norm`, `Denorm`, `Sterbenz` are annotations: they change nothing
  semantically but tell the analysis which error case to use, and each
  creates a side condition to prove.
- **Bounds**: a boundsmap gives each variable an interval; after
  inserting δ and ε terms, a special-purpose simplifier and Coq's
  Interval package bound the difference.
- **Running example**: one leapfrog step of a harmonic oscillator,
  `x + h(v + (h/2)(3 - x))` with `h = 1/32`, `2 <= x <= 4`,
  `-2 <= v <= 2`, in binary32, proven within `1/4,000,000` of the real
  value.
- User-defined operators and non-IEEE formats are supported if the user
  supplies their error bounds; the standard library's `sin` etc. are
  handled that way (axiomatized with error bounds).

For Bend: the error model is the per-operation law a library needs. The
reify/analyze/prove-by-computation structure fits Bend better than
Coq, because Bend's only proof method is computation: an analyzer that
is a Bend function, a soundness law proven once, and per-program bounds
closed by `{==}`. The leapfrog example is a ready validation target with
a published bound.

## Numerical Fuzz (Kellison, Hsu, 2024-2025)

Source: sections 1-3 read. <https://arxiv.org/abs/2405.04612>

- **Two parts of error analysis, separated**: *sensitivity*, how much a
  function amplifies input error in exact arithmetic; and *rounding*,
  how much error each operation adds.
- **Sensitivity from Fuzz**: every type is a metric space; `τ ⊸ σ` is a
  non-expansive function; `!_s τ` scales the metric by `s`, so
  `!_2 num ⊸ num` is a 2-sensitive function (e.g. squaring). Linearity
  enforces the accounting: using a variable twice requires the scaled
  type.
- **Rounding as a graded monad**: `M_u τ` is a computation producing `τ`
  with at most `u` rounding error; `rnd` introduces error `u` (the unit
  roundoff); sequencing adds grades, scaled by the continuation's
  sensitivity. Example: `pow2' = λx. rnd(mul(x, x)) : !_2 num ⊸ M_u
  num` and `pow4 = pow2' ∘ pow2' : !_4 num ⊸ M_{3u} num` (2u from the
  first error amplified by 2, plus u).
- **Metric**: Olver's relative precision `RP(x, x̃) = |ln(x / x̃)|`. It
  is a true metric, unlike relative error, so errors compose by the
  triangle inequality; it is close to relative error when small.
- **Soundness**: each program has an ideal semantics (`rnd` is the
  identity) and a floating-point semantics (`rnd` rounds); for type
  `M_ε num`, the two results are within ε. The model is a
  "neighborhood monad" on metric spaces: pairs of an ideal and an
  approximate value within distance.

For Bend: "one program, two semantics" is what templates already give:
write the program over a `~` number dictionary and instantiate it at
exact and at float. Bend's quantities are only `&0/&1/&2`, so they
cannot count sensitivity the way `!_s` does. Sensitivity has to be a
proven Lipschitz lemma per operation, carried by the library's laws.
The neighborhood-monad model suggests a concrete library type: a value
that holds the float, the exact value, and a proof of their distance.
`ln` is not computable in exact binary arithmetic, so a Bend version
would use relative error with rational bounds or ulps instead of RP.

## Bean (Kellison, Zielinski, Bindel, Hsu, PLDI 2025)

Source: abstract and summary. <https://arxiv.org/abs/2501.14550>

- Backward error (how much the inputs would have to change for the
  float result to be exact) tracked by a graded coeffect system: each
  linear input variable carries a bound.
- Strict linearity is required for soundness: a linear variable may not
  be duplicated. Discrete (non-error-carrying) variables may be.

For Bend: the linear/discrete split is Bend's affine versus `+`
(`Data`) split. Error-carrying values could be `Type`-kinded so the
checker refuses to duplicate them. Bend is affine, not strictly linear
(dropping a value is allowed); whether Bean's soundness needs the "at
least once" half is open. Backward error is a later concern; forward
error comes first for game physics.

## Others worth reading

- Kellison, Appel, "Verified Numerical Methods for Ordinary Differential
  Equations" (NSV 2022) and the VerifiedLeapfrog repository: the full
  pipeline for a leapfrog integrator, from C to the real ODE solution.
  <https://github.com/VeriNum/VerifiedLeapfrog>
- Gappa (Melquiond): interval and rewriting engine for round-off bounds
  that emits proofs checkable by Coq; the automation idea behind
  VCFloat's analysis. <https://arxiv.org/pdf/0801.0523>
- Figueroa, "When is double rounding innocuous?" (1995): for `+ - × ÷`
  on float32 inputs, computing in float64 then rounding to float32 gives
  the correctly rounded float32 result. This is why Bend's JS lane
  (`Math.fround(a op b)`) agrees with C.
  <https://dl.acm.org/doi/10.1145/221332.221334>
- Type-Based Approaches to Rounding Error Analysis (survey, 2025).
  <https://arxiv.org/pdf/2501.14598>
- Lean 4: FloatSpec (Flocq's structure in Lean 4),
  <https://github.com/alok/FloatSpec>; lean-ieee754 (error bounds for
  binary32/64), <https://github.com/tunnellm/lean-ieee754>.
- Verifying Numerical Methods with Isabelle/HOL (2025).
  <https://arxiv.org/pdf/2511.20550>
- Not re-read here: FPTaylor, Daisy/Rosa, Herbie, SMT-LIB FloatingPoint
  and SymFPU, Harrison (HOL Light), Russinoff (ACL2).

## What recurs across all of them

1. A float denotes an exact value (a dyadic rational), and an operation
   is "exact, then round". Every system builds on this.
2. A per-operation error law (`(1 + δ)` and `+ ε`, or a graded
   step) is the unit of reasoning; programs compose it.
3. Hardware is linked by assumption (CompCert, VCFloat) or not at all
   (analyzers). No system proves the silicon.
4. Automation matters: VCFloat, Gappa and Numerical Fuzz exist because
   composing per-operation laws by hand does not scale past a few
   operations.
