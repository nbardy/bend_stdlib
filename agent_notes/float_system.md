# Floats the Bend way

## Status (2026-09-24)

Built and gated, Base only, no language change:

- `src/float/bin.bend`: binary naturals (add, sub, mul, cmp, shifts with
  round and sticky bits).
- `src/float/format.bend`: exact values, formats as data, round to
  nearest even, IEEE `spec_add`, `spec_sub`, `spec_mul`.
- `src/float/num.bend`: the contract (`Impl`, `AddOk`, `MulOk`,
  `Correct`), which any implementation can meet.
- `src/float/sf32.bend`: binary32 decode/encode, software `add`, `sub`,
  `mul` defined as the spec, instances `soft()` and `hard()`, and the
  hardware assumption `HardOk`.
- `examples/sf32.bend`: `0.1 + 0.2` proven bit-exact in the checker;
  zero mismatches against hardware on 24x24 edge pairs and 3000 random
  pairs on JS and C (and 100000 pairs on C, run once).

Measured: the checker proves 100 software float additions in 0.8 s and
1000 in 7-13 s. A prototype checker patch that computes Base `Nat` and
`U32` operations natively cuts 1000 to 0.75 s
(`agent_notes/upstream_issue_checker_numbers.md`).

Not yet: division, square root, the universal law that `soft()` is
`Correct` (it holds at every tested point; the proof needs
`decode(encode(v)) == v` for rounded values), and the certificate and
reflection layers below.

A design built from what is new in Bend, not a port of Flocq, VCFloat or
Numerical Fuzz. The papers (`float_papers.md`) are used only for facts
about IEEE arithmetic and for what to avoid. Bend facts are in
`bend_float_facts.md`. Theory as of 2026-09-23; marked items are probed.

## What is new in Bend

The design rests on these. Each is either unusual among proof systems
or absent from all of them.

1. **Proof is computation.** No tactics, no solver: a law closes when
   both sides normalize to the same term. Automation in Bend means a
   function whose result the checker computes.
2. **Definitions have two meanings, bridged by name.** A Base
   definition has a body the checker unfolds and a native instruction
   the compiler emits (`U32.add` is `Word.adc` to the checker, one add
   at run time; `bend_float_facts.md`). The trusted seam is the name.
3. **Templates give one program many readings.** A `~` argument is
   substituted at compile time; one program can run at several number
   types, and a law over `~` arguments is proven once with them opaque.
4. **Reflection costs nothing.** A program instantiated at a syntax-tree
   builder evaluates, by `{==}`, to the same program at `F32`, for all
   inputs (probed: `agent_notes/probes/reflect.bend`).
5. **One pure program, four lanes.** The same code runs on C, CUDA,
   Metal and JS, deterministically: no scheduler-dependent results, no
   data races. Parallelism is a fork-join tree fixed by the program.
6. **Laws are the interface between human and AI.** Upstream's intended
   workflow: a human states laws, an AI writes the code and the proof,
   and the checker is the arbiter.
7. **Evidence flows through branches.** A decision can return a proof
   (`Nat.le_case : Or(LE(a, b), LE(b, a))`), so code that branches hands
   the fact it branched on to what follows.

## The design in one paragraph

A number type is a *reading*: a dictionary of operations with a checker
meaning and a runtime meaning. Programs are written once over a reading
and run at `F32`, exact dyadics, intervals, syntax trees, or a
fixed-point format. Laws about physics are stated on the exact reading,
where the checker computes. The distance between the float reading and
the exact reading is closed by *certificates*: data found by anyone
(an AI, an external tool, an unbounded search) and checked by a small
Bend function proven sound once. What floats do at the hardware level
enters through one named seam per operation, the same seam `U32` uses.
On top, Bend states laws no other system can: cross-lane determinism,
bounds tied to its parallel reduction shapes, and proofs about recorded
game runs by replaying them in the checker.

## Pillar 1: numbers with two meanings

- A float operation's checker meaning is "exact, then round" over the
  float's bits (the IEEE definition); its runtime meaning is the machine
  instruction. This is exactly the pattern Base already uses for `U32`,
  generalized. The upstream ask is small because the compiler already
  keeps native code for Base definitions with bodies.
- Until Base adopts it, the seam is a dictionary `~ieee` of equations
  `F32.add(x, y) == spec_add(x, y)`. Every law is written against it.
  When Base defines F32 structurally, the dictionary gets an instance
  and nothing downstream changes.
- **Formats are values.** binary32, bfloat16, Q16.16 fixed point and
  exact dyadics are instances of one reading interface. A game picks a
  format per subsystem (fixed point for synced simulation, `F32` for
  rendering) without rewriting code, and generic laws hold at every
  format.

What this takes from the papers: the "exact, then round" definition and
bit decode/encode (Flocq). What it drops: real numbers (dyadics suffice
and compute) and a separately axiomatized float type (the seam is the
same one Base already trusts for integers).

## Pillar 2: one program, many readings

A physics step is written once, `step(~R: Reading, x, v)`, and read as:

| reading | what it gives |
|---|---|
| `F32` | the program that runs |
| exact dyadic | the specification; physics laws are stated here and computed |
| syntax tree | input to certificate checkers (reflection, pillar 4) |
| interval | value ranges, for bounds |
| fixed point | an exactly deterministic variant with exact laws |
| a lane's reading | per-backend meaning (NaN payloads, subnormals, fast trig) |

Numerical Fuzz reaches "ideal and approximate semantics of one program"
with a new type system; in Bend it is a template instantiated twice.
VCFloat2 needs a tactic-language reifier to get a syntax tree; in Bend it
is a third instantiation, equal to the float program by `{==}`.

## Pillar 3: certificates, not tactics

Bend has no tactic language, and upstream will not add one. The design
turns that into the architecture:

- A **certificate** is ordinary data: an interval subdivision tree, a
  list of error terms, hints that a subtraction is exact.
- A **checker** is a total Bend function `check(program_tree, ranges,
  claim, certificate) -> Bool`, with one soundness law, proven once:
  `check(...) == True` implies the claim about the float reading.
- A **finder** produces certificates and is never trusted: an AI, an
  external analyzer, or Bend code that searches without a termination
  proof. Only the checker and its soundness law are trusted.
- A per-program law is then `check(tree, ranges, claim, cert) == True`,
  closed by `{==}`: the checker runs inside the proof checker.

This matches Bend's intended workflow exactly. The human writes the
physics law on the exact reading and a bound. The AI writes the float
code and finds a certificate. The checker decides. Where VCFloat2
annotates with `Norm`/`Sterbenz` (identity functions whose side
conditions must then be proven by tactics), a Bend certificate carries
the same hints as data and the checker verifies each one by computation.

Certificate kinds, in the order they are needed:

1. **Interval certificates.** A bound on a formula over input boxes,
   with the boxes subdivided where naive intervals are too loose (the
   dependency problem in `x ... (3 - x)`). The finder chooses the
   subdivision; the checker evaluates each box.
2. **Rounding-error certificates.** Per operation: normal, subnormal,
   or exact (Sterbenz, multiplication by a power of two). The checker
   confirms each claim from the operands' intervals and uses the right
   error term.
3. **Invariant certificates for loops.** For a multi-step simulation, an
   invariant region the step maps into itself, checked by the interval
   checker. This gives drift bounds over any number of steps without
   Kellison and Appel's analysis.

## Pillar 4: laws only Bend can state

These use features other systems do not have.

1. **Cross-lane determinism.** Given lane readings (C, CUDA, Metal, JS)
   that differ only where the backends differ (NaN payloads, fast trig,
   possibly subnormals on Metal), a checker `portable(tree)` computes
   whether a program avoids every point of difference; its soundness law
   says the program then gives bit-identical results on every lane. For
   rollback netcode across mixed clients this is the property that
   matters, and it is decided by computation. Today it is only tested
   (`apps/fluid.bend` matched on JS and C).
2. **Parallel reduction bounds.** `Tree.reduce` reassociates a sum by
   the tree's shape, fixed by the program, so results never depend on
   scheduling. For floats: a law that the parallel sum over a balanced
   tree of depth `d` is within about `d · u · Σ|xᵢ|` of the exact sum,
   against `n · u · Σ|xᵢ|` for a sequential fold. Parallelism here makes
   floats both reproducible and more accurate, and the law says so.
3. **Proofs about recorded runs.** With floats computing in the checker
   (pillar 1's model), a recorded input log can be replayed inside a law:
   "on this replay, energy stays within B and no body leaves the arena"
   closes by `{==}`. Games already record replays for rollback; a failing
   replay becomes a regression law. This needs only ground computation,
   no universal proof, so it is useful before any error analysis
   exists. Its cost is checker speed on software floats.
4. **Evidence-carrying comparisons.** `F32.cmp_ev(x, y)` returns a proof
   about the exact values (for example that `x` is below `y` by more
   than the rounding error), so collision code that branches on a float
   comparison hands its proof to the response code. This is the
   `le_case` pattern extended to floats.

## Building blocks

Needed by all pillars, smallest first:

1. **Bits**: decode/encode between `F32` and a sum type
   (`Zero | Inf | NaN | Fin{..., ok}`), proven inverse. Decoding
   literals already computes (probed: `agent_notes/probes/decode.bend`).
2. **Binary numbers and dyadics**: exact arithmetic on bit lists with
   ordered-ring laws. Must be binary: unary `Nat` overflows the checker.
3. **Rounding**: round-to-nearest-even for a format given as a value,
   and the half-ulp law.
4. **Readings**: the reading dictionary, and instances for `F32`,
   dyadic, interval, syntax, fixed point, and per lane.

## What we deliberately do not take

| from | what | why not in Bend |
|---|---|---|
| Flocq / Coquelicot | real numbers as the model | dyadics are exact for the operations used, and they compute |
| VCFloat2 | a tactic reifier | a template instance is the syntax tree, for free |
| VCFloat2 / Gappa | trusted automation inside the prover | untrusted finders, checked certificates |
| Numerical Fuzz / Bean | new type-system grades | Bend's quantities are fixed at three; computation replaces grades |
| CompCert | a separately axiomatized float type | reuse Base's existing two-meaning seam |

## Experiments that could sink the design

1. **Checker speed of software floats.** Ground-replay a few hundred
   steps of a 2-body float step in the checker. If it takes minutes,
   pillar 4.3 is out and pillar 3 needs coarser certificates.
2. **A certificate checker end to end.** An interval checker for one
   polynomial with a subdivision certificate, its soundness law, and a
   per-program law closed by `{==}`. This measures proof size without
   tactics, the biggest unknown.
3. **The portability checker.** Lane readings that differ in NaN
   payload and trig, and a `portable` function whose soundness law
   holds. Cheap, and useful on its own for netcode.
4. **Tree-reduction bound.** The depth law, first over exact dyadics
   with a rounding function, then against `~ieee`.

## Open questions

- Can a checker's soundness law be proven at a reasonable size without
  tactics? This decides pillar 3.
- Can a finder that is `@unsafe`, or unproven to terminate, be used
  while keeping the verdict clean, if only its output reaches a law?
- Metal subnormal behavior: needs a device run before lane readings can
  be written honestly.
- How much of the model upstream would take into Base, given its
  32k-token cap.
