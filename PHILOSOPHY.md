# Philosophy: why this stdlib is its own

Bend is not "Haskell with proofs" or "Clojure with types". Four
facts combined force a different standard library, and every
module here must be able to say which facts it exploits and
which limits it respects. If it cannot say both, it does not
belong here — it is a normal lib with Bend syntax.

## The four facts

**F1 — Affine and total.** Every value is used at most once;
every function terminates. Therefore: no lazy infinites
(streams take `Nat` fuel); no aliasing bugs to defend against
(laws need no "assuming no aliasing" preambles); every loop
budgets in its signature; every potentially-unbounded API
(channels, schedulers, marchers) is a fuel-bounded state
machine. Servers recharge fuel per tick — frame budgets were
already fuel-shaped.

**F2 — Proofs are build-gate terms, erased at runtime.**
Therefore: laws ship *with* structures (a structure without
its invariant laws is unfinished); each law must be consumed
by a layer above, or it is tautology weight and gets cut;
expensive runtime checks (bounds, capacities, sortedness) move
to build time — the library gets *faster* the more it proves.

**F3 — Match only on params; `Bool.pick` is opaque.** The
single non-negotiable design rule: **recursion shape must
equal proof case-split shape.** Computed-test definitions are
banned from core. Inherited opaque definitions are repaired
with structural twins + bridge lemmas, never by forking Base.
`Cmp` (a sum type) owns order dispatch; the six `is_*` Bool
predicates are derived views with correspondence bridges.

**F4 — One codebase, three backends; floats are axioms.**
`Array` code is O(log n) native, O(n)-copy on JS — performance
reasoning is per-backend and documented. GPU kernels are
uniform-numeric SoA until ADT-on-GPU is verified by a native
`--gpu` run. `F32` operators are uninterpreted host laws:
provable geometry is integer/fixed-point, float flesh stays
tested — every numeric module splits along this line
explicitly. Script-path float output is symbolic; prototype
vec math in `U32`/`Nat`.

## Consequences (the house rules)

1. One definition, dual use: it must reduce definitionally on
   constructors (so `{==}` closes ground goals) AND recurse
   structurally (so induction works). Otherwise rejected.
2. Computed tests get pushed into matchable params via helpers
   (`pick_succ(c, x, y)` takes `c` as a param; callers pass
   `Nat.is_lt(ap, bp)`).
3. Pure-`Data` crunchers take `+` args; linear `Type` things
   stay affine. Two-variable induction lemmas use `for +a`
   law binders (proof `def`s keep bare binders — `+` there is
   a syntax error — but inherit reusability from the law).
4. Loops take fuel in the API from day one. Nothing infinite.
5. No tautology laws: each law earns its place by being used
   in the next layer up.
6. Never fork Base. Upstream proposals are additive by
   default; where a replacement is genuinely better
   (structural `Nat.max`: same values, provable, at stated
   O(min)-allocation cost), propose the replacement HONESTLY
   — same-values-plus-cost-note, differential test, and the
   downstream proof-migration path documented — never smuggled
   inside "behavior-identical".
7. Backend honesty: CPU claims from runs, GPU claims only from
   native `--gpu` runs, never from the script path.

## Relation to Rust and Clojure

Rust's `core`/`alloc`/`std` split is worth stealing (a core
that needs no IO and checks anywhere); its borrow checker,
`unsafe`, and trait coherence are not (affinity is simpler and
total; `@unsafe` exits proofs rather than suspending safety;
dispatch is type-directed). Clojure's transducers fit Bend
*better* than Clojure (single-use composition is native);
its laziness, atoms, and multimethods do not port (fuel
colists; linear `Array` + `Chan`; type-directed dispatch).
`core.async` ports except `alt!`, which needs a runtime
primitive — our one filed upstream runtime ask.

## F5 — expressiveness limits (verified by probe, 2026-09-19)

These are not style choices; they are checker facts that change
signatures. Every one was confirmed by running, not by reading.

- **No runtime closures.** `~` binders are compile-time
  templates over closed top-level names: a law mentioning
  `List.map`/`filter`/`sort` with a *quantified* function
  fails at parse ("expected: a defined name"), even reflexively.
  Consequence: sort/fusion/reduce laws are stated PER concrete
  comparator/kernel in the instantiating book, or over a
  defunctionalized `Data` function-code. "Transducers compose"
  does not port; a fixed menu of monomorphic kernels does.
- **Functions are never `Data`.** `+f` is rejected, so no
  user-written higher-order recursion and no reusable
  callbacks. Type-level predicates may use function binders
  freely (types check dead) — specs can be higher-order even
  when programs cannot.
- **No GADTs, no funext.** Native datatypes are parametric, not
  constructor-indexed (negative tests in-repo); equations
  between functions are dead on arrival. Index-flavored designs
  (`Vec(n)`, `Mat` with structural shape rejection) must be
  re-expressed as `Data` container + computed relation
  (the `LE`/`SameLen` pattern in `src/kernel.bend`).
- **F32 is opaque on literals.** `F32.add(1.0,1.0) == 2.0`
  does not reduce; U32 ground goals DO (bit-wise `Word.adc`).
  The float boundary is total, not gradual.
- **`Array` needs `Perfect`.** Indices wrap silently
  (`U32.and(i, n-1)`), and ragged trees typecheck while
  `size`/`get` lie about them. Every `Array` law takes a
  `Perfect(d, a)` premise first; sizes are 2^d only.
- **Unary `Nat` overflows the checker** (~4000–6000 in ground
  goals). Coordinates fine; pixel counts are not Nat-carried.
- **The missing decision lemmas** (`Bool.split`, `Cmp.split`)
  now live on the upstream branch — 46 staging helpers, one
  root cause.

## Layout

- `src/` — library modules (`order.bend` seeds L1–L3).
- `proofs/` — per-module proof files where a module's laws
  outgrow living next to their defs (Base precedent keeps
  small laws adjacent; large developments split).
- Gate: every module checks standalone AND the whole tree
  checks together. No new axioms beyond Base's host laws.
