# 10 stdlibs: proposal with dependencies, signatures, behaviors

Companion to `agent_notes.md` (§6 is the derivation; each lib below
names what it exploits and what it respects). Dependency DAG first,
then one block per lib: purpose, key signatures (Bend-flavored),
load-bearing laws, behavior characteristics.

```
Base
 └─ L1 bool ─ L2 order ─ L3 nat ─┬─ L4 list ─┬─ L5 containers
                                 │           └─ L10 numerics (needs L4 + L7)
                                 ├─ L6 text
                                 └─ L7 fixvec ─┬─ L8 canvas (needs L7 + flat Array)
                                               └─ L10 numerics
Base IO/Chan + L3 (Nat.min) + L4 (lengths) ─ L9 async (wants upstream Chan.select)
```

Build order: L1 → L2 → L3 → L4 → L5+L7 (parallel) → L6+L9
(L9 needs only L3+L4, not L8) → L8 → L10. Each lib gates on
`bend PROOF.bend`.

Conventions used below: `+x` = reusable (Data); fuel is always an
explicit first `Nat` param named `fuel`; every `law` listed is
checked — small laws adjacent to their defs (Base precedent),
large developments in the lib's `proofs/` file, never both
(one home per law). "Exploits / respects" ties back to
`agent_notes.md` §6 facts F1–F4.

---

## L1 `bool` — branch theory (seed: repo `order.bend`, grow it)

Purpose: make `Bool.pick` (Bend's `if`) reasoning load-bearing.
Blasé in other languages; foundational here because every
computed branch in every proof flows through pick-lemmas.

- `pick_merge(c, f, x, y)`: `{f(pick(c,x,y)) == pick(c,f(x),f(y))}` —
  the workhorse; every "commute a function through a branch" step.
  Subsumes `pick_succ` (at `f = x => 1n+x`); `pick` on literal
  `True{}/False{}` already delta-reduces and plain congruence is
  just `Equal.cong` — no wrappers (tautology rule).
- `and_false/and_true/and_comm/and_assoc`, `or_*`, `not_not`,
  `de_morgan_*` — full Boolean algebra, each consumed by L2+.
- Behavior: zero runtime content (all laws erase); the *test* is
  that L2–L4 proofs get shorter. If a lemma is never used above,
  cut it (tautology rule).
- Exploits F2 (erasure: infinite proof value, zero runtime cost).
  Respects F3 (pick takes the test as a matchable param).

## L2 `order` — `Cmp` as the canonical order type

Purpose: one sum type (`LT/EQ/GT`) owns all order dispatch;
the six `is_*` Bool predicates become derived views.

- `cmp_refl(a)`: `{cmp(a,a) == EQ{}}` (have for Nat; U32 via
  `Word.cmp` recursion + a `Bool.cmp`-refl lemma, no shortcut).
  String is NOT this shape: `String.cmp` returns
  `(String & String) & Cmp` (hands inputs back for linearity),
  so its refl law is `{String.cmp(a,a) == ((a,a), EQ{})}` with
  `+a` — same for `Char.cmp`.
- `cmp_swap(a, b, e)`: `{cmp(a,b) == LT{}} → {cmp(b,a) == GT{}}`
  (+ symmetric arms).
- `le_trans(a, b, c, ab, bc)`: Bool-`le` transitivity, proved via
  one `Cmp` case analysis — the template for "case on the sum,
  not on six Bools".
- View laws: `is_le(a,b)==True ↔ cmp∈{LT,EQ}` etc., so callers
  use cheap Bools at runtime and `Cmp` in proofs, with bridges.
- Behavior: `cmp` must reduce definitionally on constructors
  (else `{==}` ground goals fail — reject any impl that doesn't).
- Exploits F3 (sums dispatch). Respects F3 (no computed-test
  definitions enter core).

## L3 `nat` — arithmetic you can actually use in proofs

Purpose: the Nat theory Base forgot. Structural twins +
bridges for everything Base defined opaquely.

- `add_zero/add_succ/add_comm/add_assoc`, `mul_*`,
  `sub_spec`, `divmod_spec` (quotient/remainder relation).
- `SMax/SMin` + `max_bridge` (done in `order.bend`; move
  here): `{SMax(a,b) == Nat.max(a,b)}`, with `smax_ge_l/r`,
  `smin_le_l`, and transport laws `nat_max_ge_l/r` (each ~2
  lines + a `trans`, NOT free — the reappearing variable
  tightens the affinity budget). `smax_idem/comm`,
  `min_bridge` not yet written — do not cite.
  NOTE: if the upstream structural-`Nat.max` branch lands,
  twins die and direct laws (`Nat.max_ge_l/r`, already in the
  branch) replace all of this — the right outcome, absorb it.
- `le_add_mono`, `lt_add_succ` — the two monotonicity facts
  every bounds proof needs.
- Behavior: twin-before-theorem always; the law binders for
  2-variable lemmas are `for +a` (affine-checker rule, see
  `max_bridge` NOTE). Ground goals close by `{==}`.
- Exploits F1 (structural recursion = free induction), F2.
  Respects F3.

## L4 `list` — lengths, `Sorted`, `Perm`, sort-as-spec

Purpose: the meeting-fixer layer. Lists are the proof-friendly
sequence; everything indexed and fast lives elsewhere (L5/L10).

- Length algebra: `length_append`, `length_map/filter/take/drop`,
  `length_reverse`, `length_replicate/range` — every container
  above needs these.
- `Sorted(le, xs) : Type` predicate + `sorted_cons`/`sorted_tail`
  intro/elim; `Perm(xs, ys)` relation (or multiset-count
  characterization — whichever proves shorter).
- `sort_sorted(le, xs)`: `{Sorted(le, sort(le, xs))}` and
  `sort_perm(le, xs)`: `{Perm(xs, sort(le, xs))}` — against the
  structurally simplest correct sort first, bridged to Base's
  fuel-merge-sort via fuel-irrelevance (prove enough-fuel =
  length suffices — needs a runs-halve-per-pass induction, the
  real work item, not a footnote).
- `map_fusion`, `filter_comm`, `fold_append` — transducer
  correctness facts, consumed by L10.
- Behavior: `Sorted` is a hypothesis-carrier: downstream laws
  ("no two output plans overlap") take it as a premise. That
  premise-passing shape is THE point of the lib.
- Exploits F1/F2. Respects F3 (sort spec proved on simple
  definitional sort, bridged to fast one).

## L5 `containers` — queue, heap, sorted-map, persistent vector

Purpose: fill §3.3 of the notes. Four structures, one file each,
sharing L4's length/order theory. Rust `alloc` + Clojure
persistent-collections analogues, redesigned per §6.

- **Queue** (two-list banker): `push : Q -> A -> Q`,
  `pop : Q -> Q & Maybe<A>`, `len : Q -> Nat` with
  `len_push`, `len_pop`, `fifo_order` (pop sequence == push
  sequence — the statement Clojure can't check).
- **Heap** (priority queue): `push`, `pop_min : H -> H & Maybe<A>`,
  `heap_push_pop` (pop-all yields `Sorted`), `len_*`. For A* and
  timer/event scheduling.
- **SortedMap/IntMap** (Nat-keyed Patricia trie over `Word`;
  String-keyed sorted layer above): `set/get/del`,
  `get_after_set` (same-key / different-key arms — the latter
  needs decidable `Word` disequality, its own lemma),
  `keys_sorted` (iteration order law — the single largest proof
  in this plan; needs the prefix/branching-bit invariant as a
  type FIRST, budget accordingly). The calendar fixer's home.
- **PVec** (persistent bit-partitioned-trie vector): `get/set`
  with O(log₃₂ n) paths, `len_*`, `get_after_set`,
  `persistent_sharing` (old version unchanged after set — conj
  semantics as law). Same tree-shape family as linear `Array`,
  minus linearity plus sharing; document the Array-vs-PVec
  choice explicitly (hot linear buffers vs shared snapshots).
- Behavior: all four are `Data` (freely shared, never in-place);
  hot game state stays in linear `Array` (L10). Fuel appears
  only in rebalancing helpers with structural measures
  documented. Every op states its complexity in comments
  (per-backend where it differs).
- Exploits F1 (no-aliasing laws need no preambles), F2.
  Respects F1 (fuel on rebalancing), F4 (per-backend notes).

## L6 `text` — rope with size laws

Purpose: `String`-as-linked-chars does not survive editors,
HUDs, or dialogue. Chunked rope; the Clojure-`string` analogue
minus regex (host-side concern).

- `Rope = Leaf(String) / Cat(Rope, Rope, Nat-cached-len)` with
  `len` in O(1) via cache + `len_cat` law keeping the cache
  honest.
- `append/take/drop/split_at/concat` with `len_*` laws;
  `to_string` + `rope_roundtrip`.
- `lines/words` (fuel-bounded) with length-partition laws
  (`len(s) == len(take)+len(drop)`), consumed by L8 HUD code.
- Behavior: chunk size is a tuning constant with a documented
  per-backend note (JS string concat vs native blocks). Laws
  are all size/shape — content equality is `{==}`-definitional.
- Exploits F2. Respects F4 (backend string-cost note).

## L7 `fixvec` — provable geometry: fixed-point + V2/V3 + RNG

Purpose: the §6-F4 split made concrete — integer-coordinate
geometry where proofs live, float flesh tested elsewhere.

- `Fix` (U32-backed fixed-point, documented scale). WARNING:
  there is NO `to_nat`-style homomorphism lift — `U32` wraps
  mod 2³² where `Nat` doesn't (`a+b ≥ 2³²` is a counterexample;
  `sub` truncates vs wraps). Arithmetic laws must go through
  the `Word` layer, priced like Base priced `Word.add_comm`
  (adc + arm + go for commutativity alone); `U32.add_assoc`
  is a carry-propagation proof, not a lift. Budget weeks,
  not a day. Alternatively bound `Fix` to a non-wrapping range
  and prove the bound preserved — smaller claim, shippable.
- `V2/V3` as `Data` records over `Fix` (verified pattern in
  `/tmp/vec_probe.bend`): `add/sub/scale/dot/cross` with
  identities that reduce definitionally where possible
  (`add_comm/assoc/zero` — these DO prove, unlike F32).
- Layout bridge: `aos_soa_equiv` — `Array<V3>` and
  `(Array<Fix> & Array<Fix> & Array<Fix>)` decode to the same
  logical mesh. The `max_bridge` move applied to GPU migration.
- `Rng` (seeded, pure step): `step : Rng -> Rng & U32`,
  `range_shape` (bounds law, not statistical claim — honesty:
  distribution quality is tested, bounds are proven).
  Reproducibility is `{==}`-free from purity: cite it in prose,
  do NOT write it as a law (tautology rule).
- Behavior: coordinates are `Fix`, never `F32`, inside this
  lib — the one rule that keeps every law here checkable.
  GPU kernels consume the SoA side (uniform numeric arrays);
  CPU logic the AoS side.
- Exploits F1/F2/F3. Respects F4 (Fix-not-F32 rule; SoA-for-GPU
  default until ADT-on-GPU is verified).

## L8 `canvas` — 2D drawing on `Image`, both backends

Purpose: turn Base's `Pix`/`Qua` + `Window` + page-bundler into
a usable 2D API. First lib with a visible artifact.

- Constructors: `blank(w, h, color)`, `pixel`, `hline/vline`,
  `rect_fill`, `rect_stroke`, `circle` (fuel-bounded midpoint),
  `blit(dst, src, x, y)`, `text(row-of-glyphs via L6)`.
- `to_image : Canvas -> Image`, `from_array : Array<U32> ->
  Canvas` (the missing conversion — raymarcher output to
  screen), palette helpers (`rgb`, named colors as `U32`
  consts with documented packing).
- Laws (the differentiator): `blit_bounds` (writes stay in
  bounds, all inputs), `blank_extent`, `blit_transparent`
  (out-of-range blits are identity — total, no partial ops),
  `render_extent` (output tree depth matches canvas dims).
- Frame plumbing: fixed-timestep `step` helper
  (`tick(fuel, acc, dt, state)`), input fold over
  `List<Event>` (mouse/key → game input record), score/HUD
  text via L6. (App-shell conventions live here, not as a
  separate lib — they are three small functions, not a layer.)
- Behavior: construction is quadrant-parallel by default
  (matching the scheduler); per-pixel loops go through flat
  `Array<U32>` + `from_array`. Native presents via
  `Window.frame`; web via page bundle — one `view`, both
  targets. Depth-9 (512²) trees are the tested size; document
  bigger.
- Exploits F1 (fuel loops), scheduler-matched construction.
  Respects F4 (two-path write strategy with per-backend note).

## L9 `async` — promise/channel combinators (no new syntax)

Purpose: core.async's usable 90% over existing `Chan`/
`fork`/`join`/`sleep`. Deliberately NOT async/await syntax
(`fork`+`join`+`do` already is that).

- `Promise(A) = Chan(A)` alias + `all : List<IO(A)> ->
  IO(List<A>)`, `map2 : IO(A) -> IO(B) -> (A->B->C) ->
  IO(C)` (fork both, join both).
- `timeout(ms) : IO(Chan(Unit))` (sleeper task pattern);
  `race(a, b)` via merged channel (first message wins);
  `fan_in : List<Chan(A)> -> IO(Chan(A))` (forwarder task per
  input — no select needed).
- `pipe(fuel, f, in, out)` / `pipe_filter`: fuel-bounded
  channel map/filter with `forwards_min_len` law (exactly
  `min(fuel, n)` items, in order — the provable core).
- Behavior: every loop takes fuel; servers recharge per App
  tick. Closed channels surface as `None`, never hangs.
  Documented NON-goal: true `alt!`/selective backpressure —
  filed as the one upstream runtime ask (`Chan.try_recv` or
  `select`; verified absent from `effs/` by grep).
- Exploits IO/Chan as shipped. Respects F1 (fuel in every
  loop signature), honesty rule (no verified-protocol claims;
  nondeterministic interleavings are tested, sequential
  forwarding counts are proven).

## L10 `numerics` — numpy-subset with shape laws

Purpose: `map/reduce/scan` over `Array`, matmul, SoA vec/mat —
torch-like parallelism by annotation, numpy-like API, with the
one thing neither has: dimensions that reject misuse at build.

- `reduce/scan(fuel-or-structural, f, z, arr)` with
  `reduce_append` (split-and-join == whole — the fact that
  makes `!` distribution *correct*, not just fast),
  `scan_len`, `map_fusion` (from L4, re-homed to `Array`).
- `Mat(r, c : Nat, data : Array<Fix>)` with `matmul` requiring
  `c1 == r2`. NARROWED CLAIM (review): `Array<T>` carries no
  length/depth index, so the type as drawn rejects `c1 ≠ r2`
  but accepts data of the wrong size, and runtime-derived dims
  need an explicit `{c1 == r2}` argument (definitional equality
  fires only for statically-known Nats). Honest options: (a)
  depth-indexed `Array` wrapper (bigger change, real guarantee),
  (b) `matmul` takes `{c1 == r2}` + a `len(data) == r*c` premise
  (smaller, still build-checked). Pick one before promising
  "build rejection". `matvec`, `transpose` (`transpose_twice`),
  `identity` (`mul_ident`) stand either way.
- `stencil(fuel, radius, f, arr)` with bounds laws (from L3
  monotonicity) — the fluid-grid primitive this repo's
  `fluid.bend`/`headrace` reimplement by hand today.
- Behavior: GPU path is uniform-numeric SoA only; shapes are
  `Nat`s carried in types; `Fix` inside (L7), `F32` variants
  explicitly marked tested-not-proven per the F4 split.
  Complexities documented per backend (JS-slice warning from
  the notes).
- Exploits F2 (`reduce_append` makes parallelism provably
  safe), scheduler (`!` distribution). Respects F4 throughout.

---

## What was deliberately left out

- Regex/parsing (host-side; ship roundtrip `show/read` laws
  only where cheap). Full HTTP client (wrap `effs` TCP/UDP with
  `Result` + capacity laws — wanted but a separate proposal).
- Float identities anywhere (unprovable by construction).
- A game-engine "scene graph" (three small App-shell functions
  in L8 cover this repo's needs; engines are apps, not stdlib).
- Lazy/infinite structures of any kind (F1 forbids; fuel
  colists are the pattern, documented in L9).

## Acceptance bar (applies to all ten)

1. `bend PROOF.bend` green, introducing no new axioms beyond
   Base's host laws. 2. Every law consumed by a layer above
   (tautology rule). 3. Per-backend complexity notes where
   behavior differs. 4. Every looping/fuel-burning `def` states
   its termination story (structural arg or fuel budget) — note
   this binds the proof `def`s' recursion, NOT the `for`
   binders, which are plain universal quantification. 5. Each
   lib's README names its Rust analogue (usually
   `core`/`alloc`/named crate) and its Clojure analogue
   (usually `clojure.core`/`core.async`/persistent collection)
   AND the sentence explaining why the Bend version differs —
   §6 receipt, per lib.

---

## Measured facts (probe session 2026-09-19, vendor/bend @ 0b7e2b1)

Numbers only; see the probe file `design/probe_notwin.bend` for the
type-checked counter-example to the twin pattern.

- **Checker cost is not a constraint.** `import Base` + empty main:
  0.099s. `order.bend`: 0.080s. A generated file with **200**
  two-variable inductive lemmas (3214 lines): 0.080s. Flat. The gate
  does gate: a false law errors and exits 1.
- **Base ships ~9 propositional theorems** in 2900 lines. Of its 76
  `law` blocks, most are type signatures or host axioms (`F32.*`,
  `Word`, `Chan`, `File`); the equality-typed ones are `Equal.cong/
  sym/trans`, `Nat.cmp_refl`, `Nat.ge_refl`, `Nat.max_ge_l/r`,
  `Word.add_comm`, `U32.add_comm`.
- **`Nat.max`/`Nat.min` are structural + law-covered ONLY on the
  `stdlib/structural-nat-max` branch** (upstream `main` is still
  `Bool.pick`). CORRECTION (2026-09-19): an earlier version of
  this bullet mistook our staged branch edit for upstream. The
  twin layer in `order.bend` is NOT superseded; it is the working
  pattern until the branch lands. The branch now also carries
  `Nat.cmp_refl/ge_refl/max_ge_l/r` and `Bool/Cmp.split`, full
  Base green under the source-built checker.
- **Unary `Nat` ground goals overflow the checker** between a result
  of 4000n and 6000n. `Nat.add(2000n,2000n)` checks; `Nat.add(3000n,
  3000n)` fails with "the machine stack overflowed". Any Nat-carried
  shape or Nat-backed `Fix` must stay under ~4000 in ground goals.
- **`Array` has no shape guarantee.** `Array<-T: Type>` is
  `ALeaf | ANode` — a general binary tree, no balance invariant, no
  length/depth index. `Array.get` masks the index
  (`U32.and(i, U32.sub(n,1))`, base.bend:2301), so out-of-range reads
  silently wrap to an in-range element instead of failing. L10's
  shape-rejection claim needs option (a) or it is untrue.
- **Twins have a verified alternative, not a replacement.**
  An opaque `Bool.pick`-over-computed-test def can be proved
  about *without* a structural twin: private helper taking the
  test as a param, a law binder carrying `for h: {test == c}`,
  plus one `cmp_swap`-shaped order lemma. Checked in
  `design/probe_notwin.bend` (verified green 2026-09-19).
  Cost: 1 public law vs 9 twin-route names — but the route is
  `Data`-only (helper needs `+` args; does not extend to linear
  `Array`), and per-law bespoke where twins amortize. Standing
  rule: characterization-first for one-off opaque defs, twins
  only when a family of laws shares the unfolding. Either way,
  both routes die where the upstream structural branch lands.
- **`Chan` really has no select/try_recv** (base.bend:215-227; nothing
  in `bend2/effs/`). L9's single upstream ask is accurate.
- Minor: Base has **five** `Cmp.is_*` views (no `Cmp.is_ne`), not six;
  `Nat.is_ne` is built as `Bool.not(Cmp.is_eq(...))`.
