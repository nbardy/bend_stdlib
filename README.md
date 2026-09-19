# bend-stdlib

A proof-carrying standard library for Bend. Every structure
ships its invariant laws; `bend PROOF.bend`-style gates check
them at build time and erase them at runtime.

Read `PHILOSOPHY.md` first — it states the four language facts
(F1–F4) that every module must exploit/respect, and the house
rules (dual-use definitions, fuel in signatures, no tautology
laws, never fork Base).

## Status

Building. Modules (each checks standalone via `bend src/<mod>.bend`):

- `src/order.bend` — Bool/Cmp/Nat starter theory + structural
  `SMax`/`SMin` twins with the `max_bridge` transport.
  Legacy Bool-propositional style; new work uses `kernel.bend`.
- `src/kernel.bend` — LE-relation kernel (277 lines, 16 laws):
  computed `LE` family, `le_trans/add_r/eq_r`, goal-A
  interval/NoOv proofs, goal-B `blit_bounds`, goal-C
  `SameLen`/`dot`/`Conform`/`matvec`.
- `src/absurd.bend` — `bool_absurd` + Cmp-discrimination trio
  + `nat_absurd_zero_succ`. Prerequisite for impossible arms.
- `src/perfect.bend` — `Perfect` Array invariant, `snd_size`,
  `dbl`, one-level `size_node_snd/shl`, `perfect_new`.
  Records the linear-induction composition barrier.
- `src/sorted.bend` — ported flagship certified insertion sort
  (sortedness + length preservation, 221 lines). Concrete Nat
  comparator (no template problem); LE-duplication with kernel
  recorded for future dedup.
- Roadmap (deps, signatures, behaviors): see
  `design/stdlibs.md` in the games repo until it migrates here.

## Gates

- Each module checks standalone: `bend src/<mod>.bend`.
- Full tree must check together before anything is taken as
  done. No new axioms beyond Base's host laws.

## Upstream branches

Proposed Base changes live as branches, prepared here,
submitted from a Bend checkout: structural `Nat.max`/`Nat.min`
(behavior-identical, proof-transparent), Bool/order starter
laws, `Chan` select (needs runtime support — issue first).
External twins + bridges remain the working pattern until an
upstream change ships in a release (installed toolchain ≠
source checkout — record required Bend versions per module).

## Validation log

- 2026-09-19: `vendor/bend:stdlib/structural-nat-max` (structural
  `Nat.min`/`Nat.max`) verified end-to-end with the source-built
  checker (`bun bend2/main.ts`): edited Base prints structurally;
  `max_ge_l`/`max_ge_r` prove *directly over `Nat.max`* (the
  previously-unprovable shape); the old pick-based `max_bridge`
  breaks exactly as predicted (its `pick_succ` machinery is
  obsolete — both sides now unfold identically, so each arm
  closes with at most one `cong`; the goal is still stuck on
  variables since the defs remain distinct). If the branch
  lands, external `SMax`/`SMin`/`pick_succ` die — the right
  outcome. Full gate remains Bend's own CI. Seed here
  (`src/order.bend`) stays pick-compatible until the upstream
  change ships in a release (installed toolchain: 2.0.5).
- Branch now also carries `Bool.split`/`Cmp.split` (decision
  lemmas: the root fix for all 46 staging helpers) — full Base
  green under the source-built checker.
- `src/kernel.bend`: landed LE-relation kernel (277 lines,
  16 laws, green) — computed `LE`/`SameLen` relations replace
  Bool/Cmp propositional style per density audit; see
  PHILOSOPHY F5 for the expressiveness limits that forced it
  (no runtime closures, no GADTs, functions never `Data`).
