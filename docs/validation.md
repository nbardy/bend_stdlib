# Validation log

Dated receipts for claims made elsewhere. Each entry states what
was run, against which toolchain, and what it showed. The full
gate remains Bend's own CI; nothing here substitutes for it.

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
  outcome. Seed (`src/order.bend`) stays pick-compatible until
  the upstream change ships in a release (installed toolchain:
  2.0.5).
- Branch now also carries `Bool.split`/`Cmp.split` (decision
  lemmas: the root fix for all 46 staging helpers) — full Base
  green under the source-built checker.
- `src/kernel.bend`: landed LE-relation kernel (277 lines,
  15 laws, green) — computed `LE`/`SameLen` relations replace
  Bool/Cmp propositional style per density audit; see
  PHILOSOPHY F5 for the expressiveness limits that forced it
  (no runtime closures, no GADTs, functions never `Data`).
- Submitted as draft upstream PR (bendlang/bend#860): structural
  min/max + order laws + split lemmas, with the honest
  O(min)-allocation cost note and proof-migration path.
- Probe session 2026-09-19 (4 Opus reviews): density audit
  (minimal kernel landed), composability trace (gap lemma
  lists feed the roadmap), adversarial review (absorbed:
  consumer-driven scoping, Fix demotion, fuel correction),
  Base opacity inventory (43 axioms, 46 staging helpers,
  167/373 defs downstream). Review artifacts in `/tmp`
  (`opus_review.md`, `probe_{density,compose,adversary,base}.md`,
  `kprobe/`, `bp/`) — throwaway by convention; findings that
  mattered are recorded in-repo, the rest left to expire.
