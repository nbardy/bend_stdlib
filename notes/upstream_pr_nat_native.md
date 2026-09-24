# Draft: second upstream PR (not opened)

Branch: <https://github.com/nbardy/bend/tree/nat-native> (one commit,
`35a0c7b0`, on upstream `b7ebee92`), independent of #1016. Open it only
after the user has read every line; then change the last line of the
body to "AI-assisted; I read and approved every line."

Variants measured (1000 SF32 additions, median of 3, load avg ~200):

| variant | bend.ts lines | time |
|---|---|---|
| unpatched | 0 | 19.1 s |
| closedness guard, 6 ops (first draft) | 46 | 7.9 s |
| no guard, add/sub/max/cmp (this PR) | 23 | 6.4 s |
| no guard, add/sub/cmp | 23 | 8.3 s |
| literals only, no Succ walk | 20 | 32.9 s |

The closedness guard was dropped: all 1441 tests gave identical output
without it, and `tests/proof/shift_left_mask.bend` (the file it was for)
checks in 0.7 s. Instrumented, the benchmark calls only add (6006),
sub (5997), cmp (9036, including is_eq/is_ge/is_le/is_gt) and max
(2026); mul and min, never.

---

**Title:** Base Nat.add, sub, max and cmp compute natively in the checker

These unfold one `Succ` per unit, so a law about closed numbers costs
time linear in their size. Proving 1000 software-float additions over
`Word` bits ([example](https://github.com/nbardy/bend_stdlib/tree/main/src/float))
takes 19 s.

When both arguments of one of these Base defs normalize to a number
(`Succ`s over a `Nat` literal, or `Zero`), `term_wnf` now computes the
result as the compiler does: a `Nat` literal, or `LT`/`EQ`/`GT`.
Otherwise the def unfolds as before.

- 1000 SF32 additions: 19.1 s -> 6.4 s (median of 3, same machine)
- every file in `tests/*/*.bend` (1445) gives identical `--check-only`
  output; suite total 920.6 s -> 921.7 s (6 in parallel)
- no new `tsc --strict` errors
- new test: `tests/check/nat_closed_ops.bend`, each op on small numbers,
  `sub` stopping at 0, all three `cmp` results, a successor over a
  computed number, and a symbolic argument; under a second either way

23 lines in `bend2/bend.ts`, all added.

AI-assisted.
