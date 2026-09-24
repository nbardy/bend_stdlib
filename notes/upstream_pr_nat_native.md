# Draft: second upstream PR (not opened)

Branch: <https://github.com/nbardy/bend/tree/nat-native> (commit
`0a8969be`, on upstream `ac0ddb7b`), independent of #1016. Open it only
after the user has read every line; then change the last line of the
body to "AI-assisted; I read and approved every line."

---

**Title:** Base Nat operations on closed numbers compute natively in the checker

`Nat.add`, `sub`, `mul`, `min`, `max` and `cmp` unfold one `Succ` per
unit, so a law about closed numbers costs time linear in their size.
Proving 1000 software-float additions over `Word` bits
([example](https://github.com/nbardy/bend_stdlib/tree/main/src/float))
takes 44 s.

When both arguments of one of these Base defs are closed, `term_wnf`
now computes the result as the compiler does: a `Nat` literal, or
`LT`/`EQ`/`GT`. A symbolic argument still unfolds; forcing it would cache
its unfolded form and hang inductions such as
`tests/proof/shift_left_mask.bend`.

- 1000 SF32 additions: 44.2 s -> 11.8 s (median of 3, same machine)
- `{Nat.cmp(Nat.mul(3000n, 3000n), ...) == GT{}}`: over 5 min -> 3 s
- every file in `tests/*/*.bend` (1441) gives identical `--check-only`
  output; suite total 3341 s -> 3360 s (6 in parallel, within noise)
- no new `tsc --strict` errors
- new test: `tests/check/nat_closed_ops.bend`

46 lines in `bend2/bend.ts`, all added.

AI-assisted.
