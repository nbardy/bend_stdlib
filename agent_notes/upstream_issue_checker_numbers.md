# Draft PR: the checker computes Base Nat operations on closed numbers natively

For HigherOrderCO/Bend. Not opened. The change is
`agent_notes/patches/checker_native_numbers.diff`: 31 added lines in
`bend2/bend.ts`, no existing line changed, against `main` at `ff7a40c`.

---

**Title:** Base Nat operations on closed numbers are computed natively in the checker

**The bug.** The checker evaluates `Nat.add` and its siblings by
unfolding `Succ` once per unit, so arithmetic the runtime does instantly
overflows the checker's stack:

```python
import Base
law big:
  {Nat.add(100000n, 100000n) == 200000n : Nat}
def big():
  {==}
```

On 2.0.25 this fails with "the machine stack overflowed" (it checks at
`1000n`); so do `Nat.mul(2n, 100000n)` and `Nat.max(70000n, 90000n)`.

**The change.** When `Nat.add`, `sub`, `mul`, `min`, `max` or `cmp` (and
so the `is_*` tests) from Base has both arguments, and both are closed
(no free variable), the checker evaluates them; if both are numbers, it
computes the result with machine integers, as the compiler already does
for the same definitions, and returns a literal or `LT`/`EQ`/`GT`.
Otherwise it unfolds as before; results past 2^53 unfold as before.
Two added lines hook this into `term_wnf` where a definition unfolds;
the rest is the table and two small helpers.

The closedness test is the one subtle part. A version without it hung on
`tests/proof/shift_left_mask.bend`: evaluating a symbolic argument early
cached its stuck, expanded form, and later comparisons of symbolic
terms blew up. A symbolic argument is now never evaluated by this path.

**Evidence** (Apple M-series, `bun bend2/main.ts`):

| | 2.0.25 | patched |
|---|---|---|
| `Nat.add(100000n, 100000n) == 200000n`, `Nat.mul(2n, 100000n) == ...`, nested sums | stack overflow | check |
| false laws for each operation (`Nat.add(100000n, 1n) == 100000n`, `Nat.sub(5n, 9n) == 1n`, `Nat.max(70000n, 90000n) == 70000n`, ...) | overflow or error | error, with expected and observed values |
| all 1427 files in `tests/*/*.bend`, `--check-only` | baseline | identical output; total time within noise (897 s vs 914 s, 6 in parallel) |
| 1000 binary32 additions done in software over `Word(32n)`, proven bit-equal to hardware | 6.5 s | 3.0 s |

A smaller variant that fires only when both arguments are already
literals (13 lines) also fixes the overflow examples, but makes the last
row 2.5x slower than unpatched, so it is not proposed.

**Use case.** bend_stdlib implements IEEE binary32 in software so the
checker can compute float results, and proves them bit-exact against
hardware (`src/float/`, `examples/sf32.bend`):
<https://github.com/nbardy/bend_stdlib/tree/stdlib-rewrite>. Nothing is
added to Base.
