# Draft PR: comparing a long constructor chain no longer overflows the checker

For HigherOrderCO/Bend. Not opened. The change is
`agent_notes/patches/checker_compare_overflow.diff` against `main` at
`ff7a40c`: `bend2/bend.ts` +2 -1, `bend2/main.ts` +4 -1.

---

**Title:** A constructor's last field is compared by a tail call, so long chains check

**The bug.** `term_compare` compares a constructor's fields inside
`a.x.every(...)`, so comparing two `Succ` chains recurses once per unit:

```python
import Base
law big:
  {Nat.add(100000n, 100000n) == 200000n : Nat}
def big():
  {==}
```

On 2.0.25 this fails with "the machine stack overflowed" (it checks at
`1000n`). The arithmetic is fine; the comparison of the 200000-deep result
with `200000n` is what recurses. Long lists, strings and words compare
the same way.

**The change.**

1. `term_compare`'s `Ctr` case compares every field but the last inside
   `every`, and returns the comparison of the last field directly. In
   strict code JavaScriptCore (bun) makes that a proper tail call, so a
   chain through last fields (`Succ`, `Con`'s tail, `WCon`'s tail)
   compares in constant stack.
2. `book_err` catches an overflow raised while an error is being shown
   (a false law about a huge term) and reports it as the overflow it
   already reports, instead of crashing.

**Evidence** (Apple M-series, `bun bend2/main.ts`):

| | 2.0.25 | patched |
|---|---|---|
| `Nat.add(100000n, 100000n) == 200000n` | stack overflow | checks, 0.7 s |
| `Nat.mul(2n, 100000n) == 200000n`, `Nat.add(Nat.add(100000n, 1n), 5n) == 100006n` | stack overflow | check |
| `Nat.add(1000000n, 1000000n) == 2000000n` | stack overflow | checks, 1.1 s |
| `Nat.add(100n, 1n) == 100n` | error, expected and observed shown | same |
| `Nat.add(100000n, 1n) == 100000n` | "machine stack overflowed" | same (rejected) |
| all 1427 files in `tests/*/*.bend`, `--check-only` | baseline | identical output; total time 656 s vs 641 s |

**Limit.** This depends on proper tail calls, which JavaScriptCore has
and V8 (node) does not. Under node nothing changes, better or worse. An
explicit loop in `term_compare` would not depend on the engine, at the
cost of restructuring the function.

**Not in this PR.** Checking stays unary: `100000n + 100000n` takes
100000 steps. A separate patch
(`agent_notes/patches/checker_nat_native.diff`, 31 added lines) computes
Base `Nat` operations on closed numbers natively and roughly halves proof
time for bend_stdlib's software floats (1000 binary32 additions proven
bit-equal to hardware: about 6 s to 3 s,
<https://github.com/nbardy/bend_stdlib/tree/stdlib-rewrite>). It is
offered only if the speed is wanted.
