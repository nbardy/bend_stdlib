# Filed: bendlang/bend#1016 (PR)

Opened 2026-09-24 as <https://github.com/bendlang/bend/pull/1016>, after
the user read and approved every line; the PR says it is AI-assisted.
Rebased onto 2.0.26 (`6a77e124`): all 1427 files in `tests/*/*.bend` give
identical `--check-only` output. Branch: `nbardy/bend:long-chain-compare`.
The text below is the earlier bug-issue draft, kept for reference.

---

**Title:** Comparing a long Succ chain overflows the checker's stack

### What you did

`bend big.bend --check-only`

### What happened

```text
Error: the machine stack overflowed (a deep recursion, or a literal too large to expand)
```

It checks at `1000n`. `Nat.mul(2n, 100000n) == 200000n`, long lists and
long strings take the same path.

### The file

```python
import Base

law big:
  {Nat.add(100000n, 100000n) == 200000n : Nat}

def big():
  {==}
```

### bend --version

bend 2.0.25

### uname -sm

Darwin arm64

### clang --version (the first line)

Apple clang version 17.0.0 (clang-1700.0.13.5)

### Cause

The addition is fine. `term_compare`'s `Ctr` case compares fields inside
`a.x.every(...)`, so comparing the result with `200000n` recurses once
per `Succ`.

### A fix, if useful

Walking the last field (`Succ`'s predecessor, a list's tail, a word's
bits) in a loop inside the `Ctr` case removes the depth; the other fields
recurse as now. Showing a false law about a huge term can overflow too,
so `book_err` also catches an overflow raised while showing an error.
About 25 lines in `bend2/bend.ts` (2 removed), 5 in `bend2/main.ts`, and a test
(`tests/check/nat_long_chain.bend`); the diff is at
<https://github.com/nbardy/bend_stdlib/blob/stdlib-rewrite/notes/patches/checker_compare_overflow.diff>.
With it: this law checks in 0.3 s and the same law at `1000000n` in
0.7 s; false laws are rejected with the same messages as today; every
file in `tests/*/*.bend` gives identical `--check-only` output. The
sketch was written by an AI agent, so it is here for you to take or
rewrite rather than as a PR.
