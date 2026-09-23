# Draft issue: the checker computes Base numeric primitives natively

Draft for bendlang/bend, not posted. Evidence and patch are in this
repository; the patch is a prototype against `main` at `ff7a40c`
(`agent_notes/patches/checker_native_numbers.diff`), offered as a
demonstration, not a pull request.

---

**Title:** The checker overflows on `Nat` arithmetic past a few
thousand; compute Base `Nat` and `U32` operations on known values natively

**Problem.** The checker evaluates `Nat.add` and friends by unfolding
`Succ` one step at a time, and `U32` operations bit by bit. The runtime
already computes the same Base definitions natively (`nat_add`,
`u32_add`, ...). So arithmetic that runs instantly fails in a proof:

```python
import Base
law big:
  {Nat.add(100000n, 100000n) == Nat.mul(2n, 100000n) : Nat}
def big():
  {==}
```

On 2.0.25 this stops with "the machine stack overflowed". It passes at
`1000n`.

**Proposal.** When a Base definition from a fixed table is applied to all
its arguments, and every argument reduces to a known value (a `Nat`
literal or `Succ` chain on one, or a `U32` whose 32 bits are all known),
compute the result with machine integers and return a literal (or `True`,
`False`, `LT`, `EQ`, `GT`). Otherwise unfold as today. This is the rule
the compiler already follows for Base definitions with bodies, applied
to the checker; the trust is the same: each native result must equal
the Base body. Lean 4's kernel does this for `Nat` with GMP.

**Table.** `Nat.add sub mul double min max cmp is_eq is_ne is_lt is_le
is_gt is_ge`; `U32.add sub mul inc and or xor not shl shr shln shrn div
mod min max from_nat to_nat cmp is_eq is_ne is_lt is_le is_gt is_ge
is_zero`. Each entry follows its Base body: `Nat.sub` truncates at zero,
`U32.div` by zero is 0, `U32.mod` by zero is the dividend, shifts past 31
give 0, `U32.from_nat` wraps modulo 2^32, `U32.min`/`max` choose by
`is_lt`. Results past 2^53 fall back to unfolding.

**Prototype.** About 150 lines in `bend2/bend.ts`: a table, two value
readers, and a check in `term_wnf`'s `Ref` case before a definition
unfolds.

**Evidence** (Apple M-series, `bun bend2/main.ts`):

| check | 2.0.25 | patched |
|---|---|---|
| `Nat.add(100000n, 100000n) == Nat.mul(2n, 100000n)` | stack overflow | checks, 0.06 s |
| `Nat.add(4000000000n, 4000000000n) == ...` | stack overflow | checks |
| false laws (`Nat.add(100000n, 1n) == 100000n`, `Nat.sub(5n, 9n) == 1n`) | overflow / error | rejected, with the expected and observed values |
| 1000 IEEE binary32 additions in software (bstdlib `SF32`), result bits proven equal to hardware | 6.9 s | 0.75 s |
| every file under `tests/*/*.bend` (1427), `--check-only` output | baseline | identical to baseline (RESULT PENDING) |

**Why it matters beyond speed.** Proofs that compute with numbers (bit
decoding, fixed-point game state, software floats checked against
hardware, replays of recorded runs) currently hit the overflow or take
seconds per thousand operations. With native evaluation, the checker
proves results about a thousand float operations in under a second,
and Base stays small: nothing new is added to it.
