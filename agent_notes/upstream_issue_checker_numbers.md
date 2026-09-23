# Draft PR: the checker computes Base numeric primitives natively

For HigherOrderCO/Bend. Not opened. The change is
`agent_notes/patches/checker_native_numbers.diff` (about 140 lines, one
file, `bend2/bend.ts`), against `main` at `ff7a40c`.

---

**Title:** A Base Nat or U32 operation on closed, known numbers is computed natively in the checker

**What breaks today.** The checker evaluates `Nat.add` and its siblings by
unfolding `Succ` one step at a time, and `U32` operations bit by bit. The
compiler already emits native code for the same Base definitions
(`nat_add`, `u32_add`, ...). So arithmetic that runs instantly fails in a
proof:

```python
import Base
law big:
  {Nat.add(100000n, 100000n) == Nat.mul(2n, 100000n) : Nat}
def big():
  {==}
```

On 2.0.25 this stops with "the machine stack overflowed". It checks at
`1000n`.

**The change.** In `term_wnf`, when a Base definition from a fixed table
(`Nat.add sub mul double min max cmp is_*`; `U32.add sub mul and or xor
div mod min max inc not shl shr shln shrn from_nat to_nat cmp is_*`) has
all its arguments, and those arguments are known numbers, the checker
computes the result with machine integers and returns a literal (or
`True`/`False`/`LT`/`EQ`/`GT`). Otherwise it unfolds as before. Each entry
follows its Base body: `Nat.sub` truncates at zero, `U32.div` by zero is
0, `U32.mod` by zero is the dividend, shifts past 31 give 0, `from_nat`
wraps. Results past 2^53 unfold as before.

Two rules keep behavior identical everywhere else:

1. An argument is evaluated only if the Base body forces it anyway
   (`Nat.add` forces its first argument, never its second; `U32.shln`
   forces the word only for a count above zero). Other arguments count
   only if they are already values.
2. An argument is evaluated only if it is closed (no free variable,
   checked once per term node). A first version without this rule hung
   on `tests/proof/shift_left_mask.bend`: evaluating a symbolic
   `U32.shln(a, 16n)` early cached its stuck, expanded form where the
   compact call had been, and the later comparison of
   `U32.shln(a, Nat.add(16n, 16n))` with `U32.shln(a, 32n)` blew up.
   With the rule, symbolic terms are never touched.

The trust is unchanged: the compiler already assumes the same native
operations agree with the same Base bodies.

**Evidence** (Apple M-series, `bun bend2/main.ts`):

| check | 2.0.25 | patched |
|---|---|---|
| `Nat.add(100000n, 100000n) == Nat.mul(2n, 100000n)` | stack overflow | checks, 0.13 s |
| `Nat.add(4000000000n, 4000000000n) == ...` | stack overflow | checks |
| false laws (`Nat.add(100000n, 1n) == 100000n`, `Nat.sub(5n, 9n) == 1n`) | overflow / rejected | rejected, with expected and observed values |
| `tests/proof/shift_left_mask.bend` (symbolic shifts) | 0.13 s | 0.16 s |
| all 1427 files in `tests/*/*.bend`, `--check-only` output | baseline | identical; total time 763 s vs 762 s |
| 1000 IEEE binary32 additions done in software, proven bit-equal to hardware | 12.9 s | 4.5 s |

**Why it matters.** Proofs that compute with numbers hit the overflow or
take seconds: bit decoding, fixed-point game state, replays of recorded
runs. The last row is from bend_stdlib, where binary32 floats are
implemented in software over `Word(32n)` so the checker can compute them
(`src/float/`), and `examples/sf32.bend` proves float results bit-exact
against hardware: <https://github.com/nbardy/bend_stdlib/tree/stdlib-rewrite>.
Nothing is added to Base.
