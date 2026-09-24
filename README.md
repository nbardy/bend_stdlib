# bend_stdlib

Data structures and laws for [Bend](https://github.com/HigherOrderCO/Bend).
Laws are checked at build time and erased at run time. Design rules are
in [PHILOSOPHY.md](PHILOSOPHY.md).

```python
import Base
import ./src/nat.bend as Nat
import ./src/sorted.bend as Sorted

def sort(xs: List<&2, Nat>) -> List<&2, Nat>:
  Sorted.sort(~Nat, ~Nat.ord(), xs)

law sort_ok:
  for xs: List<&2, Nat>
  Sorted.Sorted(~Nat, ~Nat.ord(), sort(xs))

def sort_ok(xs):
  Sorted.sort_sorted(~Nat, ~Nat.ord(), xs)
```

## Install

With pnpm, straight from git (pin a tag or commit for reproducible builds):

```sh
pnpm add bend_stdlib@github:nbardy/bend_stdlib#stdlib-rewrite
```

then import by path: `import ./node_modules/bend_stdlib/src/nat.bend as Nat`.
Copying `src/` into a project works too; Bend imports are plain paths.

## Examples

Each is checked and run by `./gate.sh` on the interpreter and as a
native binary:

- `examples/paddle.bend`: a game state machine; the paddle stays on the
  field after every input sequence.
- `examples/rewind.bend`: 2D integer physics run 100000 steps and
  rewound to the exact start state, with a law that this holds for every
  state and step count.
- `examples/tour.bend`: sort, queue, parallel sum, vectors.
- `examples/sf32.bend`: float facts closed by `{==}` (`0.1 + 0.2` is
  `0x3E99999A`), and software floats, comparison and negation against
  the hardware's on edge cases and random bit patterns.

## Apps

- `apps/breakout.bend`: Breakout with `F32` physics, played with the
  mouse by `apps/breakout_window.bend`. For every input list, including
  NaN and infinite mouse positions: the paddle and ball stay in the
  arena; the ball's speed never changes, bit for bit; score + 10 x
  (bricks left) never changes; lives never increase.
- `apps/fluid.bend`: stable fluids on a 32x32 torus. Proven: the torus
  neighbours and cell indices, and that every back-traced position gives
  an in-range cell index and interpolation weight, so `F32.to_u32`
  never gets a value it is undefined on.

The float laws assume only that the hardware's `<` and negation are
IEEE 754's (`F32.LtOk()`, `F32.NegOk()`), passed as `~` arguments.

The gate also checks each module on its own and that no name shadows
Base. It passes on Bend 2.0.20 and 2.0.26.

## Modules

### `class.bend` as `C`: operations with their laws

Generic code takes one of these as a `~` argument and reads it through
the accessors (`C.Ord.R`, `C.Ord.dec`, `C.Semigroup.op`, ...).

| type | fields | instances |
|---|---|---|
| `Ord<A>` | `R`, `dec : Or(R(x,y), R(y,x))` | `Nat.ord()` |
| `Semigroup<A>` | `op`, `assoc` | `Nat.add_sg()` |
| `Group<A>` | `add`, `sub`, `sub_add`, `add_sub` | `U32.group()`, `V2.group()` |

### `machine.bend` as `M`: invariants over every input sequence

| | name | |
|---|---|---|
| def | `run(~S, ~I, ~step, s, inputs)` | `List.foldl` of `step` |
| law | `run_inv(~S, ~I, ~step, ~Inv, ~keep, inputs, s)` | if one step keeps `Inv`, every run does |

### `sim.bend` as `Sim`: reversible integer physics

| | name | |
|---|---|---|
| type | `State<P>` | position `x`, velocity `v` |
| def | `step`, `back`, `run`, `rewind` | take `~g: C.Group<P>` and a force `~F: P -> P` |
| law | `back_step` | `back` undoes `step` |
| law | `rewind_run` | `rewind(n, run(n, s)) == s` |

### `sorted.bend` as `Sorted`

| | name | |
|---|---|---|
| def | `Sorted(~A, ~o, xs)`, `from(~A, ~o, lo, xs)` | |
| def | `insert`, `sort` | over `~o: C.Ord<A>`; O(n²) |
| def | `count(~A, ~eq, y, xs)` | |
| law | `sort_sorted` | the output is `Sorted` |
| law | `sort_count` | every element's count is unchanged |

### `tree.bend` as `Tree`

| | name | |
|---|---|---|
| type | `Tree<A>` | `Tip{x}` or `Fork{l, r}` |
| def | `reduce(~A, ~m, t)` | reduces the two halves with a parallel call |
| def | `build(~f, d, lo)`, `to_list` | |
| law | `reduce_foldr` | for any `~m: C.Semigroup<A>`, `reduce` agrees with `List.foldr` |

### `queue.bend` as `Q`

| | name | |
|---|---|---|
| type | `Queue<A>` | linear; front list and reversed rear list |
| def | `empty`, `push`, `pop`, `model` | `pop` returns `List.Step<&1, A, Queue<A>>` |
| law | `push_model` | `model(push(q, x)) == model(q) ++ [x]` |
| law | `pop_model` | `pop` returns the head and tail of `model(q)` |

### `vec.bend` as `Vec`

| | name | |
|---|---|---|
| def | `Vec(A, n)` | a list of length `n`, as a type |
| def | `from_list(xs)` | `Vec(A, length xs)` |
| def | `get(n, v, i, lt)` | `lt : Nat.LT(i, n)` |
| def | `zip_with`, `foldr` | |

### `v2.bend` as `V2`

| | name | |
|---|---|---|
| type | `V2` | `V2{x: U32, y: U32}` |
| def | `add`, `sub`, `group()` | |
| law | `sub_add`, `add_sub` | lifted from U32 |

### `u32.bend` as `U32`

| | name | |
|---|---|---|
| law | `cmp_nat` | `Nat.cmp(to_nat a, to_nat b) == U32.cmp(a, b)` |
| def | `LE(a, b)` | `Nat.LE` on the numbers |
| law | `min_le_r`, `le_max_r` | about Base's `U32.min` and `U32.max` |
| law | `clamp_le_hi` | `U32.clamp(x, lo, hi) <= hi` for every `x` |
| law | `lo_le_clamp` | `lo <= U32.clamp(x, lo, hi)` for every `x`, given `lo <= hi` |
| law | `sub_add`, `add_sub` | wrapping `+` and `-` undo each other |
| def | `group()` | U32 as a `C.Group` |

### `nat.bend` as `Nat`, `list.bend` as `List`

| | name | |
|---|---|---|
| def | `Nat.LE`, `Nat.LT`, `Nat.le_case` | order as a type, and the decision |
| law | `Nat.le_refl`, `Nat.le_step`, `Nat.le_trans`, `Nat.sub_le` | |
| law | `Nat.le_of_is_lt`, `Nat.ge_of_not_lt`, `Nat.add_assoc` | |
| type | `List.Step<a, A, S>` | `Stop` or `Next{x, rest}` |
| law | `List.append_nil`, `List.append_assoc`, `List.reverse_go` | about Base's `List.append` and `List.reverse` |

### `float/`: floats as bits

Design and related work: [docs/floats.md](docs/floats.md).

| module | as | |
|---|---|---|
| `float/f32.bend` | `F32` | IEEE `<` (`lt_bits`, `LE`) and negation (`neg_bits`) on the bits; laws about Base's `F32.clamp` (`clamp_le_hi`, `lo_le_clamp`) and `F32.neg` (`neg_mag`, `neg_key`) under `LtOk()` / `NegOk()` |
| `float/sf32.bend` | `SF32` | binary32 `add`, `sub`, `mul` in software, computed by the checker; `soft()`, `hard()`, `HardOk()` |
| `float/format.bend` | `Fmt` | exact values, formats, round to nearest even, `spec_add`, `spec_mul` |
| `float/num.bend` | `Num` | the contract an implementation meets: `Impl`, `AddOk`, `MulOk`, `Correct` |
| `float/bin.bend` | `Bin` | binary naturals: add, sub, mul, compare, shifts with round and sticky bits |
