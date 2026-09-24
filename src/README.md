# Modules

Each file is one topic, with its laws next to its definitions. Import a
module by path, under the name shown; a module that extends a Base type
takes that type's name (`nat.bend as Nat`), so `Nat.add` is still
Base's and `Nat.le_trans` is this library's. Every module is used by at
least one example or app, linked below; `./gate.sh` checks and runs
them all.

Floats have their own guide: [float/README.md](float/README.md).

| module | as | for | used in |
|---|---|---|---|
| [`class.bend`](#classbend-as-c) | `C` | operations bundled with their laws | everything generic |
| [`machine.bend`](#machinebend-as-m) | `M` | invariants over every input sequence | paddle, breakout |
| [`sim.bend`](#simbend-as-sim) | `Sim` | reversible integer physics | rewind |
| [`sorted.bend`](#sortedbend-as-sorted) | `Sorted` | insertion sort, proven sorted and a permutation | tour |
| [`tree.bend`](#treebend-as-tree) | `Tree` | parallel reduction, proven equal to a fold | tour |
| [`queue.bend`](#queuebend-as-q) | `Q` | a linear FIFO queue, specified by a list | tour |
| [`vec.bend`](#vecbend-as-vec) | `Vec` | length-indexed vectors, no bounds checks | tour |
| [`v2.bend`](#v2bend-as-v2) | `V2` | 2D wrapping integer vectors | rewind |
| [`u32.bend`](#u32bend-as-u32) | `U32` | order and wrapping laws for Base's U32 | paddle, rewind |
| [`nat.bend`](#natbend-as-nat-listbend-as-list) | `Nat` | order as a type | breakout, fluid, tour |
| [`list.bend`](#natbend-as-nat-listbend-as-list) | `List` | laws about Base's append and reverse | queue, tour |
| [`float/`](float/README.md) | `F32`, `SF32`, ... | laws about float code | breakout, fluid, sf32 |

## `class.bend` as `C`

An operation and its laws as one value, passed as a `~` argument.
Generic code reads it through accessors (`C.Ord.R`, `C.Ord.dec`,
`C.Semigroup.op`, `C.Group.sub_add`, ...); a `match` on a `~` argument
inside generic code cannot be typed.

| type | fields | instances |
|---|---|---|
| `Ord<A>` | `R`, `dec : Or(R(x,y), R(y,x))` | `Nat.ord()` |
| `Semigroup<A>` | `op`, `assoc` | `Nat.add_sg()` |
| `Group<A>` | `add`, `sub`, `sub_add`, `add_sub` | `U32.group()`, `V2.group()` |

```python
Sorted.sort(~Nat, ~Nat.ord(), xs)                # any C.Ord
Tree.reduce(~Nat, ~Nat.add_sg(), t)              # any C.Semigroup
```

A caller's law must use the same dictionary as the library law:
`List.foldr` over `~Nat.add` and over `~C.Semigroup.fn(~Nat,
~Nat.add_sg())` compute the same values, but the checker does not
equate the two template instances. `examples/tour.bend` (`psum_is_sum`)
shows the working form.

## `machine.bend` as `M`

A state machine is a step `S -> I -> S`. Prove that one step keeps an
invariant, and `run_inv` gives it for every input list.

| | name | |
|---|---|---|
| def | `run(~S, ~I, ~step, s, inputs)` | `List.foldl` of `step` |
| law | `run_inv(~S, ~I, ~step, ~Inv, ~keep, inputs, s)` | if one step keeps `Inv`, every run does |

```python
law always_on_field:
  for +g: Game
  for inputs: List<&2, Input>
  OnField(g) -> OnField(M.run(~Game, ~Input, ~step, g, inputs))

def always_on_field(g, inputs):
  M.run_inv(~Game, ~Input, ~step, ~OnField, ~keep, inputs, g)
```

Used in [`examples/paddle.bend`](../examples/paddle.bend) (the smallest
example) and [`apps/breakout.bend`](../apps/breakout.bend) (arena,
speed and score over every input list).

## `sim.bend` as `Sim`

Integer physics that runs backwards exactly. A state is a position and
a velocity in any `C.Group`; the force is any function of the position.

| | name | |
|---|---|---|
| type | `State<P>` | position `x`, velocity `v` |
| def | `step`, `back`, `run`, `rewind` | take `~g: C.Group<P>` and a force `~F: P -> P` |
| law | `back_step` | `back` undoes `step` |
| law | `rewind_run` | `rewind(n, run(n, s)) == s` |

Used in [`examples/rewind.bend`](../examples/rewind.bend): a body under
gravity and wind runs 100000 steps and rewinds to its exact start, with
a law that this holds for every state and step count.

## `sorted.bend` as `Sorted`

| | name | |
|---|---|---|
| def | `Sorted(~A, ~o, xs)`, `from(~A, ~o, lo, xs)` | sortedness as a type |
| def | `insert`, `sort` | over `~o: C.Ord<A>`; O(n²) |
| def | `count(~A, ~eq, y, xs)` | |
| law | `sort_sorted` | the output is `Sorted` |
| law | `sort_count` | every element's count is unchanged |

```python
law nat_sort_sorted:
  for xs: List<&2, Nat>
  Sorted.Sorted(~Nat, ~Nat.ord(), Sorted.sort(~Nat, ~Nat.ord(), xs))

def nat_sort_sorted(xs):
  Sorted.sort_sorted(~Nat, ~Nat.ord(), xs)
```

Used in [`examples/tour.bend`](../examples/tour.bend).

## `tree.bend` as `Tree`

| | name | |
|---|---|---|
| type | `Tree<A>` | `Tip{x}` or `Fork{l, r}` |
| def | `reduce(~A, ~m, t)` | reduces the two halves with a parallel call |
| def | `build(~f, d, lo)`, `to_list` | |
| law | `reduce_foldr` | for any `~m: C.Semigroup<A>`, `reduce` agrees with `List.foldr` |

`reduce_foldr` says the parallel result is the sequential fold, for
any associative operation. Used in
[`examples/tour.bend`](../examples/tour.bend) (`psum_is_sum`).

## `queue.bend` as `Q`

A queue is linear (`&1`): it is used once and never copied.

| | name | |
|---|---|---|
| type | `Queue<A>` | front list and reversed rear list |
| def | `empty`, `push`, `pop`, `model` | `pop` returns `List.Step<&1, A, Queue<A>>` |
| law | `push_model` | `model(push(q, x)) == model(q) ++ [x]` |
| law | `pop_model` | `pop` returns the head and tail of `model(q)` |

`model(q)` is the list the queue holds; the two laws specify the queue
by that list. Used in [`examples/tour.bend`](../examples/tour.bend).

## `vec.bend` as `Vec`

| | name | |
|---|---|---|
| def | `Vec(A, n)` | a list of length `n`, as a type |
| def | `from_list(xs)` | `Vec(A, length xs)` |
| def | `get(n, v, i, lt)` | `lt : Nat.LT(i, n)`; no out-of-bounds case exists |
| def | `zip_with`, `foldr` | two vectors of one length; no mismatch case exists |

```python
def dot(+n: Nat, xs: Vec.Vec(U32, n), ys: Vec.Vec(U32, n)) -> U32:
  Vec.foldr(~U32, ~U32, ~U32.add, n, Vec.zip_with(~U32, ~U32, ~U32, ~U32.mul, n, xs, ys), 0)
```

Used in [`examples/tour.bend`](../examples/tour.bend).

## `v2.bend` as `V2`

| | name | |
|---|---|---|
| type | `V2` | `V2{x: U32, y: U32}` |
| def | `add`, `sub`, `group()` | |
| law | `sub_add`, `add_sub` | lifted from U32 |

Used in [`examples/rewind.bend`](../examples/rewind.bend) as the
`C.Group` for 2D physics.

## `u32.bend` as `U32`

| | name | |
|---|---|---|
| law | `cmp_nat` | `Nat.cmp(to_nat a, to_nat b) == U32.cmp(a, b)` |
| def | `LE(a, b)` | `Nat.LE` on the numbers |
| law | `min_le_r`, `le_max_r` | about Base's `U32.min` and `U32.max` |
| law | `clamp_le_hi` | `U32.clamp(x, lo, hi) <= hi` for every `x` |
| law | `lo_le_clamp` | `lo <= U32.clamp(x, lo, hi)` for every `x`, given `lo <= hi` |
| law | `sub_add`, `add_sub` | wrapping `+` and `-` undo each other |
| def | `group()` | U32 as a `C.Group` |

```python
(U32.lo_le_clamp(U32.sub(p, 8), 20, 236, Unit{}), U32.clamp_le_hi(U32.sub(p, 8), 20, 236))
```

Used in [`examples/paddle.bend`](../examples/paddle.bend) (the paddle
stays on the field) and [`examples/rewind.bend`](../examples/rewind.bend).
`float/f32.bend` proves the same clamp laws for `F32`.

## `nat.bend` as `Nat`, `list.bend` as `List`

| | name | |
|---|---|---|
| def | `Nat.LE`, `Nat.LT`, `Nat.le_case` | order as a type, and the decision |
| law | `Nat.le_refl`, `Nat.le_step`, `Nat.le_trans`, `Nat.sub_le` | |
| law | `Nat.le_of_is_lt`, `Nat.ge_of_not_lt` | turn a `Nat.is_lt` result into `LE` |
| law | `Nat.add_assoc` | |
| type | `List.Step<a, A, S>` | `Stop` or `Next{x, rest}` |
| law | `List.append_nil`, `List.append_assoc`, `List.reverse_go` | about Base's `List.append` and `List.reverse` |

`Nat.LE(a, b)` computes to `Unit` or `Empty`, so a proof of `3 <= 5` is
`Unit{}` and `LT(i, 0n)` cannot be built. Used in
[`apps/breakout.bend`](../apps/breakout.bend) (lives never increase),
[`apps/fluid.bend`](../apps/fluid.bend) (grid indices) and
[`examples/tour.bend`](../examples/tour.bend).
