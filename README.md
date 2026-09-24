# bend_stdlib

Data structures and laws for [Bend](https://github.com/HigherOrderCO/Bend).
Laws are checked at build time and erased at run time. Design rules are
in [PHILOSOPHY.md](PHILOSOPHY.md).

```python
import Base
import bend-lawful-stdlib@0.1.0.0/src/nat.bend as Nat
import bend-lawful-stdlib@0.1.0.0/src/sorted.bend as Sorted

def sort(xs: List<&2, Nat>) -> List<&2, Nat>:
  Sorted.sort(~Nat, ~Nat.ord(), xs)

law sort_ok:
  for xs: List<&2, Nat>
  Sorted.Sorted(~Nat, ~Nat.ord(), sort(xs))

def sort_ok(xs):
  Sorted.sort_sorted(~Nat, ~Nat.ord(), xs)
```

## Install

From the Bend hub, by name. Nothing to install; import the modules you
use:

```python
import bend-lawful-stdlib@0.1.0.0/src/nat.bend as Nat
import bend-lawful-stdlib@0.1.0.0/src/float/f32.bend as F32
```

The version is fixed by content hash
(`0x5f97f469d15c04a181dae0e4e64e1d3d`), so a build never changes under
you.

With pnpm, from git (`#v0.1.0` pins the same release):

```sh
pnpm add bend_stdlib@github:nbardy/bend_stdlib#v0.1.0
```

then import by path: `import ./node_modules/bend_stdlib/src/nat.bend as Nat`.
Copying `src/` into a project works too; Bend imports are plain paths.

MIT licensed.

## Examples

Each is checked and run by `./gate.sh` on the interpreter and as a
native binary:

- [`examples/paddle.bend`](examples/paddle.bend): a game state machine; the paddle stays on the
  field after every input sequence.
- [`examples/rewind.bend`](examples/rewind.bend): 2D integer physics run 100000 steps and
  rewound to the exact start state, with a law that this holds for every
  state and step count.
- [`examples/tour.bend`](examples/tour.bend): sort, queue, parallel sum, vectors.
- [`examples/sf32.bend`](examples/sf32.bend): float facts closed by `{==}` (`0.1 + 0.2` is
  `0x3E99999A`), and software floats, comparison and negation against
  the hardware's on edge cases and random bit patterns.
- [`examples/drift.bend`](examples/drift.bend): an Euler step `x + v * dt` on the
  hardware's floats, with the proven bound on its error against exact
  arithmetic, and a run that measures the actual error exactly.

## Apps

- [`apps/breakout.bend`](apps/breakout.bend): Breakout with `F32` physics, played with the
  mouse by [`apps/breakout_window.bend`](apps/breakout_window.bend). For every input list, including
  NaN and infinite mouse positions: the paddle and ball stay in the
  arena; the ball's speed never changes, bit for bit; score + 10 x
  (bricks left) never changes; lives never increase.
- [`apps/fluid.bend`](apps/fluid.bend): stable fluids on a 32x32 torus. Proven: the torus
  neighbours and cell indices for any grid size; every back-traced
  position gives an in-range cell index and interpolation weight, so
  `F32.to_u32` never gets a value it is undefined on; and the app's own
  pressure projection, run by the checker in software floats on a 4x4
  fixture, lowers the total |divergence| from 2.4 to about 2.25e-6, with
  the exact bits stated. `main` runs the fixture on the machine's floats
  and prints whether the bits agree.

The float laws assume only that the hardware's `<` and negation are
IEEE 754's (`F32.LtOk()`, `F32.NegOk()`), passed as `~` arguments.

The gate also checks each module on its own and that no name shadows
Base. It passes on Bend 2.0.20, 2.0.26 and 2.0.27.

## Modules

Each module's definitions, laws and the examples that use it:

- [src/README.md](src/README.md): `class`, `machine`, `sim`, `sorted`,
  `tree`, `queue`, `vec`, `v2`, `u32`, `nat`, `list`.
- [src/float/README.md](src/float/README.md): laws about float code,
  and floats computed in the checker.

Design rules: [PHILOSOPHY.md](PHILOSOPHY.md). Float design and related
work: [docs/floats.md](docs/floats.md).
