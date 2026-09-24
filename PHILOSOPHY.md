# Philosophy

The rules this library follows, and the Bend facts they come from.
Checked on Bend 2.0.20, 2.0.25, 2.0.26 and 2.0.27 (2026-09-25); `./gate.sh` re-runs the
checks.

## Facts

1. `{==}` closes a goal when both sides normalize to the same term.
   There are no tactics, so how a definition unfolds decides how hard
   its proofs are.
2. Variables are used at most once. `+x` allows copies of a `Data`
   value. A closure can be called once. A `~` template argument is
   substituted at compile time and can be used any number of times.
3. A law can take `~` parameters, including other laws, and is checked
   once with them opaque. Breaking an arm of such a proof is rejected.
4. `match` works on parameters and pattern variables, not computed
   values. Scrutinees follow binder order, a `let` cannot come before a
   match on a parameter, and a match does not refine hypotheses already
   in scope.
5. At runtime a `Nat` is a 48-bit machine value (upstream WONTFIX #779),
   and in the checker a literal is one node (2.0.24).
6. A module imported as `Nat` that defines `ge_refl` replaces Base's
   `Nat.ge_refl` in the importing file, with no warning.
7. A pair `A & B` is a `Type`, so a proof pair cannot be copied with
   `+`. A function whose clauses overlap (`case BZ{} b`, then
   `case a BZ{}`) reduces only once every scrutinee's constructor is
   known.
8. Every `F32` operation in Base is an unproven law, so no float
   arithmetic computes in the checker. A float is its 32 bits, so
   functions of the bits do (`src/float/`).

## Do and don't

### Types

- Do state an invariant as a type computed from the data: `Nat.LE`,
  `Sorted.from`, `Vec.Vec(A, n)`. Its proofs then recurse the same way
  the data does.
- Don't use `{Nat.is_le(a, b) == True{}}` as a premise in laws. It
  needs a case split at every step. Convert it once with
  `Nat.le_of_is_lt` or `Nat.ge_of_not_lt`.
- Do make impossible cases impossible to write. `Vec.zip_with` takes
  two `Vec(_, n)`, so it has no length-mismatch case; `Vec.get` at
  `n = 0n` holds `Nat.LT(i, 0n)`, which is `Empty`.
- Don't return a made-up value for a case that should not happen. Change
  the type instead.
- Do convert raw input once, at the boundary (`Vec.from_list`).
- Do give each outcome its own constructor (`List.Step`: `Stop` or
  `Next`). Don't use one constructor, such as `None`, for two different
  outcomes.

### Branching

- Do branch on a comparison that returns a proof, such as
  `Nat.le_case(a, b) : Or(LE(a, b), LE(b, a))`. The proof then has the
  fact each branch was taken on.
- Don't branch on a `Bool` and re-prove the fact afterwards.
- Do handle Base's branches on computed tests (`U32.min` is
  `Bool.pick(U32.is_lt(a, b), a, b)`) by taking the test's result `c` and
  `{U32.is_lt(a, b) == c}` as parameters (`U32.min_le_r.go`).
- Do use Base's `Or(A, B)` for a two-way result.

### Recursion

- Do pass a computed value to a helper that matches on its parameter
  (`Q.pop` passes `List.reverse(rear)` to `pop.rot`).
- Don't add fuel to a function whose recursion is bounded by its input.
  Fuel is for loops bounded by the outside world.
- Do pass a recursive call as a thunk (`u => insert(x, t)`) when only
  one branch uses it. Arguments are evaluated before the call.
- Do take hypotheses after a match, as a function each branch returns.
  If a hypothesis is needed both for the current step and for the
  induction, pass the induction step in as a function too
  (`Sorted.insert_from.go`).

### Composition

- Do write functions and laws over `~` operations and `~` laws, as in
  `Sorted.sort_sorted` and `Tree.reduce_foldr`.
- Do pass an operation and its laws as one dictionary (`C.Ord`,
  `C.Semigroup`, `C.Group`) and read it through accessors such as
  `C.Ord.dec`; a match on a `~` dictionary inside generic code cannot be
  typed. Put instances with their types (`Nat.ord()`, `U32.group()`).
- Do state a caller's law through the same dictionary the library law
  uses. Template instances are equal only when their `~` arguments are
  the same terms: `List.foldr` over `~Nat.add` and over
  `~C.Semigroup.fn(~Nat, ~Nat.add_sg())` compute the same values but the
  checker does not equate them.
- Do prove a state machine's invariant for one step and get it for every
  input sequence from `M.run_inv`.
- Do give laws that are passed as `~` arguments plain binders. `+` and
  `-` are part of a law's type, so `@a -> @-b -> @-c -> ...` does not
  fit `~assoc: @x -> @y -> @z -> ...`. Copy inside a branch with
  `+x = x`.
- Do prove laws about Base's functions (`List.append`, `List.reverse`,
  `List.foldr`, `U32.clamp`). Don't copy a Base function and prove laws
  about the copy.
- Do write each equation with the side a caller will rewrite away on the
  right, since `%e : P` replaces `e`'s right side with its left side.
- Do specify a data structure by a function to a simpler type and laws
  about it: `Q.model(q)` is the list a queue holds, `push_model` and
  `pop_model` state push and pop on that list.

### Modules

- Do keep one topic per file, with each law next to the definitions it
  is about.
- Do import a module that extends a Base type under that type's name
  (`nat.bend as Nat`), and don't define a name Base already defines
  (fact 6). `gate.sh` checks every name against `bend base`.
- Don't add a law that nothing in this repository uses. When a law's
  last user goes, delete the law.

### Numbers

- Do use `Nat` for counts, indices and anything a proof inducts on.
- Do keep game state in `U32` and prove order facts through
  `U32.cmp_nat`.
- Do state a float law through the bits: specify the operation on the
  bits and take "the hardware matches" as a `~` argument
  (`~lt: F32.LtOk()`), so each law says what it assumes. Prefer exact
  operations (comparison, negation, clamping); their hypotheses hold on
  every lane.
- Do clamp a float before it becomes an index or leaves the bounds a
  law is about. `F32.clamp_le_hi` and `F32.lo_le_clamp` hold for every
  input, NaN and infinities included.
- Test what is not proven: `examples/sf32.bend` compares the software
  floats with the hardware's.

### Tests

- The laws are the tests. `gate.sh` adds what the checker does not
  cover: each module checks on its own, each example prints its
  expected output on the interpreter and as a native binary, and no
  name shadows Base.
- Do break a new generic proof once and confirm it is rejected. Do
  make every gate check able to fail.
- Don't write tests that restate a value `{==}` would prove.
- Don't claim a speedup or GPU behavior without a measured run.
