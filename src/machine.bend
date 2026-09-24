import Base

# machine.bend: invariants of state machines, over every input sequence.
#
#   import ./machine.bend as M
#   M.run(~S, ~I, ~step, s, inputs)
#
# A state machine is a step ~step: S -> I -> S, and run folds it over a
# list of inputs with Base's List.foldl. run_inv: if one step keeps an
# invariant Inv, so does every run, over every input list. A caller
# proves the one-step fact and gets the rest.

def run(~S: Data, ~I: Data, ~step: S -> I -> S, s: S, xs: List<&2, I>) -> S:
  List.foldl(~&2, ~I, ~S, ~step, xs, s)

# a step that keeps Inv keeps it over any input list
law run_inv:
  for ~S: Data
  for ~I: Data
  for ~step: S -> I -> S
  for ~Inv: S -> Type
  for ~keep: @s: S -> @i: I -> Inv(s) -> Inv(step(s, i))
  for xs: List<&2, I>
  for +s: S
  Inv(s) -> Inv(run(~S, ~I, ~step, s, xs))

def run_inv(S, I, step, Inv, keep, xs, s):
  match xs:
    case Nil{}:
      k => k
    case +h <> t:
      k => run_inv(~S, ~I, ~step, ~Inv, ~keep, t, step(s, h))(keep(s, h, k))
