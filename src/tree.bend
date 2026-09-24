import Base
import ./class.bend as C

# tree.bend: binary trees reduced with parallel calls.
#
#   import ./tree.bend as Tree
#   Tree.reduce(~Nat, ~Nat.add_sg(), t)
#
# reduce evaluates the two halves of each Fork with a parallel call. The
# law reduce_foldr says that for any C.Semigroup, reduce gives the same
# result as Base's List.foldr over the leaves in order. It needs no
# identity element, because a tree always has a leaf.
#
# Not yet measured: the speedup of reduce on the CPU, and any run on the
# GPU.

type Tree<-A: Data> is Data:
  Tip{x: A}
  Fork{l: Tree<A>, r: Tree<A>}

def reduce(~A: Data, ~m: C.Semigroup<A>, t: Tree<A>) -> A:
  match t:
    case Tip{x}:
      x
    case Fork{l, r}:
      a b = reduce(~A, ~m, l) reduce(~A, ~m, r)
      C.Semigroup.op(A, m, a, b)

# the leaves, left to right, in front of acc
def to_list.go(-A: Data, t: Tree<A>, acc: List<&2, A>) -> List<&2, A>:
  match t:
    case Tip{x}:
      x <> acc
    case Fork{l, r}:
      to_list.go(A, l, to_list.go(A, r, acc))

def to_list(-A: Data, t: Tree<A>) -> List<&2, A>:
  to_list.go(A, t, Nil{})

# a balanced tree with 2^d leaves f(lo), f(lo+1), ..., so both halves of
# each parallel call do the same amount of work
def build(~A: Data, ~f: Nat -> A, +d: Nat, +lo: Nat) -> Tree<A>:
  match d:
    case 0n:
      Tip{f(lo)}
    case 1n+p:
      l r = build(~A, ~f, p, lo) build(~A, ~f, p, Nat.add(lo, Nat.pow(2n, p)))
      Fork{l, r}

# reduce agrees with foldr. With acc = Nil{}:
# {op(reduce(t), z) == foldr(to_list(t), z)}.
law reduce_foldr:
  for ~A: Data
  for ~m: C.Semigroup<A>
  for t: Tree<A>
  for +acc: List<&2, A>
  for +z: A
  {C.Semigroup.op(A, m, reduce(~A, ~m, t), List.foldr(~&2, ~A, ~A, ~C.Semigroup.fn(~A, ~m), acc, z)) == List.foldr(~&2, ~A, ~A, ~C.Semigroup.fn(~A, ~m), to_list.go(A, t, acc), z) : A}

def reduce_foldr(A, m, t, acc, z):
  match t:
    case Tip{x}:
      {==}
    case Fork{+l, +r}:
      -fz = List.foldr(~&2, ~A, ~A, ~C.Semigroup.fn(~A, ~m), acc, z)
      -g = C.Semigroup.op(A, m, C.Semigroup.op(A, m, reduce(~A, ~m, l), reduce(~A, ~m, r)), fz)
      %reduce_foldr(~A, ~m, l, to_list.go(A, r, acc), z) : {g == _ : A}
      %reduce_foldr(~A, ~m, r, acc, z) : {g == C.Semigroup.op(A, m, reduce(~A, ~m, l), _) : A}
      Equal.sym(A, C.Semigroup.op(A, m, reduce(~A, ~m, l), C.Semigroup.op(A, m, reduce(~A, ~m, r), fz)), g,
        C.Semigroup.assoc(A, m, reduce(~A, ~m, l), reduce(~A, ~m, r), List.foldr(~&2, ~A, ~A, ~C.Semigroup.fn(~A, ~m), acc, z)))
