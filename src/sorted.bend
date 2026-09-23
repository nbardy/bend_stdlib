import Base
import ./class.bend as C

# sorted.bend: insertion sort over any C.Ord, with laws that its output is
# sorted and keeps every element's count.
#
#   import ./sorted.bend as Sorted
#   Sorted.sort(~Nat, ~Nat.ord(), xs)
#
# The order's decision returns a proof of the side that holds. insert
# branches on that proof, and the sortedness proof receives the same
# proof in each branch, so it needs no transitivity. The laws are proven
# once, with the order opaque.
#
# Insertion sort is O(n^2). Base's List.sort is a merge sort with no laws.

# every element is at least lo, and the list ascends
def from(~A: Data, ~o: C.Ord<A>, lo: A, xs: List<&2, A>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      (C.Ord.R(A, o, lo, h) & from(~A, ~o, h, t))

# the list ascends
def Sorted(~A: Data, ~o: C.Ord<A>, xs: List<&2, A>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      from(~A, ~o, h, t)

# insert's step after comparing x with h. The recursive insert is passed
# as a thunk so that the x-first branch does not run it.
def insert.go(-A: Data, -o: C.Ord<A>, x: A, h: A, t: List<&2, A>, rec: Unit -> List<&2, A>, c: Or(C.Ord.R(A, o, x, h), C.Ord.R(A, o, h, x))) -> List<&2, A>:
  match c:
    case Inl{e}:
      x <> h <> t
    case Inr{e}:
      h <> rec(Unit{})

def insert(~A: Data, ~o: C.Ord<A>, +x: A, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      [x]
    case +h <> +t:
      insert.go(A, o, x, h, t, u => insert(~A, ~o, x, t), C.Ord.dec(A, o, x, h))

def sort(~A: Data, ~o: C.Ord<A>, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      insert(~A, ~o, h, sort(~A, ~o, t))

# A match does not refine hypotheses already in scope, so these laws take
# their hypotheses after the match, as functions returned by each arm.

law insert_from.go:
  for -A: Data
  for -o: C.Ord<A>
  for -lo: A
  for -x: A
  for -h: A
  for -t: List<&2, A>
  for -rec: Unit -> List<&2, A>
  for s: from(~A, ~o, lo, h <> t)
  for lx: C.Ord.R(A, o, lo, x)
  for ih: from(~A, ~o, h, t) -> C.Ord.R(A, o, h, x) -> from(~A, ~o, h, rec(Unit{}))
  for c: Or(C.Ord.R(A, o, x, h), C.Ord.R(A, o, h, x))
  from(~A, ~o, lo, insert.go(A, o, x, h, t, rec, c))

def insert_from.go(A, o, lo, x, h, t, rec, s, lx, ih, c):
  (lh, st) = s
  match c:
    case Inl{e}:
      (lx, e, st)
    case Inr{e}:
      (lh, ih(st, e))

law insert_from:
  for ~A: Data
  for ~o: C.Ord<A>
  for +x: A
  for xs: List<&2, A>
  for -lo: A
  from(~A, ~o, lo, xs) -> C.Ord.R(A, o, lo, x) -> from(~A, ~o, lo, insert(~A, ~o, x, xs))

def insert_from(A, o, x, xs, lo):
  match xs:
    case Nil{}:
      s => lx => (lx, Unit{})
    case +h <> +t:
      s => lx => insert_from.go(A, o, lo, x, h, t, u => insert(~A, ~o, x, t), s, lx,
        insert_from(~A, ~o, x, t, h), C.Ord.dec(A, o, x, h))

law insert_sorted.go:
  for -A: Data
  for -o: C.Ord<A>
  for -x: A
  for -h: A
  for -t: List<&2, A>
  for -rec: Unit -> List<&2, A>
  for s: from(~A, ~o, h, t)
  for ih: from(~A, ~o, h, t) -> C.Ord.R(A, o, h, x) -> from(~A, ~o, h, rec(Unit{}))
  for c: Or(C.Ord.R(A, o, x, h), C.Ord.R(A, o, h, x))
  Sorted(~A, ~o, insert.go(A, o, x, h, t, rec, c))

def insert_sorted.go(A, o, x, h, t, rec, s, ih, c):
  match c:
    case Inl{e}:
      (e, s)
    case Inr{e}:
      ih(s, e)

law insert_sorted:
  for ~A: Data
  for ~o: C.Ord<A>
  for +x: A
  for xs: List<&2, A>
  Sorted(~A, ~o, xs) -> Sorted(~A, ~o, insert(~A, ~o, x, xs))

def insert_sorted(A, o, x, xs):
  match xs:
    case Nil{}:
      s => Unit{}
    case +h <> +t:
      s => insert_sorted.go(A, o, x, h, t, u => insert(~A, ~o, x, t), s,
        insert_from(~A, ~o, x, t, h), C.Ord.dec(A, o, x, h))

# LAW: sort's output is sorted.
law sort_sorted:
  for ~A: Data
  for ~o: C.Ord<A>
  for xs: List<&2, A>
  Sorted(~A, ~o, sort(~A, ~o, xs))

def sort_sorted(A, o, xs):
  match xs:
    case Nil{}:
      Unit{}
    case h <> +t:
      insert_sorted(~A, ~o, h, sort(~A, ~o, t))(sort_sorted(~A, ~o, t))

def bump(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      1n+n
    case False{}:
      n

law bump_swap:
  for a: Bool
  for b: Bool
  for -n: Nat
  {bump(a, bump(b, n)) == bump(b, bump(a, n)) : Nat}

def bump_swap(a, b, n):
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# how many elements of xs ~eq calls equal to y
def count(~A: Data, ~eq: A -> A -> Bool, +y: A, xs: List<&2, A>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      bump(eq(y, h), count(~A, ~eq, y, t))

law insert_count.go:
  for ~A: Data
  for ~eq: A -> A -> Bool
  for -o: C.Ord<A>
  for +y: A
  for +x: A
  for +h: A
  for +t: List<&2, A>
  for -rec: Unit -> List<&2, A>
  for ih: {bump(eq(y, x), count(~A, ~eq, y, t)) == count(~A, ~eq, y, rec(Unit{})) : Nat}
  for c: Or(C.Ord.R(A, o, x, h), C.Ord.R(A, o, h, x))
  {bump(eq(y, x), count(~A, ~eq, y, h <> t)) == count(~A, ~eq, y, insert.go(A, o, x, h, t, rec, c)) : Nat}

def insert_count.go(A, eq, o, y, x, h, t, rec, ih, c):
  match c:
    case Inl{e}:
      {==}
    case Inr{e}:
      %ih : {bump(eq(y, x), bump(eq(y, h), count(~A, ~eq, y, t))) == bump(eq(y, h), _) : Nat}
      bump_swap(eq(y, x), eq(y, h), count(~A, ~eq, y, t))

law insert_count:
  for ~A: Data
  for ~o: C.Ord<A>
  for ~eq: A -> A -> Bool
  for +y: A
  for +x: A
  for xs: List<&2, A>
  {bump(eq(y, x), count(~A, ~eq, y, xs)) == count(~A, ~eq, y, insert(~A, ~o, x, xs)) : Nat}

def insert_count(A, o, eq, y, x, xs):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      insert_count.go(~A, ~eq, o, y, x, h, t, u => insert(~A, ~o, x, t),
        insert_count(~A, ~o, ~eq, y, x, t), C.Ord.dec(A, o, x, h))

# LAW: sort keeps every element's count.
law sort_count:
  for ~A: Data
  for ~o: C.Ord<A>
  for ~eq: A -> A -> Bool
  for +y: A
  for xs: List<&2, A>
  {count(~A, ~eq, y, xs) == count(~A, ~eq, y, sort(~A, ~o, xs)) : Nat}

def sort_count(A, o, eq, y, xs):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %insert_count(~A, ~o, ~eq, y, h, sort(~A, ~o, t)) : {count(~A, ~eq, y, h <> t) == _ : Nat}
      %sort_count(~A, ~o, ~eq, y, t) : {count(~A, ~eq, y, h <> t) == bump(eq(y, h), _) : Nat}
      {==}
