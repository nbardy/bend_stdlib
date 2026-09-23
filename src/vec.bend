import Base
import ./nat.bend as Nat

# vec.bend: lists whose length is part of their type.
#
#   import ./vec.bend as Vec
#
# Vec(A, n) is computed from n: Unit at 0n, a pair of an A and a
# Vec(A, p) at 1n+p. Matching on n tells the checker the vector's shape,
# so zip_with has no length-mismatch case and get has no out-of-bounds
# case: at n = 0n its bound Nat.LT(i, 0n) is Empty.
#
# Indexing is O(i) and every element is a separate pair. For large numeric
# data use Array.

def Vec(-A: Data, n: Nat) -> Data:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Sigma<&2, &2, A, _ => Vec(A, p)>

# a list as a Vec of its own length
def from_list(-A: Data, xs: List<&2, A>) -> Vec(A, List.length(&2, A, xs)):
  match xs:
    case Nil{}:
      Unit{}
    case h <> t:
      (h, from_list(A, t))

def get(-A: Data, n: Nat, v: Vec(A, n), i: Nat, lt: Nat.LT(i, n)) -> A:
  match n:
    case 0n:
      match lt:
    case 1n+p:
      (h, t) = v
      match i:
        case 0n:
          h
        case 1n+j:
          get(A, p, t, j, lt)

def zip_with(~A: Data, ~B: Data, ~C: Data, ~f: A -> B -> C, n: Nat, xs: Vec(A, n), ys: Vec(B, n)) -> Vec(C, n):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      (x, xt) = xs
      (y, yt) = ys
      (f(x, y), zip_with(~A, ~B, ~C, ~f, p, xt, yt))

def foldr(~A: Data, ~B: Data, ~f: A -> B -> B, n: Nat, v: Vec(A, n), z: B) -> B:
  match n:
    case 0n:
      z
    case 1n+p:
      (h, t) = v
      f(h, foldr(~A, ~B, ~f, p, t, z))
