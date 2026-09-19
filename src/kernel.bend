import Base

# K1: the order family. Definitional, evidence-carrying.
law LE:
  for a: Nat
  for b: Nat
  Data

def LE(a, b):
  match a b:
    case 0n y:
      Unit
    case 1n+x 0n:
      Empty
    case 1n+x 1n+y:
      LE(x, y)

law le_trans:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: LE(a, b)
  for bc: LE(b, c)
  LE(a, c)

def le_trans(a, b, c, ab, bc):
  match a:
    case 0n:
      Unit{}
    case 1n+x:
      match b:
        case 0n:
          Empty.absurd(LE(1n+x, c), ab)
        case 1n+y:
          match c:
            case 0n:
              Empty.absurd(LE(1n+x, 0n), bc)
            case 1n+z:
              le_trans(x, y, z, ab, bc)

# K2: monotonicity. LE(a,b) -> LE(a+c, b+c). The bounds workhorse.
law le_add_r:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: LE(a, b)
  LE(Nat.add(c, a), Nat.add(c, b))

def le_add_r(a, b, c, ab):
  match c:
    case 0n:
      ab
    case 1n+p:
      le_add_r(a, b, p, ab)


# GOAL A: calendar no-overlap.
# A well-formed interval is a dependent record: the invariant is a field.
type Iv is Data:
  Iv{s: Nat, e: Nat, wf: LE(s, e)}

# NoOv is SortedB with a projection: bound the next START by the prev END.
law NoOv:
  for xs: List<&2, Iv>
  for lo: Nat
  Type

def NoOv(xs, lo):
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      match h:
        case Iv{s, e, wf}:
          (LE(lo, s) & NoOv(t, e))

# Every interval in the list starts at or after the accumulator.
law AllGE:
  for xs: List<&2, Iv>
  for +lo: Nat
  Type

def AllGE(xs, lo):
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      match h:
        case Iv{s, e, wf}:
          (LE(lo, s) & AllGE(t, lo))

# weakening: push a lower bound down the whole list. le_trans's consumer #1.
law allge_weak:
  for xs: List<&2, Iv>
  for +lo: Nat
  for +m: Nat
  for +lm: LE(lo, m)
  for a: AllGE(xs, m)
  AllGE(xs, lo)

def allge_weak(xs, lo, m, lm, a):
  match xs:
    case Nil{}:
      Unit{}
    case h <> t:
      match h:
        case Iv{s, e, wf}:
          (ms, rest) = a
          (le_trans(lo, m, s, lm, ms), allge_weak(t, lo, m, lm, rest))


# GOAL A payoff: adjacency (NoOv) implies a global lower bound on every
# start. le_trans + the interval's own wf field are the ONLY inputs.
law noov_allge:
  for +xs: List<&2, Iv>
  for +lo: Nat
  for n: NoOv(xs, lo)
  AllGE(xs, lo)

def noov_allge(xs, lo, n):
  match xs:
    case Nil{}:
      Unit{}
    case h <> t:
      match h:
        case Iv{s, +e, wf}:
          (+los, rest) = n
          (los, allge_weak(t, lo, e, le_trans(lo, s, e, los, wf),
                           noov_allge(t, e, rest)))

# structural min (installed Base's Nat.min is pick-based / opaque)
def SMin(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n 0n:
      0n
    case 0n 1n+bp:
      0n
    case 1n+ap 0n:
      0n
    case 1n+ap 1n+bp:
      1n+SMin(ap, bp)

law min_le_r:
  for a: Nat
  for b: Nat
  LE(SMin(a, b), b)

def min_le_r(a, b):
  match a b:
    case 0n 0n:
      Unit{}
    case 0n 1n+bp:
      Unit{}
    case 1n+ap 0n:
      Unit{}
    case 1n+ap 1n+bp:
      min_le_r(ap, bp)

law add_sub_cancel:
  for x: Nat
  for d: Nat
  for e: LE(x, d)
  {Nat.add(x, Nat.sub(d, x)) == d : Nat}

def add_sub_cancel(x, d, e):
  match x d:
    case 0n 0n:
      {==}
    case 0n 1n+dp:
      {==}
    case 1n+xp 0n:
      Empty.absurd({Nat.add(1n+xp, Nat.sub(0n, 1n+xp)) == 0n : Nat}, e)
    case 1n+xp 1n+dp:
      Equal.cong(Nat, Nat, k => 1n+k,
        Nat.add(xp, Nat.sub(dp, xp)), dp, add_sub_cancel(xp, dp, e))

# THE LAW: a clamped blit's right edge lands inside the destination.
law blit_bounds:
  for +sw: Nat
  for +x: Nat
  for +d: Nat
  for e: LE(x, d)
  LE(Nat.add(x, SMin(sw, Nat.sub(d, x))), d)

law le_eq_r:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  for eq: {a == b : Nat}
  for le: LE(c, a)
  LE(c, b)

def le_eq_r(c, a, b, eq, le):
  %eq : LE(c, _)
  le

def blit_bounds(sw, x, d, e):
  le_eq_r(Nat.add(x, SMin(sw, Nat.sub(d, x))),
          Nat.add(x, Nat.sub(d, x)), d,
          add_sub_cancel(x, d, e),
          le_add_r(SMin(sw, Nat.sub(d, x)), Nat.sub(d, x), x,
                     min_le_r(sw, Nat.sub(d, x))))


law SameLen:
  for xs: List<&2, Nat>
  for ys: List<&2, Nat>
  Data

def SameLen(xs, ys):
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          Unit
        case yh <> yt:
          Empty
    case xh <> xt:
      match ys:
        case Nil{}:
          Empty
        case yh <> yt:
          SameLen(xt, yt)

# total, no fallback, no runtime length check: the mismatched arms are
# discharged by Empty.absurd straight off the premise.
law dot:
  for xs: List<&2, Nat>
  for ys: List<&2, Nat>
  for e: SameLen(xs, ys)
  Nat

def dot(xs, ys, e):
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          0n
        case yh <> yt:
          Empty.absurd(Nat, e)
    case xh <> xt:
      match ys:
        case Nil{}:
          Empty.absurd(Nat, e)
        case yh <> yt:
          Nat.add(Nat.mul(xh, yh), dot(xt, yt, e))

# every row conforms to the vector: the matmul shape premise.
law Conform:
  for rows: List<&2, List<&2, Nat>>
  for +v: List<&2, Nat>
  Type

def Conform(rows, v):
  match rows:
    case Nil{}:
      Unit
    case r <> rs:
      (SameLen(r, v) & Conform(rs, v))

law matvec:
  for rows: List<&2, List<&2, Nat>>
  for +v: List<&2, Nat>
  for e: Conform(rows, v)
  List<&2, Nat>

def matvec(rows, v, e):
  match rows:
    case Nil{}:
      Nil{}
    case r <> rs:
      (h, t) = e
      dot(r, v, h) <> matvec(rs, v, t)


def main() -> List<&2, Nat>:
  matvec([[1n, 2n, 3n], [4n, 5n, 6n]], [1n, 0n, 2n], (Unit{}, (Unit{}, Unit{})))
