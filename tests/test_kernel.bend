import Base
import ../src/kernel.bend as K

# Oracles:
#   dot([1,2,3],[1,0,2]) = 1+0+6 = 7        (evidence: Unit{})
#   matvec([[1,2,3],[4,5,6]],[1,0,2]) = [7,16]
#   SMin(4,9) = 4
# SameLen evidence reduces definitionally (Unit at the base), so
# concrete calls pass Unit{}; Conform evidence nests one per row.

def check(tag: String, ok: Bool) -> IO(Unit):
  IO.print(tag ++ Bool.pick(String, ok, ": PASS", ": FAIL"))

def eq_nats(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} _ <> _:
      False{}
    case _ <> _ Nil{}:
      False{}
    case x <> xt y <> yt:
      Bool.and(Nat.is_eq(x, y), eq_nats(xt, yt))

def main() -> IO(Unit):
  do IO<Unit>:
    check("dot_7", Nat.is_eq(K.dot([1n, 2n, 3n], [1n, 0n, 2n], Unit{}), 7n))
    check("matvec_7_16", eq_nats(K.matvec([[1n, 2n, 3n], [4n, 5n, 6n]], [1n, 0n, 2n], (Unit{}, (Unit{}, Unit{}))), [7n, 16n]))
    check("smin_4_9", Nat.is_eq(K.SMin(4n, 9n), 4n))
