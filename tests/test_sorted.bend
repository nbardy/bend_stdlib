import Base
import ../src/sorted.bend as S

# Oracles:
#   isort([2,0,1]) = [0,1,2]
#   isort([]) = []   isort([1]) = [1]   isort([3,3,1]) = [1,3,3]
#   isort([5,4,3,2,1,0]) = [0,1,2,3,4,5]
#   LL.length([9,8]) = 2
# Sortedness/length-preservation are proved by checking; these pin
# the computational sort on ties, empties, and a longer input.

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
    check("isort_201", eq_nats(S.isort([2n, 0n, 1n]), [0n, 1n, 2n]))
    check("isort_nil", eq_nats(S.isort(Nil{}), Nil{}))
    check("isort_1", eq_nats(S.isort([1n]), [1n]))
    check("isort_ties", eq_nats(S.isort([3n, 3n, 1n]), [1n, 3n, 3n]))
    check("isort_543210", eq_nats(S.isort([5n, 4n, 3n, 2n, 1n, 0n]), [0n, 1n, 2n, 3n, 4n, 5n]))
    check("len_2", Nat.is_eq(S.LL.length(Nat, [9n, 8n]), 2n))
