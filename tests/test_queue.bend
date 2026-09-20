import Base
import ../src/queue.bend as Q

# Oracles (pop takes fuel; 1+len suffices, 0 answers None):
#   pop(3,[1,2]) -> Some{1}, rest to_list [2], rest len 1
#   pop(3,Q{Nil,[3,2]}) -> Some{2} (rotation), rest to_list [3], len 1
#   pop(3,empty) -> None (getor sentinel 999)
#   pop(0,[1,2]) -> None (out of fuel)
#   to_list(push(push(empty,1),2)) = [1,2], len 2
# pop_cons/pop_rotate/pop_empty + len_push/to_list_push prove by
# checking; these pin dispatch, rotation, and fuel behavior.

def check(tag: String, ok: Bool) -> IO(Unit):
  IO.print(tag ++ Bool.pick(String, ok, ": PASS", ": FAIL"))

def getor(p: Q.Queue & Maybe<Nat>) -> Nat:
  (q2, m) = p
  match m:
    case None{}:
      999n
    case Some{v}:
      v

def restlen(p: Q.Queue & Maybe<Nat>) -> Nat:
  (q2, m) = p
  Q.qlen_total(q2)

def restlist(p: Q.Queue & Maybe<Nat>) -> List<&2, Nat>:
  (q2, m) = p
  Q.to_list(q2)

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
    check("pop_value", Nat.is_eq(getor(Q.pop(3n, Q.push(Q.push(Q.empty(), 1n), 2n))), 1n))
    check("pop_rest", eq_nats(restlist(Q.pop(3n, Q.push(Q.push(Q.empty(), 1n), 2n))), [2n]))
    check("pop_rest_len", Nat.is_eq(restlen(Q.pop(3n, Q.push(Q.push(Q.empty(), 1n), 2n))), 1n))
    check("rotate_value", Nat.is_eq(getor(Q.pop(3n, Q.Q{Nil{}, [3n, 2n]})), 2n))
    check("rotate_rest", eq_nats(restlist(Q.pop(3n, Q.Q{Nil{}, [3n, 2n]})), [3n]))
    check("empty_none", Nat.is_eq(getor(Q.pop(3n, Q.empty())), 999n))
    check("fuel_none", Nat.is_eq(getor(Q.pop(0n, Q.push(Q.push(Q.empty(), 1n), 2n))), 999n))
    check("fifo_list", eq_nats(Q.to_list(Q.push(Q.push(Q.empty(), 1n), 2n)), [1n, 2n]))
