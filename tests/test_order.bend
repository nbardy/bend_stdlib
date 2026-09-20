import Base
import ../src/order.bend as O

# Oracles (Nat ground values):
#   SMax(3,5)=5  SMin(3,5)=3  SMax(5,3)=5  SMin(5,3)=3
#   SMax(0,0)=0  SMin(0,7)=0  SMax(7,0)=7
# Laws (and_false/comm, cmp_refl, ...) are proved by checking;
# these tests pin the computational twins they transport from.

def check(tag: String, ok: Bool) -> IO(Unit):
  IO.print(tag ++ Bool.pick(String, ok, ": PASS", ": FAIL"))

def eq(got: Nat, want: Nat) -> Bool:
  Nat.is_eq(got, want)

def main() -> IO(Unit):
  do IO<Unit>:
    check("smax_3_5", eq(O.SMax(3n, 5n), 5n))
    check("smin_3_5", eq(O.SMin(3n, 5n), 3n))
    check("smax_5_3", eq(O.SMax(5n, 3n), 5n))
    check("smin_5_3", eq(O.SMin(5n, 3n), 3n))
    check("smax_0_0", eq(O.SMax(0n, 0n), 0n))
    check("smin_0_7", eq(O.SMin(0n, 7n), 0n))
    check("smax_7_0", eq(O.SMax(7n, 0n), 7n))
