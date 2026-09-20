import Base
import ../src/perfect.bend as P

# Oracles (U32 ground values):
#   dbl(0)=1  dbl(1)=2  dbl(2)=4  dbl(3)=8
#   size(Array.new(Nat,2n,7n)) = 4  (depth-2 tree, 4 leaves)
# Perfect/size_node laws are proved by checking; these pin dbl
# and the size projection they compose.

def check(tag: String, ok: Bool) -> IO(Unit):
  IO.print(tag ++ Bool.pick(String, ok, ": PASS", ": FAIL"))

def main() -> IO(Unit):
  do IO<Unit>:
    check("dbl_0", U32.is_eq(P.dbl(0n), 1))
    check("dbl_1", U32.is_eq(P.dbl(1n), 2))
    check("dbl_2", U32.is_eq(P.dbl(2n), 4))
    check("dbl_3", U32.is_eq(P.dbl(3n), 8))
    check("size_new_2", U32.is_eq(P.snd_size(Nat, Array.size(Nat, Array.new(Nat, 2n, 7n))), 4))
