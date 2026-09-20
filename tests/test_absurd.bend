import Base
import ../src/absurd.bend as A

# The absurdity laws discharge impossible arms; their premises are
# uninhabited by construction, so these tests prove BY CHECKING:
#   wilful: a concrete contradiction ({is_lt(0,0)==True}, i.e.
#     {False==True} definitionally) derives a value.
#   motive checks: IsFalse/IsZero reduce on constructors.
# If any motive direction were wrong, this file would not check.

def wilful(e: {Nat.is_lt(0n, 0n) == True{} : Bool}) -> Array<Nat>:
  A.bool_absurd(Array<Nat>, e)

def t_false() -> A.Bool.IsFalse(False{}):
  Unit{}

def t_zero() -> A.Nat.IsZero(0n):
  Unit{}

def check(tag: String, ok: Bool) -> IO(Unit):
  IO.print(tag ++ Bool.pick(String, ok, ": PASS", ": FAIL"))

def main() -> IO(Unit):
  do IO<Unit>:
    u = t_false()
    z = t_zero()
    check("motives_reduce", True{})
