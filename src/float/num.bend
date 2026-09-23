import Base
import ./format.bend as Fmt

# num.bend: the contract a float implementation meets.
#
#   import ./num.bend as Num
#
# An implementation is a carrier type T, the exact value each T stands
# for, and its operations. It is correctly rounded for its format when
# each operation's result stands for the spec result on the operands'
# values (AddOk, MulOk). Hardware F32 and the software SF32 are both
# implementations over the carrier F32 (see sf32.bend); anyone can add
# another carrier, format or algorithm, and code written against Impl
# works with all of them.

type Impl<-T: Data> is Type:
  Impl{fmt: Fmt.Format, value: T -> Fmt.Val, add: T -> T -> T, mul: T -> T -> T}

def Impl.fmt(-T: Data, i: Impl<T>) -> Fmt.Format:
  match i:
    case Impl{fmt, value, add, mul}:
      fmt

def Impl.value(-T: Data, i: Impl<T>, x: T) -> Fmt.Val:
  match i:
    case Impl{fmt, value, add, mul}:
      value(x)

def Impl.add(-T: Data, i: Impl<T>, a: T, b: T) -> T:
  match i:
    case Impl{fmt, value, add, mul}:
      add(a, b)

def Impl.mul(-T: Data, i: Impl<T>, a: T, b: T) -> T:
  match i:
    case Impl{fmt, value, add, mul}:
      mul(a, b)

# add is correctly rounded at a and b
def AddOk(~T: Data, ~i: Impl<T>, a: T, b: T) -> Type:
  {Fmt.canon(Impl.value(T, i, Impl.add(T, i, a, b))) == Fmt.canon(Fmt.spec_add(Impl.fmt(T, i), Impl.value(T, i, a), Impl.value(T, i, b))) : Fmt.Val}

# mul is correctly rounded at a and b
def MulOk(~T: Data, ~i: Impl<T>, a: T, b: T) -> Type:
  {Fmt.canon(Impl.value(T, i, Impl.mul(T, i, a, b))) == Fmt.canon(Fmt.spec_mul(Impl.fmt(T, i), Impl.value(T, i, a), Impl.value(T, i, b))) : Fmt.Val}

# an implementation that is correctly rounded everywhere
type Correct<-T: Data, -i: Impl<T>> is Type:
  Correct{add: @a: T -> @b: T -> AddOk(~T, ~i, a, b), mul: @a: T -> @b: T -> MulOk(~T, ~i, a, b)}
