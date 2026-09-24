import Base
import ../src/float/format.bend as Fmt
import ../src/float/num.bend as Num
import ../src/float/sf32.bend as SF32
import ../src/float/f32.bend as F32

# sf32.bend: software binary32 checked two ways.
#
# In the checker: float facts that Base's axiomatic F32 cannot state close
# by {==}, because SF32 computes.
#
# At run time: SF32.add and SF32.mul against the hardware's F32.add and
# F32.mul, and F32.lt_bits and F32.neg_bits against F32.is_lt and F32.neg
# (the hypotheses LtOk and NegOk), on random bit patterns (every exponent, subnormals, infinities,
# NaNs) and on hand-picked edge cases. A mismatch means the spec in
# format.bend differs from IEEE 754 as the backend implements it.

# 1.5 + 2.25 is exactly 3.75
law add_exact:
  {SF32.add(1.5, 2.25) == 3.75 : F32}

def add_exact():
  {==}

# 0.1 + 0.2 rounds to the float just above 0.3 (0x3E99999A)
law add_rounds:
  {SF32.bits(SF32.add(0.1, 0.2)) == 1050253722 : U32}

def add_rounds():
  {==}

# the software implementation meets the contract at a point
law soft_ok:
  Num.AddOk(~F32, ~SF32.soft(), 0.1, 0.2)

def soft_ok():
  {==}

# Differential test
# -----------------

def next(x: U32) -> U32:
  U32.add(U32.mul(x, 1664525), 1013904223)

def is_nan(+x: F32) -> Bool:
  Bool.and(U32.is_eq(U32.and(SF32.bits(x), 2139095040), 2139095040), U32.is_ne(U32.and(SF32.bits(x), 8388607), 0))

def same(+a: F32, +b: F32) -> Bool:
  Bool.or(U32.is_eq(SF32.bits(a), SF32.bits(b)), Bool.and(is_nan(a), is_nan(b)))

def bump(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      n
    case False{}:
      1n+n

# negation is compared bit for bit on non-NaNs (NegOk leaves NaNs out)
def exact(+a: F32, +b: F32) -> Bool:
  Bool.or(U32.is_eq(SF32.bits(a), SF32.bits(b)), is_nan(a))

def pair(+a: F32, +b: F32, n: Nat) -> Nat:
  +m = bump(same(SF32.mul(a, b), F32.mul(a, b)), bump(same(SF32.add(a, b), F32.add(a, b)), n))
  bump(exact(F32.neg_bits(a), F32.neg(a)), bump(Bool.not(Bool.xor(F32.lt_bits(a, b), F32.is_lt(a, b))), m))

# mismatches over k random pairs
def random(k: Nat, +s: U32, n: Nat) -> Nat:
  match k:
    case 0n:
      n
    case 1n+j:
      +s1 = next(s)
      +s2 = next(s1)
      random(j, s2, pair(SF32.of_bits(s1), SF32.of_bits(s2), n))

def cross.row(+x: F32, ys: List<&2, F32>, n: Nat) -> Nat:
  match ys:
    case Nil{}:
      n
    case +y <> t:
      cross.row(x, t, pair(x, y, n))

# mismatches over every pair of the list
def cross(xs: List<&2, F32>, +ys: List<&2, F32>, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case +x <> t:
      cross(t, ys, cross.row(x, ys, n))

# zeros, ones, halfway cases, the smallest and largest subnormals and
# normals, the largest finite, infinity, NaN, and values that cancel
def edges() -> List<&2, F32>:
  [0.0, SF32.of_bits(2147483648), 1.0, SF32.of_bits(3212836864), 0.1, 0.2, 0.3, 3.0, 16777216.0, 16777217.0, 0.5, 1.5, 2.5,
   SF32.of_bits(1), SF32.of_bits(8388607), SF32.of_bits(8388608), SF32.of_bits(2139095039), SF32.of_bits(4286578687),
   SF32.of_bits(2139095040), SF32.of_bits(4286578688), SF32.of_bits(2143289344), 1.0000001, 0.9999999, 33554430.0]

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("edge mismatches   " ++ Nat.show(cross(edges(), edges(), 0n)))
    IO.print("random mismatches " ++ Nat.show(random(3000n, 12345, 0n)))

#|edge mismatches   0
#|random mismatches 0
