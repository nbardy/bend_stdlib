import Base
import ./bin.bend as Bin
import ./format.bend as Fmt
import ./num.bend as Num

# sf32.bend: binary32 floats in software, and the two F32 implementations.
#
#   import ./sf32.bend as SF32
#   SF32.add(a, b)          # software IEEE add on F32 bit patterns
#   SF32.soft(), SF32.hard() # Num.Impl<F32>: software, and hardware
#
# decode and encode convert between F32 bits (sign, 8 exponent bits, 23
# mantissa bits) and exact values. The software operations are the spec
# itself: decode, exact operation and rounding, encode. They compute in
# the checker and give the same bits on every backend; they are also far
# slower than hardware. A faster algorithm can be another Num.Impl.
#
# hard() uses Base's F32.add and F32.mul, which the checker cannot
# compute. HardOk is the assumption that they are correctly rounded:
# a law that needs it takes ~ok: HardOk, and it stays a named hypothesis.

def bits(x: F32) -> U32:
  match x:
    case F32{w}:
      U32{w}

def of_bits(x: U32) -> F32:
  match x:
    case U32{w}:
      F32{w}

# Decoding
# --------

def decode.cls(neg: Bool, ex: U32, fr: U32, top: Bool, low: Bool, fz: Bool) -> Fmt.Val:
  match top low fz:
    case True{} low True{}:
      Fmt.Inf{neg}
    case True{} low False{}:
      Fmt.NaN{}
    case False{} True{} True{}:
      Fmt.Z{neg}
    case False{} True{} False{}:
      Fmt.Fin{neg, Bin.of_u32(fr), 151n}
    case False{} False{} fz:
      Fmt.Fin{neg, Bin.of_u32(U32.add(fr, 8388608)), Nat.add(U32.to_nat(ex), 150n)}

def decode.go(neg: Bool, +ex: U32, +fr: U32) -> Fmt.Val:
  decode.cls(neg, ex, fr, U32.is_eq(ex, 255), U32.is_eq(ex, 0), U32.is_eq(fr, 0))

# the exact value of a float
def decode(x: F32) -> Fmt.Val:
  +b = bits(x)
  decode.go(U32.is_ne(U32.shrn(b, 31n), 0), U32.and(U32.shrn(b, 23n), 255), U32.and(b, 8388607))

# Encoding
# --------

def sign(neg: Bool) -> U32:
  match neg:
    case True{}:
      2147483648
    case False{}:
      0

def first(r: Bin.Bin & Bool & Bool) -> Bin.Bin:
  (q, a, b) = r
  q

# m moved to have its last bit at exponent t
def align(m: Bin.Bin, +e: Nat, +t: Nat, right: Bool) -> Bin.Bin:
  match right:
    case True{}:
      first(Bin.shr(Nat.sub(t, e), m, False{}, False{}))
    case False{}:
      Bin.shl(m, Nat.sub(e, t))

def field(+t: Nat, normal: Bool) -> U32:
  match normal:
    case True{}:
      U32.from_nat(Nat.sub(t, 150n))
    case False{}:
      0

def put(neg: Bool, t: Nat, +m: Bin.Bin) -> F32:
  of_bits(U32.or(sign(neg), U32.or(U32.shln(field(t, Nat.is_eq(Bin.len(m), 24n)), 23n), U32.and(Bin.to_u32(m), 8388607))))

# a finite value that fits binary32, as bits: 24 mantissa bits when
# normal, fewer at the smallest exponent when subnormal
def encode.fin(neg: Bool, +m: Bin.Bin, +e: Nat) -> F32:
  +t = Nat.max(Nat.sub(Nat.add(e, Bin.len(m)), 24n), 151n)
  put(neg, t, align(m, e, t, Nat.is_ge(t, e)))

def encode(v: Fmt.Val) -> F32:
  match v:
    case Fmt.Z{neg}:
      of_bits(sign(neg))
    case Fmt.Inf{neg}:
      of_bits(U32.or(sign(neg), 2139095040))
    case Fmt.NaN{}:
      of_bits(2143289344)
    case Fmt.Fin{neg, m, e}:
      encode.fin(neg, m, e)

# Software operations
# -------------------

def add(a: F32, b: F32) -> F32:
  encode(Fmt.spec_add(Fmt.binary32(), decode(a), decode(b)))

def sub(a: F32, b: F32) -> F32:
  encode(Fmt.spec_sub(Fmt.binary32(), decode(a), decode(b)))

def mul(a: F32, b: F32) -> F32:
  encode(Fmt.spec_mul(Fmt.binary32(), decode(a), decode(b)))

# Implementations
# ---------------

def soft() -> Num.Impl<F32>:
  Num.Impl{Fmt.binary32(), decode, add, mul}

def hard() -> Num.Impl<F32>:
  Num.Impl{Fmt.binary32(), decode, F32.add, F32.mul}

# the hardware assumption: Base's F32.add and F32.mul are correctly rounded
def HardOk() -> Type:
  Num.Correct<F32, hard()>
