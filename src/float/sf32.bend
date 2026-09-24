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
# The fields are read off the word in one pass (23 mantissa bits, 8
# exponent bits, the sign), not with U32 shifts and masks: the checker
# evaluates a U32 operation bit by bit, and each shift costs a full pass.

def decode.go(neg: Bool, e: Nat, f: Bin.Bin, top: Bool, low: Bool, fz: Bool) -> Fmt.Val:
  match top low fz:
    case True{} low True{}:
      Fmt.Inf{neg}
    case True{} low False{}:
      Fmt.NaN{}
    case False{} True{} True{}:
      Fmt.Z{neg}
    case False{} True{} False{}:
      Fmt.Fin{neg, f, 151n}
    case False{} False{} fz:
      Fmt.Fin{neg, Bin.add(f, Bin.pow2(23n)), Nat.add(e, 150n)}

def decode.cls(neg: Bool, +e: Nat, +f: Bin.Bin) -> Fmt.Val:
  decode.go(neg, e, f, Nat.is_eq(e, 255n), Nat.is_eq(e, 0n), Bin.is_zero(f))

def decode.sign(f: Bin.Bin, e: Bin.Bin, w: Word(1n)) -> Fmt.Val:
  match w:
    case WCon{s, t}:
      decode.cls(s, Bin.to_nat(e), f)

def decode.exp(f: Bin.Bin, p: Bin.Bin & Word(1n)) -> Fmt.Val:
  (e, w) = p
  decode.sign(f, e, w)

def decode.man(p: Bin.Bin & Word(9n)) -> Fmt.Val:
  (f, w) = p
  decode.exp(f, Bin.take(8n, 1n, w))

# the exact value of a float
def decode(x: F32) -> Fmt.Val:
  match x:
    case F32{w}:
      decode.man(Bin.take(23n, 9n, w))

# Encoding
# --------

# the sign bit, as it sits above the 8 exponent bits
def sign(neg: Bool) -> Bin.Bin:
  match neg:
    case True{}:
      Bin.pow2(8n)
    case False{}:
      Bin.BZ{}

# a word from its fields: 23 mantissa bits, then exponent and sign above
def word(frac: Bin.Bin, exp: Bin.Bin, neg: Bool) -> F32:
  F32{Bin.to_word(32n, Bin.add(Bin.low(23n, frac), Bin.shl(Bin.add(exp, sign(neg)), 23n)))}

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

def field(+t: Nat, normal: Bool) -> Bin.Bin:
  match normal:
    case True{}:
      Bin.of_nat(Nat.sub(t, 150n))
    case False{}:
      Bin.BZ{}

def put(neg: Bool, t: Nat, +m: Bin.Bin) -> F32:
  word(m, field(t, Nat.is_eq(Bin.len(m), 24n)), neg)

# a finite value that fits binary32, as bits: 24 mantissa bits when
# normal, fewer at the smallest exponent when subnormal
def encode.fin(neg: Bool, +m: Bin.Bin, +e: Nat) -> F32:
  +t = Nat.max(Nat.sub(Nat.add(e, Bin.len(m)), 24n), 151n)
  put(neg, t, align(m, e, t, Nat.is_ge(t, e)))

def encode(v: Fmt.Val) -> F32:
  match v:
    case Fmt.Z{neg}:
      word(Bin.BZ{}, Bin.BZ{}, neg)
    case Fmt.Inf{neg}:
      word(Bin.BZ{}, Bin.of_nat(255n), neg)
    case Fmt.NaN{}:
      of_bits(2143289344) # 0x7FC00000, the quiet NaN
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

# |x|: the sign bit cleared. Exact, like negation.
def abs(x: F32) -> F32:
  of_bits(U32.and(bits(x), 2147483647)) # 0x7FFFFFFF
