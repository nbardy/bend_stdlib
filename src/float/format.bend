import Base
import ./bin.bend as Bin

# format.bend: what IEEE float operations mean, for any binary format.
#
#   import ./format.bend as Fmt
#
# A value is exact: m * 2^(e - 300) with m a binary natural, plus signed
# zeros, infinities and NaN. A Format says how many mantissa bits there
# are and which exponents exist; round fits an exact value into a format
# (to nearest, ties to even). The spec_ functions are the IEEE 754
# operations on values: the exact result, then round. Every NaN is the
# same value, so NaN bit patterns (which differ between backends) never
# reach a law.
#
# The exponent is a Nat offset by 300, which covers every binary32 value
# and every product of two, and keeps exponents small enough for the
# checker's unary Nat.

type Val is Data:
  Z{neg: Bool}
  Inf{neg: Bool}
  NaN{}
  Fin{neg: Bool, m: Bin.Bin, e: Nat}

# p: mantissa bits; emin, emax: lowest and highest exponent (offset by
# 300) of a mantissa's last bit
type Format is Data:
  Format{p: Nat, emin: Nat, emax: Nat}

# binary32: 24 bits; smallest subnormal 2^-149; largest 2^104 * (2^24 - 1)
def binary32() -> Format:
  Format{24n, 151n, 404n}

# the same value with its low zero bits moved into the exponent and its
# high zero bits dropped, so that equal values are equal terms
def strip(neg: Bool, m: Bin.Bin, e: Nat) -> Val:
  match m:
    case Bin.BZ{}:
      Z{neg}
    case Bin.B0{r}:
      strip(neg, r, 1n+e)
    case Bin.B1{r}:
      Fin{neg, Bin.B1{Bin.trim(r)}, e}

def canon(v: Val) -> Val:
  match v:
    case Z{neg}:
      Z{neg}
    case Inf{neg}:
      Inf{neg}
    case NaN{}:
      NaN{}
    case Fin{neg, m, e}:
      strip(neg, m, e)

# Rounding
# --------

def over.go(neg: Bool, m: Bin.Bin, e: Nat, zero: Bool, big: Bool) -> Val:
  match zero big:
    case True{} big:
      Z{neg}
    case False{} True{}:
      Inf{neg}
    case False{} False{}:
      Fin{neg, m, e}

def over(+top: Nat, neg: Bool, +m: Bin.Bin, +e: Nat) -> Val:
  over.go(neg, m, e, Bin.is_zero(m), Nat.is_gt(Nat.add(e, Bin.len(m)), top))

def round.up(q: Bin.Bin, up: Bool) -> Bin.Bin:
  match up:
    case True{}:
      Bin.inc(q)
    case False{}:
      q

def round.fin(+top: Nat, neg: Bool, +t: Nat, qrs: Bin.Bin & Bool & Bool) -> Val:
  (+q, r, s) = qrs
  over(top, neg, round.up(q, Bool.and(r, Bool.or(s, Bin.odd(q)))), t)

def round.go(+top: Nat, neg: Bool, m: Bin.Bin, +e: Nat, +t: Nat, exact: Bool) -> Val:
  match exact:
    case True{}:
      over(top, neg, m, e)
    case False{}:
      round.fin(top, neg, t, Bin.shr(Nat.sub(t, e), m, False{}, False{}))

# the float of format f nearest to (-1)^neg * m * 2^(e - 300), ties to even
def round(f: Format, neg: Bool, +m: Bin.Bin, +e: Nat) -> Val:
  Format{+p, emin, emax} = f
  +t = Nat.max(Nat.sub(Nat.add(e, Bin.len(m)), p), emin)
  round.go(Nat.add(emax, p), neg, m, e, t, Nat.is_le(t, e))

# Addition
# --------

# add two finite values once their mantissas share the exponent e
def add.fin.cmp(f: Format, na: Bool, nb: Bool, a: Bin.Bin, b: Bin.Bin, e: Nat, c: Cmp) -> Val:
  match c:
    case LT{}:
      round(f, nb, Bin.sub(b, a), e)
    case EQ{}:
      Z{False{}}
    case GT{}:
      round(f, na, Bin.sub(a, b), e)

def add.fin.signs(f: Format, na: Bool, nb: Bool, +a: Bin.Bin, +b: Bin.Bin, e: Nat, differ: Bool) -> Val:
  match differ:
    case False{}:
      round(f, na, Bin.add(a, b), e)
    case True{}:
      add.fin.cmp(f, na, nb, a, b, e, Bin.cmp(a, b))

def add.fin.aligned(f: Format, +na: Bool, +nb: Bool, a: Bin.Bin, b: Bin.Bin, e: Nat) -> Val:
  add.fin.signs(f, na, nb, a, b, e, Bool.xor(na, nb))

def add.fin.go(f: Format, na: Bool, a: Bin.Bin, +ea: Nat, nb: Bool, b: Bin.Bin, +eb: Nat, a_high: Bool) -> Val:
  match a_high:
    case True{}:
      add.fin.aligned(f, na, nb, Bin.shl(a, Nat.sub(ea, eb)), b, eb)
    case False{}:
      add.fin.aligned(f, na, nb, a, Bin.shl(b, Nat.sub(eb, ea)), ea)

def add.fin(f: Format, na: Bool, a: Bin.Bin, +ea: Nat, b: Val) -> Val:
  match b:
    case Z{nb}:
      Fin{na, a, ea}
    case Inf{nb}:
      Inf{nb}
    case NaN{}:
      NaN{}
    case Fin{nb, mb, +eb}:
      add.fin.go(f, na, a, ea, nb, mb, eb, Nat.is_ge(ea, eb))

def add.inf.go(na: Bool, differ: Bool) -> Val:
  match differ:
    case True{}:
      NaN{}
    case False{}:
      Inf{na}

def add.inf(+na: Bool, b: Val) -> Val:
  match b:
    case Inf{+nb}:
      add.inf.go(na, Bool.xor(na, nb))
    case NaN{}:
      NaN{}
    case Z{nb}:
      Inf{na}
    case Fin{nb, mb, eb}:
      Inf{na}

def add.zero(na: Bool, b: Val) -> Val:
  match b:
    case Z{nb}:
      Z{Bool.and(na, nb)}
    case Inf{nb}:
      Inf{nb}
    case NaN{}:
      NaN{}
    case Fin{nb, mb, eb}:
      Fin{nb, mb, eb}

# IEEE addition: the exact sum, rounded; x + (-x) is +0
def spec_add(f: Format, a: Val, b: Val) -> Val:
  match a:
    case NaN{}:
      NaN{}
    case Inf{na}:
      add.inf(na, b)
    case Z{na}:
      add.zero(na, b)
    case Fin{na, ma, ea}:
      add.fin(f, na, ma, ea, b)

def neg(v: Val) -> Val:
  match v:
    case Z{n}:
      Z{Bool.not(n)}
    case Inf{n}:
      Inf{Bool.not(n)}
    case NaN{}:
      NaN{}
    case Fin{n, m, e}:
      Fin{Bool.not(n), m, e}

def spec_sub(f: Format, a: Val, b: Val) -> Val:
  spec_add(f, a, neg(b))

# Multiplication
# --------------

def mul.fin(f: Format, na: Bool, a: Bin.Bin, ea: Nat, b: Val) -> Val:
  match b:
    case Z{nb}:
      Z{Bool.xor(na, nb)}
    case Inf{nb}:
      Inf{Bool.xor(na, nb)}
    case NaN{}:
      NaN{}
    case Fin{nb, mb, eb}:
      round(f, Bool.xor(na, nb), Bin.mul(a, mb), Nat.sub(Nat.add(ea, eb), 300n))

def mul.inf(na: Bool, b: Val) -> Val:
  match b:
    case Z{nb}:
      NaN{}
    case Inf{nb}:
      Inf{Bool.xor(na, nb)}
    case NaN{}:
      NaN{}
    case Fin{nb, mb, eb}:
      Inf{Bool.xor(na, nb)}

def mul.zero(na: Bool, b: Val) -> Val:
  match b:
    case Z{nb}:
      Z{Bool.xor(na, nb)}
    case Inf{nb}:
      NaN{}
    case NaN{}:
      NaN{}
    case Fin{nb, mb, eb}:
      Z{Bool.xor(na, nb)}

# IEEE multiplication: the exact product, rounded
def spec_mul(f: Format, a: Val, b: Val) -> Val:
  match a:
    case NaN{}:
      NaN{}
    case Inf{na}:
      mul.inf(na, b)
    case Z{na}:
      mul.zero(na, b)
    case Fin{na, ma, ea}:
      mul.fin(f, na, ma, ea, b)
