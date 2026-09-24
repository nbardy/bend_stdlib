import Base
import ../nat.bend as Nat

# f32.bend: laws about Base's F32 functions, under named hardware
# hypotheses.
#
#   import ./f32.bend as F32
#   F32.clamp_le_hi(~lt, x, lo, hi, lh)   # clamp(x, lo, hi) <= hi, any x
#
# Base's F32 operations are unfilled laws, so the checker cannot compute
# them. Comparison and negation are specified here on the float's bits,
# where it can: lt_bits is IEEE 754's a < b, neg_bits flips the sign bit.
# A law about Base's F32.is_lt or F32.neg takes the hypothesis that the
# hardware matches them (~lt: LtOk(), ~ng: NegOk()) as a template
# argument, so each law states what it assumes. IEEE 754 comparison and
# negation are exact; C, CUDA, Metal and JS implement them this way.

def void(-A: Type, v: Empty) -> A:
  match v:

# {False == True} and {True == False} are empty
def no_f(e: {False{} == True{} : Bool}) -> Empty:
  %e : Nat.IsFalse(_)
  Unit{}

def no_t(e: {True{} == False{} : Bool}) -> Empty:
  %e : Nat.IsTrue(_)
  Unit{}

# Bits
# ----

def first(r: Word(31n) & Bool) -> Word(31n):
  (m, s) = r
  m

def split.cons(-n: Nat, b: Bool, r: Word(n) & Bool) -> Word(1n+n) & Bool:
  (w, s) = r
  (WCon{b, w}, s)

# a word's first n bits, and its last bit (the sign, for n = 31)
def split(n: Nat, w: Word(1n+n)) -> Word(n) & Bool:
  match n:
    case 0n:
      match w:
        case WCon{b, t}:
          (WNil{}, b)
    case 1n+p:
      match w:
        case WCon{b, t}:
          split.cons(p, b, split(p, t))

# a word with s appended as its last bit
def unsplit(n: Nat, w: Word(n), s: Bool) -> Word(1n+n):
  match n:
    case 0n:
      WCon{s, WNil{}}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{b, unsplit(p, t, s)}

law split_unsplit:
  for n: Nat
  for w: Word(n)
  for s: Bool
  {(w, s) == split(n, unsplit(n, w, s)) : Word(n) & Bool}

def split_unsplit(n, w, s):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, +t}:
          %split_unsplit(p, t, s) : {(WCon{b, t}, s) == split.cons(p, b, _) : Word(1n+p) & Bool}
          {==}

# the 31 bits below the sign: exponent and fraction
def mag(x: F32) -> Word(31n):
  match x:
    case F32{w}:
      first(split(31n, w))

def neg.go(r: Word(31n) & Bool) -> Word(32n):
  (m, s) = r
  unsplit(31n, m, Bool.not(s))

# IEEE 754 negation: the sign bit flipped
def neg_bits(x: F32) -> F32:
  match x:
    case F32{w}:
      F32{neg.go(split(31n, w))}

# Order
# -----

# how the IEEE order reads a float: NaN, or a number with a sign and a
# magnitude.
# Magnitudes are ordered as integers; above infinity's they are NaNs.
type Key is Data:
  KNaN{}
  Num{neg: Bool, mag: Word(31n)}

def IsKey(k: Key) -> Data:
  match k:
    case KNaN{}:
      Empty
    case Num{s, m}:
      Unit

# infinity's magnitude, 0x7F800000
def inf_mag.go(x: U32) -> F32:
  match x:
    case U32{w}:
      F32{w}

def inf_mag() -> F32:
  inf_mag.go(2139095040)

def key.cls(s: Bool, m: Word(31n), c: Cmp) -> Key:
  match c:
    case LT{}:
      Num{s, m}
    case EQ{}:
      Num{s, m}
    case GT{}:
      KNaN{}

def key.go(r: Word(31n) & Bool) -> Key:
  (+m, s) = r
  key.cls(s, m, Word.cmp(31n, m, mag(inf_mag())))

def key(x: F32) -> Key:
  match x:
    case F32{w}:
      key.go(split(31n, w))

def zero(m: Word(31n)) -> Bool:
  Cmp.is_eq(Word.cmp(31n, m, Word.zero(31n)))

def lt.signs(s: Bool, t: Bool, +x: Word(31n), +y: Word(31n)) -> Bool:
  match s t:
    case False{} False{}:
      Cmp.is_lt(Word.cmp(31n, x, y))
    case True{} True{}:
      Cmp.is_lt(Word.cmp(31n, y, x))
    case True{} False{}:
      Bool.not(Bool.and(zero(x), zero(y)))
    case False{} True{}:
      False{}

def lt.key(a: Key, b: Key) -> Bool:
  match a b:
    case KNaN{} KNaN{}:
      False{}
    case KNaN{} Num{t, y}:
      False{}
    case Num{s, x} KNaN{}:
      False{}
    case Num{s, x} Num{t, y}:
      lt.signs(s, t, x, y)

# IEEE 754 a < b: false when either is NaN; -0 and +0 are equal
def lt_bits(a: F32, b: F32) -> Bool:
  lt.key(key(a), key(b))

def NotGT(c: Cmp) -> Data:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      Unit
    case GT{}:
      Empty

def le.signs(s: Bool, t: Bool, +x: Word(31n), +y: Word(31n)) -> Type:
  match s t:
    case False{} False{}:
      NotGT(Word.cmp(31n, x, y))
    case True{} True{}:
      NotGT(Word.cmp(31n, y, x))
    case True{} False{}:
      Unit
    case False{} True{}:
      Nat.IsFalse(lt.signs(True{}, False{}, y, x))

def LE.key(a: Key, b: Key) -> Type:
  match a b:
    case KNaN{} KNaN{}:
      Empty
    case KNaN{} Num{t, y}:
      Empty
    case Num{s, x} KNaN{}:
      Empty
    case Num{s, x} Num{t, y}:
      le.signs(s, t, x, y)

# a <= b in the IEEE order, as a type: Empty when either is NaN
def LE(a: F32, b: F32) -> Type:
  LE.key(key(a), key(b))

# Order laws
# ----------

def swap(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

law bool_cmp_refl:
  for x: Bool
  {EQ{} == Bool.cmp(x, x) : Cmp}

def bool_cmp_refl(x):
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

law Word.cmp_refl:
  for +n: Nat
  for a: Word(n)
  {EQ{} == Word.cmp(n, a, a) : Cmp}

def Word.cmp_refl(n, a):
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{+x, +at}:
          %Word.cmp_refl(p, at) : {EQ{} == Word.cmp.fin(x, x, _) : Cmp}
          bool_cmp_refl(x)

law fin_swap:
  for c: Cmp
  for x: Bool
  for y: Bool
  {swap(Word.cmp.fin(x, y, c)) == Word.cmp.fin(y, x, swap(c)) : Cmp}

def fin_swap(c, x, y):
  match c x y:
    case LT{} x y:
      {==}
    case GT{} x y:
      {==}
    case EQ{} False{} False{}:
      {==}
    case EQ{} False{} True{}:
      {==}
    case EQ{} True{} False{}:
      {==}
    case EQ{} True{} True{}:
      {==}

law Word.cmp_swap:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  {swap(Word.cmp(n, a, b)) == Word.cmp(n, b, a) : Cmp}

def Word.cmp_swap(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          %Word.cmp_swap(p, at, bt) : {swap(Word.cmp.fin(x, y, Word.cmp(p, at, bt))) == Word.cmp.fin(y, x, _) : Cmp}
          fin_swap(Word.cmp(p, at, bt), x, y)

law lt_notgt:
  for c: Cmp
  {Cmp.is_lt(c) == True{} : Bool} -> NotGT(c)

def lt_notgt(c):
  match c:
    case LT{}:
      e => Unit{}
    case EQ{}:
      e => Unit{}
    case GT{}:
      e => no_f(e)

law notlt_swap:
  for c: Cmp
  {Cmp.is_lt(c) == False{} : Bool} -> NotGT(swap(c))

def notlt_swap(c):
  match c:
    case LT{}:
      e => no_t(e)
    case EQ{}:
      e => Unit{}
    case GT{}:
      e => Unit{}

law lt_le.signs:
  for s: Bool
  for t: Bool
  for +x: Word(31n)
  for +y: Word(31n)
  {lt.signs(s, t, x, y) == True{} : Bool} -> le.signs(s, t, x, y)

def lt_le.signs(s, t, x, y):
  match s t:
    case False{} False{}:
      lt_notgt(Word.cmp(31n, x, y))
    case True{} True{}:
      lt_notgt(Word.cmp(31n, y, x))
    case True{} False{}:
      e => Unit{}
    case False{} True{}:
      e => void(Nat.IsFalse(lt.signs(True{}, False{}, y, x)), no_f(e))

# a < b gives a <= b
law lt_le.key:
  for a: Key
  for b: Key
  {lt.key(a, b) == True{} : Bool} -> LE.key(a, b)

def lt_le.key(a, b):
  match a b:
    case KNaN{} KNaN{}:
      e => no_f(e)
    case KNaN{} Num{t, y}:
      e => no_f(e)
    case Num{s, x} KNaN{}:
      e => no_f(e)
    case Num{s, x} Num{t, y}:
      lt_le.signs(s, t, x, y)

# only an ordered value is below something
law lt_key:
  for a: Key
  for b: Key
  {lt.key(a, b) == True{} : Bool} -> IsKey(a)

def lt_key(a, b):
  match a b:
    case KNaN{} KNaN{}:
      e => no_f(e)
    case KNaN{} Num{t, y}:
      e => no_f(e)
    case Num{s, x} KNaN{}:
      e => Unit{}
    case Num{s, x} Num{t, y}:
      e => Unit{}

law le_key_l:
  for a: Key
  for b: Key
  LE.key(a, b) -> IsKey(a)

def le_key_l(a, b):
  match a b:
    case KNaN{} KNaN{}:
      l => l
    case KNaN{} Num{t, y}:
      l => l
    case Num{s, x} KNaN{}:
      l => Unit{}
    case Num{s, x} Num{t, y}:
      l => Unit{}

law le_key_r:
  for a: Key
  for b: Key
  LE.key(a, b) -> IsKey(b)

def le_key_r(a, b):
  match a b:
    case KNaN{} KNaN{}:
      l => l
    case KNaN{} Num{t, y}:
      l => void(Unit, l)
    case Num{s, x} KNaN{}:
      l => l
    case Num{s, x} Num{t, y}:
      l => Unit{}

law le_refl.signs:
  for s: Bool
  for +m: Word(31n)
  le.signs(s, s, m, m)

def le_refl.signs(s, m):
  match s:
    case False{}:
      %Word.cmp_refl(31n, m) : NotGT(_)
      Unit{}
    case True{}:
      %Word.cmp_refl(31n, m) : NotGT(_)
      Unit{}

law le_refl.key:
  for k: Key
  IsKey(k) -> LE.key(k, k)

def le_refl.key(k):
  match k:
    case KNaN{}:
      h => h
    case Num{s, m}:
      h => le_refl.signs(s, m)

law total.same:
  for +x: Word(31n)
  for +y: Word(31n)
  for e: {Cmp.is_lt(Word.cmp(31n, x, y)) == False{} : Bool}
  NotGT(Word.cmp(31n, y, x))

def total.same(x, y, e):
  %Word.cmp_swap(31n, x, y) : NotGT(_)
  notlt_swap(Word.cmp(31n, x, y))(e)

law total.mixed:
  for +x: Word(31n)
  for +y: Word(31n)
  for e: {lt.signs(True{}, False{}, x, y) == False{} : Bool}
  Nat.IsFalse(lt.signs(True{}, False{}, x, y))

def total.mixed(x, y, e):
  %Equal.sym(Bool, lt.signs(True{}, False{}, x, y), False{}, e) : Nat.IsFalse(_)
  Unit{}

law total.signs:
  for s: Bool
  for t: Bool
  for +x: Word(31n)
  for +y: Word(31n)
  {lt.signs(s, t, x, y) == False{} : Bool} -> le.signs(t, s, y, x)

def total.signs(s, t, x, y):
  match s t:
    case False{} False{}:
      e => total.same(x, y, e)
    case True{} True{}:
      e => total.same(y, x, e)
    case True{} False{}:
      e => total.mixed(x, y, e)
    case False{} True{}:
      e => Unit{}

# two ordered values: not a < b gives b <= a
law total.key:
  for a: Key
  for b: Key
  IsKey(a) -> IsKey(b) -> {lt.key(a, b) == False{} : Bool} -> LE.key(b, a)

def total.key(a, b):
  match a b:
    case KNaN{} KNaN{}:
      ha => hb => e => ha
    case KNaN{} Num{t, y}:
      ha => hb => e => ha
    case Num{s, x} KNaN{}:
      ha => hb => e => hb
    case Num{s, x} Num{t, y}:
      ha => hb => total.signs(s, t, x, y)

# Laws about Base's F32
# ---------------------

# the hardware's < is IEEE 754's
def LtOk() -> Type:
  @a: F32 -> @b: F32 -> {F32.is_lt(a, b) == lt_bits(a, b) : Bool}

# the hardware's negation flips the sign bit of every non-NaN float. A
# NaN's sign and payload are left out: the JS lane does not keep them.
def NegOk() -> Type:
  @a: F32 -> IsKey(key(a)) -> {F32.neg(a) == neg_bits(a) : F32}

law bits_lt:
  for ~lt: LtOk()
  for +a: F32
  for +b: F32
  for -c: Bool
  for e: {F32.is_lt(a, b) == c : Bool}
  {lt_bits(a, b) == c : Bool}

def bits_lt(lt, a, b, c, e):
  %lt(a, b) : {_ == c : Bool}
  e

# Base's F32.min(a, b) is Bool.pick(F32.is_lt(a, b), a, b); as in
# u32.bend, each .go lemma takes the test's result c and its equation.

law min_le_r.go:
  for ~lt: LtOk()
  for +a: F32
  for +b: F32
  for c: Bool
  for e: {F32.is_lt(a, b) == c : Bool}
  for bb: LE(b, b)
  LE(Bool.pick(F32, c, a, b), b)

def min_le_r.go(lt, a, b, c, e, bb):
  match c:
    case True{}:
      lt_le.key(key(a), key(b))(bits_lt(~lt, a, b, True{}, e))
    case False{}:
      bb

# clamp(x, lo, hi) <= hi for every x, NaN and infinities included
law clamp_le_hi:
  for ~lt: LtOk()
  for +x: F32
  for +lo: F32
  for +hi: F32
  for lh: LE(lo, hi)
  LE(F32.clamp(x, lo, hi), hi)

def clamp_le_hi(lt, x, lo, hi, lh):
  +m = F32.max(x, lo)
  min_le_r.go(~lt, m, hi, F32.is_lt(m, hi), {==}, le_refl.key(key(hi))(le_key_r(key(lo), key(hi))(lh)))

law lo_le_clamp.go:
  for ~lt: LtOk()
  for +x: F32
  for +lo: F32
  for +hi: F32
  for c1: Bool
  for e1: {F32.is_lt(x, lo) == c1 : Bool}
  for c2: Bool
  for e2: {F32.is_lt(Bool.pick(F32, c1, lo, x), hi) == c2 : Bool}
  for lh: LE(lo, hi)
  LE(lo, Bool.pick(F32, c2, Bool.pick(F32, c1, lo, x), hi))

def lo_le_clamp.go(lt, x, lo, hi, c1, e1, c2, e2, lh):
  match c1 c2:
    case True{} True{}:
      le_refl.key(key(lo))(le_key_l(key(lo), key(hi))(lh))
    case False{} True{}:
      total.key(key(x), key(lo))(lt_key(key(x), key(hi))(bits_lt(~lt, x, hi, True{}, e2)))(le_key_l(key(lo), key(hi))(lh))(bits_lt(~lt, x, lo, False{}, e1))
    case True{} False{}:
      lh
    case False{} False{}:
      lh

# lo <= clamp(x, lo, hi) for every x, when lo <= hi
law lo_le_clamp:
  for ~lt: LtOk()
  for +x: F32
  for +lo: F32
  for +hi: F32
  for lh: LE(lo, hi)
  LE(lo, F32.clamp(x, lo, hi))

def lo_le_clamp(lt, x, lo, hi, lh):
  lo_le_clamp.go(~lt, x, lo, hi, F32.is_lt(x, lo), {==}, F32.is_lt(F32.max(x, lo), hi), {==}, lh)

# Negation
# --------

law neg_mag.go:
  for r: Word(31n) & Bool
  {first(r) == first(split(31n, neg.go(r))) : Word(31n)}

def neg_mag.go(r):
  (+m, +s) = r
  Equal.cong(Word(31n) & Bool, Word(31n), first, (m, Bool.not(s)), split(31n, unsplit(31n, m, Bool.not(s))), split_unsplit(31n, m, Bool.not(s)))

law neg_mag.bits:
  for a: F32
  {mag(a) == mag(neg_bits(a)) : Word(31n)}

def neg_mag.bits(a):
  match a:
    case F32{w}:
      neg_mag.go(split(31n, w))

# |-a| is |a|, bit for bit
law neg_mag:
  for ~ng: NegOk()
  for +a: F32
  for ka: IsKey(key(a))
  {mag(a) == mag(F32.neg(a)) : Word(31n)}

def neg_mag(ng, a, ka):
  %Equal.sym(F32, F32.neg(a), neg_bits(a), ng(a, ka)) : {mag(a) == mag(_) : Word(31n)}
  neg_mag.bits(a)

# whether a value is NaN does not depend on its sign
law key_sign:
  for s: Bool
  for t: Bool
  for m: Word(31n)
  for c: Cmp
  IsKey(key.cls(s, m, c)) -> IsKey(key.cls(t, m, c))

def key_sign(s, t, m, c):
  match c:
    case LT{}:
      h => Unit{}
    case EQ{}:
      h => Unit{}
    case GT{}:
      h => h

law neg_key.go:
  for r: Word(31n) & Bool
  IsKey(key.go(r)) -> IsKey(key.go(split(31n, neg.go(r))))

def neg_key.go(r):
  (+m, +s) = r
  %split_unsplit(31n, m, Bool.not(s)) : IsKey(key.go((m, s))) -> IsKey(key.go(_))
  key_sign(s, Bool.not(s), m, Word.cmp(31n, m, mag(inf_mag())))

law neg_key.bits:
  for a: F32
  IsKey(key(a)) -> IsKey(key(neg_bits(a)))

def neg_key.bits(a):
  match a:
    case F32{w}:
      neg_key.go(split(31n, w))

# the negation of a non-NaN is not NaN
law neg_key:
  for ~ng: NegOk()
  for +a: F32
  for +ka: IsKey(key(a))
  IsKey(key(F32.neg(a)))

def neg_key(ng, a, ka):
  %Equal.sym(F32, F32.neg(a), neg_bits(a), ng(a, ka)) : IsKey(key(_))
  neg_key.bits(a)(ka)
