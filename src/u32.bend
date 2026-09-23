import Base
import ./nat.bend as Nat
import ./class.bend as C

# u32.bend: U32 laws that hold for every input.
#
#   import ./u32.bend as U32
#
# cmp_nat says U32.cmp(a, b) is Nat.cmp of the two numbers; it is proven
# by induction on the word width. The laws after it use it to reduce U32
# order to Nat order. LE(a, b) is Nat.LE on the numbers. The clamp laws
# are about Base's own U32.min, U32.max and U32.clamp. sub_add and add_sub
# say wrapping + and - undo each other.

def bit(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

# comparing bit + 2*rest compares the rests first, then the bits, which is
# what Word.cmp.fin does
law cmp_bits:
  for x: Bool
  for y: Bool
  for a: Nat
  for b: Nat
  {Word.cmp.fin(x, y, Nat.cmp(a, b)) == Nat.cmp(Nat.add(bit(x), Nat.double(a)), Nat.add(bit(y), Nat.double(b))) : Cmp}

def cmp_bits(x, y, a, b):
  match x y a b:
    case False{} False{} 0n 0n:
      {==}
    case False{} True{} 0n 0n:
      {==}
    case True{} False{} 0n 0n:
      {==}
    case True{} True{} 0n 0n:
      {==}
    case False{} False{} 0n 1n+q:
      {==}
    case False{} True{} 0n 1n+q:
      {==}
    case True{} False{} 0n 1n+q:
      {==}
    case True{} True{} 0n 1n+q:
      {==}
    case False{} False{} 1n+p 0n:
      {==}
    case False{} True{} 1n+p 0n:
      {==}
    case True{} False{} 1n+p 0n:
      {==}
    case True{} True{} 1n+p 0n:
      {==}
    case False{} False{} 1n+p 1n+q:
      cmp_bits(False{}, False{}, p, q)
    case False{} True{} 1n+p 1n+q:
      cmp_bits(False{}, True{}, p, q)
    case True{} False{} 1n+p 1n+q:
      cmp_bits(True{}, False{}, p, q)
    case True{} True{} 1n+p 1n+q:
      cmp_bits(True{}, True{}, p, q)

law Word.cmp_nat:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  {Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) == Word.cmp(n, a, b) : Cmp}

def Word.cmp_nat(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          %Word.cmp_nat(p, at, bt) : {Nat.cmp(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))) == Word.cmp.fin(False{}, False{}, _) : Cmp}
          Equal.sym(Cmp, Word.cmp.fin(False{}, False{}, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))), Nat.cmp(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))), cmp_bits(False{}, False{}, Word.to_nat(p, at), Word.to_nat(p, bt)))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          %Word.cmp_nat(p, at, bt) : {Nat.cmp(Nat.double(Word.to_nat(p, at)), 1n+Nat.double(Word.to_nat(p, bt))) == Word.cmp.fin(False{}, True{}, _) : Cmp}
          Equal.sym(Cmp, Word.cmp.fin(False{}, True{}, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))), Nat.cmp(Nat.double(Word.to_nat(p, at)), 1n+Nat.double(Word.to_nat(p, bt))), cmp_bits(False{}, True{}, Word.to_nat(p, at), Word.to_nat(p, bt)))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          %Word.cmp_nat(p, at, bt) : {Nat.cmp(1n+Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))) == Word.cmp.fin(True{}, False{}, _) : Cmp}
          Equal.sym(Cmp, Word.cmp.fin(True{}, False{}, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))), Nat.cmp(1n+Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))), cmp_bits(True{}, False{}, Word.to_nat(p, at), Word.to_nat(p, bt)))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          %Word.cmp_nat(p, at, bt) : {Nat.cmp(1n+Nat.double(Word.to_nat(p, at)), 1n+Nat.double(Word.to_nat(p, bt))) == Word.cmp.fin(True{}, True{}, _) : Cmp}
          Equal.sym(Cmp, Word.cmp.fin(True{}, True{}, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))), Nat.cmp(1n+Nat.double(Word.to_nat(p, at)), 1n+Nat.double(Word.to_nat(p, bt))), cmp_bits(True{}, True{}, Word.to_nat(p, at), Word.to_nat(p, bt)))

law cmp_nat:
  for a: U32
  for b: U32
  {Nat.cmp(U32.to_nat(a), U32.to_nat(b)) == U32.cmp(a, b) : Cmp}

def cmp_nat(a, b):
  match a b:
    case U32{x} U32{y}:
      Word.cmp_nat(32n, x, y)

# a <= b on U32
def LE(a: U32, b: U32) -> Data:
  Nat.LE(U32.to_nat(a), U32.to_nat(b))

# a result of U32.is_lt is the same result of Nat.is_lt on the numbers
law is_lt_nat:
  for +a: U32
  for +b: U32
  for -c: Bool
  for e: {U32.is_lt(a, b) == c : Bool}
  {Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) == c : Bool}

def is_lt_nat(a, b, c, e):
  %Equal.sym(Cmp, Nat.cmp(U32.to_nat(a), U32.to_nat(b)), U32.cmp(a, b), cmp_nat(a, b)) : {Cmp.is_lt(_) == c : Bool}
  e

# Base's U32.min(a, b) is Bool.pick(U32.is_lt(a, b), a, b). A match cannot
# inspect the computed test, so each .go lemma takes its result c and
# {U32.is_lt(a, b) == c} as parameters; callers pass the test and {==}.

law min_le_r.go:
  for +a: U32
  for +b: U32
  for c: Bool
  for e: {U32.is_lt(a, b) == c : Bool}
  LE(Bool.pick(U32, c, a, b), b)

def min_le_r.go(a, b, c, e):
  match c:
    case True{}:
      Nat.le_of_is_lt(U32.to_nat(a), U32.to_nat(b), is_lt_nat(a, b, True{}, e))
    case False{}:
      Nat.le_refl(U32.to_nat(b))

# LAW: min(a, b) <= b
law min_le_r:
  for +a: U32
  for +b: U32
  LE(U32.min(a, b), b)

def min_le_r(a, b):
  min_le_r.go(a, b, U32.is_lt(a, b), {==})

law le_max_r.go:
  for +a: U32
  for +b: U32
  for c: Bool
  for e: {U32.is_lt(a, b) == c : Bool}
  LE(b, Bool.pick(U32, c, b, a))

def le_max_r.go(a, b, c, e):
  match c:
    case True{}:
      Nat.le_refl(U32.to_nat(b))
    case False{}:
      Nat.ge_of_not_lt(U32.to_nat(a), U32.to_nat(b), is_lt_nat(a, b, False{}, e))

# LAW: b <= max(a, b)
law le_max_r:
  for +a: U32
  for +b: U32
  LE(b, U32.max(a, b))

def le_max_r(a, b):
  le_max_r.go(a, b, U32.is_lt(a, b), {==})

# LAW: clamp(x, lo, hi) <= hi, even when lo > hi
law clamp_le_hi:
  for +x: U32
  for +lo: U32
  for +hi: U32
  LE(U32.clamp(x, lo, hi), hi)

def clamp_le_hi(x, lo, hi):
  min_le_r(U32.max(x, lo), hi)

law lo_le_clamp.go:
  for +lo: U32
  for +m: U32
  for +hi: U32
  for lm: LE(lo, m)
  for lh: LE(lo, hi)
  for c: Bool
  LE(lo, Bool.pick(U32, c, m, hi))

def lo_le_clamp.go(lo, m, hi, lm, lh, c):
  match c:
    case True{}:
      lm
    case False{}:
      lh

# LAW: lo <= clamp(x, lo, hi) when lo <= hi
law lo_le_clamp:
  for +x: U32
  for +lo: U32
  for +hi: U32
  for lh: LE(lo, hi)
  LE(lo, U32.clamp(x, lo, hi))

def lo_le_clamp(x, lo, hi, lh):
  lo_le_clamp.go(lo, U32.max(x, lo), hi, le_max_r(x, lo), lh, U32.is_lt(U32.max(x, lo), hi))

# Wrapping + and - undo each other
# ---------------------------------
# Word.adc(n, a, b, flip, c) adds a, b (negated when flip) and carry c.
# Adding b with carry c and then subtracting b with carry not(c) returns
# a, and the carry out of each bit is again not(c)'s counterpart, so the
# induction runs bit by bit. U32.add uses carry False, U32.sub carry True.

# (a + b + c) - b, with carry not(c), is a
law Word.sub_add:
  for +n: Nat
  for a: Word(n)
  for +b: Word(n)
  for c: Bool
  {a == Word.adc(n, Word.adc(n, a, b, False{}, c), b, True{}, Bool.not(c)) : Word(n)}

def Word.sub_add(n, a, b, c):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, at} WCon{False{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            at, Word.adc(p, Word.adc(p, at, bt, False{}, False{}), bt, True{}, Bool.not(False{})),
            Word.sub_add(p, at, bt, False{}))
        case WCon{False{}, at} WCon{False{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            at, Word.adc(p, Word.adc(p, at, bt, False{}, False{}), bt, True{}, Bool.not(False{})),
            Word.sub_add(p, at, bt, False{}))
        case WCon{False{}, at} WCon{True{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            at, Word.adc(p, Word.adc(p, at, bt, False{}, False{}), bt, True{}, Bool.not(False{})),
            Word.sub_add(p, at, bt, False{}))
        case WCon{False{}, at} WCon{True{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            at, Word.adc(p, Word.adc(p, at, bt, False{}, True{}), bt, True{}, Bool.not(True{})),
            Word.sub_add(p, at, bt, True{}))
        case WCon{True{}, at} WCon{False{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            at, Word.adc(p, Word.adc(p, at, bt, False{}, False{}), bt, True{}, Bool.not(False{})),
            Word.sub_add(p, at, bt, False{}))
        case WCon{True{}, at} WCon{False{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            at, Word.adc(p, Word.adc(p, at, bt, False{}, True{}), bt, True{}, Bool.not(True{})),
            Word.sub_add(p, at, bt, True{}))
        case WCon{True{}, at} WCon{True{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            at, Word.adc(p, Word.adc(p, at, bt, False{}, True{}), bt, True{}, Bool.not(True{})),
            Word.sub_add(p, at, bt, True{}))
        case WCon{True{}, at} WCon{True{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            at, Word.adc(p, Word.adc(p, at, bt, False{}, True{}), bt, True{}, Bool.not(True{})),
            Word.sub_add(p, at, bt, True{}))

# (a - b) + b, with carry not(c), is a
law Word.add_sub:
  for +n: Nat
  for a: Word(n)
  for +b: Word(n)
  for c: Bool
  {a == Word.adc(n, Word.adc(n, a, b, True{}, c), b, False{}, Bool.not(c)) : Word(n)}

def Word.add_sub(n, a, b, c):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, at} WCon{False{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            at, Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, Bool.not(False{})),
            Word.add_sub(p, at, bt, False{}))
        case WCon{False{}, at} WCon{False{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            at, Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, Bool.not(True{})),
            Word.add_sub(p, at, bt, True{}))
        case WCon{False{}, at} WCon{True{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            at, Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, Bool.not(False{})),
            Word.add_sub(p, at, bt, False{}))
        case WCon{False{}, at} WCon{True{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            at, Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, Bool.not(False{})),
            Word.add_sub(p, at, bt, False{}))
        case WCon{True{}, at} WCon{False{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            at, Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, Bool.not(True{})),
            Word.add_sub(p, at, bt, True{}))
        case WCon{True{}, at} WCon{False{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            at, Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, Bool.not(True{})),
            Word.add_sub(p, at, bt, True{}))
        case WCon{True{}, at} WCon{True{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            at, Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, Bool.not(False{})),
            Word.add_sub(p, at, bt, False{}))
        case WCon{True{}, at} WCon{True{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            at, Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, Bool.not(True{})),
            Word.add_sub(p, at, bt, True{}))

# LAW: subtracting b undoes adding b, with wraparound
law sub_add:
  for a: U32
  for b: U32
  {a == U32.sub(U32.add(a, b), b) : U32}

def sub_add(a, b):
  match a b:
    case U32{x} U32{+y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, Word.sub(32n, Word.add(32n, x, y), y), Word.sub_add(32n, x, y, False{}))

# LAW: adding b undoes subtracting b, with wraparound
law add_sub:
  for a: U32
  for b: U32
  {a == U32.add(U32.sub(a, b), b) : U32}

def add_sub(a, b):
  match a b:
    case U32{x} U32{+y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, Word.add(32n, Word.sub(32n, x, y), y), Word.add_sub(32n, x, y, True{}))

# wrapping + and - as a C.Group
def group() -> C.Group<U32>:
  C.Group{U32.add, U32.sub, sub_add, add_sub}
