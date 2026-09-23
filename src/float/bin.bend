import Base

# bin.bend: natural numbers in binary, little-endian (lowest bit first).
#
#   import ./bin.bend as Bin
#
# Nat is unary in the checker, so exact arithmetic on large numbers
# (a float's 24-bit mantissa, an aligned sum of two floats) overflows it.
# These numbers compute in the checker in time linear or quadratic in
# their bit length. Trailing zero bits are allowed; every function reads
# BZ as zeros, so B0{BZ{}} and BZ{} are the same number.

type Bin is Data:
  BZ{}
  B0{r: Bin}
  B1{r: Bin}

def one() -> Bin:
  B1{BZ{}}

def is_zero(a: Bin) -> Bool:
  match a:
    case BZ{}:
      True{}
    case B0{r}:
      is_zero(r)
    case B1{r}:
      False{}

def trim.cons0(t: Bin) -> Bin:
  match t:
    case BZ{}:
      BZ{}
    case t:
      B0{t}

# the same number without high zero bits, so equal numbers are equal terms
def trim(a: Bin) -> Bin:
  match a:
    case BZ{}:
      BZ{}
    case B0{r}:
      trim.cons0(trim(r))
    case B1{r}:
      B1{trim(r)}

def odd(a: Bin) -> Bool:
  match a:
    case B1{r}:
      True{}
    case _:
      False{}

def inc(a: Bin) -> Bin:
  match a:
    case BZ{}:
      B1{BZ{}}
    case B0{r}:
      B1{r}
    case B1{r}:
      B0{inc(r)}

def cons(s: Bool, r: Bin) -> Bin:
  match s:
    case False{}:
      B0{r}
    case True{}:
      B1{r}

def adc.one(a: Bin, c: Bool) -> Bin:
  match c:
    case False{}:
      a
    case True{}:
      inc(a)

# a + b + carry, one bit at a time: bits 0+0 pass the carry through and
# carry nothing, 0+1 flip it and carry it, 1+1 pass it and carry one
def adc(a: Bin, b: Bin, +c: Bool) -> Bin:
  match a b:
    case BZ{} b:
      adc.one(b, c)
    case a BZ{}:
      adc.one(a, c)
    case B0{x} B0{y}:
      cons(c, adc(x, y, False{}))
    case B0{x} B1{y}:
      cons(Bool.not(c), adc(x, y, c))
    case B1{x} B0{y}:
      cons(Bool.not(c), adc(x, y, c))
    case B1{x} B1{y}:
      cons(c, adc(x, y, True{}))

def add(a: Bin, b: Bin) -> Bin:
  adc(a, b, False{})

def dec(a: Bin) -> Bin:
  match a:
    case BZ{}:
      BZ{}
    case B1{r}:
      B0{r}
    case B0{r}:
      B1{dec(r)}

def sbb.one(a: Bin, w: Bool) -> Bin:
  match w:
    case False{}:
      a
    case True{}:
      dec(a)

# a - b - borrow, for a >= b (callers order the operands with cmp first)
def sbb(a: Bin, b: Bin, +w: Bool) -> Bin:
  match a b:
    case a BZ{}:
      sbb.one(a, w)
    case BZ{} b:
      BZ{}
    case B0{x} B0{y}:
      cons(w, sbb(x, y, w))
    case B0{x} B1{y}:
      cons(Bool.not(w), sbb(x, y, True{}))
    case B1{x} B0{y}:
      cons(Bool.not(w), sbb(x, y, False{}))
    case B1{x} B1{y}:
      cons(w, sbb(x, y, w))

def sub(a: Bin, b: Bin) -> Bin:
  sbb(a, b, False{})

def mul(a: Bin, +b: Bin) -> Bin:
  match a:
    case BZ{}:
      BZ{}
    case B0{r}:
      B0{mul(r, b)}
    case B1{r}:
      add(b, B0{mul(r, b)})

def cmp.fin(p: Bool, q: Bool, hi: Cmp) -> Cmp:
  match hi:
    case LT{}:
      LT{}
    case EQ{}:
      Bool.cmp(p, q)
    case GT{}:
      GT{}

def cmp(a: Bin, b: Bin) -> Cmp:
  match a b:
    case BZ{} BZ{}:
      EQ{}
    case BZ{} B0{y}:
      cmp(BZ{}, y)
    case BZ{} B1{y}:
      LT{}
    case B0{x} BZ{}:
      cmp(x, BZ{})
    case B1{x} BZ{}:
      GT{}
    case B0{x} B0{y}:
      cmp.fin(False{}, False{}, cmp(x, y))
    case B0{x} B1{y}:
      cmp.fin(False{}, True{}, cmp(x, y))
    case B1{x} B0{y}:
      cmp.fin(True{}, False{}, cmp(x, y))
    case B1{x} B1{y}:
      cmp.fin(True{}, True{}, cmp(x, y))

# a * 2^n
def shl(a: Bin, n: Nat) -> Bin:
  match n:
    case 0n:
      a
    case 1n+k:
      B0{shl(a, k)}

def pow2(n: Nat) -> Bin:
  shl(one(), n)

def len.up(l: Nat) -> Nat:
  match l:
    case 0n:
      0n
    case 1n+k:
      2n+k

# number of significant bits
def len(a: Bin) -> Nat:
  match a:
    case BZ{}:
      0n
    case B0{r}:
      len.up(len(r))
    case B1{r}:
      1n+len(r)

# a / 2^k, with the last bit shifted out (round) and whether any bit
# below it was set (sticky); r and s are the bits already shifted out
def shr(k: Nat, a: Bin, r: Bool, s: Bool) -> Bin & Bool & Bool:
  match k:
    case 0n:
      (a, r, s)
    case 1n+j:
      match a:
        case BZ{}:
          shr(j, BZ{}, False{}, Bool.or(r, s))
        case B0{x}:
          shr(j, x, False{}, Bool.or(r, s))
        case B1{x}:
          shr(j, x, True{}, Bool.or(r, s))

# the n low bits of a word, and back
def of_word(n: Nat, w: Word(n)) -> Bin:
  match n:
    case 0n:
      BZ{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          cons(b, of_word(p, t))

def to_word(n: Nat, a: Bin) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match a:
        case BZ{}:
          WCon{False{}, to_word(p, BZ{})}
        case B0{r}:
          WCon{False{}, to_word(p, r)}
        case B1{r}:
          WCon{True{}, to_word(p, r)}

def of_u32(x: U32) -> Bin:
  match x:
    case U32{w}:
      of_word(32n, w)

def to_u32(a: Bin) -> U32:
  U32{to_word(32n, a)}

def to_nat(a: Bin) -> Nat:
  match a:
    case BZ{}:
      0n
    case B0{r}:
      Nat.double(to_nat(r))
    case B1{r}:
      1n+Nat.double(to_nat(r))

def of_nat(n: Nat) -> Bin:
  match n:
    case 0n:
      BZ{}
    case 1n+k:
      inc(of_nat(k))

# the low k bits of a
def low(k: Nat, a: Bin) -> Bin:
  match k:
    case 0n:
      BZ{}
    case 1n+j:
      match a:
        case BZ{}:
          BZ{}
        case B0{r}:
          B0{low(j, r)}
        case B1{r}:
          B1{low(j, r)}

def take.cons(-r: Nat, b: Bool, p: Bin & Word(r)) -> Bin & Word(r):
  (x, w) = p
  (cons(b, x), w)

# the low k bits of a word as a Bin, and the word that remains
def take(k: Nat, -r: Nat, w: Word(Nat.add(k, r))) -> Bin & Word(r):
  match k:
    case 0n:
      (BZ{}, w)
    case 1n+j:
      match w:
        case WCon{b, t}:
          take.cons(r, b, take(j, r, t))
