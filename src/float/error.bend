import Base
import ../nat.bend as Nat
import ./bin.bend as Bin
import ./format.bend as Fmt
import ./num.bend as Num
import ./sf32.bend as SF32

# error.bend: how far a rounded result is from the exact one.
#
#   import ./error.bend as Err
#   Err.round_near(f, neg, m, e)    # Fmt.round is within half an ulp
#
# Values are compared as natural numbers at one exponent: a mantissa m at
# exponent t is sh(m, t - e) at exponent e, where sh(q, n) is q * 2^n.
# Bound(Y, X, k) says 2|Y - X| <= 2^k, written as two inequalities
# without subtraction. For a result with k low bits rounded off, 2^k is
# one ulp at exponent e, so Bound(Y, X, k) is "within half an ulp".
#
# The proofs are symbolic, so the Nat numbers they mention are never
# built; a law about a 24-bit mantissa costs the same as one about 3.

# q * 2^n
def sh(q: Nat, n: Nat) -> Nat:
  match n:
    case 0n:
      q
    case 1n+k:
      Nat.double(sh(q, k))

law sh_zero:
  for n: Nat
  {0n == sh(0n, n) : Nat}

def sh_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+k:
      %sh_zero(k) : {0n == Nat.double(_) : Nat}
      {==}

law sh_double:
  for +q: Nat
  for n: Nat
  {Nat.double(sh(q, n)) == sh(Nat.double(q), n) : Nat}

def sh_double(q, n):
  match n:
    case 0n:
      {==}
    case 1n+k:
      %sh_double(q, k) : {Nat.double(Nat.double(sh(q, k))) == Nat.double(_) : Nat}
      {==}

law sh_add:
  for +a: Nat
  for +b: Nat
  for n: Nat
  {Nat.add(sh(a, n), sh(b, n)) == sh(Nat.add(a, b), n) : Nat}

def sh_add(a, b, n):
  match n:
    case 0n:
      {==}
    case 1n++k:
      %sh_add(a, b, k) : {Nat.add(Nat.double(sh(a, k)), Nat.double(sh(b, k))) == Nat.double(_) : Nat}
      Nat.double_add(sh(a, k), sh(b, k))

law one_le_double:
  for x: Nat
  for h: Nat.LE(1n, x)
  Nat.LE(1n, Nat.double(x))

def one_le_double(x, h):
  match x:
    case 0n:
      match h:
    case 1n+p:
      Unit{}

# an ulp is at least 1
law one_le_sh:
  for n: Nat
  Nat.LE(1n, sh(1n, n))

def one_le_sh(n):
  match n:
    case 0n:
      Unit{}
    case 1n++k:
      one_le_double(sh(1n, k), one_le_sh(k))

law num_inc:
  for a: Bin.Bin
  {1n+Bin.to_nat(a) == Bin.to_nat(Bin.inc(a)) : Nat}

def num_inc(a):
  match a:
    case Bin.BZ{}:
      {==}
    case Bin.B0{r}:
      {==}
    case Bin.B1{+r}:
      %num_inc(r) : {2n+Nat.double(Bin.to_nat(r)) == Nat.double(_) : Nat}
      {==}

# The bits shifted out
# --------------------
# Bin.shr shifts k bits off a mantissa, keeping the last one (r) and
# whether any before it was set (s). If T is the value of the bits
# shifted out so far, n of them, then D = 2T against U = 2^n is one of
# four cases, and r and s say which:
#   r s
#   F F   D = 0              nothing shifted out: exact
#   F T   0 < D < U          below half an ulp
#   T F   D = U              exactly half: a tie
#   T T   U < D < 2U         above half an ulp
# Rounding needs only this, not T itself.

def Tail(r: Bool, s: Bool, +D: Nat, +U: Nat) -> Type:
  match r s:
    case False{} False{}:
      Nat.LE(D, 0n)
    case False{} True{}:
      Nat.LT(0n, D) & Nat.LT(D, U)
    case True{} False{}:
      Nat.LE(D, U) & Nat.LE(U, D)
    case True{} True{}:
      Nat.LT(U, D) & Nat.LT(D, Nat.double(U))

law lt_double:
  for U: Nat
  for hu: Nat.LE(1n, U)
  Nat.LT(U, Nat.double(U))

def lt_double(U, hu):
  match U:
    case 0n:
      match hu:
    case 1n+p:
      Nat.le_double(p)

law tail0.below:
  for +D: Nat
  for +U: Nat
  for h: Nat.LT(0n, D) & Nat.LT(D, U)
  Nat.LT(0n, D) & Nat.LT(D, Nat.double(U))

def tail0.below(D, U, h):
  (a, b) = h
  (a, Nat.le_trans(1n+D, U, Nat.double(U), b, Nat.le_double(U)))

law tail0.half:
  for +D: Nat
  for +U: Nat
  for +hu: Nat.LE(1n, U)
  for h: Nat.LE(D, U) & Nat.LE(U, D)
  Nat.LT(0n, D) & Nat.LT(D, Nat.double(U))

def tail0.half(D, U, hu, h):
  (l1, l2) = h
  (Nat.le_trans(1n, U, D, hu, l2), Nat.le_trans(1n+D, 1n+U, Nat.double(U), l1, lt_double(U, hu)))

law tail0.above:
  for +D: Nat
  for +U: Nat
  for h: Nat.LT(U, D) & Nat.LT(D, Nat.double(U))
  Nat.LT(0n, D) & Nat.LT(D, Nat.double(U))

def tail0.above(D, U, h):
  (a, b) = h
  (Nat.le_trans(1n, 1n+U, D, Unit{}, a), b)

# a 0 bit shifted out at position n
law tail0:
  for r: Bool
  for s: Bool
  for +D: Nat
  for +U: Nat
  for hu: Nat.LE(1n, U)
  Tail(r, s, D, U) -> Tail(False{}, Bool.or(r, s), D, Nat.double(U))

def tail0(r, s, D, U, hu):
  match r s:
    case False{} False{}:
      h => h
    case False{} True{}:
      h => tail0.below(D, U, h)
    case True{} False{}:
      h => tail0.half(D, U, hu, h)
    case True{} True{}:
      h => tail0.above(D, U, h)

# 2U < 2U + D, when D > 0
law tail1.lo:
  for +U: Nat
  for +D: Nat
  for h: Nat.LE(1n, D)
  Nat.LT(Nat.double(U), Nat.add(Nat.double(U), D))

def tail1.lo(U, D, h):
  %Equal.sym(Nat, Nat.add(Nat.double(U), D), Nat.add(D, Nat.double(U)), Nat.add_comm(Nat.double(U), D)) : Nat.LT(Nat.double(U), _)
  Nat.add_mono_r(1n, D, Nat.double(U), h)

# 2U + D < 4U, when D < 2U
law tail1.hi:
  for +U: Nat
  for +D: Nat
  for h: Nat.LT(D, Nat.double(U))
  Nat.LT(Nat.add(Nat.double(U), D), Nat.double(Nat.double(U)))

def tail1.hi(U, D, h):
  +X = Nat.double(U)
  %Nat.add_succ_r(X, D) : Nat.LE(_, Nat.double(X))
  %Nat.double_is_add(X) : Nat.LE(Nat.add(X, 1n+D), _)
  Nat.add_mono_l(X, 1n+D, X, h)

law tail1.none.le:
  for +X: Nat
  for +D: Nat
  for h: Nat.LE(D, 0n)
  Nat.LE(Nat.add(X, D), X)

def tail1.none.le(X, D, h):
  %Equal.sym(Nat, X, Nat.add(X, 0n), Nat.add_zero_r(X)) : Nat.LE(Nat.add(X, D), _)
  Nat.add_mono_l(X, D, 0n, h)

law tail1.none:
  for +U: Nat
  for +D: Nat
  for h: Nat.LE(D, 0n)
  Nat.LE(Nat.add(Nat.double(U), D), Nat.double(U)) & Nat.LE(Nat.double(U), Nat.add(Nat.double(U), D))

def tail1.none(U, D, h):
  +X = Nat.double(U)
  (tail1.none.le(X, D, h), Nat.le_add_r(X, D))

law tail1.below:
  for +D: Nat
  for +U: Nat
  for h: Nat.LT(0n, D) & Nat.LT(D, U)
  Tail(True{}, True{}, Nat.add(Nat.double(U), D), Nat.double(U))

def tail1.below(D, U, h):
  (a, b) = h
  (tail1.lo(U, D, a), tail1.hi(U, D, Nat.le_trans(1n+D, U, Nat.double(U), b, Nat.le_double(U))))

law tail1.half:
  for +D: Nat
  for +U: Nat
  for +hu: Nat.LE(1n, U)
  for h: Nat.LE(D, U) & Nat.LE(U, D)
  Tail(True{}, True{}, Nat.add(Nat.double(U), D), Nat.double(U))

def tail1.half(D, U, hu, h):
  (l1, l2) = h
  (tail1.lo(U, D, Nat.le_trans(1n, U, D, hu, l2)), tail1.hi(U, D, Nat.le_trans(1n+D, 1n+U, Nat.double(U), l1, lt_double(U, hu))))

law tail1.above:
  for +D: Nat
  for +U: Nat
  for h: Nat.LT(U, D) & Nat.LT(D, Nat.double(U))
  Tail(True{}, True{}, Nat.add(Nat.double(U), D), Nat.double(U))

def tail1.above(D, U, h):
  (a, b) = h
  (tail1.lo(U, D, Nat.le_trans(1n, 1n+U, D, Unit{}, a)), tail1.hi(U, D, b))

# a 1 bit shifted out at position n: T grows by U = 2^n, so D by 2U
law tail1:
  for r: Bool
  for s: Bool
  for +D: Nat
  for +U: Nat
  for hu: Nat.LE(1n, U)
  Tail(r, s, D, U) -> Tail(True{}, Bool.or(r, s), Nat.add(Nat.double(U), D), Nat.double(U))

def tail1(r, s, D, U, hu):
  match r s:
    case False{} False{}:
      h => tail1.none(U, D, h)
    case False{} True{}:
      h => tail1.below(D, U, h)
    case True{} False{}:
      h => tail1.half(D, U, hu, h)
    case True{} True{}:
      h => tail1.above(D, U, h)

# tail1's D, rewritten as 2(U + T)
law tail1.fix:
  for r: Bool
  for s: Bool
  for +P: Nat
  for +T: Nat
  for x: Tail(r, s, Nat.add(Nat.double(P), Nat.double(T)), Nat.double(P))
  Tail(r, s, Nat.double(Nat.add(P, T)), Nat.double(P))

def tail1.fix(r, s, P, T, x):
  %Nat.double_add(P, T) : Tail(r, s, _, Nat.double(P))
  x

# The value shifted
# -----------------
# M = a * 2^n + T. Shifting a's low bit b out makes it
# M = (a / 2) * 2^(n+1) + (b * 2^n + T).

law val0:
  for +X: Nat
  for +n: Nat
  for -T: Nat
  for -M: Nat
  for e: {M == Nat.add(sh(Nat.double(X), n), T) : Nat}
  {M == Nat.add(sh(X, 1n+n), T) : Nat}

def val0(X, n, T, M, e):
  %Equal.sym(Nat, Nat.double(sh(X, n)), sh(Nat.double(X), n), sh_double(X, n)) : {M == Nat.add(_, T) : Nat}
  e

law val1:
  for +X: Nat
  for +n: Nat
  for +T: Nat
  for -M: Nat
  for e: {M == Nat.add(sh(1n+Nat.double(X), n), T) : Nat}
  {M == Nat.add(sh(X, 1n+n), Nat.add(sh(1n, n), T)) : Nat}

def val1(X, n, T, M, e):
  +P = sh(1n, n)
  +S = Nat.double(sh(X, n))
  %Nat.add_swap(P, S, T) : {M == _ : Nat}
  %Equal.sym(Nat, Nat.add(P, Nat.add(S, T)), Nat.add(Nat.add(P, S), T), Nat.add_assoc(P, S, T)) : {M == _ : Nat}
  %Equal.sym(Nat, S, sh(Nat.double(X), n), sh_double(X, n)) : {M == Nat.add(Nat.add(P, _), T) : Nat}
  %Equal.sym(Nat, Nat.add(P, sh(Nat.double(X), n)), sh(1n+Nat.double(X), n), sh_add(1n, Nat.double(X), n)) : {M == Nat.add(_, T) : Nat}
  e

# what shr(k, a, r, s) has shifted out, added to T, with n bits already out
def rest(k: Nat, a: Bin.Bin, +n: Nat, T: Nat) -> Nat:
  match k:
    case 0n:
      T
    case 1n+j:
      match a:
        case Bin.BZ{}:
          rest(j, Bin.BZ{}, 1n+n, T)
        case Bin.B0{x}:
          rest(j, x, 1n+n, T)
        case Bin.B1{x}:
          rest(j, x, 1n+n, Nat.add(sh(1n, n), T))

# after a shift: M = q * 2^N + T, and the tail bits say where T is
def After(res: Bin.Bin & Bool & Bool, +M: Nat, +N: Nat, +T: Nat) -> Type:
  (q, r, s) = res
  {M == Nat.add(sh(Bin.to_nat(q), N), T) : Nat} & Tail(r, s, Nat.double(T), sh(1n, N))

law after_succ:
  for res: Bin.Bin & Bool & Bool
  for +M: Nat
  for +j: Nat
  for +n: Nat
  for +T: Nat
  for x: After(res, M, Nat.add(j, 1n+n), T)
  After(res, M, 1n+Nat.add(j, n), T)

def after_succ(res, M, j, n, T, x):
  %Nat.add_succ_r(j, n) : After(res, M, _, T)
  x

# shr keeps the invariant: from M = a * 2^n + T with T's tail cases, the
# result q, r, s has M = q * 2^(k+n) + rest, with rest's tail cases
law shr_ok:
  for k: Nat
  for a: Bin.Bin
  for +r: Bool
  for +s: Bool
  for +n: Nat
  for +M: Nat
  for +T: Nat
  {M == Nat.add(sh(Bin.to_nat(a), n), T) : Nat} -> Tail(r, s, Nat.double(T), sh(1n, n)) -> After(Bin.shr(k, a, r, s), M, Nat.add(k, n), rest(k, a, n, T))

def shr_ok(k, a, r, s, n, M, T):
  match k:
    case 0n:
      e => h => (e, h)
    case 1n++j:
      match a:
        case Bin.BZ{}:
          e => h => after_succ(Bin.shr(j, Bin.BZ{}, False{}, Bool.or(r, s)), M, j, n, rest(j, Bin.BZ{}, 1n+n, T),
            shr_ok(j, Bin.BZ{}, False{}, Bool.or(r, s), 1n+n, M, T)(val0(0n, n, T, M, e))(tail0(r, s, Nat.double(T), sh(1n, n), one_le_sh(n))(h)))
        case Bin.B0{+x}:
          e => h => after_succ(Bin.shr(j, x, False{}, Bool.or(r, s)), M, j, n, rest(j, x, 1n+n, T),
            shr_ok(j, x, False{}, Bool.or(r, s), 1n+n, M, T)(val0(Bin.to_nat(x), n, T, M, e))(tail0(r, s, Nat.double(T), sh(1n, n), one_le_sh(n))(h)))
        case Bin.B1{+x}:
          e => h => after_succ(Bin.shr(j, x, True{}, Bool.or(r, s)), M, j, n, rest(j, x, 1n+n, Nat.add(sh(1n, n), T)),
            shr_ok(j, x, True{}, Bool.or(r, s), 1n+n, M, Nat.add(sh(1n, n), T))(val1(Bin.to_nat(x), n, T, M, e))(tail1.fix(True{}, Bool.or(r, s), sh(1n, n), T, tail1(r, s, Nat.double(T), sh(1n, n), one_le_sh(n))(h))))

# Rounding
# --------

# 2|Y - X| <= 2^k: Y is within half of 2^k of X
def Bound(+Y: Nat, +X: Nat, +k: Nat) -> Type:
  Nat.LE(Nat.double(Y), Nat.add(Nat.double(X), sh(1n, k))) & Nat.LE(Nat.double(X), Nat.add(Nat.double(Y), sh(1n, k)))

law near_down.lo:
  for +dY: Nat
  for +D: Nat
  for +U: Nat
  Nat.LE(dY, Nat.add(Nat.add(dY, D), U))

def near_down.lo(dY, D, U):
  %Nat.add_assoc(dY, D, U) : Nat.LE(dY, _)
  Nat.le_add_r(dY, Nat.add(D, U))

# rounding down: 2X = 2Y + D with D <= U
law near_down:
  for +dY: Nat
  for +D: Nat
  for +U: Nat
  for h: Nat.LE(D, U)
  Nat.LE(dY, Nat.add(Nat.add(dY, D), U)) & Nat.LE(Nat.add(dY, D), Nat.add(dY, U))

def near_down(dY, D, U, h):
  (near_down.lo(dY, D, U), Nat.add_mono_l(dY, D, U, h))

# rounding up: the result is 2^k more, with U <= D <= 2U
law near_up.lo:
  for +dY: Nat
  for +D: Nat
  for +U: Nat
  for h1: Nat.LE(U, D)
  Nat.LE(Nat.add(Nat.double(U), dY), Nat.add(Nat.add(dY, D), U))

def near_up.lo(dY, D, U, h1):
  %Nat.add_comm(dY, Nat.double(U)) : Nat.LE(_, Nat.add(Nat.add(dY, D), U))
  %Nat.add_assoc(dY, D, U) : Nat.LE(Nat.add(dY, Nat.double(U)), _)
  %Nat.double_is_add(U) : Nat.LE(Nat.add(dY, _), Nat.add(dY, Nat.add(D, U)))
  Nat.add_mono_l(dY, Nat.add(U, U), Nat.add(D, U), Nat.add_mono_r(U, D, U, h1))

law near_up.hi:
  for +dY: Nat
  for +D: Nat
  for +U: Nat
  for h2: Nat.LE(D, Nat.double(U))
  Nat.LE(Nat.add(dY, D), Nat.add(Nat.add(Nat.double(U), dY), U))

def near_up.hi(dY, D, U, h2):
  %Nat.add_comm(dY, Nat.double(U)) : Nat.LE(Nat.add(dY, D), Nat.add(_, U))
  %Nat.add_assoc(dY, Nat.double(U), U) : Nat.LE(Nat.add(dY, D), _)
  Nat.add_mono_l(dY, D, Nat.add(Nat.double(U), U), Nat.le_trans(D, Nat.double(U), Nat.add(Nat.double(U), U), h2, Nat.le_add_r(Nat.double(U), U)))

# M = Y + T at scale 2^k, rounded down to Y
law fin_down:
  for +Q: Nat
  for +k: Nat
  for +T: Nat
  for -M: Nat
  for e: {M == Nat.add(sh(Q, k), T) : Nat}
  for h: Nat.LE(Nat.double(T), sh(1n, k))
  Bound(sh(Q, k), M, k)

def fin_down(Q, k, T, M, e, h):
  %Equal.sym(Nat, M, Nat.add(sh(Q, k), T), e) : Bound(sh(Q, k), _, k)
  %Nat.double_add(sh(Q, k), T) : Nat.LE(Nat.double(sh(Q, k)), Nat.add(_, sh(1n, k))) & Nat.LE(_, Nat.add(Nat.double(sh(Q, k)), sh(1n, k)))
  near_down(Nat.double(sh(Q, k)), Nat.double(T), sh(1n, k), h)

# M = Y + T at scale 2^k, rounded up to Y + 2^k
law fin_up:
  for +Q: Nat
  for +k: Nat
  for +T: Nat
  for -M: Nat
  for e: {M == Nat.add(sh(Q, k), T) : Nat}
  for h1: Nat.LE(sh(1n, k), Nat.double(T))
  for h2: Nat.LE(Nat.double(T), Nat.double(sh(1n, k)))
  Bound(sh(1n+Q, k), M, k)

def fin_up(Q, k, T, M, e, h1, h2):
  +U = sh(1n, k)
  +Y = sh(Q, k)
  %Equal.sym(Nat, M, Nat.add(Y, T), e) : Bound(sh(1n+Q, k), _, k)
  %sh_add(1n, Q, k) : Bound(_, Nat.add(Y, T), k)
  %Nat.double_add(U, Y) : Nat.LE(_, Nat.add(Nat.double(Nat.add(Y, T)), U)) & Nat.LE(Nat.double(Nat.add(Y, T)), Nat.add(_, U))
  %Nat.double_add(Y, T) : Nat.LE(Nat.add(Nat.double(U), Nat.double(Y)), Nat.add(_, U)) & Nat.LE(_, Nat.add(Nat.add(Nat.double(U), Nat.double(Y)), U))
  (near_up.lo(Nat.double(Y), Nat.double(T), U, h1), near_up.hi(Nat.double(Y), Nat.double(T), U, h2))

law fin_inc:
  for +q: Bin.Bin
  for +k: Nat
  for +T: Nat
  for -M: Nat
  for e: {M == Nat.add(sh(Bin.to_nat(q), k), T) : Nat}
  for h1: Nat.LE(sh(1n, k), Nat.double(T))
  for h2: Nat.LE(Nat.double(T), Nat.double(sh(1n, k)))
  Bound(sh(Bin.to_nat(Bin.inc(q)), k), M, k)

def fin_inc(q, k, T, M, e, h1, h2):
  %num_inc(q) : Bound(sh(_, k), M, k)
  fin_up(Bin.to_nat(q), k, T, M, e, h1, h2)

# a tie rounds to even, which may be either way; both are half an ulp off
law fin_tie:
  for +q: Bin.Bin
  for c: Bool
  for +k: Nat
  for +T: Nat
  for -M: Nat
  for e: {M == Nat.add(sh(Bin.to_nat(q), k), T) : Nat}
  for +l1: Nat.LE(Nat.double(T), sh(1n, k))
  for l2: Nat.LE(sh(1n, k), Nat.double(T))
  Bound(sh(Bin.to_nat(Fmt.round.up(q, c)), k), M, k)

def fin_tie(q, c, k, T, M, e, l1, l2):
  match c:
    case True{}:
      fin_inc(q, k, T, M, e, l2, Nat.le_trans(Nat.double(T), sh(1n, k), Nat.double(sh(1n, k)), l1, Nat.le_double(sh(1n, k))))
    case False{}:
      fin_down(Bin.to_nat(q), k, T, M, e, l1)

law fin_ff:
  for +q: Bin.Bin
  for +k: Nat
  for +T: Nat
  for -M: Nat
  for x: {M == Nat.add(sh(Bin.to_nat(q), k), T) : Nat} & Nat.LE(Nat.double(T), 0n)
  Bound(sh(Bin.to_nat(q), k), M, k)

def fin_ff(q, k, T, M, x):
  (e, h) = x
  fin_down(Bin.to_nat(q), k, T, M, e, Nat.le_trans(Nat.double(T), 0n, sh(1n, k), h, Unit{}))

law fin_ft:
  for +q: Bin.Bin
  for +k: Nat
  for +T: Nat
  for -M: Nat
  for x: {M == Nat.add(sh(Bin.to_nat(q), k), T) : Nat} & (Nat.LT(0n, Nat.double(T)) & Nat.LT(Nat.double(T), sh(1n, k)))
  Bound(sh(Bin.to_nat(q), k), M, k)

def fin_ft(q, k, T, M, x):
  (e, h) = x
  (a, b) = h
  fin_down(Bin.to_nat(q), k, T, M, e, Nat.le_trans(Nat.double(T), 1n+Nat.double(T), sh(1n, k), Nat.le_step(Nat.double(T)), b))

law fin_tf:
  for +q: Bin.Bin
  for +k: Nat
  for +T: Nat
  for -M: Nat
  for x: {M == Nat.add(sh(Bin.to_nat(q), k), T) : Nat} & (Nat.LE(Nat.double(T), sh(1n, k)) & Nat.LE(sh(1n, k), Nat.double(T)))
  Bound(sh(Bin.to_nat(Fmt.round.up(q, Bin.odd(q))), k), M, k)

def fin_tf(q, k, T, M, x):
  (e, h) = x
  (l1, l2) = h
  fin_tie(q, Bin.odd(q), k, T, M, e, l1, l2)

law fin_tt:
  for +q: Bin.Bin
  for +k: Nat
  for +T: Nat
  for -M: Nat
  for x: {M == Nat.add(sh(Bin.to_nat(q), k), T) : Nat} & (Nat.LT(sh(1n, k), Nat.double(T)) & Nat.LT(Nat.double(T), Nat.double(sh(1n, k))))
  Bound(sh(Bin.to_nat(Bin.inc(q)), k), M, k)

def fin_tt(q, k, T, M, x):
  (e, h) = x
  (a, b) = h
  fin_inc(q, k, T, M, e,
    Nat.le_trans(sh(1n, k), 1n+sh(1n, k), Nat.double(T), Nat.le_step(sh(1n, k)), a),
    Nat.le_trans(Nat.double(T), 1n+Nat.double(T), Nat.double(sh(1n, k)), Nat.le_step(Nat.double(T)), b))

# round to nearest, ties to even, on the mantissa shr left
law fin_near:
  for +q: Bin.Bin
  for r: Bool
  for s: Bool
  for +M: Nat
  for +k: Nat
  for +T: Nat
  After((q, r, s), M, k, T) -> Bound(sh(Bin.to_nat(Fmt.round.up(q, Bool.and(r, Bool.or(s, Bin.odd(q))))), k), M, k)

def fin_near(q, r, s, M, k, T):
  match r s:
    case False{} False{}:
      x => fin_ff(q, k, T, M, x)
    case False{} True{}:
      x => fin_ft(q, k, T, M, x)
    case True{} False{}:
      x => fin_tf(q, k, T, M, x)
    case True{} True{}:
      x => fin_tt(q, k, T, M, x)

# The rounded value
# -----------------
# From here values are compared on one scale: m at exponent t is
# sh(m, t), so no exponent is subtracted and bounds from different
# operations add up.

# a rounded value v of the exact X: a finite v is within half its own ulp
# (2^t, t its exponent) of X, and its mantissa is not zero; zero is
# within half of 2^u, the ulp of the smallest value it was rounded from;
# infinity (overflow) carries no bound; rounding never gives NaN
def Near(v: Fmt.Val, +X: Nat, +u: Nat) -> Type:
  match v:
    case Fmt.Z{n}:
      Bound(0n, X, u)
    case Fmt.Inf{n}:
      Unit
    case Fmt.NaN{}:
      Empty
    case Fmt.Fin{n, +R, +t}:
      Bound(sh(Bin.to_nat(R), t), X, t) & Nat.IsFalse(Bin.is_zero(R))

def no_f(e: {False{} == True{} : Bool}) -> Empty:
  %e : Nat.IsFalse(_)
  Unit{}

def no_t(e: {True{} == False{} : Bool}) -> Empty:
  %e : Nat.IsTrue(_)
  Unit{}

def void(-A: Type, v: Empty) -> A:
  match v:

law zero_double:
  for +x: Nat
  for e: {0n == x : Nat}
  {0n == Nat.double(x) : Nat}

def zero_double(x, e):
  %e : {0n == Nat.double(_) : Nat}
  {==}

law zero_num:
  for a: Bin.Bin
  {Bin.is_zero(a) == True{} : Bool} -> {0n == Bin.to_nat(a) : Nat}

def zero_num(a):
  match a:
    case Bin.BZ{}:
      e => {==}
    case Bin.B0{+r}:
      e => zero_double(Bin.to_nat(r), zero_num(r)(e))
    case Bin.B1{r}:
      e => void({0n == 1n+Nat.double(Bin.to_nat(r)) : Nat}, no_f(e))

# a zero mantissa at any scale is 0
law sh_num_zero:
  for +R: Bin.Bin
  for +s: Nat
  for ez: {Bin.is_zero(R) == True{} : Bool}
  {sh(Bin.to_nat(R), s) == 0n : Nat}

def sh_num_zero(R, s, ez):
  Equal.trans(Nat, sh(Bin.to_nat(R), s), sh(0n, s), 0n,
    Equal.cong(Nat, Nat, x => sh(x, s), Bin.to_nat(R), 0n, Equal.sym(Nat, 0n, Bin.to_nat(R), zero_num(R)(ez))),
    Equal.sym(Nat, 0n, sh(0n, s), sh_zero(s)))

law nonzero:
  for +R: Bin.Bin
  for ez: {Bin.is_zero(R) == False{} : Bool}
  Nat.IsFalse(Bin.is_zero(R))

def nonzero(R, ez):
  %Equal.sym(Bool, Bin.is_zero(R), False{}, ez) : Nat.IsFalse(_)
  Unit{}

law over_near.go:
  for neg: Bool
  for +R: Bin.Bin
  for +t: Nat
  for +X: Nat
  for +u: Nat
  for z: Bool
  for ez: {Bin.is_zero(R) == z : Bool}
  for big: Bool
  for bf: Bound(sh(Bin.to_nat(R), t), X, t)
  for zf: Bound(sh(Bin.to_nat(R), t), X, t) -> {Bin.is_zero(R) == True{} : Bool} -> Bound(0n, X, u)
  Near(Fmt.over.go(neg, R, t, z, big), X, u)

def over_near.go(neg, R, t, X, u, z, ez, big, bf, zf):
  match z big:
    case True{} big:
      zf(bf)(ez)
    case False{} True{}:
      Unit{}
    case False{} False{}:
      (bf, nonzero(R, ez))

# over keeps a bound: zero if the mantissa is zero, infinity if too big
law over_near:
  for +top: Nat
  for neg: Bool
  for +R: Bin.Bin
  for +t: Nat
  for +X: Nat
  for +u: Nat
  for bf: Bound(sh(Bin.to_nat(R), t), X, t)
  for zf: Bound(sh(Bin.to_nat(R), t), X, t) -> {Bin.is_zero(R) == True{} : Bool} -> Bound(0n, X, u)
  Near(Fmt.over(top, neg, R, t), X, u)

def over_near(top, neg, R, t, X, u, bf, zf):
  over_near.go(neg, R, t, X, u, Bin.is_zero(R), {==}, Nat.is_gt(Nat.add(t, Bin.len(R)), top), bf, zf)

law bound_sh.step:
  for +A: Nat
  for +B: Nat
  for +U: Nat
  for h: Nat.LE(A, Nat.add(B, U))
  Nat.LE(Nat.double(A), Nat.add(Nat.double(B), Nat.double(U)))

def bound_sh.step(A, B, U, h):
  %Equal.sym(Nat, Nat.add(Nat.double(B), Nat.double(U)), Nat.double(Nat.add(B, U)), Nat.double_add(B, U)) : Nat.LE(Nat.double(A), _)
  Nat.double_mono(A, Nat.add(B, U), h)

law bound_sh.go:
  for +Y: Nat
  for +X: Nat
  for +k: Nat
  for b: Bound(Y, X, k)
  Bound(Nat.double(Y), Nat.double(X), 1n+k)

def bound_sh.go(Y, X, k, b):
  (l, r) = b
  (bound_sh.step(Nat.double(Y), Nat.double(X), sh(1n, k), l), bound_sh.step(Nat.double(X), Nat.double(Y), sh(1n, k), r))

# a bound scaled by 2^e
law bound_sh:
  for +Y: Nat
  for +X: Nat
  for +k: Nat
  for e: Nat
  for b: Bound(Y, X, k)
  Bound(sh(Y, e), sh(X, e), Nat.add(e, k))

def bound_sh(Y, X, k, e, b):
  match e:
    case 0n:
      b
    case 1n++j:
      bound_sh.go(sh(Y, j), sh(X, j), Nat.add(j, k), bound_sh(Y, X, k, j, b))

law sh_sh:
  for +q: Nat
  for +k: Nat
  for e: Nat
  {sh(sh(q, k), e) == sh(q, Nat.add(e, k)) : Nat}

def sh_sh(q, k, e):
  match e:
    case 0n:
      {==}
    case 1n+j:
      %sh_sh(q, k, j) : {Nat.double(sh(sh(q, k), j)) == Nat.double(_) : Nat}
      {==}

law add_sub_gt.succ:
  for +ep: Nat
  for +tp: Nat
  for e: {Nat.add(ep, Nat.sub(tp, ep)) == tp : Nat}
  {1n+Nat.add(ep, Nat.sub(tp, ep)) == 1n+tp : Nat}

def add_sub_gt.succ(ep, tp, e):
  %e : {1n+Nat.add(ep, Nat.sub(tp, ep)) == 1n+_ : Nat}
  {==}

# t > e: e + (t - e) is t
law add_sub_gt:
  for e: Nat
  for +t: Nat
  {Nat.is_le(t, e) == False{} : Bool} -> {Nat.add(e, Nat.sub(t, e)) == t : Nat}

def add_sub_gt(e, t):
  match e t:
    case 0n 0n:
      h => {==}
    case 0n 1n+tp:
      h => {==}
    case 1n++ep 0n:
      h => void({Nat.add(1n+ep, 0n) == 0n : Nat}, no_t(h))
    case 1n++ep 1n++tp:
      h => add_sub_gt.succ(ep, tp, add_sub_gt(ep, tp)(h))


# the rounded mantissa R at t, from its bound at e with k = t - e bits off
law lift:
  for +R: Bin.Bin
  for +X: Nat
  for +e: Nat
  for +t: Nat
  for heq: {Nat.add(e, Nat.sub(t, e)) == t : Nat}
  for b: Bound(sh(Bin.to_nat(R), Nat.sub(t, e)), X, Nat.sub(t, e))
  Bound(sh(Bin.to_nat(R), t), sh(X, e), t)

def lift(R, X, e, t, heq, b):
  %heq : Bound(sh(Bin.to_nat(R), _), sh(X, e), _)
  %sh_sh(Bin.to_nat(R), Nat.sub(t, e), e) : Bound(_, sh(X, e), Nat.add(e, Nat.sub(t, e)))
  bound_sh(sh(Bin.to_nat(R), Nat.sub(t, e)), X, Nat.sub(t, e), e, b)

law lift_zero.go:
  for +R: Bin.Bin
  for +X: Nat
  for +t: Nat
  for bf: Bound(sh(Bin.to_nat(R), t), X, t)
  for ez: {Bin.is_zero(R) == True{} : Bool}
  Bound(0n, X, t)

def lift_zero.go(R, X, t, bf, ez):
  %sh_num_zero(R, t, ez) : Bound(_, X, t)
  bf


law round_fin_near.at:
  for +top: Nat
  for neg: Bool
  for +t: Nat
  for +X: Nat
  for +e: Nat
  for +R: Bin.Bin
  for +heq: {Nat.add(e, Nat.sub(t, e)) == t : Nat}
  for b: Bound(sh(Bin.to_nat(R), Nat.sub(t, e)), X, Nat.sub(t, e))
  Near(Fmt.over(top, neg, R, t), sh(X, e), t)

def round_fin_near.at(top, neg, t, X, e, R, heq, b):
  over_near(top, neg, R, t, sh(X, e), t, lift(R, X, e, t, heq, b), bf => ez => lift_zero.go(R, sh(X, e), t, bf, ez))

law round_fin_near.go:
  for +top: Nat
  for neg: Bool
  for +t: Nat
  for +X: Nat
  for +e: Nat
  for +q: Bin.Bin
  for +r: Bool
  for +s: Bool
  for +T: Nat
  for +heq: {Nat.add(e, Nat.sub(t, e)) == t : Nat}
  After((q, r, s), X, Nat.sub(t, e), T) -> Near(Fmt.round.fin(top, neg, t, (q, r, s)), sh(X, e), t)

def round_fin_near.go(top, neg, t, X, e, q, r, s, T, heq):
  +R = Fmt.round.up(q, Bool.and(r, Bool.or(s, Bin.odd(q))))
  x => round_fin_near.at(top, neg, t, X, e, R, heq, fin_near(q, r, s, X, Nat.sub(t, e), T)(x))

law round_fin_near:
  for +top: Nat
  for neg: Bool
  for +t: Nat
  for +X: Nat
  for +e: Nat
  for res: Bin.Bin & Bool & Bool
  for +T: Nat
  for +heq: {Nat.add(e, Nat.sub(t, e)) == t : Nat}
  After(res, X, Nat.sub(t, e), T) -> Near(Fmt.round.fin(top, neg, t, res), sh(X, e), t)

def round_fin_near(top, neg, t, X, e, res, T, heq):
  (q, r, s) = res
  round_fin_near.go(top, neg, t, X, e, q, r, s, T, heq)

law exact_near.zero:
  for +m: Bin.Bin
  for +e: Nat
  for +t: Nat
  for ez: {Bin.is_zero(m) == True{} : Bool}
  Bound(0n, sh(Bin.to_nat(m), e), t)

def exact_near.zero(m, e, t, ez):
  %Equal.sym(Nat, sh(Bin.to_nat(m), e), 0n, sh_num_zero(m, e, ez)) : Bound(0n, _, t)
  (Unit{}, Unit{})

# exact: m kept at e, so its value is X itself
law exact_near:
  for +top: Nat
  for neg: Bool
  for +m: Bin.Bin
  for +e: Nat
  for +t: Nat
  Near(Fmt.over(top, neg, m, e), sh(Bin.to_nat(m), e), t)

def exact_near(top, neg, m, e, t):
  +Z = sh(Bin.to_nat(m), e)
  over_near(top, neg, m, e, Z, t, (Nat.le_add_r(Nat.double(Z), sh(1n, e)), Nat.le_add_r(Nat.double(Z), sh(1n, e))), bf => ez => exact_near.zero(m, e, t, ez))


law after_zero:
  for res: Bin.Bin & Bool & Bool
  for +M: Nat
  for +k: Nat
  for +T: Nat
  for x: After(res, M, Nat.add(k, 0n), T)
  After(res, M, k, T)

def after_zero(res, M, k, T, x):
  %Equal.sym(Nat, k, Nat.add(k, 0n), Nat.add_zero_r(k)) : After(res, M, _, T)
  x

law round_go_near:
  for +top: Nat
  for neg: Bool
  for +m: Bin.Bin
  for +e: Nat
  for +t: Nat
  for exact: Bool
  for eq: {Nat.is_le(t, e) == exact : Bool}
  Near(Fmt.round.go(top, neg, m, e, t, exact), sh(Bin.to_nat(m), e), t)

def round_go_near(top, neg, m, e, t, exact, eq):
  match exact:
    case True{}:
      exact_near(top, neg, m, e, t)
    case False{}:
      +k = Nat.sub(t, e)
      +X = Bin.to_nat(m)
      round_fin_near(top, neg, t, X, e, Bin.shr(k, m, False{}, False{}), rest(k, m, 0n, 0n), add_sub_gt(e, t)(eq))(
        after_zero(Bin.shr(k, m, False{}, False{}), X, k, rest(k, m, 0n, 0n),
          shr_ok(k, m, False{}, False{}, 0n, X, 0n)(Nat.add_zero_r(X))(Unit{})))

# Fmt.round is correct to half an ulp: a finite result is within half its
# own ulp of m * 2^e, a zero within half of 2^lsb; or it overflows to
# infinity
law round_near:
  for +f: Fmt.Format
  for neg: Bool
  for +m: Bin.Bin
  for +e: Nat
  Near(Fmt.round(f, neg, m, e), sh(Bin.to_nat(m), e), Fmt.lsb(f, m, e))

def round_near(f, neg, m, e):
  +t = Fmt.lsb(f, m, e)
  round_go_near(Fmt.top(f), neg, m, e, t, Nat.is_le(t, e), {==})

# Exact binary arithmetic
# -----------------------
# Bin.add, Bin.mul and Bin.shl compute the exact sum, product and
# scaling of the numbers, so a bound on a rounded Bin result is a bound
# against the exact value.

def bit(c: Bool) -> Nat:
  match c:
    case False{}:
      0n
    case True{}:
      1n

law cons_num:
  for c: Bool
  for +r: Bin.Bin
  {Nat.add(bit(c), Nat.double(Bin.to_nat(r))) == Bin.to_nat(Bin.cons(c, r)) : Nat}

def cons_num(c, r):
  match c:
    case False{}:
      {==}
    case True{}:
      {==}

law adc_one_ok:
  for +a: Bin.Bin
  for c: Bool
  {Nat.add(bit(c), Bin.to_nat(a)) == Bin.to_nat(Bin.adc.one(a, c)) : Nat}

def adc_one_ok(a, c):
  match c:
    case False{}:
      {==}
    case True{}:
      num_inc(a)

# bits 0 and 0 carry c into the low bit and nothing up
law adc_00:
  for +c: Bool
  for +X: Nat
  for +Y: Nat
  for +r: Bin.Bin
  for ih: {Nat.add(X, Y) == Bin.to_nat(r) : Nat}
  {Nat.add(bit(c), Nat.add(Nat.double(X), Nat.double(Y))) == Bin.to_nat(Bin.cons(c, r)) : Nat}

def adc_00(c, X, Y, r, ih):
  %cons_num(c, r) : {Nat.add(bit(c), Nat.add(Nat.double(X), Nat.double(Y))) == _ : Nat}
  %ih : {Nat.add(bit(c), Nat.add(Nat.double(X), Nat.double(Y))) == Nat.add(bit(c), Nat.double(_)) : Nat}
  %Nat.double_add(X, Y) : {Nat.add(bit(c), Nat.add(Nat.double(X), Nat.double(Y))) == Nat.add(bit(c), _) : Nat}
  {==}

# bits 1 and 1 carry c into the low bit and 1 up
law adc_11:
  for +c: Bool
  for +X: Nat
  for +Y: Nat
  for +r: Bin.Bin
  for ih: {1n+Nat.add(X, Y) == Bin.to_nat(r) : Nat}
  {Nat.add(bit(c), Nat.add(1n+Nat.double(X), 1n+Nat.double(Y))) == Bin.to_nat(Bin.cons(c, r)) : Nat}

def adc_11(c, X, Y, r, ih):
  %cons_num(c, r) : {Nat.add(bit(c), Nat.add(1n+Nat.double(X), 1n+Nat.double(Y))) == _ : Nat}
  %ih : {Nat.add(bit(c), Nat.add(1n+Nat.double(X), 1n+Nat.double(Y))) == Nat.add(bit(c), Nat.double(_)) : Nat}
  %Nat.double_add(X, Y) : {Nat.add(bit(c), Nat.add(1n+Nat.double(X), 1n+Nat.double(Y))) == Nat.add(bit(c), 2n+_) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.double(X), 1n+Nat.double(Y)), 1n+Nat.add(Nat.double(X), Nat.double(Y)), Nat.add_succ_r(Nat.double(X), Nat.double(Y))) : {Nat.add(bit(c), 1n+_) == Nat.add(bit(c), 2n+Nat.add(Nat.double(X), Nat.double(Y))) : Nat}
  {==}

# one bit set: the low bit is not(c), and c carries up
law adc_10:
  for c: Bool
  for +X: Nat
  for +Y: Nat
  for +r: Bin.Bin
  for ih: {Nat.add(bit(c), Nat.add(X, Y)) == Bin.to_nat(r) : Nat}
  {Nat.add(bit(c), 1n+Nat.add(Nat.double(X), Nat.double(Y))) == Bin.to_nat(Bin.cons(Bool.not(c), r)) : Nat}

def adc_10(c, X, Y, r, ih):
  match c:
    case False{}:
      %ih : {1n+Nat.add(Nat.double(X), Nat.double(Y)) == 1n+Nat.double(_) : Nat}
      %Nat.double_add(X, Y) : {1n+Nat.add(Nat.double(X), Nat.double(Y)) == 1n+_ : Nat}
      {==}
    case True{}:
      %ih : {2n+Nat.add(Nat.double(X), Nat.double(Y)) == Nat.double(_) : Nat}
      %Nat.double_add(X, Y) : {2n+Nat.add(Nat.double(X), Nat.double(Y)) == 2n+_ : Nat}
      {==}

law adc_01:
  for +c: Bool
  for +X: Nat
  for +Y: Nat
  for +r: Bin.Bin
  for ih: {Nat.add(bit(c), Nat.add(X, Y)) == Bin.to_nat(r) : Nat}
  {Nat.add(bit(c), Nat.add(Nat.double(X), 1n+Nat.double(Y))) == Bin.to_nat(Bin.cons(Bool.not(c), r)) : Nat}

def adc_01(c, X, Y, r, ih):
  %Equal.sym(Nat, Nat.add(Nat.double(X), 1n+Nat.double(Y)), 1n+Nat.add(Nat.double(X), Nat.double(Y)), Nat.add_succ_r(Nat.double(X), Nat.double(Y))) : {Nat.add(bit(c), _) == Bin.to_nat(Bin.cons(Bool.not(c), r)) : Nat}
  adc_10(c, X, Y, r, ih)

# Bin.adc is exact: bit(c) + a + b
law adc_ok:
  for a: Bin.Bin
  for b: Bin.Bin
  for +c: Bool
  {Nat.add(bit(c), Nat.add(Bin.to_nat(a), Bin.to_nat(b))) == Bin.to_nat(Bin.adc(a, b, c)) : Nat}

# Bin.adc's clauses overlap (BZ b, then a BZ), so adc(BZ, b, c) reduces
# only once b's constructor is known: the BZ case splits b.
def adc_ok(a, b, c):
  match a b:
    case Bin.BZ{} Bin.BZ{}:
      adc_one_ok(Bin.BZ{}, c)
    case Bin.BZ{} Bin.B0{y}:
      adc_one_ok(Bin.B0{y}, c)
    case Bin.BZ{} Bin.B1{y}:
      adc_one_ok(Bin.B1{y}, c)
    case Bin.B0{+x} Bin.BZ{}:
      %Nat.add_zero_r(Nat.double(Bin.to_nat(x))) : {Nat.add(bit(c), _) == Bin.to_nat(Bin.adc.one(Bin.B0{x}, c)) : Nat}
      adc_one_ok(Bin.B0{x}, c)
    case Bin.B1{+x} Bin.BZ{}:
      %Nat.add_zero_r(1n+Nat.double(Bin.to_nat(x))) : {Nat.add(bit(c), _) == Bin.to_nat(Bin.adc.one(Bin.B1{x}, c)) : Nat}
      adc_one_ok(Bin.B1{x}, c)
    case Bin.B0{+x} Bin.B0{+y}:
      adc_00(c, Bin.to_nat(x), Bin.to_nat(y), Bin.adc(x, y, False{}), adc_ok(x, y, False{}))
    case Bin.B0{+x} Bin.B1{+y}:
      adc_01(c, Bin.to_nat(x), Bin.to_nat(y), Bin.adc(x, y, c), adc_ok(x, y, c))
    case Bin.B1{+x} Bin.B0{+y}:
      adc_10(c, Bin.to_nat(x), Bin.to_nat(y), Bin.adc(x, y, c), adc_ok(x, y, c))
    case Bin.B1{+x} Bin.B1{+y}:
      adc_11(c, Bin.to_nat(x), Bin.to_nat(y), Bin.adc(x, y, True{}), adc_ok(x, y, True{}))

# Bin.add is exact
law add_ok:
  for +a: Bin.Bin
  for +b: Bin.Bin
  {Nat.add(Bin.to_nat(a), Bin.to_nat(b)) == Bin.to_nat(Bin.add(a, b)) : Nat}

def add_ok(a, b):
  adc_ok(a, b, False{})

law mul_double:
  for R: Nat
  for +B: Nat
  {Nat.mul(Nat.double(R), B) == Nat.double(Nat.mul(R, B)) : Nat}

def mul_double(R, B):
  match R:
    case 0n:
      {==}
    case 1n++p:
      %Nat.double_add(B, Nat.mul(p, B)) : {Nat.add(B, Nat.add(B, Nat.mul(Nat.double(p), B))) == _ : Nat}
      %mul_double(p, B) : {Nat.add(B, Nat.add(B, Nat.mul(Nat.double(p), B))) == Nat.add(Nat.double(B), _) : Nat}
      %Nat.double_is_add(B) : {Nat.add(B, Nat.add(B, Nat.mul(Nat.double(p), B))) == Nat.add(_, Nat.mul(Nat.double(p), B)) : Nat}
      Nat.add_assoc(B, B, Nat.mul(Nat.double(p), B))

# Bin.mul is exact
law mul_ok:
  for a: Bin.Bin
  for +b: Bin.Bin
  {Nat.mul(Bin.to_nat(a), Bin.to_nat(b)) == Bin.to_nat(Bin.mul(a, b)) : Nat}

def mul_ok(a, b):
  match a:
    case Bin.BZ{}:
      {==}
    case Bin.B0{+r}:
      %mul_ok(r, b) : {Nat.mul(Nat.double(Bin.to_nat(r)), Bin.to_nat(b)) == Nat.double(_) : Nat}
      mul_double(Bin.to_nat(r), Bin.to_nat(b))
    case Bin.B1{+r}:
      %add_ok(b, Bin.B0{Bin.mul(r, b)}) : {Nat.add(Bin.to_nat(b), Nat.mul(Nat.double(Bin.to_nat(r)), Bin.to_nat(b))) == _ : Nat}
      %mul_ok(r, b) : {Nat.add(Bin.to_nat(b), Nat.mul(Nat.double(Bin.to_nat(r)), Bin.to_nat(b))) == Nat.add(Bin.to_nat(b), Nat.double(_)) : Nat}
      %Equal.sym(Nat, Nat.mul(Nat.double(Bin.to_nat(r)), Bin.to_nat(b)), Nat.double(Nat.mul(Bin.to_nat(r), Bin.to_nat(b))), mul_double(Bin.to_nat(r), Bin.to_nat(b))) : {Nat.add(Bin.to_nat(b), _) == Nat.add(Bin.to_nat(b), Nat.double(Nat.mul(Bin.to_nat(r), Bin.to_nat(b)))) : Nat}
      {==}

# Bin.shl is exact scaling
law shl_ok:
  for +a: Bin.Bin
  for n: Nat
  {Bin.to_nat(Bin.shl(a, n)) == sh(Bin.to_nat(a), n) : Nat}

def shl_ok(a, n):
  match n:
    case 0n:
      {==}
    case 1n+k:
      %shl_ok(a, k) : {Nat.double(Bin.to_nat(Bin.shl(a, k))) == Nat.double(_) : Nat}
      {==}

# t >= e: e + (t - e) is t
law add_sub_ge:
  for e: Nat
  for +t: Nat
  {Nat.is_ge(t, e) == True{} : Bool} -> {Nat.add(e, Nat.sub(t, e)) == t : Nat}

def add_sub_ge(e, t):
  match e t:
    case 0n 0n:
      h => {==}
    case 0n 1n+tp:
      h => {==}
    case 1n++ep 0n:
      h => void({Nat.add(1n+ep, 0n) == 0n : Nat}, no_f(h))
    case 1n++ep 1n++tp:
      h => add_sub_gt.succ(ep, tp, add_sub_ge(ep, tp)(h))

# e < t: e + (t - e) is t
law add_sub_lt:
  for e: Nat
  for +t: Nat
  {Nat.is_ge(e, t) == False{} : Bool} -> {Nat.add(e, Nat.sub(t, e)) == t : Nat}

def add_sub_lt(e, t):
  match e t:
    case 0n 0n:
      h => void({0n == 0n : Nat}, no_t(h))
    case 0n 1n+tp:
      h => {==}
    case 1n++ep 0n:
      h => void({Nat.add(1n+ep, 0n) == 0n : Nat}, no_t(h))
    case 1n++ep 1n++tp:
      h => add_sub_gt.succ(ep, tp, add_sub_lt(ep, tp)(h))

# Laws about the IEEE operations
# ------------------------------

# the exponent of a product's exact value, 2^(ea-300) * 2^(eb-300) in
# the offset form (both at least 150 for every binary32 value)
def mul_exp(+ea: Nat, +eb: Nat) -> Nat:
  Nat.sub(Nat.add(ea, eb), 300n)

# a product of finite values is within half its own ulp of the exact
# product ma * mb * 2^(ea + eb), or it overflows
law mul_near:
  for +f: Fmt.Format
  for na: Bool
  for +ma: Bin.Bin
  for +ea: Nat
  for nb: Bool
  for +mb: Bin.Bin
  for +eb: Nat
  Near(Fmt.spec_mul(f, Fmt.Fin{na, ma, ea}, Fmt.Fin{nb, mb, eb}), sh(Nat.mul(Bin.to_nat(ma), Bin.to_nat(mb)), mul_exp(ea, eb)), Fmt.lsb(f, Bin.mul(ma, mb), mul_exp(ea, eb)))

def mul_near(f, na, ma, ea, nb, mb, eb):
  %Equal.sym(Nat, Nat.mul(Bin.to_nat(ma), Bin.to_nat(mb)), Bin.to_nat(Bin.mul(ma, mb)), mul_ok(ma, mb)) : Near(Fmt.spec_mul(f, Fmt.Fin{na, ma, ea}, Fmt.Fin{nb, mb, eb}), sh(_, mul_exp(ea, eb)), Fmt.lsb(f, Bin.mul(ma, mb), mul_exp(ea, eb)))
  round_near(f, Bool.xor(na, nb), Bin.mul(ma, mb), mul_exp(ea, eb))

# the ulp exponent spec_add rounds a sum of same-sign values to
def sum_lsb.go(+f: Fmt.Format, +ma: Bin.Bin, +ea: Nat, +mb: Bin.Bin, +eb: Nat, hi: Bool) -> Nat:
  match hi:
    case True{}:
      Fmt.lsb(f, Bin.add(Bin.shl(ma, Nat.sub(ea, eb)), mb), eb)
    case False{}:
      Fmt.lsb(f, Bin.add(ma, Bin.shl(mb, Nat.sub(eb, ea))), ea)

def sum_lsb(+f: Fmt.Format, +ma: Bin.Bin, +ea: Nat, +mb: Bin.Bin, +eb: Nat) -> Nat:
  sum_lsb.go(f, ma, ea, mb, eb, Nat.is_ge(ea, eb))

# the exact sum of a and b aligned at b's exponent (ea >= eb)
law add_near.hi:
  for +f: Fmt.Format
  for +n: Bool
  for +ma: Bin.Bin
  for +ea: Nat
  for +mb: Bin.Bin
  for +eb: Nat
  for eh: {Nat.is_ge(ea, eb) == True{} : Bool}
  Near(Fmt.round(f, n, Bin.add(Bin.shl(ma, Nat.sub(ea, eb)), mb), eb), Nat.add(sh(Bin.to_nat(ma), ea), sh(Bin.to_nat(mb), eb)), Fmt.lsb(f, Bin.add(Bin.shl(ma, Nat.sub(ea, eb)), mb), eb))

def add_near.hi(f, n, ma, ea, mb, eb, eh):
  +d = Nat.sub(ea, eb)
  +A = Bin.shl(ma, d)
  +R = Fmt.round(f, n, Bin.add(A, mb), eb)
  +L = Fmt.lsb(f, Bin.add(A, mb), eb)
  %add_sub_ge(eb, ea)(eh) : Near(R, Nat.add(sh(Bin.to_nat(ma), _), sh(Bin.to_nat(mb), eb)), L)
  %sh_sh(Bin.to_nat(ma), d, eb) : Near(R, Nat.add(_, sh(Bin.to_nat(mb), eb)), L)
  %shl_ok(ma, d) : Near(R, Nat.add(sh(_, eb), sh(Bin.to_nat(mb), eb)), L)
  %Equal.sym(Nat, Nat.add(sh(Bin.to_nat(A), eb), sh(Bin.to_nat(mb), eb)), sh(Nat.add(Bin.to_nat(A), Bin.to_nat(mb)), eb), sh_add(Bin.to_nat(A), Bin.to_nat(mb), eb)) : Near(R, _, L)
  %Equal.sym(Nat, Nat.add(Bin.to_nat(A), Bin.to_nat(mb)), Bin.to_nat(Bin.add(A, mb)), add_ok(A, mb)) : Near(R, sh(_, eb), L)
  round_near(f, n, Bin.add(A, mb), eb)

# the exact sum aligned at a's exponent (ea < eb)
law add_near.lo:
  for +f: Fmt.Format
  for +n: Bool
  for +ma: Bin.Bin
  for +ea: Nat
  for +mb: Bin.Bin
  for +eb: Nat
  for eh: {Nat.is_ge(ea, eb) == False{} : Bool}
  Near(Fmt.round(f, n, Bin.add(ma, Bin.shl(mb, Nat.sub(eb, ea))), ea), Nat.add(sh(Bin.to_nat(ma), ea), sh(Bin.to_nat(mb), eb)), Fmt.lsb(f, Bin.add(ma, Bin.shl(mb, Nat.sub(eb, ea))), ea))

def add_near.lo(f, n, ma, ea, mb, eb, eh):
  +d = Nat.sub(eb, ea)
  +B = Bin.shl(mb, d)
  +R = Fmt.round(f, n, Bin.add(ma, B), ea)
  +L = Fmt.lsb(f, Bin.add(ma, B), ea)
  %add_sub_lt(ea, eb)(eh) : Near(R, Nat.add(sh(Bin.to_nat(ma), ea), sh(Bin.to_nat(mb), _)), L)
  %sh_sh(Bin.to_nat(mb), d, ea) : Near(R, Nat.add(sh(Bin.to_nat(ma), ea), _), L)
  %shl_ok(mb, d) : Near(R, Nat.add(sh(Bin.to_nat(ma), ea), sh(_, ea)), L)
  %Equal.sym(Nat, Nat.add(sh(Bin.to_nat(ma), ea), sh(Bin.to_nat(B), ea)), sh(Nat.add(Bin.to_nat(ma), Bin.to_nat(B)), ea), sh_add(Bin.to_nat(ma), Bin.to_nat(B), ea)) : Near(R, _, L)
  %Equal.sym(Nat, Nat.add(Bin.to_nat(ma), Bin.to_nat(B)), Bin.to_nat(Bin.add(ma, B)), add_ok(ma, B)) : Near(R, sh(_, ea), L)
  round_near(f, n, Bin.add(ma, B), ea)

law add_near.go:
  for +f: Fmt.Format
  for n: Bool
  for +ma: Bin.Bin
  for +ea: Nat
  for +mb: Bin.Bin
  for +eb: Nat
  for hi: Bool
  for eh: {Nat.is_ge(ea, eb) == hi : Bool}
  Near(Fmt.add.fin.go(f, n, ma, ea, n, mb, eb, hi), Nat.add(sh(Bin.to_nat(ma), ea), sh(Bin.to_nat(mb), eb)), sum_lsb.go(f, ma, ea, mb, eb, hi))

def add_near.go(f, n, ma, ea, mb, eb, hi, eh):
  match n hi:
    case False{} True{}:
      add_near.hi(f, False{}, ma, ea, mb, eb, eh)
    case True{} True{}:
      add_near.hi(f, True{}, ma, ea, mb, eb, eh)
    case False{} False{}:
      add_near.lo(f, False{}, ma, ea, mb, eb, eh)
    case True{} False{}:
      add_near.lo(f, True{}, ma, ea, mb, eb, eh)

# a sum of two finite values of the same sign is within half its own ulp
# of the exact sum, or it overflows
law add_near:
  for +f: Fmt.Format
  for +n: Bool
  for +ma: Bin.Bin
  for +ea: Nat
  for +mb: Bin.Bin
  for +eb: Nat
  Near(Fmt.spec_add(f, Fmt.Fin{n, ma, ea}, Fmt.Fin{n, mb, eb}), Nat.add(sh(Bin.to_nat(ma), ea), sh(Bin.to_nat(mb), eb)), sum_lsb(f, ma, ea, mb, eb))

def add_near(f, n, ma, ea, mb, eb):
  add_near.go(f, n, ma, ea, mb, eb, Nat.is_ge(ea, eb), {==})

# Canonical form
# --------------
# Num.Correct compares results through Fmt.canon, which moves a
# mantissa's trailing zeros into the exponent. That keeps the value and
# can only grow a finite result's own ulp, so it keeps the bound.

# a bound for an ulp stays a bound for twice that ulp
law bound_up.step:
  for +A: Nat
  for +B: Nat
  for +U: Nat
  for h: Nat.LE(A, Nat.add(B, U))
  Nat.LE(A, Nat.add(B, Nat.double(U)))

def bound_up.step(A, B, U, h):
  Nat.le_trans(A, Nat.add(B, U), Nat.add(B, Nat.double(U)), h, Nat.add_mono_l(B, U, Nat.double(U), Nat.le_double(U)))

law bound_up:
  for +Y: Nat
  for +X: Nat
  for +k: Nat
  for b: Bound(Y, X, k)
  Bound(Y, X, 1n+k)

def bound_up(Y, X, k, b):
  (l, r) = b
  (bound_up.step(Nat.double(Y), Nat.double(X), sh(1n, k), l), bound_up.step(Nat.double(X), Nat.double(Y), sh(1n, k), r))

law cons0_num:
  for x: Bin.Bin
  {Bin.to_nat(Bin.trim.cons0(x)) == Nat.double(Bin.to_nat(x)) : Nat}

def cons0_num(x):
  match x:
    case Bin.BZ{}:
      {==}
    case Bin.B0{y}:
      {==}
    case Bin.B1{y}:
      {==}

# trimming high zero bits keeps the number
law trim_num:
  for a: Bin.Bin
  {Bin.to_nat(Bin.trim(a)) == Bin.to_nat(a) : Nat}

def trim_num(a):
  match a:
    case Bin.BZ{}:
      {==}
    case Bin.B0{+r}:
      %Equal.sym(Nat, Bin.to_nat(Bin.trim.cons0(Bin.trim(r))), Nat.double(Bin.to_nat(Bin.trim(r))), cons0_num(Bin.trim(r))) : {_ == Nat.double(Bin.to_nat(r)) : Nat}
      %Equal.sym(Nat, Bin.to_nat(Bin.trim(r)), Bin.to_nat(r), trim_num(r)) : {Nat.double(_) == Nat.double(Bin.to_nat(r)) : Nat}
      {==}
    case Bin.B1{+r}:
      %Equal.sym(Nat, Bin.to_nat(Bin.trim(r)), Bin.to_nat(r), trim_num(r)) : {1n+Nat.double(_) == 1n+Nat.double(Bin.to_nat(r)) : Nat}
      {==}

law strip_b0:
  for +r: Bin.Bin
  for +t: Nat
  for +X: Nat
  for b: Bound(sh(Nat.double(Bin.to_nat(r)), t), X, t)
  Bound(sh(Bin.to_nat(r), 1n+t), X, 1n+t)

def strip_b0(r, t, X, b):
  %Equal.sym(Nat, Nat.double(sh(Bin.to_nat(r), t)), sh(Nat.double(Bin.to_nat(r)), t), sh_double(Bin.to_nat(r), t)) : Bound(_, X, 1n+t)
  bound_up(sh(Nat.double(Bin.to_nat(r)), t), X, t, b)

law strip_b1:
  for +r: Bin.Bin
  for +t: Nat
  for +X: Nat
  for b: Bound(sh(1n+Nat.double(Bin.to_nat(r)), t), X, t)
  Bound(sh(1n+Nat.double(Bin.to_nat(Bin.trim(r))), t), X, t)

def strip_b1(r, t, X, b):
  %Equal.sym(Nat, Bin.to_nat(Bin.trim(r)), Bin.to_nat(r), trim_num(r)) : Bound(sh(1n+Nat.double(_), t), X, t)
  b

law strip_near:
  for neg: Bool
  for m: Bin.Bin
  for +t: Nat
  for +X: Nat
  for +u: Nat
  Bound(sh(Bin.to_nat(m), t), X, t) -> Nat.IsFalse(Bin.is_zero(m)) -> Near(Fmt.strip(neg, m, t), X, u)

def strip_near(neg, m, t, X, u):
  match m:
    case Bin.BZ{}:
      b => nz => void(Bound(0n, X, u), nz)
    case Bin.B0{+r}:
      b => nz => strip_near(neg, r, 1n+t, X, u)(strip_b0(r, t, X, b))(nz)
    case Bin.B1{+r}:
      b => nz => (strip_b1(r, t, X, b), Unit{})

law canon_fin:
  for n: Bool
  for +m: Bin.Bin
  for +t: Nat
  for +X: Nat
  for +u: Nat
  for h: Bound(sh(Bin.to_nat(m), t), X, t) & Nat.IsFalse(Bin.is_zero(m))
  Near(Fmt.strip(n, m, t), X, u)

def canon_fin(n, m, t, X, u, h):
  (b, nz) = h
  strip_near(n, m, t, X, u)(b)(nz)

# the canonical form of a rounded value keeps its bound
law canon_near:
  for v: Fmt.Val
  for +X: Nat
  for +u: Nat
  Near(v, X, u) -> Near(Fmt.canon(v), X, u)

def canon_near(v, X, u):
  match v:
    case Fmt.Z{n}:
      h => h
    case Fmt.Inf{n}:
      h => h
    case Fmt.NaN{}:
      h => h
    case Fmt.Fin{n, +m, +t}:
      h => canon_fin(n, m, t, X, u, h)

# Hardware
# --------
# Under SF32.HardOk (the hardware's F32.add and F32.mul round correctly),
# the bounds hold for Base's own operations: the hardware result, in
# canonical form, is within half its own ulp of the exact result.

law hard_mul_near:
  for ~ok: SF32.HardOk()
  for +a: F32
  for +b: F32
  for +na: Bool
  for +ma: Bin.Bin
  for +ea: Nat
  for +nb: Bool
  for +mb: Bin.Bin
  for +eb: Nat
  for da: {SF32.decode(a) == Fmt.Fin{na, ma, ea} : Fmt.Val}
  for db: {SF32.decode(b) == Fmt.Fin{nb, mb, eb} : Fmt.Val}
  Near(Fmt.canon(SF32.decode(F32.mul(a, b))), sh(Nat.mul(Bin.to_nat(ma), Bin.to_nat(mb)), mul_exp(ea, eb)), Fmt.lsb(Fmt.binary32(), Bin.mul(ma, mb), mul_exp(ea, eb)))

def hard_mul_near(ok, a, b, na, ma, ea, nb, mb, eb, da, db):
  +X = sh(Nat.mul(Bin.to_nat(ma), Bin.to_nat(mb)), mul_exp(ea, eb))
  +u = Fmt.lsb(Fmt.binary32(), Bin.mul(ma, mb), mul_exp(ea, eb))
  %Equal.sym(Fmt.Val, Fmt.canon(SF32.decode(F32.mul(a, b))), Fmt.canon(Fmt.spec_mul(Fmt.binary32(), SF32.decode(a), SF32.decode(b))), Num.Correct.mul(F32, SF32.hard(), ok, a, b)) : Near(_, X, u)
  %Equal.sym(Fmt.Val, SF32.decode(a), Fmt.Fin{na, ma, ea}, da) : Near(Fmt.canon(Fmt.spec_mul(Fmt.binary32(), _, SF32.decode(b))), X, u)
  %Equal.sym(Fmt.Val, SF32.decode(b), Fmt.Fin{nb, mb, eb}, db) : Near(Fmt.canon(Fmt.spec_mul(Fmt.binary32(), Fmt.Fin{na, ma, ea}, _)), X, u)
  canon_near(Fmt.spec_mul(Fmt.binary32(), Fmt.Fin{na, ma, ea}, Fmt.Fin{nb, mb, eb}), X, u)(mul_near(Fmt.binary32(), na, ma, ea, nb, mb, eb))

law hard_add_near:
  for ~ok: SF32.HardOk()
  for +a: F32
  for +b: F32
  for +n: Bool
  for +ma: Bin.Bin
  for +ea: Nat
  for +mb: Bin.Bin
  for +eb: Nat
  for da: {SF32.decode(a) == Fmt.Fin{n, ma, ea} : Fmt.Val}
  for db: {SF32.decode(b) == Fmt.Fin{n, mb, eb} : Fmt.Val}
  Near(Fmt.canon(SF32.decode(F32.add(a, b))), Nat.add(sh(Bin.to_nat(ma), ea), sh(Bin.to_nat(mb), eb)), sum_lsb(Fmt.binary32(), ma, ea, mb, eb))

def hard_add_near(ok, a, b, n, ma, ea, mb, eb, da, db):
  +X = Nat.add(sh(Bin.to_nat(ma), ea), sh(Bin.to_nat(mb), eb))
  +u = sum_lsb(Fmt.binary32(), ma, ea, mb, eb)
  %Equal.sym(Fmt.Val, Fmt.canon(SF32.decode(F32.add(a, b))), Fmt.canon(Fmt.spec_add(Fmt.binary32(), SF32.decode(a), SF32.decode(b))), Num.Correct.add(F32, SF32.hard(), ok, a, b)) : Near(_, X, u)
  %Equal.sym(Fmt.Val, SF32.decode(a), Fmt.Fin{n, ma, ea}, da) : Near(Fmt.canon(Fmt.spec_add(Fmt.binary32(), _, SF32.decode(b))), X, u)
  %Equal.sym(Fmt.Val, SF32.decode(b), Fmt.Fin{n, mb, eb}, db) : Near(Fmt.canon(Fmt.spec_add(Fmt.binary32(), Fmt.Fin{n, ma, ea}, _)), X, u)
  canon_near(Fmt.spec_add(Fmt.binary32(), Fmt.Fin{n, ma, ea}, Fmt.Fin{n, mb, eb}), X, u)(add_near(Fmt.binary32(), n, ma, ea, mb, eb))


# A physics step
# --------------
# x' = x + v * dt rounds twice: the product, then the sum. The sum is
# within half its ulp of x + p, p within half its ulp of v * dt, so x' is
# within half of ulp(x') + ulp(p) of the exact x + v * dt.

# the exponent of the canonical form of m at t: its ulp; u if m is zero
def ulp_of(m: Bin.Bin, +t: Nat, u: Nat) -> Nat:
  match m:
    case Bin.BZ{}:
      u
    case Bin.B0{r}:
      ulp_of(r, 1n+t, u)
    case Bin.B1{r}:
      t

law strip_val.z:
  for +t: Nat
  for +X: Nat
  for +u: Nat
  for h: Bound(0n, X, u)
  Bound(sh(0n, t), X, u)

def strip_val.z(t, X, u, h):
  %sh_zero(t) : Bound(_, X, u)
  h

law strip_val.b0:
  for +r: Bin.Bin
  for +t: Nat
  for +X: Nat
  for +W: Nat
  for h: Bound(sh(Bin.to_nat(r), 1n+t), X, W)
  Bound(sh(Nat.double(Bin.to_nat(r)), t), X, W)

def strip_val.b0(r, t, X, W, h):
  %sh_double(Bin.to_nat(r), t) : Bound(_, X, W)
  h

law strip_val.b1:
  for +r: Bin.Bin
  for +t: Nat
  for +X: Nat
  for h: Bound(sh(1n+Nat.double(Bin.to_nat(Bin.trim(r))), t), X, t) & Nat.IsFalse(Bin.is_zero(Bin.B1{Bin.trim(r)}))
  Bound(sh(1n+Nat.double(Bin.to_nat(r)), t), X, t)

def strip_val.b1(r, t, X, h):
  (b, nz) = h
  %trim_num(r) : Bound(sh(1n+Nat.double(_), t), X, t)
  b

# the canonical form's bound is a bound on the value it came from, at the
# canonical form's ulp
law strip_val:
  for n: Bool
  for m: Bin.Bin
  for +t: Nat
  for +X: Nat
  for +u: Nat
  Near(Fmt.strip(n, m, t), X, u) -> Bound(sh(Bin.to_nat(m), t), X, ulp_of(m, t, u))

def strip_val(n, m, t, X, u):
  match m:
    case Bin.BZ{}:
      h => strip_val.z(t, X, u, h)
    case Bin.B0{+r}:
      h => strip_val.b0(r, t, X, ulp_of(r, 1n+t, u), strip_val(n, r, 1n+t, X, u)(h))
    case Bin.B1{+r}:
      h => strip_val.b1(r, t, X, h)

# 2|Y - X| <= 2^k + 2^w
def Bound2(+Y: Nat, +X: Nat, +k: Nat, +w: Nat) -> Type:
  Nat.LE(Nat.double(Y), Nat.add(Nat.add(Nat.double(X), sh(1n, k)), sh(1n, w))) & Nat.LE(Nat.double(X), Nat.add(Nat.add(Nat.double(Y), sh(1n, k)), sh(1n, w)))

law compose.lo.m:
  for +A: Nat
  for +P: Nat
  for +Pe: Nat
  for +W: Nat
  for h2: Nat.LE(Nat.double(P), Nat.add(Nat.double(Pe), W))
  Nat.LE(Nat.double(Nat.add(A, P)), Nat.add(Nat.double(A), Nat.add(Nat.double(Pe), W)))

def compose.lo.m(A, P, Pe, W, h2):
  %Nat.double_add(A, P) : Nat.LE(_, Nat.add(Nat.double(A), Nat.add(Nat.double(Pe), W)))
  Nat.add_mono_l(Nat.double(A), Nat.double(P), Nat.add(Nat.double(Pe), W), h2)

law compose.lo:
  for +Y: Nat
  for +A: Nat
  for +P: Nat
  for +Pe: Nat
  for +K: Nat
  for +W: Nat
  for h1: Nat.LE(Nat.double(Y), Nat.add(Nat.double(Nat.add(A, P)), K))
  for h2: Nat.LE(Nat.double(P), Nat.add(Nat.double(Pe), W))
  Nat.LE(Nat.double(Y), Nat.add(Nat.add(Nat.double(Nat.add(A, Pe)), K), W))

def compose.lo(Y, A, P, Pe, K, W, h1, h2):
  +dA = Nat.double(A)
  +dPe = Nat.double(Pe)
  %Nat.double_add(A, Pe) : Nat.LE(Nat.double(Y), Nat.add(Nat.add(_, K), W))
  %Nat.add_right_comm(Nat.add(dA, dPe), W, K) : Nat.LE(Nat.double(Y), _)
  %Nat.add_assoc(dA, dPe, W) : Nat.LE(Nat.double(Y), Nat.add(_, K))
  Nat.le_trans(Nat.double(Y), Nat.add(Nat.double(Nat.add(A, P)), K), Nat.add(Nat.add(dA, Nat.add(dPe, W)), K), h1,
    Nat.add_mono_r(Nat.double(Nat.add(A, P)), Nat.add(dA, Nat.add(dPe, W)), K, compose.lo.m(A, P, Pe, W, h2)))

law compose.hi.m:
  for +A: Nat
  for +P: Nat
  for +W: Nat
  for +Z: Nat
  for h1: Nat.LE(Nat.double(Nat.add(A, P)), Z)
  Nat.LE(Nat.add(Nat.double(A), Nat.add(Nat.double(P), W)), Nat.add(Z, W))

def compose.hi.m(A, P, W, Z, h1):
  %Equal.sym(Nat, Nat.add(Nat.double(A), Nat.add(Nat.double(P), W)), Nat.add(Nat.add(Nat.double(A), Nat.double(P)), W), Nat.add_assoc(Nat.double(A), Nat.double(P), W)) : Nat.LE(_, Nat.add(Z, W))
  %Equal.sym(Nat, Nat.add(Nat.double(A), Nat.double(P)), Nat.double(Nat.add(A, P)), Nat.double_add(A, P)) : Nat.LE(Nat.add(_, W), Nat.add(Z, W))
  Nat.add_mono_r(Nat.double(Nat.add(A, P)), Z, W, h1)

law compose.hi:
  for +Y: Nat
  for +A: Nat
  for +P: Nat
  for +Pe: Nat
  for +K: Nat
  for +W: Nat
  for h1: Nat.LE(Nat.double(Nat.add(A, P)), Nat.add(Nat.double(Y), K))
  for h2: Nat.LE(Nat.double(Pe), Nat.add(Nat.double(P), W))
  Nat.LE(Nat.double(Nat.add(A, Pe)), Nat.add(Nat.add(Nat.double(Y), K), W))

def compose.hi(Y, A, P, Pe, K, W, h1, h2):
  +dA = Nat.double(A)
  %Nat.double_add(A, Pe) : Nat.LE(_, Nat.add(Nat.add(Nat.double(Y), K), W))
  Nat.le_trans(Nat.add(dA, Nat.double(Pe)), Nat.add(dA, Nat.add(Nat.double(P), W)), Nat.add(Nat.add(Nat.double(Y), K), W),
    Nat.add_mono_l(dA, Nat.double(Pe), Nat.add(Nat.double(P), W), h2),
    compose.hi.m(A, P, W, Nat.add(Nat.double(Y), K), h1))

# Y near A + P, and P near Pe: Y near A + Pe, with both ulps
law compose:
  for +Y: Nat
  for +A: Nat
  for +P: Nat
  for +Pe: Nat
  for +k: Nat
  for +w: Nat
  for b1: Bound(Y, Nat.add(A, P), k)
  for b2: Bound(P, Pe, w)
  Bound2(Y, Nat.add(A, Pe), k, w)

def compose(Y, A, P, Pe, k, w, b1, b2):
  (l1, r1) = b1
  (l2, r2) = b2
  (compose.lo(Y, A, P, Pe, sh(1n, k), sh(1n, w), l1, l2), compose.hi(Y, A, P, Pe, sh(1n, k), sh(1n, w), r1, r2))

# what a law says about x' = x + p against x + (the exact product): a
# finite x' is within half of ulp(x') + ulp(p); a zero within half of
# 2^u + ulp(p); an overflow carries no bound
def Drift(v: Fmt.Val, +X: Nat, +u: Nat, +w: Nat) -> Type:
  match v:
    case Fmt.Z{n}:
      Bound2(0n, X, u, w)
    case Fmt.Inf{n}:
      Unit
    case Fmt.NaN{}:
      Empty
    case Fmt.Fin{n, R, +t}:
      Bound2(sh(Bin.to_nat(R), t), X, t, w)

law drift_fin:
  for +R: Bin.Bin
  for +t: Nat
  for +A: Nat
  for +P: Nat
  for +Pe: Nat
  for +w: Nat
  for b2: Bound(P, Pe, w)
  for h: Bound(sh(Bin.to_nat(R), t), Nat.add(A, P), t) & Nat.IsFalse(Bin.is_zero(R))
  Bound2(sh(Bin.to_nat(R), t), Nat.add(A, Pe), t, w)

def drift_fin(R, t, A, P, Pe, w, b2, h):
  (b1, nz) = h
  compose(sh(Bin.to_nat(R), t), A, P, Pe, t, w, b1, b2)

law drift_of:
  for v: Fmt.Val
  for +A: Nat
  for +P: Nat
  for +Pe: Nat
  for +u: Nat
  for +w: Nat
  for b2: Bound(P, Pe, w)
  Near(v, Nat.add(A, P), u) -> Drift(v, Nat.add(A, Pe), u, w)

def drift_of(v, A, P, Pe, u, w, b2):
  match v:
    case Fmt.Z{n}:
      h => compose(0n, A, P, Pe, u, w, h, b2)
    case Fmt.Inf{n}:
      h => Unit{}
    case Fmt.NaN{}:
      h => h
    case Fmt.Fin{n, +R, +t}:
      h => drift_fin(R, t, A, P, Pe, w, b2, h)

law recast:
  for -p: F32
  for +mp: Bin.Bin
  for +tp: Nat
  for +Pe: Nat
  for +u: Nat
  for dp: {SF32.decode(p) == Fmt.Fin{False{}, mp, tp} : Fmt.Val}
  for h: Near(Fmt.canon(SF32.decode(p)), Pe, u)
  Near(Fmt.canon(Fmt.Fin{False{}, mp, tp}), Pe, u)

def recast(p, mp, tp, Pe, u, dp, h):
  %dp : Near(Fmt.canon(_), Pe, u)
  h

# one Euler step x + v * dt on Base's F32, for positive finite x, v, dt
# and a positive finite product: the result is within half of
# ulp(x') + ulp(v * dt) of the exact x + v * dt (assuming HardOk)
law hard_step_near:
  for ~ok: SF32.HardOk()
  for +x: F32
  for +v: F32
  for +dt: F32
  for +mx: Bin.Bin
  for +ex: Nat
  for +mv: Bin.Bin
  for +ev: Nat
  for +md: Bin.Bin
  for +ed: Nat
  for +mp: Bin.Bin
  for +tp: Nat
  for dx: {SF32.decode(x) == Fmt.Fin{False{}, mx, ex} : Fmt.Val}
  for dv: {SF32.decode(v) == Fmt.Fin{False{}, mv, ev} : Fmt.Val}
  for ddt: {SF32.decode(dt) == Fmt.Fin{False{}, md, ed} : Fmt.Val}
  for +dp: {SF32.decode(F32.mul(v, dt)) == Fmt.Fin{False{}, mp, tp} : Fmt.Val}
  Drift(Fmt.canon(SF32.decode(F32.add(x, F32.mul(v, dt)))),
    Nat.add(sh(Bin.to_nat(mx), ex), sh(Nat.mul(Bin.to_nat(mv), Bin.to_nat(md)), mul_exp(ev, ed))),
    sum_lsb(Fmt.binary32(), mx, ex, mp, tp),
    ulp_of(mp, tp, Fmt.lsb(Fmt.binary32(), Bin.mul(mv, md), mul_exp(ev, ed))))

def hard_step_near(ok, x, v, dt, mx, ex, mv, ev, md, ed, mp, tp, dx, dv, ddt, dp):
  +p = F32.mul(v, dt)
  +Pe = sh(Nat.mul(Bin.to_nat(mv), Bin.to_nat(md)), mul_exp(ev, ed))
  +u1 = Fmt.lsb(Fmt.binary32(), Bin.mul(mv, md), mul_exp(ev, ed))
  +A = sh(Bin.to_nat(mx), ex)
  +P = sh(Bin.to_nat(mp), tp)
  drift_of(Fmt.canon(SF32.decode(F32.add(x, p))), A, P, Pe, sum_lsb(Fmt.binary32(), mx, ex, mp, tp), ulp_of(mp, tp, u1),
    strip_val(False{}, mp, tp, Pe, u1)(recast(p, mp, tp, Pe, u1, dp, hard_mul_near(~ok, v, dt, False{}, mv, ev, False{}, md, ed, dv, ddt))))(
    hard_add_near(~ok, x, p, False{}, mx, ex, mp, tp, dx, dp))
