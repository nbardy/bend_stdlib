import Base
import ../nat.bend as Nat
import ./bin.bend as Bin
import ./format.bend as Fmt

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

# what a law says about a rounded value v of the exact X * 2^(e - 300),
# with k low bits rounded off: a finite v is within half an ulp (2^k at
# exponent e); zero is too; an overflow to infinity carries no bound;
# rounding never gives NaN
def Near(v: Fmt.Val, +X: Nat, +e: Nat, +k: Nat) -> Type:
  match v:
    case Fmt.Z{n}:
      Bound(0n, X, k)
    case Fmt.Inf{n}:
      Unit
    case Fmt.NaN{}:
      Empty
    case Fmt.Fin{n, R, t}:
      Bound(sh(Bin.to_nat(R), Nat.sub(t, e)), X, k)

def no_f(e: {False{} == True{} : Bool}) -> Empty:
  %e : Nat.IsFalse(_)
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

law over_near.zero:
  for +R: Bin.Bin
  for +s: Nat
  for +X: Nat
  for +k: Nat
  for ez: {Bin.is_zero(R) == True{} : Bool}
  for b: Bound(sh(Bin.to_nat(R), s), X, k)
  Bound(0n, X, k)

def over_near.zero(R, s, X, k, ez, b):
  %sh_num_zero(R, s, ez) : Bound(_, X, k)
  b

law over_near.go:
  for neg: Bool
  for +R: Bin.Bin
  for +t: Nat
  for +X: Nat
  for +e: Nat
  for +k: Nat
  for z: Bool
  for ez: {Bin.is_zero(R) == z : Bool}
  for big: Bool
  for b: Bound(sh(Bin.to_nat(R), Nat.sub(t, e)), X, k)
  Near(Fmt.over.go(neg, R, t, z, big), X, e, k)

def over_near.go(neg, R, t, X, e, k, z, ez, big, b):
  match z big:
    case True{} big:
      over_near.zero(R, Nat.sub(t, e), X, k, ez, b)
    case False{} True{}:
      Unit{}
    case False{} False{}:
      b

law over_near:
  for +top: Nat
  for neg: Bool
  for +R: Bin.Bin
  for +t: Nat
  for +X: Nat
  for +e: Nat
  for +k: Nat
  for b: Bound(sh(Bin.to_nat(R), Nat.sub(t, e)), X, k)
  Near(Fmt.over(top, neg, R, t), X, e, k)

def over_near(top, neg, R, t, X, e, k, b):
  over_near.go(neg, R, t, X, e, k, Bin.is_zero(R), {==}, Nat.is_gt(Nat.add(t, Bin.len(R)), top), b)

law sub_self:
  for e: Nat
  {0n == Nat.sub(e, e) : Nat}

def sub_self(e):
  match e:
    case 0n:
      {==}
    case 1n+p:
      sub_self(p)

# nothing rounded off: the value is exact
law exact_near:
  for +X: Nat
  for +k: Nat
  for +e: Nat
  Bound(sh(X, Nat.sub(e, e)), X, k)

def exact_near(X, k, e):
  %sub_self(e) : Bound(sh(X, _), X, k)
  (Nat.le_add_r(Nat.double(X), sh(1n, k)), Nat.le_add_r(Nat.double(X), sh(1n, k)))

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
  After((q, r, s), X, Nat.sub(t, e), T) -> Near(Fmt.round.fin(top, neg, t, (q, r, s)), X, e, Nat.sub(t, e))

def round_fin_near.go(top, neg, t, X, e, q, r, s, T):
  x => over_near(top, neg, Fmt.round.up(q, Bool.and(r, Bool.or(s, Bin.odd(q)))), t, X, e, Nat.sub(t, e), fin_near(q, r, s, X, Nat.sub(t, e), T)(x))

law round_fin_near:
  for +top: Nat
  for neg: Bool
  for +t: Nat
  for +X: Nat
  for +e: Nat
  for res: Bin.Bin & Bool & Bool
  for +T: Nat
  After(res, X, Nat.sub(t, e), T) -> Near(Fmt.round.fin(top, neg, t, res), X, e, Nat.sub(t, e))

def round_fin_near(top, neg, t, X, e, res, T):
  (q, r, s) = res
  round_fin_near.go(top, neg, t, X, e, q, r, s, T)

law round_go_near:
  for +top: Nat
  for neg: Bool
  for +m: Bin.Bin
  for +e: Nat
  for +t: Nat
  for exact: Bool
  Near(Fmt.round.go(top, neg, m, e, t, exact), Bin.to_nat(m), e, Nat.sub(t, e))

def round_go_near(top, neg, m, e, t, exact):
  match exact:
    case True{}:
      +k = Nat.sub(t, e)
      +X = Bin.to_nat(m)
      over_near(top, neg, m, e, X, e, k, exact_near(X, k, e))
    case False{}:
      +k = Nat.sub(t, e)
      +X = Bin.to_nat(m)
      round_fin_near(top, neg, t, X, e, Bin.shr(k, m, False{}, False{}), rest(k, m, 0n, 0n))(
        after_zero(Bin.shr(k, m, False{}, False{}), X, k, rest(k, m, 0n, 0n),
          shr_ok(k, m, False{}, False{}, 0n, X, 0n)(Nat.add_zero_r(X))(Unit{})))

# Fmt.round is correct to half an ulp: the result is within 2^(k-1) of
# m at exponent e, where k = lsb - e bits were rounded off; or it is
# infinity, when it overflows
law round_near:
  for +f: Fmt.Format
  for neg: Bool
  for +m: Bin.Bin
  for +e: Nat
  Near(Fmt.round(f, neg, m, e), Bin.to_nat(m), e, Nat.sub(Fmt.lsb(f, m, e), e))

def round_near(f, neg, m, e):
  +t = Fmt.lsb(f, m, e)
  round_go_near(Fmt.top(f), neg, m, e, t, Nat.is_le(t, e))
