import Base
import ../src/float/bin.bend as Bin
import ../src/float/format.bend as Fmt
import ../src/float/sf32.bend as SF32
import ../src/float/error.bend as Err

# drift.bend: one Euler step x + v * dt on the hardware's floats, against
# exact arithmetic.
#
# step_near is the proven bound for this file's own step: assuming
# SF32.HardOk (the hardware's F32.add and F32.mul round correctly), for
# positive finite x, v, dt with a positive finite product, the float
# result x' is within half of ulp(x') + ulp(v * dt) of the exact
# x + v * dt. main runs the step on the hardware and measures the actual
# error exactly, as binary integers, against that bound.

def step(x: F32, +v: F32, dt: F32) -> F32:
  F32.add(x, F32.mul(v, dt))

law step_near:
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
  Err.Drift(Fmt.canon(SF32.decode(step(x, v, dt))),
    Nat.add(Err.sh(Bin.to_nat(mx), ex), Err.sh(Nat.mul(Bin.to_nat(mv), Bin.to_nat(md)), Err.mul_exp(ev, ed))),
    Err.sum_lsb(Fmt.binary32(), mx, ex, mp, tp),
    Err.ulp_of(mp, tp, Fmt.lsb(Fmt.binary32(), Bin.mul(mv, md), Err.mul_exp(ev, ed))))

def step_near(ok, x, v, dt, mx, ex, mv, ev, md, ed, mp, tp, dx, dv, ddt, dp):
  Err.hard_step_near(~ok, x, v, dt, mx, ex, mv, ev, md, ed, mp, tp, dx, dv, ddt, dp)

# Measuring
# ---------

# a positive finite value's mantissa and exponent, or anything else
type Pos is Data:
  Pos{m: Bin.Bin, e: Nat}
  Other{}

def pos.sign(neg: Bool, m: Bin.Bin, e: Nat) -> Pos:
  match neg:
    case False{}:
      Pos{m, e}
    case True{}:
      Other{}

def pos(v: Fmt.Val) -> Pos:
  match v:
    case Fmt.Z{n}:
      Other{}
    case Fmt.Inf{n}:
      Other{}
    case Fmt.NaN{}:
      Other{}
    case Fmt.Fin{n, m, e}:
      pos.sign(n, m, e)

# one step measured: skipped (an input or result is not positive finite),
# or checked: whether the error is zero, within the bound, and above half
# the bound
type Outcome is Data:
  Skip{}
  Checked{exact: Bool, within: Bool, tight: Bool}

def absdiff.go(a: Bin.Bin, b: Bin.Bin, c: Cmp) -> Bin.Bin:
  match c:
    case LT{}:
      Bin.sub(b, a)
    case EQ{}:
      Bin.BZ{}
    case GT{}:
      Bin.sub(a, b)

def absdiff(+a: Bin.Bin, +b: Bin.Bin) -> Bin.Bin:
  absdiff.go(a, b, Bin.cmp(a, b))

def not_gt(c: Cmp) -> Bool:
  Bool.not(Cmp.is_gt(c))

# y = R * 2^t against exact = mx * 2^ex + mv * md * 2^(ev + ed - 300),
# all scaled to the smallest exponent involved; bound 2^t + 2^w
def measure(mx: Bin.Bin, +ex: Nat, mv: Bin.Bin, ev: Nat, md: Bin.Bin, ed: Nat, +w: Nat, R: Bin.Bin, +t: Nat) -> Outcome:
  +e1 = Err.mul_exp(ev, ed)
  +base = Nat.min(Nat.min(ex, e1), Nat.min(t, w))
  +exact = Bin.add(Bin.shl(mx, Nat.sub(ex, base)), Bin.shl(Bin.mul(mv, md), Nat.sub(e1, base)))
  +d = absdiff(Bin.shl(R, Nat.sub(t, base)), exact)
  +bound = Bin.add(Bin.pow2(Nat.sub(t, base)), Bin.pow2(Nat.sub(w, base)))
  Checked{Bin.is_zero(d), not_gt(Bin.cmp(Bin.B0{d}, bound)), Cmp.is_gt(Bin.cmp(Bin.B0{Bin.B0{d}}, bound))}

def check.y(mx: Bin.Bin, ex: Nat, mv: Bin.Bin, ev: Nat, md: Bin.Bin, ed: Nat, w: Nat, y: Pos) -> Outcome:
  match y:
    case Pos{R, t}:
      measure(mx, ex, mv, ev, md, ed, w, R, t)
    case Other{}:
      Skip{}

def check.p(mx: Bin.Bin, ex: Nat, mv: Bin.Bin, ev: Nat, md: Bin.Bin, ed: Nat, p: Pos, y: Pos) -> Outcome:
  match p:
    case Pos{mp, tp}:
      check.y(mx, ex, mv, ev, md, ed, Err.ulp_of(mp, tp, 0n), y)
    case Other{}:
      Skip{}

def check.dt(mx: Bin.Bin, ex: Nat, mv: Bin.Bin, ev: Nat, c: Pos, p: Pos, y: Pos) -> Outcome:
  match c:
    case Pos{md, ed}:
      check.p(mx, ex, mv, ev, md, ed, p, y)
    case Other{}:
      Skip{}

def check.v(mx: Bin.Bin, ex: Nat, b: Pos, c: Pos, p: Pos, y: Pos) -> Outcome:
  match b:
    case Pos{mv, ev}:
      check.dt(mx, ex, mv, ev, c, p, y)
    case Other{}:
      Skip{}

def check.x(a: Pos, b: Pos, c: Pos, p: Pos, y: Pos) -> Outcome:
  match a:
    case Pos{mx, ex}:
      check.v(mx, ex, b, c, p, y)
    case Other{}:
      Skip{}

def check(+x: F32, +v: F32, +dt: F32) -> Outcome:
  +p = F32.mul(v, dt)
  check.x(pos(SF32.decode(x)), pos(SF32.decode(v)), pos(SF32.decode(dt)), pos(SF32.decode(p)), pos(Fmt.canon(SF32.decode(F32.add(x, p)))))

# Counting
# --------

type Tally is Data:
  Tally{steps: Nat, skipped: Nat, rounded: Nat, within: Nat, tight: Nat}

def bump(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      1n+n
    case False{}:
      n

def tally.go(o: Outcome, n: Nat, s: Nat, r: Nat, w: Nat, h: Nat) -> Tally:
  match o:
    case Skip{}:
      Tally{1n+n, 1n+s, r, w, h}
    case Checked{e, ok, tg}:
      Tally{1n+n, s, bump(Bool.not(e), r), bump(ok, w), bump(tg, h)}

def tally(o: Outcome, t: Tally) -> Tally:
  match t:
    case Tally{n, s, r, w, h}:
      tally.go(o, n, s, r, w, h)

def show(t: Tally) -> String:
  match t:
    case Tally{+n, +s, r, w, h}:
      "checked " ++ Nat.show(Nat.sub(n, s)) ++ " of " ++ Nat.show(n) ++ ", rounded " ++ Nat.show(r) ++ ", within the bound " ++ Nat.show(w) ++ ", above half of it " ++ Nat.show(h)

# a body moving at v, stepped n times
def trajectory(n: Nat, +x: F32, +v: F32, +dt: F32, t: Tally) -> Tally:
  match n:
    case 0n:
      t
    case 1n+k:
      trajectory(k, step(x, v, dt), v, dt, tally(check(x, v, dt), t))

def next(x: U32) -> U32:
  U32.add(U32.mul(x, 1664525), 1013904223)

# a positive float with an exponent near 1.0 (bits 0x3C000000 to
# 0x43FFFFFF: about 2^-7 to 2^8)
def positive(r: U32) -> F32:
  SF32.of_bits(U32.add(U32.and(r, 134217727), 1006632960))

def random(n: Nat, +s: U32, t: Tally) -> Tally:
  match n:
    case 0n:
      t
    case 1n+k:
      +s1 = next(s)
      +s2 = next(s1)
      +s3 = next(s2)
      random(k, s3, tally(check(positive(s1), positive(s2), positive(s3)), t))

def main() -> IO(Unit):
  +zero = {Tally{0n, 0n, 0n, 0n, 0n} : Tally}
  do IO<Unit>:
    IO.print("trajectory: " ++ show(trajectory(1000n, 1.0, 3.7, 0.016666668, zero)))
    IO.print("random:     " ++ show(random(2000n, 7, zero)))

#|trajectory: checked 1000 of 1000, rounded 1000, within the bound 1000, above half of it 0
#|random:     checked 2000 of 2000, rounded 2000, within the bound 2000, above half of it 237
