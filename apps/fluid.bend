import Base
import ../src/nat.bend as Nat
import ../src/float/f32.bend as F32
import ../src/float/sf32.bend as SF32

# fluid.bend: 2D incompressible Navier-Stokes by stable fluids (Stam 1999)
# on a 32x32 torus.
#
# A step: add a jet of dye and upward velocity at the bottom; advect the
# velocity by itself (semi-Lagrangian, bilinear); project it to be
# divergence-free (Jacobi pressure solve, then subtract the pressure
# gradient); advect the dye by the result. Viscosity is left out; the
# advection's interpolation smooths the flow instead.
#
# Proven, about the grid (Nat coordinates, any size 1 + m):
#   right_lt, left_lt     a neighbour of a cell is a cell
#   left_right, right_left the torus neighbours undo each other
#   idx_lt                a cell's index is inside its field, so the
#                         fields packed in one array never overlap, and
#                         Array's silent index wraparound never aliases
#                         two cells
# Proven, about the floats (src/float/f32.bend, assuming LtOk):
#   cell_ok               every back-traced position, NaN and infinities
#                         included, gives a cell index in [0, 95] and an
#                         interpolation weight in [0, 1], so F32.to_u32
#                         never sees a value it is undefined on
# Proven by computation (software floats, src/float/sf32.bend):
#   projection            the app's project, 20 Jacobi sweeps, on a 4x4
#                         fixture lowers the total |divergence|, from
#                         2.4 to 1.1796875 * 2^-19, these exact bits
# The projection kernels take their float operations as a template
# argument (Ops): the app runs hard(), the machine's F32; the laws run
# soft(). main runs the fixture on both and prints whether the bits
# agree, which carries the laws to the machine by test.
# Not proven: the 32x32 run and advection (machine floats only). main
# prints the dye total and the divergence before and after projection.
# 20 Jacobi sweeps remove most short-range divergence but converge
# slowly on smooth, large-scale divergence (at 400 sweeps the residual
# falls about 13x further).
#
# All fields live in one Array<F32>, threaded through each kernel by a
# state monad (St), so a kernel is a do block of reads and writes.

# Grid lemmas
# ------------

# a < b means Nat.is_eq says they differ
law lt_ne:
  for a: Nat
  for b: Nat
  for lt: Nat.LT(a, b)
  {False{} == Nat.is_eq(a, b) : Bool}

def lt_ne(a, b, lt):
  match a b:
    case 0n 0n:
      match lt:
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      match lt:
    case 1n+p 1n+q:
      lt_ne(p, q, lt)

law eq_of_is_eq:
  for a: Nat
  for b: Nat
  for e: {Nat.is_eq(a, b) == True{} : Bool}
  {a == b : Nat}

def eq_of_is_eq(a, b, e):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, %e : Nat.IsFalse(_); Unit{})
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, %e : Nat.IsFalse(_); Unit{})
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, eq_of_is_eq(p, q, e))

# x < n+1 and x differs from n, so x+1 < n+1
law lt_step:
  for x: Nat
  for n: Nat
  for lt: Nat.LT(x, 1n+n)
  for ne: {Nat.is_eq(x, n) == False{} : Bool}
  Nat.LT(1n+x, 1n+n)

def lt_step(x, n, lt, ne):
  match x n:
    case 0n 0n:
      Empty.absurd(Nat.LT(1n, 1n), %ne : Nat.IsTrue(_); Unit{})
    case 0n 1n+m:
      Unit{}
    case 1n+p 0n:
      match lt:
    case 1n+p 1n+m:
      lt_step(p, m, lt, ne)

# a <= b implies a <= b + c
law le_add:
  for a: Nat
  for b: Nat
  for -c: Nat
  for h: Nat.LE(a, b)
  Nat.LE(a, Nat.add(b, c))

def le_add(a, b, c, h):
  match a b:
    case 0n y:
      Unit{}
    case 1n+x 0n:
      match h:
    case 1n+x 1n+y:
      le_add(x, y, c, h)

# The torus
# ---------
# The grid is (1 + m) x (1 + m) cells, coordinates 0..m. The app runs
# m = 31; the checked projection law runs the same kernels at m = 3.

def right.go(x: Nat, top: Bool) -> Nat:
  match top:
    case True{}:
      0n
    case False{}:
      1n+x

def right(+m: Nat, +x: Nat) -> Nat:
  right.go(x, Nat.is_eq(x, m))

def left(m: Nat, x: Nat) -> Nat:
  match x:
    case 0n:
      m
    case 1n+p:
      p

def cells(+m: Nat) -> Nat:
  Nat.mul(1n+m, 1n+m)

def idx(+m: Nat, y: Nat, x: Nat) -> Nat:
  Nat.add(Nat.mul(y, 1n+m), x)

law is_eq_refl:
  for m: Nat
  {True{} == Nat.is_eq(m, m) : Bool}

def is_eq_refl(m):
  match m:
    case 0n:
      {==}
    case 1n+p:
      is_eq_refl(p)

law right_lt.go:
  for m: Nat
  for +x: Nat
  for c: Bool
  for e: {Nat.is_eq(x, m) == c : Bool}
  for lt: Nat.LT(x, 1n+m)
  Nat.LT(right.go(x, c), 1n+m)

def right_lt.go(m, x, c, e, lt):
  match c:
    case True{}:
      Unit{}
    case False{}:
      lt_step(x, m, lt, e)

# the right neighbour of a cell is a cell
law right_lt:
  for +m: Nat
  for +x: Nat
  for lt: Nat.LT(x, 1n+m)
  Nat.LT(right(m, x), 1n+m)

def right_lt(m, x, lt):
  right_lt.go(m, x, Nat.is_eq(x, m), {==}, lt)

# the left neighbour of a cell is a cell
law left_lt:
  for +m: Nat
  for x: Nat
  for lt: Nat.LT(x, 1n+m)
  Nat.LT(left(m, x), 1n+m)

def left_lt(m, x, lt):
  match x:
    case 0n:
      Nat.le_refl(m)
    case 1n+p:
      Nat.le_trans(1n+p, m, 1n+m, lt, Nat.le_step(m))

law left_right.go:
  for m: Nat
  for +x: Nat
  for c: Bool
  for e: {Nat.is_eq(x, m) == c : Bool}
  {left(m, right.go(x, c)) == x : Nat}

def left_right.go(m, x, c, e):
  match c:
    case True{}:
      Equal.sym(Nat, x, m, eq_of_is_eq(x, m, e))
    case False{}:
      {==}

# stepping right then left returns to the cell
law left_right:
  for +m: Nat
  for +x: Nat
  {left(m, right(m, x)) == x : Nat}

def left_right(m, x):
  left_right.go(m, x, Nat.is_eq(x, m), {==})

# stepping left then right returns to the cell
law right_left:
  for +m: Nat
  for x: Nat
  for lt: Nat.LT(x, 1n+m)
  {right(m, left(m, x)) == x : Nat}

def right_left(m, x, lt):
  match x:
    case 0n:
      %is_eq_refl(m) : {right.go(m, _) == 0n : Nat}
      {==}
    case 1n+p:
      +p2 = p
      %lt_ne(p2, m, lt) : {right.go(p2, _) == 1n+p2 : Nat}
      {==}

# s + a < s + b when a < b
law lt_add_l:
  for s: Nat
  for -a: Nat
  for -b: Nat
  for h: Nat.LT(a, b)
  Nat.LT(Nat.add(s, a), Nat.add(s, b))

def lt_add_l(s, a, b, h):
  match s:
    case 0n:
      h
    case 1n+q:
      lt_add_l(q, a, b, h)

law idx_lt.go:
  for +m: Nat
  for y: Nat
  for +x: Nat
  for n: Nat
  for hx: Nat.LT(x, 1n+m)
  for hy: Nat.LT(y, n)
  Nat.LT(idx(m, y, x), Nat.mul(n, 1n+m))

def idx_lt.go(m, y, x, n, hx, hy):
  match y n:
    case 0n 0n:
      match hy:
    case 0n 1n+k:
      le_add(1n+x, 1n+m, Nat.mul(k, 1n+m), hx)
    case 1n+p 0n:
      match hy:
    case 1n++p 1n+k:
      %Nat.add_assoc(1n+m, Nat.mul(p, 1n+m), x) : Nat.LT(_, Nat.mul(1n+k, 1n+m))
      lt_add_l(1n+m, idx(m, p, x), Nat.mul(k, 1n+m), idx_lt.go(m, p, x, k, hx, hy))

# a cell's index is inside its field, so the fields packed in one array
# ((1 + m)^2 slots each) never overlap, and Array's silent index
# wraparound never aliases two cells
law idx_lt:
  for +m: Nat
  for y: Nat
  for +x: Nat
  for hx: Nat.LT(x, 1n+m)
  for hy: Nat.LT(y, 1n+m)
  Nat.LT(idx(m, y, x), cells(m))

def idx_lt(m, y, x, hx, hy):
  idx_lt.go(m, y, x, 1n+m, hx, hy)

# A state monad over a linear state
# ---------------------------------
# A let can only destructure a parameter, so reading an array (which
# hands the array back beside the value) needs a helper per read. bind is
# that helper, written once; do blocks then read like straight-line code.

def St(S: Type, A: Type) -> Type:
  S -> S & A

def St.pure(-S: Type, -A: Type, x: A) -> St(S, A):
  s => (s, x)

def St.bind.go(-S: Type, -A: Type, -B: Type, r: S & A, f: A -> St(S, B)) -> S & B:
  (s2, x) = r
  f(x)(s2)

def St.bind(-S: Type, -A: Type, -B: Type, m: St(S, A), f: A -> St(S, B)) -> St(S, B):
  s => St.bind.go(S, A, B, m(s), f)

def St.exec(-S: Type, -A: Type, r: S & A) -> S:
  (s2, x) = r
  s2

# Float operations
# ----------------
# The projection's kernels take their float operations as a template
# argument. hard() is the machine's F32, which the app runs; soft() is
# src/float/sf32.bend's software binary32, which the checker computes.

type Ops is Type:
  Ops{add: F32 -> F32 -> F32, sub: F32 -> F32 -> F32, mul: F32 -> F32 -> F32, abs: F32 -> F32}

def Ops.add(o: Ops, a: F32, b: F32) -> F32:
  match o:
    case Ops{add, sub, mul, abs}:
      add(a, b)

def Ops.sub(o: Ops, a: F32, b: F32) -> F32:
  match o:
    case Ops{add, sub, mul, abs}:
      sub(a, b)

def Ops.mul(o: Ops, a: F32, b: F32) -> F32:
  match o:
    case Ops{add, sub, mul, abs}:
      mul(a, b)

def Ops.abs(o: Ops, a: F32) -> F32:
  match o:
    case Ops{add, sub, mul, abs}:
      abs(a)

def hard() -> Ops:
  Ops{F32.add, F32.sub, F32.mul, F32.abs}

def soft() -> Ops:
  Ops{SF32.add, SF32.sub, SF32.mul, SF32.abs}

# Fields
# ------
# All fields live in one Array<F32>, (1 + m)^2 slots each.

def U() -> Nat:
  0n
def V() -> Nat:
  1n
def D() -> Nat:
  2n
def U2() -> Nat:
  3n
def V2() -> Nat:
  4n
def D2() -> Nat:
  5n
def P() -> Nat:
  6n
def P2() -> Nat:
  7n
def DIV() -> Nat:
  8n
def ACC() -> Nat:
  9n

def slot(+m: Nat, f: Nat, x: Nat, y: Nat) -> U32:
  U32.from_nat(Nat.add(Nat.mul(f, cells(m)), idx(m, y, x)))

def get(+m: Nat, f: Nat, x: Nat, y: Nat) -> St(Array<F32>, F32):
  +i = slot(m, f, x, y)
  a => Array.get(F32, a, i)

def put(+m: Nat, f: Nat, x: Nat, y: Nat, v: F32) -> St(Array<F32>, Unit):
  +i = slot(m, f, x, y)
  a => (Array.set(F32, a, i, v), Unit{})

def get_raw(+i: U32) -> St(Array<F32>, F32):
  a => Array.get(F32, a, i)

# a kernel's grid and its source and destination fields
type Cfg is Data:
  Cfg{m: Nat, src: Nat, dst: Nat}

def Cfg.side(c: Cfg) -> Nat:
  match c:
    case Cfg{m, src, dst}:
      1n+m

# Advection (machine floats, m = 31)
# ----------------------------------

def dt() -> F32:
  0.8

# where p falls on the grid: the cell's index as a float, and how far p
# is into that cell. Both are clamped, so the index handed to
# F32.to_u32 is always in [0, 95] and the weight in [0, 1], for every p
# (cell_ok). A float outside u32's range, or NaN, makes that conversion
# undefined in C, and the lanes would disagree.
type Cell is Data:
  Cell{i: F32, s: F32}

def cell(+p: F32) -> Cell:
  +f = F32.floor(p)
  Cell{F32.clamp(f, 0.0, 95.0), F32.clamp(F32.sub(p, f), 0.0, 1.0)}

def InCell(c: Cell) -> Type:
  match c:
    case Cell{i, s}:
      F32.LE(0.0, i) & F32.LE(i, 95.0) & F32.LE(0.0, s) & F32.LE(s, 1.0)

# every float, NaN and infinities included, lands in a cell (assumes
# LtOk: the hardware's < is IEEE's)
law cell_ok:
  for ~lt: F32.LtOk()
  for +p: F32
  InCell(cell(p))

def cell_ok(lt, p):
  +f = F32.floor(p)
  +s = F32.sub(p, f)
  (F32.lo_le_clamp(~lt, f, 0.0, 95.0, Unit{}), F32.clamp_le_hi(~lt, f, 0.0, 95.0, Unit{}),
   F32.lo_le_clamp(~lt, s, 0.0, 1.0, Unit{}), F32.clamp_le_hi(~lt, s, 0.0, 1.0, Unit{}))

def sample.go(f: Nat, cx: Cell, cy: Cell) -> St(Array<F32>, F32):
  Cell{fx, +sx} = cx
  Cell{fy, +sy} = cy
  +base = U32.from_nat(Nat.mul(f, 1024n))
  +ix = F32.to_u32(fx)
  +iy = F32.to_u32(fy)
  +i0 = U32.and(ix, 31)
  +j0 = U32.mul(U32.and(iy, 31), 32)
  +i1 = U32.and(U32.add(i0, 1), 31)
  +j1 = U32.mul(U32.and(U32.add(U32.and(iy, 31), 1), 31), 32)
  do St<Array<F32>, F32>:
    a00 : F32 <- get_raw(U32.add(base, U32.add(j0, i0)))
    a10 : F32 <- get_raw(U32.add(base, U32.add(j0, i1)))
    a01 : F32 <- get_raw(U32.add(base, U32.add(j1, i0)))
    a11 : F32 <- get_raw(U32.add(base, U32.add(j1, i1)))
    return F32.lerp(F32.lerp(a00, a10, sx), F32.lerp(a01, a11, sx), sy)

# bilinear sample of field f at (px, py), both offset by +32 to stay
# positive; the 31 masks make this m = 31 only
def sample(f: Nat, +px: F32, +py: F32) -> St(Array<F32>, F32):
  sample.go(f, cell(px), cell(py))

def back(+c: Nat, +vel: F32) -> F32:
  F32.add(F32.sub(F32.from_nat(c), F32.mul(dt(), vel)), 32.0)

def adv_uv(c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  Cfg{+m, src, dst} = c
  do St<Array<F32>, Unit>:
    +uc : F32 <- get(m, U(), x, y)
    +vc : F32 <- get(m, V(), x, y)
    su : F32 <- sample(U(), back(x, uc), back(y, vc))
    sv : F32 <- sample(V(), back(x, uc), back(y, vc))
    put(m, U2(), x, y, su)
    put(m, V2(), x, y, sv)

# advect field src into dst along (U, V)
def adv(c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  Cfg{+m, +src, +dst} = c
  do St<Array<F32>, Unit>:
    uc : F32 <- get(m, U(), x, y)
    vc : F32 <- get(m, V(), x, y)
    sd : F32 <- sample(src, back(x, uc), back(y, vc))
    put(m, dst, x, y, sd)

# Projection (any Ops, any m)
# ---------------------------

def copy(c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  Cfg{+m, src, dst} = c
  do St<Array<F32>, Unit>:
    v : F32 <- get(m, src, x, y)
    put(m, dst, x, y, v)

# divergence by forward differences
def div_at(~o: Ops, c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  Cfg{+m, src, dst} = c
  do St<Array<F32>, Unit>:
    ur : F32 <- get(m, U(), right(m, x), y)
    uc : F32 <- get(m, U(), x, y)
    vd : F32 <- get(m, V(), x, right(m, y))
    vc : F32 <- get(m, V(), x, y)
    put(m, DIV(), x, y, Ops.add(o, Ops.sub(o, ur, uc), Ops.sub(o, vd, vc)))

# one Jacobi sweep of lap(p) = div, with the 5-point Laplacian
def jac_at(~o: Ops, c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  Cfg{+m, src, dst} = c
  do St<Array<F32>, Unit>:
    dv : F32 <- get(m, DIV(), x, y)
    pr : F32 <- get(m, P(), right(m, x), y)
    pl : F32 <- get(m, P(), left(m, x), y)
    pd : F32 <- get(m, P(), x, right(m, y))
    pu : F32 <- get(m, P(), x, left(m, y))
    put(m, P2(), x, y, Ops.mul(o, 0.25, Ops.sub(o, Ops.add(o, Ops.add(o, pr, pl), Ops.add(o, pd, pu)), dv)))

# subtract the pressure gradient by backward differences; with the
# forward divergence this makes div(grad p) the same 5-point Laplacian
def grad_at(~o: Ops, c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  Cfg{+m, src, dst} = c
  do St<Array<F32>, Unit>:
    +pc : F32 <- get(m, P(), x, y)
    pl : F32 <- get(m, P(), left(m, x), y)
    pu : F32 <- get(m, P(), x, left(m, y))
    uc : F32 <- get(m, U(), x, y)
    vc : F32 <- get(m, V(), x, y)
    put(m, U(), x, y, Ops.sub(o, uc, Ops.sub(o, pc, pl)))
    put(m, V(), x, y, Ops.sub(o, vc, Ops.sub(o, pc, pu)))

def clear_p(c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  Cfg{+m, src, dst} = c
  put(m, P(), x, y, 0.0)

# add |src| (or src) at this cell into ACC slot 0
def abs_sum(~o: Ops, c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  Cfg{+m, src, dst} = c
  do St<Array<F32>, Unit>:
    v : F32 <- get(m, src, x, y)
    t : F32 <- get(m, ACC(), 0n, 0n)
    put(m, ACC(), 0n, 0n, Ops.add(o, t, Ops.abs(o, v)))

def sum(~o: Ops, c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  Cfg{+m, src, dst} = c
  do St<Array<F32>, Unit>:
    v : F32 <- get(m, src, x, y)
    t : F32 <- get(m, ACC(), 0n, 0n)
    put(m, ACC(), 0n, 0n, Ops.add(o, t, v))

# a jet: dye and upward velocity added at a cell
def jet(~o: Ops, c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  Cfg{+m, src, dst} = c
  do St<Array<F32>, Unit>:
    uc : F32 <- get(m, U(), x, y)
    vc : F32 <- get(m, V(), x, y)
    dc : F32 <- get(m, D(), x, y)
    put(m, U(), x, y, Ops.add(o, uc, 0.1))
    put(m, V(), x, y, Ops.sub(o, vc, 0.6))
    put(m, D(), x, y, Ops.add(o, dc, 1.0))

# Sweeps
# ------

def row(~k: @c: Cfg -> @+x: Nat -> @+y: Nat -> St(Array<F32>, Unit), +c: Cfg, n: Nat, +x: Nat, +y: Nat, a: Array<F32>) -> Array<F32>:
  match n:
    case 0n:
      a
    case 1n+j:
      row(~k, c, j, 1n+x, y, St.exec(Array<F32>, Unit, k(c, x, y)(a)))

def rows(~k: @c: Cfg -> @+x: Nat -> @+y: Nat -> St(Array<F32>, Unit), +c: Cfg, +w: Nat, +x0: Nat, n: Nat, +y: Nat, a: Array<F32>) -> Array<F32>:
  match n:
    case 0n:
      a
    case 1n+j:
      rows(~k, c, w, x0, j, 1n+y, row(~k, c, w, x0, y, a))

# every cell
def each(~k: @c: Cfg -> @+x: Nat -> @+y: Nat -> St(Array<F32>, Unit), +c: Cfg, a: Array<F32>) -> Array<F32>:
  +s = Cfg.side(c)
  rows(~k, c, s, 0n, s, 0n, a)

def jacobi(~o: Ops, +m: Nat, n: Nat, a: Array<F32>) -> Array<F32>:
  match n:
    case 0n:
      a
    case 1n+j:
      jacobi(~o, m, j, each(~copy, Cfg{m, P2(), P()}, each(~jac_at(~o), Cfg{m, 0n, 0n}, a)))

# make the velocity divergence-free: n Jacobi sweeps for the pressure,
# then subtract its gradient
def project(~o: Ops, +m: Nat, n: Nat, a: Array<F32>) -> Array<F32>:
  each(~grad_at(~o), Cfg{m, 0n, 0n}, jacobi(~o, m, n, each(~clear_p, Cfg{m, 0n, 0n}, each(~div_at(~o), Cfg{m, 0n, 0n}, a))))

def step(a: Array<F32>) -> Array<F32>:
  a1 = rows(~jet(~hard()), Cfg{31n, 0n, 0n}, 4n, 14n, 4n, 26n, a)
  a2 = each(~copy, Cfg{31n, V2(), V()}, each(~copy, Cfg{31n, U2(), U()}, each(~adv_uv, Cfg{31n, 0n, 0n}, a1)))
  each(~copy, Cfg{31n, D2(), D()}, each(~adv, Cfg{31n, D(), D2()}, project(~hard(), 31n, 20n, a2)))

def run(n: Nat, a: Array<F32>) -> Array<F32>:
  match n:
    case 0n:
      a
    case 1n+j:
      run(j, step(a))

# Measuring
# ---------

# whole-grid passes as state actions
def sweep(~k: @c: Cfg -> @+x: Nat -> @+y: Nat -> St(Array<F32>, Unit), +c: Cfg) -> St(Array<F32>, Unit):
  a => (each(~k, c, a), Unit{})

def projected(~o: Ops, +m: Nat, +n: Nat) -> St(Array<F32>, Unit):
  a => (project(~o, m, n, a), Unit{})

# sum of |DIV| or of D over the grid, via ACC slot 0
def total(~k: @c: Cfg -> @+x: Nat -> @+y: Nat -> St(Array<F32>, Unit), +m: Nat, +src: Nat) -> St(Array<F32>, F32):
  do St<Array<F32>, F32>:
    put(m, ACC(), 0n, 0n, 0.0)
    sweep(~k, Cfg{m, src, 0n})
    t : F32 <- get(m, ACC(), 0n, 0n)
    return t

# dye total, and total |divergence| before and after n projection sweeps
def stats(~o: Ops, +m: Nat, +n: Nat) -> St(Array<F32>, F32 & F32 & F32):
  do St<Array<F32>, F32 & F32 & F32>:
    sweep(~div_at(~o), Cfg{m, 0n, 0n})
    before : F32 <- total(~abs_sum(~o), m, DIV())
    projected(~o, m, n)
    sweep(~div_at(~o), Cfg{m, 0n, 0n})
    after : F32 <- total(~abs_sum(~o), m, DIV())
    dye : F32 <- total(~sum(~o), m, D())
    return (dye, before, after)

# The projection, checked
# -----------------------
# The app's project, on a 4 x 4 torus (m = 3) with a jet at two cells,
# computed by the checker with the software floats. The laws hold for
# soft(); main runs the same fixture on hard() and prints whether the
# bits agree, which carries the result to the machine by test.

def small(~o: Ops) -> Array<F32>:
  rows(~jet(~o), Cfg{3n, 0n, 0n}, 2n, 1n, 1n, 2n, [0.0 : F32^8n])

def results(r: Array<F32> & (F32 & F32 & F32)) -> F32 & F32 & F32:
  (a, s) = r
  s

# dye total, |div| before and after projecting, on the small grid
def checked(~o: Ops) -> F32 & F32 & F32:
  results(stats(~o, 3n, 20n)(small(~o)))

# the three results as bit patterns
type Bits3 is Data:
  Bits3{dye: U32, before: U32, after: U32}

def bits3(s: F32 & F32 & F32) -> Bits3:
  (dye, before, after) = s
  Bits3{SF32.bits(dye), SF32.bits(before), SF32.bits(after)}

# the result's bits, and whether |div| went down. One law states both,
# so the checker runs the projection once.
type Summary is Data:
  Summary{bits: Bits3, reduced: Bool}

def summary.go(dye: F32, +before: F32, +after: F32) -> Summary:
  Summary{Bits3{SF32.bits(dye), SF32.bits(before), SF32.bits(after)}, F32.lt_bits(after, before)}

def summary(s: F32 & F32 & F32) -> Summary:
  (dye, before, after) = s
  summary.go(dye, before, after)

# projecting lowers the total |divergence|: dye total 2.0, |div| 2.4
# before projecting and 1.1796875 * 2^-19 (about 2.25e-6) after, bit for
# bit
law projection:
  {summary(checked(~soft())) == Summary{Bits3{1073741824, 1075419546, 907468800}, True{}} : Summary}

def projection():
  {==}

# Playing
# -------

def jetted() -> St(Array<F32>, Unit):
  a => (rows(~jet(~hard()), Cfg{31n, 0n, 0n}, 4n, 14n, 4n, 26n, a), Unit{})

def scaled(x: F32, k: F32) -> String:
  U32.show(F32.to_u32(F32.mul(x, k)))

def report(r: Array<F32> & (F32 & F32 & F32)) -> IO(Unit):
  (a, (dye, before, after)) = r
  do IO<Unit>:
    IO.print("dye total x10            " ++ scaled(dye, 10.0))
    IO.print("|div| x1000 after jet    " ++ scaled(before, 1000.0))
    IO.print("|div| x1000 projected    " ++ scaled(after, 1000.0))

def same3(a: Bits3, b: Bits3) -> Bool:
  match a b:
    case Bits3{a1, a2, a3} Bits3{b1, b2, b3}:
      Bool.and(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), U32.is_eq(a3, b3)))

def show3(s: Bits3) -> String:
  match s:
    case Bits3{a1, a2, a3}:
      U32.show(a1) ++ " " ++ U32.show(a2) ++ " " ++ U32.show(a3)

def compare(+h: Bits3, s: Bits3) -> IO(Unit):
  do IO<Unit>:
    IO.print("4x4 bits (dye before after) " ++ show3(h))
    IO.print("4x4 hardware = software     " ++ Bool.show(same3(h, s)))

def main() -> IO(Unit):
  do IO<Unit>:
    report(St.bind(Array<F32>, Unit, F32 & F32 & F32, jetted(), u => stats(~hard(), 31n, 20n))(run(24n, [0.0 : F32^14n])))
    compare(bits3(checked(~hard())), bits3(checked(~soft())))

#|dye total x10            4125
#||div| x1000 after jet    15719
#||div| x1000 projected    8088
#|4x4 bits (dye before after) 1073741824 1075419546 907468800
#|4x4 hardware = software     True
