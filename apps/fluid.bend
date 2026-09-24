import Base
import ../src/nat.bend as Nat
import ../src/float/f32.bend as F32

# fluid.bend: 2D incompressible Navier-Stokes by stable fluids (Stam 1999)
# on a 32x32 torus.
#
# A step: add a jet of dye and upward velocity at the bottom; advect the
# velocity by itself (semi-Lagrangian, bilinear); project it to be
# divergence-free (Jacobi pressure solve, then subtract the pressure
# gradient); advect the dye by the result. Viscosity is left out; the
# advection's interpolation smooths the flow instead.
#
# Proven, about the grid (Nat coordinates):
#   right_lt, left_lt     a neighbour of a cell is a cell
#   left_right, right_left the torus neighbours undo each other
#   idx_lt                a cell's index is below 1024, so the 16 fields
#                         packed in one array (1024 slots each) never
#                         overlap, and Array's silent index wraparound
#                         never aliases two cells
# Proven, about the floats (src/float/f32.bend, assuming LtOk):
#   cell_ok               every back-traced position, NaN and infinities
#                         included, gives a cell index in [0, 95] and an
#                         interpolation weight in [0, 1], so F32.to_u32
#                         never sees a value it is undefined on
# Not proven: the values the solver computes. main prints the dye total
# and the divergence before and after projection instead. The pressure
# solve is 20 Jacobi sweeps, which removes most short-range divergence
# but converges slowly on smooth, large-scale divergence (at 400 sweeps
# the residual falls about 13x further).
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

def right.go(x: Nat, top: Bool) -> Nat:
  match top:
    case True{}:
      0n
    case False{}:
      1n+x

def right(+x: Nat) -> Nat:
  right.go(x, Nat.is_eq(x, 31n))

def left(x: Nat) -> Nat:
  match x:
    case 0n:
      31n
    case 1n+p:
      p

def idx(x: Nat, y: Nat) -> Nat:
  Nat.add(Nat.mul(y, 32n), x)

law right_lt.go:
  for +x: Nat
  for c: Bool
  for e: {Nat.is_eq(x, 31n) == c : Bool}
  for lt: Nat.LT(x, 32n)
  Nat.LT(right.go(x, c), 32n)

def right_lt.go(x, c, e, lt):
  match c:
    case True{}:
      Unit{}
    case False{}:
      lt_step(x, 31n, lt, e)

# the right neighbour of a cell is a cell
law right_lt:
  for +x: Nat
  for lt: Nat.LT(x, 32n)
  Nat.LT(right(x), 32n)

def right_lt(x, lt):
  right_lt.go(x, Nat.is_eq(x, 31n), {==}, lt)

# the left neighbour of a cell is a cell
law left_lt:
  for x: Nat
  for lt: Nat.LT(x, 32n)
  Nat.LT(left(x), 32n)

def left_lt(x, lt):
  match x:
    case 0n:
      Unit{}
    case 1n+p:
      le_add(1n+p, 31n, 1n, lt)

law left_right.go:
  for +x: Nat
  for c: Bool
  for e: {Nat.is_eq(x, 31n) == c : Bool}
  {left(right.go(x, c)) == x : Nat}

def left_right.go(x, c, e):
  match c:
    case True{}:
      Equal.sym(Nat, x, 31n, eq_of_is_eq(x, 31n, e))
    case False{}:
      {==}

# stepping right then left returns to the cell
law left_right:
  for +x: Nat
  {left(right(x)) == x : Nat}

def left_right(x):
  left_right.go(x, Nat.is_eq(x, 31n), {==})

# stepping left then right returns to the cell
law right_left:
  for x: Nat
  for lt: Nat.LT(x, 32n)
  {right(left(x)) == x : Nat}

def right_left(x, lt):
  match x:
    case 0n:
      {==}
    case 1n+p:
      +p2 = p
      %lt_ne(p2, 31n, lt) : {right.go(p2, _) == 1n+p2 : Nat}
      {==}

law idx_lt.go:
  for +x: Nat
  for y: Nat
  for n: Nat
  for hx: Nat.LT(x, 32n)
  for hy: Nat.LT(y, n)
  Nat.LT(idx(x, y), Nat.mul(n, 32n))

def idx_lt.go(x, y, n, hx, hy):
  match y n:
    case 0n 0n:
      match hy:
    case 0n 1n+m:
      le_add(1n+x, 32n, Nat.mul(m, 32n), hx)
    case 1n+p 0n:
      match hy:
    case 1n+p 1n+m:
      idx_lt.go(x, p, m, hx, hy)

# a cell's index is inside the 1024-slot array
law idx_lt:
  for +x: Nat
  for y: Nat
  for hx: Nat.LT(x, 32n)
  for hy: Nat.LT(y, 32n)
  Nat.LT(idx(x, y), 1024n)

def idx_lt(x, y, hx, hy):
  idx_lt.go(x, y, 32n, hx, hy)

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

# Fields (tested, not proven)
# ---------------------------
# The grid is one Array<F32> of 16 fields x 1024 cells.

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

def slot(f: Nat, x: Nat, y: Nat) -> U32:
  U32.from_nat(Nat.add(Nat.mul(f, 1024n), idx(x, y)))

def get(f: Nat, x: Nat, y: Nat) -> St(Array<F32>, F32):
  +i = slot(f, x, y)
  a => Array.get(F32, a, i)

def put(f: Nat, x: Nat, y: Nat, v: F32) -> St(Array<F32>, Unit):
  +i = slot(f, x, y)
  a => (Array.set(F32, a, i, v), Unit{})

def get_raw(+i: U32) -> St(Array<F32>, F32):
  a => Array.get(F32, a, i)

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

# bilinear sample of field f at (px, py), both offset by +32 to stay positive
def sample(f: Nat, +px: F32, +py: F32) -> St(Array<F32>, F32):
  sample.go(f, cell(px), cell(py))

def back(+c: Nat, +vel: F32) -> F32:
  F32.add(F32.sub(F32.from_nat(c), F32.mul(dt(), vel)), 32.0)

# a kernel's source and destination fields
type Cfg is Data:
  Cfg{src: Nat, dst: Nat}

def adv_uv(c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  do St<Array<F32>, Unit>:
    +uc : F32 <- get(U(), x, y)
    +vc : F32 <- get(V(), x, y)
    su : F32 <- sample(U(), back(x, uc), back(y, vc))
    sv : F32 <- sample(V(), back(x, uc), back(y, vc))
    put(U2(), x, y, su)
    put(V2(), x, y, sv)

# advect field src into dst along (U, V)
def adv(c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  Cfg{+src, +dst} = c
  do St<Array<F32>, Unit>:
    uc : F32 <- get(U(), x, y)
    vc : F32 <- get(V(), x, y)
    sd : F32 <- sample(src, back(x, uc), back(y, vc))
    put(dst, x, y, sd)

def copy(c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  Cfg{src, dst} = c
  do St<Array<F32>, Unit>:
    v : F32 <- get(src, x, y)
    put(dst, x, y, v)

# divergence by forward differences
def div_at(c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  do St<Array<F32>, Unit>:
    ur : F32 <- get(U(), right(x), y)
    uc : F32 <- get(U(), x, y)
    vd : F32 <- get(V(), x, right(y))
    vc : F32 <- get(V(), x, y)
    put(DIV(), x, y, F32.add(F32.sub(ur, uc), F32.sub(vd, vc)))

# one Jacobi sweep of lap(p) = div, with the 5-point Laplacian
def jac_at(c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  do St<Array<F32>, Unit>:
    dv : F32 <- get(DIV(), x, y)
    pr : F32 <- get(P(), right(x), y)
    pl : F32 <- get(P(), left(x), y)
    pd : F32 <- get(P(), x, right(y))
    pu : F32 <- get(P(), x, left(y))
    put(P2(), x, y, F32.mul(0.25, F32.sub(F32.add(F32.add(pr, pl), F32.add(pd, pu)), dv)))

# subtract the pressure gradient by backward differences; with the
# forward divergence this makes div(grad p) the same 5-point Laplacian
def grad_at(c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  do St<Array<F32>, Unit>:
    +pc : F32 <- get(P(), x, y)
    pl : F32 <- get(P(), left(x), y)
    pu : F32 <- get(P(), x, left(y))
    uc : F32 <- get(U(), x, y)
    vc : F32 <- get(V(), x, y)
    put(U(), x, y, F32.sub(uc, F32.sub(pc, pl)))
    put(V(), x, y, F32.sub(vc, F32.sub(pc, pu)))

# add |src| (or src) at this cell into ACC slot 0
def abs_sum(c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  Cfg{src, dst} = c
  do St<Array<F32>, Unit>:
    v : F32 <- get(src, x, y)
    t : F32 <- get(ACC(), 0n, 0n)
    put(ACC(), 0n, 0n, F32.add(t, F32.abs(v)))

def sum(c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  Cfg{src, dst} = c
  do St<Array<F32>, Unit>:
    v : F32 <- get(src, x, y)
    t : F32 <- get(ACC(), 0n, 0n)
    put(ACC(), 0n, 0n, F32.add(t, v))

def jet(c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  do St<Array<F32>, Unit>:
    uc : F32 <- get(U(), x, y)
    vc : F32 <- get(V(), x, y)
    dc : F32 <- get(D(), x, y)
    put(U(), x, y, F32.add(uc, 0.1))
    put(V(), x, y, F32.sub(vc, 0.6))
    put(D(), x, y, F32.add(dc, 1.0))

# Sweeps
# ------

def row(~k: @c: Cfg -> @+x: Nat -> @+y: Nat -> St(Array<F32>, Unit), +c: Cfg, n: Nat, +x: Nat, +y: Nat, a: Array<F32>) -> Array<F32>:
  match n:
    case 0n:
      a
    case 1n+m:
      row(~k, c, m, 1n+x, y, St.exec(Array<F32>, Unit, k(c, x, y)(a)))

def rows(~k: @c: Cfg -> @+x: Nat -> @+y: Nat -> St(Array<F32>, Unit), +c: Cfg, +w: Nat, +x0: Nat, n: Nat, +y: Nat, a: Array<F32>) -> Array<F32>:
  match n:
    case 0n:
      a
    case 1n+m:
      rows(~k, c, w, x0, m, 1n+y, row(~k, c, w, x0, y, a))

# every cell
def each(~k: @c: Cfg -> @+x: Nat -> @+y: Nat -> St(Array<F32>, Unit), +c: Cfg, a: Array<F32>) -> Array<F32>:
  rows(~k, c, 32n, 0n, 32n, 0n, a)

def jacobi(n: Nat, a: Array<F32>) -> Array<F32>:
  match n:
    case 0n:
      a
    case 1n+m:
      jacobi(m, each(~copy, Cfg{P2(), P()}, each(~jac_at, Cfg{0n, 0n}, a)))

def clear_p(c: Cfg, +x: Nat, +y: Nat) -> St(Array<F32>, Unit):
  put(P(), x, y, 0.0)

def project(a: Array<F32>) -> Array<F32>:
  each(~grad_at, Cfg{0n, 0n}, jacobi(20n, each(~clear_p, Cfg{0n, 0n}, each(~div_at, Cfg{0n, 0n}, a))))

def step(a: Array<F32>) -> Array<F32>:
  a1 = rows(~jet, Cfg{0n, 0n}, 4n, 14n, 4n, 26n, a)
  a2 = each(~copy, Cfg{V2(), V()}, each(~copy, Cfg{U2(), U()}, each(~adv_uv, Cfg{0n, 0n}, a1)))
  each(~copy, Cfg{D2(), D()}, each(~adv, Cfg{D(), D2()}, project(a2)))

def run(n: Nat, a: Array<F32>) -> Array<F32>:
  match n:
    case 0n:
      a
    case 1n+m:
      run(m, step(a))

# whole-grid passes as state actions
def sweep(~k: @c: Cfg -> @+x: Nat -> @+y: Nat -> St(Array<F32>, Unit), +c: Cfg) -> St(Array<F32>, Unit):
  a => (each(~k, c, a), Unit{})

def projected() -> St(Array<F32>, Unit):
  a => (project(a), Unit{})

# sum of |DIV| or of D over the grid, via ACC slot 0
def total(~k: @c: Cfg -> @+x: Nat -> @+y: Nat -> St(Array<F32>, Unit), +src: Nat) -> St(Array<F32>, F32):
  do St<Array<F32>, F32>:
    put(ACC(), 0n, 0n, 0.0)
    sweep(~k, Cfg{src, 0n})
    t : F32 <- get(ACC(), 0n, 0n)
    return t

def jetted() -> St(Array<F32>, Unit):
  a => (rows(~jet, Cfg{0n, 0n}, 4n, 14n, 4n, 26n, a), Unit{})

# dye total; total |divergence| after a fresh jet, and after projecting it
def stats() -> St(Array<F32>, F32 & F32 & F32):
  do St<Array<F32>, F32 & F32 & F32>:
    jetted()
    sweep(~div_at, Cfg{0n, 0n})
    before : F32 <- total(~abs_sum, DIV())
    projected()
    sweep(~div_at, Cfg{0n, 0n})
    after : F32 <- total(~abs_sum, DIV())
    dye : F32 <- total(~sum, D())
    return (dye, before, after)

def scaled(x: F32, k: F32) -> String:
  U32.show(F32.to_u32(F32.mul(x, k)))

def report(r: Array<F32> & (F32 & F32 & F32)) -> IO(Unit):
  (a, (dye, before, after)) = r
  do IO<Unit>:
    IO.print("dye total x10            " ++ scaled(dye, 10.0))
    IO.print("|div| x1000 after jet    " ++ scaled(before, 1000.0))
    IO.print("|div| x1000 projected    " ++ scaled(after, 1000.0))

def main() -> IO(Unit):
  report(stats()(run(24n, [0.0 : F32^14n])))

#|dye total x10            4125
#||div| x1000 after jet    15719
#||div| x1000 projected    8088
