import Base

# breakout.bend: Breakout in integer pixels, using Base only.
#
# The arena is 256x256. The paddle is 40 wide at y = 240; the ball is 4x4;
# 32 bricks sit in 4 rows of 8 (32x8 px each) from y = 16 to 48. A step
# runs four phases: paddle, ball x, ball y (bounce, or lose a life), bricks.
#
# Laws, over every input list:
#   run_inv     the paddle and ball stay in the arena
#   run_pot     score + 10 * (bricks alive) never changes
#   run_lives   lives never increase
#
# main plays two scripted games headless. apps/breakout_window.bend opens
# a window and plays with the mouse.

type Dir is Data:
  Neg{}
  Pos{}

type Input is Data:
  Left{}
  Right{}
  Stay{}

type Game is Data:
  Game{pad: Nat, bx: Nat, by: Nat, dx: Dir, dy: Dir, bricks: List<&2, Bool>, lives: Nat, score: Nat}

# Order on Nat (Base has none)
# ----------------------------

def LE(a: Nat, b: Nat) -> Data:
  match a b:
    case 0n y:
      Unit
    case 1n+x 0n:
      Empty
    case 1n+x 1n+y:
      LE(x, y)

law le_refl:
  for a: Nat
  LE(a, a)

def le_refl(a):
  match a:
    case 0n:
      Unit{}
    case 1n+p:
      le_refl(p)

law le_step:
  for a: Nat
  LE(a, 1n+a)

def le_step(a):
  match a:
    case 0n:
      Unit{}
    case 1n+p:
      le_step(p)

law le_trans:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: LE(a, b)
  for bc: LE(b, c)
  LE(a, c)

def le_trans(a, b, c, ab, bc):
  match a b c:
    case 0n b c:
      Unit{}
    case 1n+x 0n c:
      match ab:
    case 1n+x 1n+y 0n:
      match bc:
    case 1n+x 1n+y 1n+z:
      le_trans(x, y, z, ab, bc)

law sub_le:
  for a: Nat
  for k: Nat
  LE(Nat.sub(a, k), a)

def sub_le(a, k):
  match a k:
    case 0n 0n:
      Unit{}
    case 0n 1n+q:
      Unit{}
    case 1n+p 0n:
      le_refl(1n+p)
    case 1n++p 1n++q:
      le_trans(Nat.sub(p, q), p, 1n+p, sub_le(p, q), le_step(p))

law min_le_r:
  for a: Nat
  for b: Nat
  LE(Nat.min(a, b), b)

def min_le_r(a, b):
  match a b:
    case 0n y:
      Unit{}
    case 1n+x 0n:
      Unit{}
    case 1n+x 1n+y:
      min_le_r(x, y)

# a >= b or a < b, with the proof of whichever holds
def ge_or_lt(a: Nat, b: Nat) -> Or(LE(b, a), LE(1n+a, b)):
  match a b:
    case 0n 0n:
      Inl{Unit{}}
    case 0n 1n+q:
      Inr{Unit{}}
    case 1n+p 0n:
      Inl{Unit{}}
    case 1n+p 1n+q:
      ge_or_lt(p, q)

# 10 moves out of a sum: add(m, 10 + s) is 10 + add(m, s)
law add_ten:
  for m: Nat
  for -s: Nat
  {Nat.add(10n, Nat.add(m, s)) == Nat.add(m, Nat.add(10n, s)) : Nat}

def add_ten(m, s):
  match m:
    case 0n:
      {==}
    case 1n+p:
      %add_ten(p, s) : {11n+Nat.add(p, s) == 1n+_ : Nat}
      {==}

# Bricks
# ------

def bump(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      1n+n
    case False{}:
      n

def count(bs: List<&2, Bool>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case h <> t:
      bump(h, count(t))

# the result of hitting brick i: it was alive (Smash) or not (Miss)
type Hit is Data:
  Miss{bs: List<&2, Bool>}
  Smash{bs: List<&2, Bool>}

def Hit.count(h: Hit) -> Nat:
  match h:
    case Miss{bs}:
      count(bs)
    case Smash{bs}:
      1n+count(bs)

def cons_hit(b: Bool, r: Hit) -> Hit:
  match r:
    case Miss{bs}:
      Miss{b <> bs}
    case Smash{bs}:
      Smash{b <> bs}

# the brick at the head: smash it if alive
def smash_head(b: Bool, t: List<&2, Bool>) -> Hit:
  match b:
    case True{}:
      Smash{False{} <> t}
    case False{}:
      Miss{False{} <> t}

# Each arm matches the list before the head bit, so smash reduces on a
# list whose head is unknown; nested patterns such as `True{} <> t` would
# split on the head first and leave that case stuck.
def smash(bs: List<&2, Bool>, i: Nat) -> Hit:
  match bs i:
    case Nil{} _:
      Miss{Nil{}}
    case h <> t 0n:
      smash_head(h, t)
    case h <> t 1n+j:
      cons_hit(h, smash(t, j))

law cons_count:
  for b: Bool
  for r: Hit
  {bump(b, Hit.count(r)) == Hit.count(cons_hit(b, r)) : Nat}

def cons_count(b, r):
  match b r:
    case True{} Miss{bs}:
      {==}
    case True{} Smash{bs}:
      {==}
    case False{} Miss{bs}:
      {==}
    case False{} Smash{bs}:
      {==}

law head_count:
  for b: Bool
  for t: List<&2, Bool>
  {count(b <> t) == Hit.count(smash_head(b, t)) : Nat}

def head_count(b, t):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: a hit removes exactly the one brick it smashes
law smash_count:
  for bs: List<&2, Bool>
  for i: Nat
  {count(bs) == Hit.count(smash(bs, i)) : Nat}

def smash_count(bs, i):
  match bs i:
    case Nil{} _:
      {==}
    case h <> t 0n:
      head_count(h, t)
    case +h <> +t 1n++j:
      %cons_count(h, smash(t, j)) : {bump(h, count(t)) == _ : Nat}
      %smash_count(t, j) : {bump(h, count(t)) == bump(h, _) : Nat}
      {==}

# Phases
# ------

def flip(d: Dir) -> Dir:
  match d:
    case Neg{}:
      Pos{}
    case Pos{}:
      Neg{}

def pick_dir(c: Bool, a: Dir, b: Dir) -> Dir:
  match c:
    case True{}:
      a
    case False{}:
      b

def pad_move(p: Nat, i: Input) -> Nat:
  match i:
    case Left{}:
      Nat.sub(p, 6n)
    case Right{}:
      Nat.min(Nat.add(p, 6n), 216n)
    case Stay{}:
      p

def pad_phase(g: Game, i: Input) -> Game:
  match g:
    case Game{pad, bx, by, dx, dy, bricks, lives, score}:
      Game{pad_move(pad, i), bx, by, dx, dy, bricks, lives, score}

def bx_move(x: Nat, d: Dir) -> Nat:
  match d:
    case Pos{}:
      Nat.min(Nat.add(x, 3n), 252n)
    case Neg{}:
      Nat.sub(x, 3n)

def dx_turn(x: Nat, d: Dir) -> Dir:
  match d:
    case Pos{}:
      pick_dir(Nat.is_ge(Nat.add(x, 3n), 252n), Neg{}, Pos{})
    case Neg{}:
      pick_dir(Nat.is_le(x, 3n), Pos{}, Neg{})

def hor_phase(g: Game) -> Game:
  match g:
    case Game{pad, +bx, by, +dx, dy, bricks, lives, score}:
      Game{pad, bx_move(bx, dx), by, dx_turn(bx, dx), dy, bricks, lives, score}

# where a falling ball lands: in flight (with proof it is above 252), on
# the paddle, or past the bottom
type Fall is Data:
  Fly{y: Nat, ok: LE(1n+y, 252n)}
  Bounce{}
  Lost{}

def fall.go(y: Nat, hit: Bool, c: Or(LE(252n, y), LE(1n+y, 252n))) -> Fall:
  match hit:
    case True{}:
      Bounce{}
    case False{}:
      match c:
        case Inl{e}:
          Lost{}
        case Inr{e}:
          Fly{y, e}

def on_paddle(+y: Nat, +x: Nat, +pad: Nat) -> Bool:
  Bool.and(Nat.is_ge(y, 236n), Bool.and(Nat.is_gt(Nat.add(x, 4n), pad), Nat.is_lt(x, Nat.add(pad, 40n))))

def fall(by: Nat, +bx: Nat, +pad: Nat) -> Fall:
  +y = Nat.add(by, 2n)
  fall.go(y, on_paddle(y, bx, pad), ge_or_lt(y, 252n))

def land(pad: Nat, bx: Nat, dx: Dir, bricks: List<&2, Bool>, lives: Nat, score: Nat, f: Fall) -> Game:
  match f:
    case Fly{y, ok}:
      Game{pad, bx, y, dx, Pos{}, bricks, lives, score}
    case Bounce{}:
      Game{pad, bx, 236n, dx, Neg{}, bricks, lives, score}
    case Lost{}:
      Game{pad, 126n, 128n, dx, Neg{}, bricks, Nat.sub(lives, 1n), score}

def vert_phase(g: Game) -> Game:
  match g:
    case Game{+pad, +bx, +by, dx, dy, bricks, lives, score}:
      match dy:
        case Neg{}:
          Game{pad, bx, Nat.sub(by, 2n), dx, pick_dir(Nat.is_le(by, 2n), Pos{}, Neg{}), bricks, lives, score}
        case Pos{}:
          land(pad, bx, dx, bricks, lives, score, fall(by, bx, pad))

def in_zone(+y: Nat) -> Bool:
  Bool.and(Nat.is_ge(y, 16n), Nat.is_lt(y, 48n))

# brick under the ball: row (y - 16) / 8, column x / 32
def brick_idx(x: Nat, y: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.div(Nat.sub(y, 16n), 8n), 8n), Nat.div(x, 32n))

def apply_hit(pad: Nat, bx: Nat, by: Nat, dx: Dir, dy: Dir, lives: Nat, score: Nat, h: Hit) -> Game:
  match h:
    case Miss{bs}:
      Game{pad, bx, by, dx, dy, bs, lives, score}
    case Smash{bs}:
      Game{pad, bx, by, dx, flip(dy), bs, lives, Nat.add(10n, score)}

def hit_at(pad: Nat, bx: Nat, by: Nat, dx: Dir, dy: Dir, lives: Nat, score: Nat, z: Bool, bricks: List<&2, Bool>, i: Nat) -> Game:
  match z:
    case False{}:
      Game{pad, bx, by, dx, dy, bricks, lives, score}
    case True{}:
      apply_hit(pad, bx, by, dx, dy, lives, score, smash(bricks, i))

def brick_phase(g: Game) -> Game:
  match g:
    case Game{pad, +bx, +by, dx, dy, bricks, lives, score}:
      hit_at(pad, bx, by, dx, dy, lives, score, in_zone(by), bricks, brick_idx(bx, by))

def step(g: Game, i: Input) -> Game:
  brick_phase(vert_phase(hor_phase(pad_phase(g, i))))

def run(g: Game, xs: List<&2, Input>) -> Game:
  List.foldl(~&2, ~Input, ~Game, ~step, xs, g)

# Invariant: paddle and ball in the arena
# ---------------------------------------

def Inv(g: Game) -> Type:
  match g:
    case Game{pad, bx, by, dx, dy, bricks, lives, score}:
      LE(pad, 216n) & LE(bx, 252n) & LE(by, 252n)

law pad_ok:
  for +p: Nat
  for i: Input
  for h: LE(p, 216n)
  LE(pad_move(p, i), 216n)

def pad_ok(p, i, h):
  match i:
    case Left{}:
      le_trans(Nat.sub(p, 6n), p, 216n, sub_le(p, 6n), h)
    case Right{}:
      min_le_r(Nat.add(p, 6n), 216n)
    case Stay{}:
      h

law pad_inv:
  for g: Game
  for i: Input
  Inv(g) -> Inv(pad_phase(g, i))

law pad_inv.go:
  for +p: Nat
  for i: Input
  for -x: Nat
  for -y: Nat
  for k: LE(p, 216n) & LE(x, 252n) & LE(y, 252n)
  LE(pad_move(p, i), 216n) & LE(x, 252n) & LE(y, 252n)

def pad_inv.go(p, i, x, y, k):
  (hp, hx, hy) = k
  (pad_ok(p, i, hp), hx, hy)

def pad_inv(g, i):
  match g:
    case Game{pad, bx, by, dx, dy, bricks, lives, score}:
      k => pad_inv.go(pad, i, bx, by, k)

law bx_ok:
  for +x: Nat
  for d: Dir
  for h: LE(x, 252n)
  LE(bx_move(x, d), 252n)

def bx_ok(x, d, h):
  match d:
    case Pos{}:
      min_le_r(Nat.add(x, 3n), 252n)
    case Neg{}:
      le_trans(Nat.sub(x, 3n), x, 252n, sub_le(x, 3n), h)

law hor_inv:
  for g: Game
  Inv(g) -> Inv(hor_phase(g))

law hor_inv.go:
  for -p: Nat
  for +x: Nat
  for d: Dir
  for -y: Nat
  for k: LE(p, 216n) & LE(x, 252n) & LE(y, 252n)
  LE(p, 216n) & LE(bx_move(x, d), 252n) & LE(y, 252n)

def hor_inv.go(p, x, d, y, k):
  (hp, hx, hy) = k
  (hp, bx_ok(x, d, hx), hy)

def hor_inv(g):
  match g:
    case Game{pad, bx, by, dx, dy, bricks, lives, score}:
      k => hor_inv.go(pad, bx, dx, by, k)

law land_inv:
  for +pad: Nat
  for +bx: Nat
  for dx: Dir
  for bricks: List<&2, Bool>
  for lives: Nat
  for score: Nat
  for f: Fall
  for hp: LE(pad, 216n)
  for hx: LE(bx, 252n)
  Inv(land(pad, bx, dx, bricks, lives, score, f))

def land_inv(pad, bx, dx, bricks, lives, score, f, hp, hx):
  match f:
    case Fly{+y, ok}:
      (hp, hx, le_trans(y, 1n+y, 252n, le_step(y), ok))
    case Bounce{}:
      (hp, hx, Unit{})
    case Lost{}:
      (hp, Unit{}, Unit{})

law vert_inv:
  for g: Game
  Inv(g) -> Inv(vert_phase(g))

law vert_up.go:
  for -p: Nat
  for -x: Nat
  for +y: Nat
  for k: LE(p, 216n) & LE(x, 252n) & LE(y, 252n)
  LE(p, 216n) & LE(x, 252n) & LE(Nat.sub(y, 2n), 252n)

def vert_up.go(p, x, y, k):
  (hp, hx, hy) = k
  (hp, hx, le_trans(Nat.sub(y, 2n), y, 252n, sub_le(y, 2n), hy))

law vert_down.go:
  for +p: Nat
  for +x: Nat
  for +y: Nat
  for dx: Dir
  for bricks: List<&2, Bool>
  for lives: Nat
  for score: Nat
  for k: LE(p, 216n) & LE(x, 252n) & LE(y, 252n)
  Inv(land(p, x, dx, bricks, lives, score, fall(y, x, p)))

def vert_down.go(p, x, y, dx, bricks, lives, score, k):
  (hp, hx, hy) = k
  land_inv(p, x, dx, bricks, lives, score, fall(y, x, p), hp, hx)

def vert_inv(g):
  match g:
    case Game{pad, bx, by, dx, dy, bricks, lives, score}:
      match dy:
        case Neg{}:
          k => vert_up.go(pad, bx, by, k)
        case Pos{}:
          k => vert_down.go(pad, bx, by, dx, bricks, lives, score, k)

law hit_inv:
  for +pad: Nat
  for +bx: Nat
  for +by: Nat
  for dx: Dir
  for dy: Dir
  for lives: Nat
  for score: Nat
  for z: Bool
  for bricks: List<&2, Bool>
  for i: Nat
  for k: LE(pad, 216n) & LE(bx, 252n) & LE(by, 252n)
  Inv(hit_at(pad, bx, by, dx, dy, lives, score, z, bricks, i))

law apply_inv:
  for +pad: Nat
  for +bx: Nat
  for +by: Nat
  for dx: Dir
  for dy: Dir
  for lives: Nat
  for score: Nat
  for h: Hit
  for k: LE(pad, 216n) & LE(bx, 252n) & LE(by, 252n)
  Inv(apply_hit(pad, bx, by, dx, dy, lives, score, h))

def apply_inv(pad, bx, by, dx, dy, lives, score, h, k):
  match h:
    case Miss{bs}:
      k
    case Smash{bs}:
      k

def hit_inv(pad, bx, by, dx, dy, lives, score, z, bricks, i, k):
  match z:
    case False{}:
      k
    case True{}:
      apply_inv(pad, bx, by, dx, dy, lives, score, smash(bricks, i), k)

law brick_inv:
  for g: Game
  Inv(g) -> Inv(brick_phase(g))

def brick_inv(g):
  match g:
    case Game{pad, +bx, +by, dx, dy, bricks, lives, score}:
      k => hit_inv(pad, bx, by, dx, dy, lives, score, in_zone(by), bricks, brick_idx(bx, by), k)

law step_inv:
  for +g: Game
  for +i: Input
  Inv(g) -> Inv(step(g, i))

def step_inv(g, i):
  k => brick_inv(vert_phase(hor_phase(pad_phase(g, i))))(vert_inv(hor_phase(pad_phase(g, i)))(hor_inv(pad_phase(g, i))(pad_inv(g, i)(k))))

# LAW: from a state in the arena, every input list keeps it in the arena
law run_inv:
  for xs: List<&2, Input>
  for +g: Game
  Inv(g) -> Inv(run(g, xs))

def run_inv(xs, g):
  match xs:
    case Nil{}:
      k => k
    case +h <> t:
      k => run_inv(t, step(g, h))(step_inv(g, h)(k))

# Conservation: score + 10 * (bricks alive)
# ----------------------------------------

def pot(g: Game) -> Nat:
  match g:
    case Game{pad, bx, by, dx, dy, bricks, lives, score}:
      Nat.add(Nat.mul(count(bricks), 10n), score)

law pad_pot:
  for g: Game
  for i: Input
  {pot(g) == pot(pad_phase(g, i)) : Nat}

def pad_pot(g, i):
  match g:
    case Game{pad, bx, by, dx, dy, bricks, lives, score}:
      {==}

law hor_pot:
  for g: Game
  {pot(g) == pot(hor_phase(g)) : Nat}

def hor_pot(g):
  match g:
    case Game{pad, bx, by, dx, dy, bricks, lives, score}:
      {==}

law land_pot:
  for pad: Nat
  for bx: Nat
  for dx: Dir
  for +bricks: List<&2, Bool>
  for lives: Nat
  for +score: Nat
  for f: Fall
  {Nat.add(Nat.mul(count(bricks), 10n), score) == pot(land(pad, bx, dx, bricks, lives, score, f)) : Nat}

def land_pot(pad, bx, dx, bricks, lives, score, f):
  match f:
    case Fly{y, ok}:
      {==}
    case Bounce{}:
      {==}
    case Lost{}:
      {==}

law vert_pot:
  for g: Game
  {pot(g) == pot(vert_phase(g)) : Nat}

def vert_pot(g):
  match g:
    case Game{+pad, +bx, +by, dx, dy, +bricks, lives, +score}:
      match dy:
        case Neg{}:
          {==}
        case Pos{}:
          land_pot(pad, bx, dx, bricks, lives, score, fall(by, bx, pad))

law apply_pot:
  for pad: Nat
  for bx: Nat
  for by: Nat
  for dx: Dir
  for dy: Dir
  for lives: Nat
  for +score: Nat
  for +h: Hit
  {Nat.add(Nat.mul(Hit.count(h), 10n), score) == pot(apply_hit(pad, bx, by, dx, dy, lives, score, h)) : Nat}

def apply_pot(pad, bx, by, dx, dy, lives, score, h):
  match h:
    case Miss{bs}:
      {==}
    case Smash{+bs}:
      add_ten(Nat.mul(count(bs), 10n), score)

law hit_pot:
  for pad: Nat
  for bx: Nat
  for by: Nat
  for dx: Dir
  for dy: Dir
  for lives: Nat
  for +score: Nat
  for z: Bool
  for +bricks: List<&2, Bool>
  for +i: Nat
  {Nat.add(Nat.mul(count(bricks), 10n), score) == pot(hit_at(pad, bx, by, dx, dy, lives, score, z, bricks, i)) : Nat}

def hit_pot(pad, bx, by, dx, dy, lives, score, z, bricks, i):
  match z:
    case False{}:
      {==}
    case True{}:
      Equal.trans(Nat, Nat.add(Nat.mul(count(bricks), 10n), score),
        Nat.add(Nat.mul(Hit.count(smash(bricks, i)), 10n), score),
        pot(apply_hit(pad, bx, by, dx, dy, lives, score, smash(bricks, i))),
        Equal.cong(Nat, Nat, n => Nat.add(Nat.mul(n, 10n), score), count(bricks), Hit.count(smash(bricks, i)), smash_count(bricks, i)),
        apply_pot(pad, bx, by, dx, dy, lives, score, smash(bricks, i)))

law brick_pot:
  for g: Game
  {pot(g) == pot(brick_phase(g)) : Nat}

def brick_pot(g):
  match g:
    case Game{pad, +bx, +by, dx, dy, +bricks, lives, +score}:
      hit_pot(pad, bx, by, dx, dy, lives, score, in_zone(by), bricks, brick_idx(bx, by))

law step_pot:
  for +g: Game
  for +i: Input
  {pot(g) == pot(step(g, i)) : Nat}

def step_pot(g, i):
  %brick_pot(vert_phase(hor_phase(pad_phase(g, i)))) : {pot(g) == _ : Nat}
  %vert_pot(hor_phase(pad_phase(g, i))) : {pot(g) == _ : Nat}
  %hor_pot(pad_phase(g, i)) : {pot(g) == _ : Nat}
  pad_pot(g, i)

# LAW: score + 10 * (bricks alive) is the same after any input list
law run_pot:
  for xs: List<&2, Input>
  for +g: Game
  {pot(g) == pot(run(g, xs)) : Nat}

def run_pot(xs, g):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      %run_pot(t, step(g, h)) : {pot(g) == _ : Nat}
      step_pot(g, h)

# Lives
# -----

def lives_of(g: Game) -> Nat:
  match g:
    case Game{pad, bx, by, dx, dy, bricks, lives, score}:
      lives

law land_lives:
  for pad: Nat
  for bx: Nat
  for dx: Dir
  for bricks: List<&2, Bool>
  for +lives: Nat
  for score: Nat
  for f: Fall
  LE(lives_of(land(pad, bx, dx, bricks, lives, score, f)), lives)

def land_lives(pad, bx, dx, bricks, lives, score, f):
  match f:
    case Fly{y, ok}:
      le_refl(lives)
    case Bounce{}:
      le_refl(lives)
    case Lost{}:
      sub_le(lives, 1n)

law apply_lives:
  for pad: Nat
  for bx: Nat
  for by: Nat
  for dx: Dir
  for dy: Dir
  for +lives: Nat
  for score: Nat
  for h: Hit
  LE(lives_of(apply_hit(pad, bx, by, dx, dy, lives, score, h)), lives)

def apply_lives(pad, bx, by, dx, dy, lives, score, h):
  match h:
    case Miss{bs}:
      le_refl(lives)
    case Smash{bs}:
      le_refl(lives)

law hit_lives:
  for pad: Nat
  for bx: Nat
  for by: Nat
  for dx: Dir
  for dy: Dir
  for +lives: Nat
  for score: Nat
  for z: Bool
  for bricks: List<&2, Bool>
  for i: Nat
  LE(lives_of(hit_at(pad, bx, by, dx, dy, lives, score, z, bricks, i)), lives)

def hit_lives(pad, bx, by, dx, dy, lives, score, z, bricks, i):
  match z:
    case False{}:
      le_refl(lives)
    case True{}:
      apply_lives(pad, bx, by, dx, dy, lives, score, smash(bricks, i))

law step_lives:
  for +g: Game
  for +i: Input
  LE(lives_of(step(g, i)), lives_of(g))

law pad_lives:
  for g: Game
  for i: Input
  LE(lives_of(pad_phase(g, i)), lives_of(g))

def pad_lives(g, i):
  match g:
    case Game{pad, bx, by, dx, dy, bricks, +lives, score}:
      le_refl(lives)

law hor_lives:
  for g: Game
  LE(lives_of(hor_phase(g)), lives_of(g))

def hor_lives(g):
  match g:
    case Game{pad, bx, by, dx, dy, bricks, +lives, score}:
      le_refl(lives)

law vert_lives:
  for g: Game
  LE(lives_of(vert_phase(g)), lives_of(g))

def vert_lives(g):
  match g:
    case Game{+pad, +bx, +by, dx, dy, bricks, +lives, score}:
      match dy:
        case Neg{}:
          le_refl(lives)
        case Pos{}:
          land_lives(pad, bx, dx, bricks, lives, score, fall(by, bx, pad))

law brick_lives:
  for g: Game
  LE(lives_of(brick_phase(g)), lives_of(g))

def brick_lives(g):
  match g:
    case Game{pad, +bx, +by, dx, dy, bricks, +lives, score}:
      hit_lives(pad, bx, by, dx, dy, lives, score, in_zone(by), bricks, brick_idx(bx, by))

def step_lives(g, i):
  +a = pad_phase(g, i)
  +b = hor_phase(a)
  +c = vert_phase(b)
  le_trans(lives_of(brick_phase(c)), lives_of(c), lives_of(g), brick_lives(c),
    le_trans(lives_of(c), lives_of(b), lives_of(g), vert_lives(b),
      le_trans(lives_of(b), lives_of(a), lives_of(g), hor_lives(a), pad_lives(g, i))))

# LAW: lives never increase over any input list
law run_lives:
  for xs: List<&2, Input>
  for +g: Game
  LE(lives_of(run(g, xs)), lives_of(g))

def run_lives(xs, g):
  match xs:
    case Nil{}:
      le_refl(lives_of(g))
    case +h <> +t:
      le_trans(lives_of(run(step(g, h), t)), lives_of(step(g, h)), lives_of(g), run_lives(t, step(g, h)), step_lives(g, h))

# Playing
# -------

def init() -> Game:
  Game{108n, 126n, 128n, Pos{}, Neg{}, List.replicate(Bool, 32n, True{}), 3n, 0n}

def pilot.go(c: Cmp) -> Input:
  match c:
    case LT{}:
      Left{}
    case EQ{}:
      Stay{}
    case GT{}:
      Right{}

# input that moves the paddle's centre toward the ball
def pilot(g: Game) -> Input:
  match g:
    case Game{pad, bx, by, dx, dy, bricks, lives, score}:
      pilot.go(Nat.cmp(Nat.add(bx, 2n), Nat.add(pad, 20n)))

def autoplay(n: Nat, +g: Game) -> Game:
  match n:
    case 0n:
      g
    case 1n+k:
      autoplay(k, step(g, pilot(g)))

def show(g: Game) -> String:
  match g:
    case Game{pad, bx, by, dx, dy, bricks, lives, score}:
      "score=" ++ Nat.show(score) ++ " bricks=" ++ Nat.show(count(bricks)) ++ " lives=" ++ Nat.show(lives) ++ " ball=" ++ Nat.show(bx) ++ "," ++ Nat.show(by)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("pilot " ++ show(autoplay(4000n, init())))
    IO.print("idle  " ++ show(run(init(), List.replicate(Input, 400n, Stay{}))))

#|pilot score=270 bricks=5 lives=3 ball=30,200
#|idle  score=180 bricks=14 lives=1 ball=66,36
