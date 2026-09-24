import Base
import ../src/nat.bend as Nat
import ../src/machine.bend as M
import ../src/float/f32.bend as F32

# breakout.bend: Breakout with float physics.
#
# The arena is 256x256. The paddle is 40 wide at y = 240; the ball is 4x4;
# 32 bricks sit in 4 rows of 8 (32x8 px each) from y = 16 to 48. Paddle,
# ball and velocity are F32, computed with Base's F32 functions, so the
# game runs on the machine's floats. The input is where the player
# points (the mouse's x): any F32.
#
# A step is sense then act. sense decides everything from the state: where
# things would move, which velocities flip, which brick is hit, whether
# the ball is lost. act applies it: clamp the positions, flip the signs,
# count. Each law is about act, so its proof names no expression twice.
#
# Laws, for every input list, with the hardware hypotheses of
# src/float/f32.bend stated as template arguments:
#   arena_run   the paddle and ball stay in the arena, whatever floats
#               come in, NaN and infinities included (assumes LtOk: the
#               hardware's < is IEEE's)
#   speed_run   the ball keeps its speed bit for bit: a bounce only flips
#               a velocity's sign (assumes NegOk)
#   pot_run     score + 10 * (bricks alive) never changes
#   lives_run   lives never increase
#
# main plays two scripted games headless. apps/breakout_window.bend opens
# a window and plays with the mouse.

type Game is Data:
  Game{pad: F32, bx: F32, by: F32, vx: F32, vy: F32, bricks: List<&2, Bool>, lives: Nat, score: Nat}

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

def Hit.bricks(h: Hit) -> List<&2, Bool>:
  match h:
    case Miss{bs}:
      bs
    case Smash{bs}:
      bs

def Hit.smashed(h: Hit) -> Bool:
  match h:
    case Miss{bs}:
      False{}
    case Smash{bs}:
      True{}

def Hit.points(h: Hit) -> Nat:
  match h:
    case Miss{bs}:
      0n
    case Smash{bs}:
      10n

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

# the brick rows, and the brick under pixel (x, y) in them
def in_rows(+y: Nat) -> Bool:
  Bool.and(Nat.is_ge(y, 16n), Nat.is_lt(y, 48n))

def brick_at(x: Nat, y: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.div(Nat.sub(y, 16n), 8n), 8n), Nat.div(x, 32n))

def hit_at(z: Bool, bricks: List<&2, Bool>, i: Nat) -> Hit:
  match z:
    case True{}:
      smash(bricks, i)
    case False{}:
      Miss{bricks}

# the ball's centre as a pixel, and what it hits
def hit.px(bricks: List<&2, Bool>, +x: Nat, +y: Nat) -> Hit:
  hit_at(in_rows(y), bricks, brick_at(x, y))

def hit(bricks: List<&2, Bool>, x: F32, y: F32) -> Hit:
  hit.px(bricks, F32.to_nat(F32.add(x, 2.0)), F32.to_nat(F32.add(y, 2.0)))

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

# a hit removes exactly the one brick it smashes
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

law hit_at_count:
  for z: Bool
  for bricks: List<&2, Bool>
  for i: Nat
  {count(bricks) == Hit.count(hit_at(z, bricks, i)) : Nat}

def hit_at_count(z, bricks, i):
  match z:
    case True{}:
      smash_count(bricks, i)
    case False{}:
      {==}

law hit_count:
  for bricks: List<&2, Bool>
  for x: F32
  for y: F32
  {count(bricks) == Hit.count(hit(bricks, x, y)) : Nat}

def hit_count(bricks, x, y):
  +px = F32.to_nat(F32.add(x, 2.0))
  +py = F32.to_nat(F32.add(y, 2.0))
  hit_at_count(in_rows(py), bricks, brick_at(px, py))

# Step
# ----

# a velocity after a bounce, or not
def turn(c: Bool, +v: F32) -> F32:
  Bool.pick(F32, c, F32.neg(v), v)

def outside(+x: F32, lo: F32, hi: F32) -> Bool:
  Bool.or(F32.is_lt(x, lo), F32.is_lt(hi, x))

# the ball meets the paddle: it falls, its bottom reaches 240, and it
# overlaps the paddle
def on_pad(+y: F32, +vy: F32, +x: F32, +pad: F32) -> Bool:
  Bool.and(F32.is_lt(0.0, vy), Bool.and(F32.is_lt(236.0, y),
    Bool.and(F32.is_lt(F32.sub(pad, 4.0), x), F32.is_lt(x, F32.add(pad, 40.0)))))

# what a step decided: positions before clamping, the velocities and
# whether each flips, the brick hit, and whether the ball was lost
type Sense is Data:
  Sense{pad: F32, x: F32, y: F32, vx: F32, vy: F32, fx: Bool, fy: Bool, h: Hit, lives: Nat, lost: Bool, score: Nat}

def sense.go(p: F32, +x1: F32, +y1: F32, vx: F32, vy: F32, h: Hit, lives: Nat, score: Nat, +bounce: Bool, +lost: Bool, +smashed: Bool) -> Sense:
  Sense{p, Bool.pick(F32, lost, 126.0, x1), Bool.pick(F32, lost, 128.0, Bool.pick(F32, bounce, 236.0, y1)),
    vx, vy, outside(x1, 0.0, 252.0), Bool.or(Bool.or(F32.is_lt(y1, 0.0), smashed), Bool.or(bounce, lost)), h, lives, lost, score}

def sense(g: Game, aim: F32) -> Sense:
  match g:
    case Game{pad, +bx, +by, +vx, +vy, bricks, lives, score}:
      +p = F32.clamp(F32.sub(aim, 20.0), 0.0, 216.0)
      +x1 = F32.add(bx, vx)
      +y1 = F32.add(by, vy)
      +bounce = on_pad(y1, vy, x1, p)
      +h = hit(bricks, bx, by)
      sense.go(p, x1, y1, vx, vy, h, lives, score, bounce, Bool.and(F32.is_lt(252.0, y1), Bool.not(bounce)), Hit.smashed(h))

def act(s: Sense) -> Game:
  match s:
    case Sense{p, x, y, vx, vy, fx, fy, +h, +lives, +lost, score}:
      Game{F32.clamp(p, 0.0, 216.0), F32.clamp(x, 0.0, 252.0), F32.clamp(y, 0.0, 252.0),
        turn(fx, vx), turn(fy, vy), Hit.bricks(h), Bool.pick(Nat, lost, Nat.sub(lives, 1n), lives),
        Nat.add(Hit.points(h), score)}

def step(g: Game, aim: F32) -> Game:
  act(sense(g, aim))

def init() -> Game:
  Game{108.0, 126.0, 128.0, 2.5, 1.75, List.replicate(Bool, 32n, True{}), 3n, 0n}

# Arena
# -----

def Arena(g: Game) -> Type:
  match g:
    case Game{pad, bx, by, vx, vy, bricks, lives, score}:
      F32.LE(0.0, pad) & F32.LE(pad, 216.0) & F32.LE(0.0, bx) & F32.LE(bx, 252.0) & F32.LE(0.0, by) & F32.LE(by, 252.0)

law arena_act:
  for ~lt: F32.LtOk()
  for s: Sense
  Arena(act(s))

def arena_act(lt, s):
  match s:
    case Sense{+p, +x, +y, vx, vy, fx, fy, h, lives, lost, score}:
      (F32.lo_le_clamp(~lt, p, 0.0, 216.0, Unit{}), F32.clamp_le_hi(~lt, p, 0.0, 216.0, Unit{}),
       F32.lo_le_clamp(~lt, x, 0.0, 252.0, Unit{}), F32.clamp_le_hi(~lt, x, 0.0, 252.0, Unit{}),
       F32.lo_le_clamp(~lt, y, 0.0, 252.0, Unit{}), F32.clamp_le_hi(~lt, y, 0.0, 252.0, Unit{}))

# one step lands in the arena from any state
def arena_step(~lt: F32.LtOk(), g: Game, aim: F32, k: Arena(g)) -> Arena(step(g, aim)):
  arena_act(~lt, sense(g, aim))

# every input list keeps the game in the arena
law arena_run:
  for ~lt: F32.LtOk()
  for xs: List<&2, F32>
  Arena(M.run(~Game, ~F32, ~step, init(), xs))

def arena_run(lt, xs):
  M.run_inv(~Game, ~F32, ~step, ~Arena, ~arena_step(~lt), xs, init())((Unit{}, Unit{}, Unit{}, Unit{}, Unit{}, Unit{}))

# Speed
# -----

# v has v0's magnitude, and is not NaN
def Same(v: F32, v0: F32) -> Type:
  {F32.mag(v) == F32.mag(v0) : Word(31n)} & F32.IsKey(F32.key(v))

def Speed(g: Game) -> Type:
  match g:
    case Game{pad, bx, by, vx, vy, bricks, lives, score}:
      Same(vx, 2.5) & Same(vy, 1.75)

law flip_mag:
  for ~ng: F32.NegOk()
  for +v: F32
  for -v0: F32
  for e: {F32.mag(v) == F32.mag(v0) : Word(31n)}
  for kv: F32.IsKey(F32.key(v))
  {F32.mag(F32.neg(v)) == F32.mag(v0) : Word(31n)}

def flip_mag(ng, v, v0, e, kv):
  %F32.neg_mag(~ng, v, kv) : {_ == F32.mag(v0) : Word(31n)}
  e

law turn_same.go:
  for ~ng: F32.NegOk()
  for c: Bool
  for +v: F32
  for -v0: F32
  for e: {F32.mag(v) == F32.mag(v0) : Word(31n)}
  for +kv: F32.IsKey(F32.key(v))
  Same(turn(c, v), v0)

def turn_same.go(ng, c, v, v0, e, kv):
  match c:
    case True{}:
      (flip_mag(~ng, v, v0, e, kv), F32.neg_key(~ng, v, kv))
    case False{}:
      (e, kv)

# a bounce keeps the magnitude, and a non-NaN stays non-NaN
law turn_same:
  for ~ng: F32.NegOk()
  for c: Bool
  for +v: F32
  for -v0: F32
  for k: Same(v, v0)
  Same(turn(c, v), v0)

def turn_same(ng, c, v, v0, k):
  (e, kv) = k
  turn_same.go(~ng, c, v, v0, e, kv)

def SenseSpeed(s: Sense) -> Type:
  match s:
    case Sense{p, x, y, vx, vy, fx, fy, h, lives, lost, score}:
      Same(vx, 2.5) & Same(vy, 1.75)

law speed_act.go:
  for ~ng: F32.NegOk()
  for fx: Bool
  for fy: Bool
  for +vx: F32
  for +vy: F32
  for k: Same(vx, 2.5) & Same(vy, 1.75)
  Same(turn(fx, vx), 2.5) & Same(turn(fy, vy), 1.75)

def speed_act.go(ng, fx, fy, vx, vy, k):
  (sx, sy) = k
  (turn_same(~ng, fx, vx, 2.5, sx), turn_same(~ng, fy, vy, 1.75, sy))

law speed_act:
  for ~ng: F32.NegOk()
  for s: Sense
  SenseSpeed(s) -> Speed(act(s))

def speed_act(ng, s):
  match s:
    case Sense{p, x, y, +vx, +vy, fx, fy, h, lives, lost, score}:
      k => speed_act.go(~ng, fx, fy, vx, vy, k)

law speed_sense:
  for g: Game
  for aim: F32
  Speed(g) -> SenseSpeed(sense(g, aim))

def speed_sense(g, aim):
  match g:
    case Game{pad, bx, by, vx, vy, bricks, lives, score}:
      k => k

def speed_step(~ng: F32.NegOk(), g: Game, aim: F32, k: Speed(g)) -> Speed(step(g, aim)):
  +g2 = g
  +a2 = aim
  speed_act(~ng, sense(g2, a2))(speed_sense(g2, a2)(k))

# every input list keeps the ball's speed, bit for bit
law speed_run:
  for ~ng: F32.NegOk()
  for xs: List<&2, F32>
  Speed(M.run(~Game, ~F32, ~step, init(), xs))

def speed_run(ng, xs):
  M.run_inv(~Game, ~F32, ~step, ~Speed, ~speed_step(~ng), xs, init())((({==}, Unit{}), ({==}, Unit{})))

# Score
# -----

def pot(g: Game) -> Nat:
  match g:
    case Game{pad, bx, by, vx, vy, bricks, lives, score}:
      Nat.add(Nat.mul(count(bricks), 10n), score)

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

law pot_hit:
  for +h: Hit
  for +score: Nat
  {Nat.add(Nat.mul(Hit.count(h), 10n), score) == Nat.add(Nat.mul(count(Hit.bricks(h)), 10n), Nat.add(Hit.points(h), score)) : Nat}

def pot_hit(h, score):
  match h:
    case Miss{bs}:
      {==}
    case Smash{+bs}:
      add_ten(Nat.mul(count(bs), 10n), score)

def Sense.pot(s: Sense) -> Nat:
  match s:
    case Sense{p, x, y, vx, vy, fx, fy, h, lives, lost, score}:
      Nat.add(Nat.mul(Hit.count(h), 10n), score)

law pot_act:
  for s: Sense
  {Sense.pot(s) == pot(act(s)) : Nat}

def pot_act(s):
  match s:
    case Sense{p, x, y, vx, vy, fx, fy, +h, lives, lost, +score}:
      pot_hit(h, score)

law pot_sense:
  for g: Game
  for aim: F32
  {pot(g) == Sense.pot(sense(g, aim)) : Nat}

def pot_sense(g, aim):
  match g:
    case Game{pad, +bx, +by, vx, vy, +bricks, lives, +score}:
      Equal.cong(Nat, Nat, n => Nat.add(Nat.mul(n, 10n), score), count(bricks), Hit.count(hit(bricks, bx, by)), hit_count(bricks, bx, by))

# the score and the bricks left trade 10 for 1
def Pot(g: Game) -> Type:
  {pot(init()) == pot(g) : Nat}

def pot_step(g: Game, aim: F32, k: Pot(g)) -> Pot(step(g, aim)):
  +g2 = g
  +a2 = aim
  Equal.trans(Nat, pot(init()), pot(g2), pot(step(g2, a2)), k,
    Equal.trans(Nat, pot(g2), Sense.pot(sense(g2, a2)), pot(act(sense(g2, a2))), pot_sense(g2, a2), pot_act(sense(g2, a2))))

# score + 10 * (bricks alive) is the same after every input list
law pot_run:
  for xs: List<&2, F32>
  Pot(M.run(~Game, ~F32, ~step, init(), xs))

def pot_run(xs):
  M.run_inv(~Game, ~F32, ~step, ~Pot, ~pot_step, xs, init())({==})

# Lives
# -----

def lives_of(g: Game) -> Nat:
  match g:
    case Game{pad, bx, by, vx, vy, bricks, lives, score}:
      lives

def Sense.lives(s: Sense) -> Nat:
  match s:
    case Sense{p, x, y, vx, vy, fx, fy, h, lives, lost, score}:
      lives

law lose:
  for c: Bool
  for +l: Nat
  Nat.LE(Bool.pick(Nat, c, Nat.sub(l, 1n), l), l)

def lose(c, l):
  match c:
    case True{}:
      Nat.sub_le(l, 1n)
    case False{}:
      Nat.le_refl(l)

law lives_act:
  for s: Sense
  Nat.LE(lives_of(act(s)), Sense.lives(s))

def lives_act(s):
  match s:
    case Sense{p, x, y, vx, vy, fx, fy, h, +lives, lost, score}:
      lose(lost, lives)

law lives_sense:
  for g: Game
  for aim: F32
  Nat.LE(Sense.lives(sense(g, aim)), lives_of(g))

def lives_sense(g, aim):
  match g:
    case Game{pad, bx, by, vx, vy, bricks, +lives, score}:
      Nat.le_refl(lives)

law lives_step:
  for +g: Game
  for +aim: F32
  Nat.LE(lives_of(step(g, aim)), lives_of(g))

def lives_step(g, aim):
  Nat.le_trans(lives_of(step(g, aim)), Sense.lives(sense(g, aim)), lives_of(g), lives_act(sense(g, aim)), lives_sense(g, aim))

# lives never increase over any input list
law lives_run:
  for xs: List<&2, F32>
  for +g: Game
  Nat.LE(lives_of(M.run(~Game, ~F32, ~step, g, xs)), lives_of(g))

def lives_run(xs, g):
  match xs:
    case Nil{}:
      Nat.le_refl(lives_of(g))
    case +h <> +t:
      Nat.le_trans(lives_of(M.run(~Game, ~F32, ~step, step(g, h), t)), lives_of(step(g, h)), lives_of(g), lives_run(t, step(g, h)), lives_step(g, h))

# Playing
# -------

# aim the paddle's centre at the ball's
def pilot(g: Game) -> F32:
  match g:
    case Game{pad, bx, by, vx, vy, bricks, lives, score}:
      F32.add(bx, 2.0)

def autoplay(n: Nat, +g: Game) -> Game:
  match n:
    case 0n:
      g
    case 1n+k:
      autoplay(k, step(g, pilot(g)))

def show(g: Game) -> String:
  match g:
    case Game{pad, bx, by, vx, vy, bricks, lives, score}:
      "score=" ++ Nat.show(score) ++ " bricks=" ++ Nat.show(count(bricks)) ++ " lives=" ++ Nat.show(lives) ++ " pad=" ++ Nat.show(F32.to_nat(pad)) ++ " ball=" ++ Nat.show(F32.to_nat(bx)) ++ "," ++ Nat.show(F32.to_nat(by))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("pilot " ++ show(autoplay(4000n, init())))
    IO.print("idle  " ++ show(M.run(~Game, ~F32, ~step, init(), List.replicate(F32, 400n, 0.0))))
    IO.print("nan   " ++ show(M.run(~Game, ~F32, ~step, init(), List.replicate(F32, 400n, F32.div(0.0, 0.0)))))

#|pilot score=290 bricks=3 lives=3 pad=4 ball=25,68
#|idle  score=20 bricks=30 lives=1 pad=0 ball=227,226
#|nan   score=20 bricks=30 lives=2 pad=216 ball=142,149
