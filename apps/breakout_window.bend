import Base
import ./breakout.bend as B

# breakout_window.bend: play apps/breakout.bend in a window with the mouse.
# The paddle's centre follows the mouse's x; closing the window or losing
# the last life ends the game.

type Play is Data:
  Play{g: B.Game, aim: F32}

def within(+x: Nat, +lo: Nat, +w: Nat) -> Bool:
  Bool.and(Nat.is_ge(x, lo), Nat.is_lt(x, Nat.add(lo, w)))

def brick_color(row: Nat) -> U32:
  match row:
    case 0n:
      15548997
    case 1n:
      16753920
    case 2n:
      16776960
    case _:
      5025616

def brick_px(alive: Maybe<&2, Bool>, row: Nat) -> U32:
  match alive:
    case Some{True{}}:
      brick_color(row)
    case Some{False{}}:
      1052688
    case None{}:
      1052688

def zone_px(z: Bool, bricks: List<&2, Bool>, +x: Nat, +y: Nat) -> U32:
  match z:
    case True{}:
      brick_px(List.get(&2, Bool, bricks, B.brick_at(x, y)), Nat.div(Nat.sub(y, 16n), 8n))
    case False{}:
      1052688

def paddle_px(on: Bool, bricks: List<&2, Bool>, +x: Nat, +y: Nat) -> U32:
  match on:
    case True{}:
      65535
    case False{}:
      zone_px(B.in_rows(y), bricks, x, y)

def ball_px(on: Bool, +pad: Nat, bricks: List<&2, Bool>, +x: Nat, +y: Nat) -> U32:
  match on:
    case True{}:
      16777215
    case False{}:
      paddle_px(Bool.and(within(x, pad, 40n), within(y, 240n, 4n)), bricks, x, y)

def color(g: B.Game, +x: Nat, +y: Nat) -> U32:
  match g:
    case B.Game{pad, bx, by, vx, vy, bricks, lives, score}:
      ball_px(Bool.and(within(x, F32.to_nat(bx), 4n), within(y, F32.to_nat(by), 4n)), F32.to_nat(pad), bricks, x, y)

# a quadtree of 2x2-pixel leaves over the square at (x, y) of side 2^(d+1)
def frame(+g: B.Game, +d: Nat, +x: Nat, +y: Nat) -> Image:
  match d:
    case 0n:
      Pix{color(g, x, y)}
    case 1n+k:
      +h = Nat.pow(2n, d)
      a b c e = frame(g, k, x, y) frame(g, k, Nat.add(x, h), y) frame(g, k, x, Nat.add(y, h)) frame(g, k, Nat.add(x, h), Nat.add(y, h))
      Qua{a, b, c, e}

def view(p: Play) -> Pair(Play, Image):
  match p:
    case Play{+g, aim}:
      (Play{g, aim}, frame(g, 7n, 0n, 0n))

def advance(g: B.Game, +aim: F32) -> Play:
  Play{B.step(g, aim), aim}

def alive(p: Play, dead: Bool) -> IO(Maybe<Play>):
  match dead:
    case True{}:
      IO.pure(Maybe<Play>, None{})
    case False{}:
      IO.pure(Maybe<Play>, Some{p})

def finish(p: Play) -> IO(Maybe<Play>):
  match p:
    case Play{+g, aim}:
      alive(Play{g, aim}, Nat.is_eq(B.lives_of(g), 0n))

def tick(events: List<Event>, p: Play) -> IO(Maybe<Play>):
  match events:
    case Nil{}:
      match p:
        case Play{g, aim}:
          finish(advance(g, aim))
    case Con{Close{}, rest}:
      IO.pure(Maybe<Play>, None{})
    case Con{Move{x, y}, rest}:
      match p:
        case Play{g, aim}:
          tick(rest, Play{g, U32.to_f32(x)})
    case Con{e, rest}:
      tick(rest, p)

def main() -> IO(Unit):
  App.run(~Play, ~App{view, tick}, "Breakout", 256, 256, Play{B.init(), 128.0})
