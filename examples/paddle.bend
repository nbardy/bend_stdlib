import Base
import ../src/u32.bend as U32
import ../src/machine.bend as M

# paddle.bend: a game state machine and an invariant that holds after
# every input sequence. The game-specific proof is keep: one step keeps
# the paddle on the field. M.run_inv extends it to every run.

type Game is Data:
  Game{paddle: U32, score: U32}

type Input is Data:
  Left{}
  Right{}
  Hit{}

def step(g: Game, i: Input) -> Game:
  match g i:
    case Game{p, s} Left{}:
      Game{U32.clamp(U32.sub(p, 8), 20, 236), s}
    case Game{p, s} Right{}:
      Game{U32.clamp(U32.add(p, 8), 20, 236), s}
    case Game{p, s} Hit{}:
      Game{p, U32.add(s, 1)}

# the paddle is on the field
def OnField(g: Game) -> Type:
  match g:
    case Game{p, s}:
      U32.LE(20, p) & U32.LE(p, 236)

def keep(g: Game, i: Input) -> OnField(g) -> OnField(step(g, i)):
  match g i:
    case Game{+p, s} Left{}:
      k => (U32.lo_le_clamp(U32.sub(p, 8), 20, 236, Unit{}), U32.clamp_le_hi(U32.sub(p, 8), 20, 236))
    case Game{+p, s} Right{}:
      k => (U32.lo_le_clamp(U32.add(p, 8), 20, 236, Unit{}), U32.clamp_le_hi(U32.add(p, 8), 20, 236))
    case Game{p, s} Hit{}:
      k => k

# from any state on the field, every input sequence stays on it
law always_on_field:
  for +g: Game
  for inputs: List<&2, Input>
  OnField(g) -> OnField(M.run(~Game, ~Input, ~step, g, inputs))

def always_on_field(g, inputs):
  M.run_inv(~Game, ~Input, ~step, ~OnField, ~keep, inputs, g)

def show(g: Game) -> String:
  match g:
    case Game{p, s}:
      "paddle=" ++ U32.show(p) ++ " score=" ++ U32.show(s)

def main() -> IO(Unit):
  +g0 = {Game{128, 0} : Game}
  do IO<Unit>:
    IO.print(show(M.run(~Game, ~Input, ~step, g0, List.replicate(Input, 30n, Left{}))))
    IO.print(show(M.run(~Game, ~Input, ~step, g0, List.replicate(Input, 30n, Right{}))))
    IO.print(show(M.run(~Game, ~Input, ~step, g0, [Left{}, Hit{}, Right{}, Right{}, Hit{}])))

#|paddle=20 score=0
#|paddle=236 score=0
#|paddle=136 score=2
