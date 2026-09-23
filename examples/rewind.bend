import Base
import ../src/u32.bend as U32
import ../src/v2.bend as V2
import ../src/sim.bend as Sim

# rewind.bend: a 2D body under gravity and a position-dependent wind, run
# forward and rewound to the exact starting state. rewind_all holds for
# every start state and step count; main runs 100000 steps.

# gravity pulls y down by 1; the wind pushes x by (y / 1024) mod 4
def force(p: V2.V2) -> V2.V2:
  match p:
    case V2.V2{x, y}:
      V2.V2{U32.and(U32.shrn(y, 10n), 3), U32.sub(0, 1)}

law rewind_all:
  for +n: Nat
  for +s: Sim.State<V2.V2>
  {s == Sim.rewind(~V2.V2, ~V2.group(), ~force, n, Sim.run(~V2.V2, ~V2.group(), ~force, n, s)) : Sim.State<V2.V2>}

def rewind_all(n, s):
  Sim.rewind_run(~V2.V2, ~V2.group(), ~force, n, s)

def show(s: Sim.State<V2.V2>) -> String:
  match s:
    case Sim.State{V2.V2{x, y}, V2.V2{vx, vy}}:
      "x=" ++ U32.show(x) ++ " y=" ++ U32.show(y) ++ " vx=" ++ U32.show(vx) ++ " vy=" ++ U32.show(vy)

def main() -> IO(Unit):
  +s0 = {Sim.State{V2.V2{10, 5000000}, V2.V2{3, 200}} : Sim.State<V2.V2>}
  +s1 = Sim.run(~V2.V2, ~V2.group(), ~force, 100000n, s0)
  do IO<Unit>:
    IO.print("start  " ++ show(s0))
    IO.print("run    " ++ show(s1))
    IO.print("rewind " ++ show(Sim.rewind(~V2.V2, ~V2.group(), ~force, 100000n, s1)))

#|start  x=10 y=5000000 vx=3 vy=200
#|run    x=3204708888 y=3614884592 vx=150013 vy=4294867496
#|rewind x=10 y=5000000 vx=3 vy=200
