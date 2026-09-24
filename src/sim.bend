import Base
import ./class.bend as C

# sim.bend: integer leapfrog steps that can be undone exactly.
#
#   import ./sim.bend as Sim
#   Sim.run(~V2, ~V2.group(), ~force, n, s)
#
# A state is a position x and a velocity v in a type P whose + and - undo
# each other (a C.Group: U32, or a record of U32s for 2D or 3D). step adds
# the force F(x) to the velocity, then the new velocity to the position;
# back undoes both. The laws hold for every state and every force ~F that
# reads only the position. Wrapping integer + and - are exact inverses,
# so no rounding is involved.
#
# A negative velocity is its two's complement: U32.sub(0, 3) moves 3 back.

type State<-P: Data> is Data:
  State{x: P, v: P}

def step(~P: Data, ~g: C.Group<P>, ~F: P -> P, s: State<P>) -> State<P>:
  match s:
    case State{+x, v}:
      +w = C.Group.add(P, g, v, F(x))
      State{C.Group.add(P, g, x, w), w}

def back(~P: Data, ~g: C.Group<P>, ~F: P -> P, s: State<P>) -> State<P>:
  match s:
    case State{x, +w}:
      +x0 = C.Group.sub(P, g, x, w)
      State{x0, C.Group.sub(P, g, w, F(x0))}

# back undoes step
law back_step:
  for ~P: Data
  for ~g: C.Group<P>
  for ~F: P -> P
  for s: State<P>
  {s == back(~P, ~g, ~F, step(~P, ~g, ~F, s)) : State<P>}

def back_step(P, g, F, s):
  match s:
    case State{+x, +v}:
      +w = C.Group.add(P, g, v, F(x))
      %C.Group.sub_add(P, g, x, w) : {State{x, v} == State{_, C.Group.sub(P, g, w, F(_))} : State<P>}
      %C.Group.sub_add(P, g, v, F(x)) : {State{x, v} == State{x, _} : State<P>}
      {==}

def run(~P: Data, ~g: C.Group<P>, ~F: P -> P, n: Nat, s: State<P>) -> State<P>:
  match n:
    case 0n:
      s
    case 1n+k:
      run(~P, ~g, ~F, k, step(~P, ~g, ~F, s))

def rewind(~P: Data, ~g: C.Group<P>, ~F: P -> P, n: Nat, s: State<P>) -> State<P>:
  match n:
    case 0n:
      s
    case 1n+k:
      rewind(~P, ~g, ~F, k, back(~P, ~g, ~F, s))

# run's last step is its outermost one
law run_step:
  for ~P: Data
  for ~g: C.Group<P>
  for ~F: P -> P
  for k: Nat
  for s: State<P>
  {step(~P, ~g, ~F, run(~P, ~g, ~F, k, s)) == run(~P, ~g, ~F, k, step(~P, ~g, ~F, s)) : State<P>}

def run_step(P, g, F, k, s):
  match k:
    case 0n:
      {==}
    case 1n+j:
      run_step(~P, ~g, ~F, j, step(~P, ~g, ~F, s))

# rewinding n steps undoes running n steps
law rewind_run:
  for ~P: Data
  for ~g: C.Group<P>
  for ~F: P -> P
  for +n: Nat
  for +s: State<P>
  {s == rewind(~P, ~g, ~F, n, run(~P, ~g, ~F, n, s)) : State<P>}

def rewind_run(P, g, F, n, s):
  match n:
    case 0n:
      {==}
    case 1n+k:
      %run_step(~P, ~g, ~F, k, s) : {s == rewind(~P, ~g, ~F, k, back(~P, ~g, ~F, _)) : State<P>}
      %back_step(~P, ~g, ~F, run(~P, ~g, ~F, k, s)) : {s == rewind(~P, ~g, ~F, k, _) : State<P>}
      rewind_run(~P, ~g, ~F, k, s)
