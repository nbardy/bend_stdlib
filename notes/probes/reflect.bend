# Probe for notes/float_system.md, layer 7: reflection is free.
# The syntax instance of a template program evaluates to its F32
# instance for every input, by {==}. Checked on Bend 2.0.20 and 2.0.25.
import Base

# a leapfrog-style step written once over any number type (x + h*(v + (h/2)*(3 - x)))
def step(~A: Data, ~add: A -> A -> A, ~sub: A -> A -> A, ~mul: A -> A -> A, ~h: A, ~h2: A, ~three: A, +x: A, v: A) -> A:
  add(x, mul(h, add(v, mul(h2, sub(three, x)))))

# expressions over two variables
type Expr is Data:
  X{}
  V{}
  K{c: F32}
  Add{a: Expr, b: Expr}
  Sub{a: Expr, b: Expr}
  Mul{a: Expr, b: Expr}

def eadd(a: Expr, b: Expr) -> Expr:
  Add{a, b}
def esub(a: Expr, b: Expr) -> Expr:
  Sub{a, b}
def emul(a: Expr, b: Expr) -> Expr:
  Mul{a, b}
def kh() -> Expr:
  K{0.03125}
def kh2() -> Expr:
  K{0.015625}
def k3() -> Expr:
  K{3.0}

def eval(e: Expr, +x: F32, +v: F32) -> F32:
  match e:
    case X{}:
      x
    case V{}:
      v
    case K{c}:
      c
    case Add{a, b}:
      F32.add(eval(a, x, v), eval(b, x, v))
    case Sub{a, b}:
      F32.sub(eval(a, x, v), eval(b, x, v))
    case Mul{a, b}:
      F32.mul(eval(a, x, v), eval(b, x, v))

def fh() -> F32:
  0.03125
def fh2() -> F32:
  0.015625
def f3() -> F32:
  3.0

# the tree built by the syntax instance evaluates to the float instance, for every x, v
law reflect:
  for +x: F32
  for +v: F32
  {eval(step(~Expr, ~eadd, ~esub, ~emul, ~kh(), ~kh2(), ~k3(), X{}, V{}), x, v) == step(~F32, ~F32.add, ~F32.sub, ~F32.mul, ~fh(), ~fh2(), ~f3(), x, v) : F32}

def reflect(x, v):
  {==}
