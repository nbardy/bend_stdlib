import Base
import ./class.bend as C

# nat.bend: Nat arithmetic and order laws.
#
#   import ./nat.bend as Nat
#   Nat.ord(), Nat.add_sg()      # instances for class.bend
#
# Equations put the side a caller rewrites away on the right: `%e : P`
# replaces e's right side in the goal with its left side.

# plain binders, so it fits C.Semigroup's assoc field
law add_assoc:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}

def add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

# a <= b, as a type: Unit when it holds, Empty when it does not.
def LE(a: Nat, b: Nat) -> Data:
  match a b:
    case 0n y:
      Unit
    case 1n+x 0n:
      Empty
    case 1n+x 1n+y:
      LE(x, y)

# a < b. LT(i, 0n) computes to Empty.
def LT(a: Nat, b: Nat) -> Data:
  LE(1n+a, b)

law le_refl:
  for a: Nat
  LE(a, a)

def le_refl(a):
  match a:
    case 0n:
      Unit{}
    case 1n+p:
      le_refl(p)

# Compares a and b and returns the proof of the side that holds.
def le_case(a: Nat, b: Nat) -> Or(LE(a, b), LE(b, a)):
  match a b:
    case 0n y:
      Inl{Unit{}}
    case 1n+x 0n:
      Inr{Unit{}}
    case 1n+x 1n+y:
      le_case(x, y)

# Motives that refute {False{} == True{}} and {True{} == False{}}.
law IsFalse:
  for c: Bool
  Type

def IsFalse(c):
  match c:
    case False{}:
      Unit
    case True{}:
      Empty

law IsTrue:
  for c: Bool
  Type

def IsTrue(c):
  match c:
    case True{}:
      Unit
    case False{}:
      Empty

# The two outcomes of Nat.is_lt as LE proofs. Base's min, max and clamp
# branch on is_lt.
law le_of_is_lt:
  for a: Nat
  for b: Nat
  for e: {Nat.is_lt(a, b) == True{} : Bool}
  LE(a, b)

def le_of_is_lt(a, b, e):
  match a b:
    case 0n y:
      Unit{}
    case 1n+x 0n:
      %e : IsFalse(_)
      Unit{}
    case 1n+x 1n+y:
      le_of_is_lt(x, y, e)

law ge_of_not_lt:
  for a: Nat
  for b: Nat
  for e: {Nat.is_lt(a, b) == False{} : Bool}
  LE(b, a)

def ge_of_not_lt(a, b, e):
  match a b:
    case 0n 0n:
      Unit{}
    case 0n 1n+y:
      %e : IsTrue(_)
      Unit{}
    case 1n+x 0n:
      Unit{}
    case 1n+x 1n+y:
      ge_of_not_lt(x, y, e)

# Nat ordered by LE
def ord() -> C.Ord<Nat>:
  C.Ord{LE, le_case}

# Nat under addition
def add_sg() -> C.Semigroup<Nat>:
  C.Semigroup{Nat.add, add_assoc}
