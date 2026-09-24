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

# a - k <= a (Nat.sub stops at 0)
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

law add_zero_r:
  for a: Nat
  {a == Nat.add(a, 0n) : Nat}

def add_zero_r(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero_r(p) : {1n+p == 1n+_ : Nat}
      {==}

law add_succ_r:
  for a: Nat
  for b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def add_succ_r(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ_r(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

law add_comm:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

def add_comm(a, b):
  match a:
    case 0n:
      add_zero_r(b)
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add_succ_r(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

law double_add:
  for a: Nat
  for +b: Nat
  {Nat.add(Nat.double(a), Nat.double(b)) == Nat.double(Nat.add(a, b)) : Nat}

def double_add(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %double_add(p, b) : {2n+Nat.add(Nat.double(p), Nat.double(b)) == 2n+_ : Nat}
      {==}

law le_add_r:
  for a: Nat
  for -b: Nat
  LE(a, Nat.add(a, b))

def le_add_r(a, b):
  match a:
    case 0n:
      Unit{}
    case 1n+p:
      le_add_r(p, b)

law le_add_l:
  for a: Nat
  for +b: Nat
  LE(b, Nat.add(a, b))

def le_add_l(a, b):
  match a:
    case 0n:
      le_refl(b)
    case 1n++p:
      le_trans(b, Nat.add(p, b), 1n+Nat.add(p, b), le_add_l(p, b), le_step(Nat.add(p, b)))

# adding the same number on the left keeps an order
law add_mono_l:
  for a: Nat
  for b: Nat
  for c: Nat
  for h: LE(b, c)
  LE(Nat.add(a, b), Nat.add(a, c))

def add_mono_l(a, b, c, h):
  match a:
    case 0n:
      h
    case 1n+p:
      add_mono_l(p, b, c, h)

# adding the same number on the right keeps an order
law add_mono_r:
  for a: Nat
  for b: Nat
  for +c: Nat
  for h: LE(a, b)
  LE(Nat.add(a, c), Nat.add(b, c))

def add_mono_r(a, b, c, h):
  match a b:
    case 0n y:
      le_add_l(y, c)
    case 1n+x 0n:
      match h:
    case 1n+x 1n+y:
      add_mono_r(x, y, c, h)

law double_mono:
  for a: Nat
  for b: Nat
  for h: LE(a, b)
  LE(Nat.double(a), Nat.double(b))

def double_mono(a, b, h):
  match a b:
    case 0n y:
      Unit{}
    case 1n+x 0n:
      match h:
    case 1n+x 1n+y:
      double_mono(x, y, h)

law le_double:
  for a: Nat
  LE(a, Nat.double(a))

def le_double(a):
  match a:
    case 0n:
      Unit{}
    case 1n++p:
      le_trans(p, Nat.double(p), 1n+Nat.double(p), le_double(p), le_step(Nat.double(p)))

law double_is_add:
  for +a: Nat
  {Nat.add(a, a) == Nat.double(a) : Nat}

def double_is_add(a):
  match a:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), add_succ_r(p, p)) : {1n+_ == Nat.double(1n+p) : Nat}
      %double_is_add(p) : {2n+Nat.add(p, p) == 2n+_ : Nat}
      {==}

law add_swap:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}

def add_swap(a, b, c):
  %Equal.sym(Nat, Nat.add(b, Nat.add(a, c)), Nat.add(Nat.add(b, a), c), add_assoc(b, a, c)) : {Nat.add(a, Nat.add(b, c)) == _ : Nat}
  %Equal.sym(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), add_assoc(a, b, c)) : {_ == Nat.add(Nat.add(b, a), c) : Nat}
  %add_comm(a, b) : {Nat.add(Nat.add(a, b), c) == Nat.add(_, c) : Nat}
  {==}

law add_right_comm:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}

def add_right_comm(a, b, c):
  %add_assoc(a, b, c) : {_ == Nat.add(Nat.add(a, c), b) : Nat}
  %add_assoc(a, c, b) : {Nat.add(a, Nat.add(b, c)) == _ : Nat}
  %add_comm(b, c) : {Nat.add(a, Nat.add(b, c)) == Nat.add(a, _) : Nat}
  {==}

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
