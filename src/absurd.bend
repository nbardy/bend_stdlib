import Base

# Absurdity lemmas: turn contradictory hypotheses into anything.
# Prerequisite for every impossible arm in order-theoretic proofs
# (compose audit T5b). Motive direction is the trap: IsFalse works,
# IsTrue does not — see below.

def Bool.IsFalse(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

law bool_absurd:
  for -A: Type
  for e: {False{} == True{} : Bool}
  A

def bool_absurd(A, e):
  Empty.absurd(A, %e : Bool.IsFalse(_); Unit{})

# Cmp discrimination: each pair of positive views on one Cmp value.
# Per arm, exactly one hypothesis reduces to {False == True}.
law cmp_absurd_lt_eq:
  for -A: Type
  for c: Cmp
  for h1: {Cmp.is_lt(c) == True{} : Bool}
  for h2: {Cmp.is_eq(c) == True{} : Bool}
  A

def cmp_absurd_lt_eq(A, c, h1, h2):
  match c:
    case LT{}:
      bool_absurd(A, h2)
    case EQ{}:
      bool_absurd(A, h1)
    case GT{}:
      bool_absurd(A, h1)

law cmp_absurd_lt_gt:
  for -A: Type
  for c: Cmp
  for h1: {Cmp.is_lt(c) == True{} : Bool}
  for h2: {Cmp.is_gt(c) == True{} : Bool}
  A

def cmp_absurd_lt_gt(A, c, h1, h2):
  match c:
    case LT{}:
      bool_absurd(A, h2)
    case EQ{}:
      bool_absurd(A, h1)
    case GT{}:
      bool_absurd(A, h1)

law cmp_absurd_eq_gt:
  for -A: Type
  for c: Cmp
  for h1: {Cmp.is_eq(c) == True{} : Bool}
  for h2: {Cmp.is_gt(c) == True{} : Bool}
  A

def cmp_absurd_eq_gt(A, c, h1, h2):
  match c:
    case LT{}:
      bool_absurd(A, h1)
    case EQ{}:
      bool_absurd(A, h2)
    case GT{}:
      bool_absurd(A, h1)

# Nat discrimination: zero never equals a successor.
def Nat.IsZero(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

law nat_absurd_zero_succ:
  for -A: Type
  for x: Nat
  for e: {0n == 1n+x : Nat}
  A

def nat_absurd_zero_succ(A, x, e):
  Empty.absurd(A, %e : Nat.IsZero(_); Unit{})

def main() -> Nat:
  0n
