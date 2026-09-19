import Base

# Proof-friendly structural max. Unlike Base's Nat.max
# (Bool.pick over a computed Nat.is_lt), this recurses on
# both args in lockstep with Nat.cmp, so proofs can case on it.
def SMax(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n 0n:
      0n
    case 0n 1n+bp:
      1n+bp
    case 1n+ap 0n:
      1n+ap
    case 1n+ap 1n+bp:
      1n+SMax(ap, bp)

def SMin(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n 0n:
      0n
    case 0n 1n+bp:
      0n
    case 1n+ap 0n:
      0n
    case 1n+ap 1n+bp:
      1n+SMin(ap, bp)

# --- Bool algebra (Opus's and_false, and_comm) ---

law and_false:
  for a: Bool
  {Bool.and(a, False{}) == False{} : Bool}

def and_false(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

law and_comm:
  for a: Bool
  for b: Bool
  {Bool.and(a, b) == Bool.and(b, a) : Bool}

def and_comm(a, b):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# --- Order theory (Opus's cmp_refl) ---

law cmp_refl:
  for a: Nat
  {Nat.cmp(a, a) == EQ{} : Cmp}

def cmp_refl(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      cmp_refl(p)

# --- Arithmetic (Opus's add_succ) ---

law add_succ:
  for a: Nat
  for b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def add_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 1n+b), 1n+Nat.add(p, b), add_succ(p, b))

# --- SMax laws (Base Nat.max is not provable by direct case analysis,
# so prove about the structural twin and transport via max_bridge) ---

law ge_refl:
  for a: Nat
  {Nat.is_ge(a, a) == True{} : Bool}

def ge_refl(a):
  Equal.cong(Cmp, Bool, Cmp.is_ge, Nat.cmp(a, a), EQ{}, cmp_refl(a))

law smax_ge_l:
  for a: Nat
  for b: Nat
  {Nat.is_ge(SMax(a, b), a) == True{} : Bool}

# NOTE: asymmetric arms are correct, not a typo. `0n 1n+bp` closes by
# {==} because cmp(1n+bp, 0n) is GT regardless of bp; `1n+ap 0n`
# needs ge_refl because cmp(ap, ap) is stuck on a variable.
def smax_ge_l(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      ge_refl(1n+ap)
    case 1n+ap 1n+bp:
      smax_ge_l(ap, bp)

law smax_ge_r:
  for a: Nat
  for b: Nat
  {Nat.is_ge(SMax(a, b), b) == True{} : Bool}

def smax_ge_r(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      ge_refl(1n+bp)
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      smax_ge_r(ap, bp)

# Bool.pick commutes with Succ. The helper takes the test as a
# parameter (matchable); callers pass the computed Nat.is_lt.
# NOTE (review finding, blocked): x/y SHOULD be erased (-) since the
# proof only scrutinizes c, but law-proof defs accept bare binders
# only — `-`/`+` prefixes there are a syntax error (same wall as the
# max_bridge `for +` discovery). Revisit if Bend relaxes this.
law pick_succ:
  for c: Bool
  for x: Nat
  for y: Nat
  {Bool.pick(Nat, c, 1n+y, 1n+x) == 1n+Bool.pick(Nat, c, y, x) : Nat}

def pick_succ(c, x, y):
  match c:
    case False{}:
      {==}
    case True{}:
      {==}

# Bridge: structural SMax agrees with Base's Nat.max on all inputs.
# Prove everything about SMax (which unfolds), transport to Nat.max.
# NOTE: law binders are `+a`/`+b` (not plain) because the proof uses
# ap/bp three times per step (IH + computed is_lt + pick_succ args;
# cong/trans/fun-args are erased positions and free). Law-proof defs
# must keep bare binders (`def max_bridge(a, b):` — `+`/`-` there is
# a syntax error), but bare binders inherit reusability from the
# law's `for +` binders.
law max_bridge:
  for +a: Nat
  for +b: Nat
  {SMax(a, b) == Nat.max(a, b) : Nat}

def max_bridge(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      Equal.trans(Nat, 1n+SMax(ap, bp), 1n+Nat.max(ap, bp), Nat.max(1n+ap, 1n+bp),
        Equal.cong(Nat, Nat, x => 1n+x, SMax(ap, bp), Nat.max(ap, bp), max_bridge(ap, bp)),
        Equal.sym(Nat, Bool.pick(Nat, Nat.is_lt(ap, bp), 1n+bp, 1n+ap), 1n+Nat.max(ap, bp),
          pick_succ(Nat.is_lt(ap, bp), ap, bp)))

# Transport: smax_* facts moved across the bridge to Base's Nat.max.
# This consumes max_bridge (dependency rule); ~2 lines per law plus a
# trans, and the reappearing `a` keeps the `for +` binders load-bearing.
law nat_max_ge_l:
  for +a: Nat
  for +b: Nat
  {Nat.is_ge(Nat.max(a, b), a) == True{} : Bool}

def nat_max_ge_l(a, b):
  Equal.trans(Bool, Nat.is_ge(Nat.max(a, b), a), Nat.is_ge(SMax(a, b), a), True{},
    Equal.sym(Bool, Nat.is_ge(SMax(a, b), a), Nat.is_ge(Nat.max(a, b), a),
      Equal.cong(Nat, Bool, m => Nat.is_ge(m, a), SMax(a, b), Nat.max(a, b), max_bridge(a, b))),
    smax_ge_l(a, b))

law nat_max_ge_r:
  for +a: Nat
  for +b: Nat
  {Nat.is_ge(Nat.max(a, b), b) == True{} : Bool}

def nat_max_ge_r(a, b):
  Equal.trans(Bool, Nat.is_ge(Nat.max(a, b), b), Nat.is_ge(SMax(a, b), b), True{},
    Equal.sym(Bool, Nat.is_ge(SMax(a, b), b), Nat.is_ge(Nat.max(a, b), b),
      Equal.cong(Nat, Bool, m => Nat.is_ge(m, b), SMax(a, b), Nat.max(a, b), max_bridge(a, b))),
    smax_ge_r(a, b))

# SMin duals (mirror of the SMax proofs; keeps SMin law-covered).
law smin_le_l:
  for a: Nat
  for b: Nat
  {Nat.is_le(SMin(a, b), a) == True{} : Bool}

def smin_le_l(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      smin_le_l(ap, bp)

law smin_le_r:
  for a: Nat
  for b: Nat
  {Nat.is_le(SMin(a, b), b) == True{} : Bool}

def smin_le_r(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      smin_le_r(ap, bp)

def main() -> Nat:
  SMax(3n, 5n)
