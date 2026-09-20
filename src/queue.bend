import Base
import ./order.bend as O

# Persistent banker's queue (two-list): push conses onto rear,
# pop takes from front, rotating rear when front runs dry.
#
# FOUND CONSTRAINT (not a style choice): the classic pop is not
# structurally recursive — the rotation target qrev(r) is a
# computed value, and the three-way mutual recursion it implies
# is banned. So pop takes Nat fuel (same shape as Base's
# List.sort.go): fuel 0 answers None; 1+len(r) always suffices.
# Laws below specify pop totally by equations instead.

type Queue is Data:
  Q{front: List<&2, Nat>, rear: List<&2, Nat>}

def qrev(xs: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      qrev(t, h <> acc)

def qlen(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      1n+qlen(t)

def qapp(xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      ys
    case h <> t:
      h <> qapp(t, ys)

def qlen_total(q: Queue) -> Nat:
  match q:
    case Q{front, rear}:
      Nat.add(qlen(front), qlen(rear))

def to_list(q: Queue) -> List<&2, Nat>:
  match q:
    case Q{front, rear}:
      qapp(front, qrev(rear, Nil{}))

def empty() -> Queue:
  Q{Nil{}, Nil{}}

def push(q: Queue, x: Nat) -> Queue:
  match q:
    case Q{front, rear}:
      Q{front, x <> rear}

def pop(fuel: Nat, q: Queue) -> Queue & Maybe<Nat>:
  match fuel:
    case 0n:
      (q, None{})
    case 1n+pfuel:
      match q:
        case Q{front, rear}:
          match front:
            case h <> t:
              (Q{t, rear}, Some{h})
            case Nil{}:
              match rear:
                case Nil{}:
                  (Q{Nil{}, Nil{}}, None{})
                case h2 <> t2:
                  pop(pfuel, Q{qrev(h2 <> t2, Nil{}), Nil{}})

# Append associativity: the composition everything else stands on.
law qapp_assoc:
  for a: List<&2, Nat>
  for b: List<&2, Nat>
  for c: List<&2, Nat>
  {qapp(qapp(a, b), c) == qapp(a, qapp(b, c)) : List<&2, Nat>}

def qapp_assoc(a, b, c):
  match a:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => h <> z, qapp(qapp(t, b), c), qapp(t, qapp(b, c)), qapp_assoc(t, b, c))

# Reverse-with-accumulator is append of reversed-then-accumulator.
# Triple use (t, h, acc) forces + binders — same affine shape as
# max_bridge, same Data justification.
law qrev_acc:
  for r: List<&2, Nat>
  for +acc: List<&2, Nat>
  {qrev(r, acc) == qapp(qrev(r, Nil{}), acc) : List<&2, Nat>}

def qrev_acc(r, acc):
  match r:
    case Nil{}:
      {==}
    case +h <> +t:
      Equal.trans(List<&2, Nat>,
        qrev(t, h <> acc),
        qapp(qrev(t, Nil{}), h <> acc),
        qapp(qrev(t, h <> Nil{}), acc),
        qrev_acc(t, h <> acc),
        Equal.trans(List<&2, Nat>,
          qapp(qrev(t, Nil{}), h <> acc),
          qapp(qapp(qrev(t, Nil{}), h <> Nil{}), acc),
          qapp(qrev(t, h <> Nil{}), acc),
          Equal.sym(List<&2, Nat>, qapp(qapp(qrev(t, Nil{}), h <> Nil{}), acc), qapp(qrev(t, Nil{}), h <> acc), qapp_assoc(qrev(t, Nil{}), h <> Nil{}, acc)),
          Equal.sym(List<&2, Nat>, qapp(qrev(t, h <> Nil{}), acc), qapp(qapp(qrev(t, Nil{}), h <> Nil{}), acc), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => qapp(z, acc), qrev(t, h <> Nil{}), qapp(qrev(t, Nil{}), h <> Nil{}), qrev_acc(t, h <> Nil{})))))

# Length respects push (via order's add_succ — cross-module reuse).
law len_push:
  for q: Queue
  for x: Nat
  {qlen_total(push(q, x)) == 1n+qlen_total(q) : Nat}

def len_push(q, x):
  match q:
    case Q{front, rear}:
      O.add_succ(qlen(front), qlen(rear))

# Model law: push snocs the logical list.
law to_list_push:
  for q: Queue
  for +x: Nat
  {to_list(push(q, x)) == qapp(to_list(q), x <> Nil{}) : List<&2, Nat>}

def to_list_push(q, x):
  match q:
    case Q{+front, +rear}:
      Equal.trans(List<&2, Nat>,
        qapp(front, qrev(rear, x <> Nil{})),
        qapp(front, qapp(qrev(rear, Nil{}), x <> Nil{})),
        qapp(qapp(front, qrev(rear, Nil{})), x <> Nil{}),
        Equal.cong(List<&2, Nat>, List<&2, Nat>, z => qapp(front, z), qrev(rear, x <> Nil{}), qapp(qrev(rear, Nil{}), x <> Nil{}), qrev_acc(rear, x <> Nil{})),
        Equal.sym(List<&2, Nat>, qapp(qapp(front, qrev(rear, Nil{})), x <> Nil{}), qapp(front, qapp(qrev(rear, Nil{}), x <> Nil{})), qapp_assoc(front, qrev(rear, Nil{}), x <> Nil{})))

# Pop dispatch, fully specified by equations.
law pop_cons:
  for fuel: Nat
  for h: Nat
  for t: List<&2, Nat>
  for r: List<&2, Nat>
  {pop(1n+fuel, Q{h <> t, r}) == (Q{t, r}, Some{h}) : Queue & Maybe<Nat>}

def pop_cons(fuel, h, t, r):
  {==}

law pop_rotate:
  for f: Nat
  for h2: Nat
  for t2: List<&2, Nat>
  {pop(1n+f, Q{Nil{}, h2 <> t2}) == pop(f, Q{qrev(h2 <> t2, Nil{}), Nil{}}) : Queue & Maybe<Nat>}

def pop_rotate(f, h2, t2):
  {==}

law pop_empty:
  for fuel: Nat
  {pop(fuel, empty()) == (empty(), None{}) : Queue & Maybe<Nat>}

def pop_empty(fuel):
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      {==}

def main() -> List<&2, Nat>:
  to_list(push(push(empty(), 1n), 2n))
