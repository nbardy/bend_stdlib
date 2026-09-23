import Base

# list.bend: laws about Base's List.append and List.reverse, for any Data
# element.
#
#   import ./list.bend as List
#
# Equations put the side a caller rewrites away on the right.

# One step of reading a sequence: nothing left, or an element and the rest.
# The quantity a is the rest's: &2 for a list, &1 for a linear queue.
type Step<a, -A: Data, -S: Kind(a)> is Kind(a):
  Stop{}
  Next{x: A, rest: S}

def uncons(-A: Data, xs: List<&2, A>) -> Step<&2, A, List<&2, A>>:
  match xs:
    case Nil{}:
      Stop{}
    case h <> t:
      Next{h, t}

law append_nil:
  for -A: Data
  for xs: List<&2, A>
  {xs == List.append(&2, A, xs, Nil{}) : List<&2, A>}

def append_nil(A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_nil(A, t) : {h <> t == h <> _ : List<&2, A>}
      {==}

law append_assoc:
  for -A: Data
  for a: List<&2, A>
  for -b: List<&2, A>
  for -c: List<&2, A>
  {List.append(&2, A, a, List.append(&2, A, b, c)) == List.append(&2, A, List.append(&2, A, a, b), c) : List<&2, A>}

def append_assoc(A, a, b, c):
  match a:
    case Nil{}:
      {==}
    case h <> t:
      %append_assoc(A, t, b, c) : {h <> List.append(&2, A, t, List.append(&2, A, b, c)) == h <> _ : List<&2, A>}
      {==}

# List.reverse is List.reverse.go(xs, Nil{}); this says what the
# accumulator does.
law reverse_go:
  for -A: Data
  for +xs: List<&2, A>
  for +acc: List<&2, A>
  {List.append(&2, A, List.reverse(&2, A, xs), acc) == List.reverse.go(&2, A, xs, acc) : List<&2, A>}

def reverse_go(A, xs, acc):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      -g = List.append(&2, A, List.reverse(&2, A, h <> t), acc)
      %reverse_go(A, t, h <> acc) : {g == _ : List<&2, A>}
      %reverse_go(A, t, [h]) : {List.append(&2, A, _, acc) == List.append(&2, A, List.reverse(&2, A, t), h <> acc) : List<&2, A>}
      Equal.sym(List<&2, A>,
        List.append(&2, A, List.reverse(&2, A, t), List.append(&2, A, [h], acc)),
        List.append(&2, A, List.append(&2, A, List.reverse(&2, A, t), [h]), acc),
        append_assoc(A, List.reverse(&2, A, t), [h], acc))
