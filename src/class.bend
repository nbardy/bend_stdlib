import Base

# class.bend: operations bundled with their laws, passed as one template
# argument.
#
#   import ./class.bend as C
#   Sorted.sort(~Nat, ~Nat.ord(), xs)
#
# A generic def or law takes ~d: C.Ord<A> (or Semigroup, Group) and reads
# it through the accessors below; a match on ~d inside generic code
# cannot be typed. Instances live with their types (Nat.ord(),
# U32.group()).

# a total order: a relation and a decision that returns the side that holds
type Ord<-A: Data> is Type:
  Ord{R: A -> A -> Type, dec: @x: A -> @y: A -> Or(R(x, y), R(y, x))}

def Ord.R(-A: Data, d: Ord<A>, x: A, y: A) -> Type:
  match d:
    case Ord{R, dec}:
      R(x, y)

def Ord.dec(-A: Data, d: Ord<A>, x: A, y: A) -> Or(Ord.R(A, d, x, y), Ord.R(A, d, y, x)):
  match d:
    case Ord{R, dec}:
      dec(x, y)

# an associative operation
type Semigroup<-A: Data> is Type:
  Semigroup{op: A -> A -> A, assoc: @x: A -> @y: A -> @z: A -> {op(x, op(y, z)) == op(op(x, y), z) : A}}

def Semigroup.op(-A: Data, d: Semigroup<A>, x: A, y: A) -> A:
  match d:
    case Semigroup{op, assoc}:
      op(x, y)

# op as a template function, for Base's templates (List.foldr, List.foldl)
def Semigroup.fn(~A: Data, ~d: Semigroup<A>, x: A, y: A) -> A:
  Semigroup.op(A, d, x, y)

def Semigroup.assoc(-A: Data, d: Semigroup<A>, x: A, y: A, z: A) -> {Semigroup.op(A, d, x, Semigroup.op(A, d, y, z)) == Semigroup.op(A, d, Semigroup.op(A, d, x, y), z) : A}:
  match d:
    case Semigroup{op, assoc}:
      assoc(x, y, z)

# addition and subtraction that undo each other (wrapping integers)
type Group<-A: Data> is Type:
  Group{add: A -> A -> A, sub: A -> A -> A,
    sub_add: @a: A -> @b: A -> {a == sub(add(a, b), b) : A},
    add_sub: @a: A -> @b: A -> {a == add(sub(a, b), b) : A}}

def Group.add(-A: Data, d: Group<A>, a: A, b: A) -> A:
  match d:
    case Group{add, sub, sub_add, add_sub}:
      add(a, b)

def Group.sub(-A: Data, d: Group<A>, a: A, b: A) -> A:
  match d:
    case Group{add, sub, sub_add, add_sub}:
      sub(a, b)

def Group.sub_add(-A: Data, d: Group<A>, a: A, b: A) -> {a == Group.sub(A, d, Group.add(A, d, a, b), b) : A}:
  match d:
    case Group{add, sub, sub_add, add_sub}:
      sub_add(a, b)

def Group.add_sub(-A: Data, d: Group<A>, a: A, b: A) -> {a == Group.add(A, d, Group.sub(A, d, a, b), b) : A}:
  match d:
    case Group{add, sub, sub_add, add_sub}:
      add_sub(a, b)
