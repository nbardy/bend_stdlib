import Base
import ../src/nat.bend as Nat
import ../src/list.bend as List
import ../src/sorted.bend as Sorted
import ../src/queue.bend as Q
import ../src/tree.bend as Tree
import ../src/vec.bend as Vec
import ../src/class.bend as C

# tour.bend: sorted, queue, tree and vec in use. The laws are checked at
# build time; main prints the lines in the #| block, which gate.sh
# compares.

# sorted.bend's laws at Nat
law nat_sort_sorted:
  for xs: List<&2, Nat>
  Sorted.Sorted(~Nat, ~Nat.ord(), Sorted.sort(~Nat, ~Nat.ord(), xs))

def nat_sort_sorted(xs):
  Sorted.sort_sorted(~Nat, ~Nat.ord(), xs)

law nat_sort_count:
  for +y: Nat
  for xs: List<&2, Nat>
  {Sorted.count(~Nat, ~Nat.is_eq, y, xs) == Sorted.count(~Nat, ~Nat.is_eq, y, Sorted.sort(~Nat, ~Nat.ord(), xs)) : Nat}

def nat_sort_count(y, xs):
  Sorted.sort_count(~Nat, ~Nat.ord(), ~Nat.is_eq, y, xs)

# tree.bend's law at Nat: the parallel sum is the sequential sum. The
# foldr must name the same dictionary: List.foldr over ~Nat.add is a
# different template instance, and the checker does not equate the two.
law psum_is_sum:
  for t: Tree.Tree<Nat>
  {Nat.add(Tree.reduce(~Nat, ~Nat.add_sg(), t), 0n) == List.foldr(~&2, ~Nat, ~Nat, ~C.Semigroup.fn(~Nat, ~Nat.add_sg()), Tree.to_list(Nat, t), 0n) : Nat}

def psum_is_sum(t):
  Tree.reduce_foldr(~Nat, ~Nat.add_sg(), t, Nil{}, 0n)

def id(n: Nat) -> Nat:
  n

def dot(+n: Nat, xs: Vec.Vec(U32, n), ys: Vec.Vec(U32, n)) -> U32:
  Vec.foldr(~U32, ~U32, ~U32.add, n, Vec.zip_with(~U32, ~U32, ~U32, ~U32.mul, n, xs, ys), 0)

def show_nats(xs: List<&2, Nat>) -> String:
  List.show(~&2, ~Nat, ~Nat.show, xs)

def show_step(s: List.Step<&1, Nat, Q.Queue<Nat>>) -> String:
  match s:
    case List.Stop{}:
      "stop"
    case List.Next{x, q}:
      "next " ++ Nat.show(x) ++ ", rest " ++ show_nats(Q.model(Nat, q))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("sort   " ++ show_nats(Sorted.sort(~Nat, ~Nat.ord(), [5n, 3n, 9n, 3n, 0n])))
    IO.print("queue  " ++ show_step(Q.pop(Nat, Q.push(Nat, Q.push(Nat, Q.push(Nat, Q.empty(Nat), 1n), 2n), 3n))))
    IO.print("drain  " ++ show_step(Q.pop(Nat, Q.empty(Nat))))
    IO.print("psum   " ++ Nat.show(Tree.reduce(~Nat, ~Nat.add_sg(), Tree.build(~Nat, ~id, 10n, 0n))))
    IO.print("dot    " ++ U32.show(dot(3n, Vec.from_list(U32, [1, 2, 3]), Vec.from_list(U32, [4, 5, 6]))))

#|sort   [0, 3, 3, 5, 9]
#|queue  next 1, rest [2, 3]
#|drain  stop
#|psum   523776
#|dot    32
