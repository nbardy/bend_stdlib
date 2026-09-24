import Base
import ./list.bend as List

# queue.bend: a FIFO queue as two lists, specified by the list it holds.
#
#   import ./queue.bend as Q
#
# push conses onto rear; pop takes from front, and when front is empty the
# reversed rear becomes the new front. Queue is linear (Type), so each
# queue value is used once; then each element is reversed at most once and
# every operation costs O(1) on average.
#
# model(q) is the list q holds. push_model and pop_model state push and
# pop in terms of it.

type Queue<-A: Data> is Type:
  Queue{front: List<&2, A>, rear: List<&2, A>}

def empty(-A: Data) -> Queue<A>:
  Queue{Nil{}, Nil{}}

def model(-A: Data, q: Queue<A>) -> List<&2, A>:
  match q:
    case Queue{f, r}:
      List.append(&2, A, f, List.reverse(&2, A, r))

def push(-A: Data, q: Queue<A>, x: A) -> Queue<A>:
  match q:
    case Queue{f, r}:
      Queue{f, x <> r}

# front is empty; f is the reversed rear
def pop.rot(-A: Data, f: List<&2, A>) -> List.Step<&1, A, Queue<A>>:
  match f:
    case Nil{}:
      List.Stop{}
    case h <> t:
      List.Next{h, Queue{t, Nil{}}}

def pop(-A: Data, q: Queue<A>) -> List.Step<&1, A, Queue<A>>:
  match q:
    case Queue{Nil{}, r}:
      pop.rot(A, List.reverse(&2, A, r))
    case Queue{h <> t, r}:
      List.Next{h, Queue{t, r}}

# pop's result with the remaining queue replaced by its model
def pop.model(-A: Data, s: List.Step<&1, A, Queue<A>>) -> List.Step<&2, A, List<&2, A>>:
  match s:
    case List.Stop{}:
      List.Stop{}
    case List.Next{x, q}:
      List.Next{x, model(A, q)}

# push appends x to the model.
law push_model:
  for -A: Data
  for q: Queue<A>
  for +x: A
  {List.append(&2, A, model(A, q), [x]) == model(A, push(A, q, x)) : List<&2, A>}

def push_model(A, q, x):
  match q:
    case Queue{+f, +r}:
      %List.reverse_go(A, r, [x]) : {List.append(&2, A, List.append(&2, A, f, List.reverse(&2, A, r)), [x]) == List.append(&2, A, f, _) : List<&2, A>}
      Equal.sym(List<&2, A>,
        List.append(&2, A, f, List.append(&2, A, List.reverse(&2, A, r), [x])),
        List.append(&2, A, List.append(&2, A, f, List.reverse(&2, A, r)), [x]),
        List.append_assoc(A, f, List.reverse(&2, A, r), [x]))

law pop_model.rot:
  for -A: Data
  for f: List<&2, A>
  {List.uncons(A, f) == pop.model(A, pop.rot(A, f)) : List.Step<&2, A, List<&2, A>>}

def pop_model.rot(A, f):
  match f:
    case Nil{}:
      {==}
    case h <> t:
      %List.append_nil(A, t) : {List.Next{h, t} == List.Next{h, _} : List.Step<&2, A, List<&2, A>>}
      {==}

# pop returns the model's head and tail.
law pop_model:
  for -A: Data
  for q: Queue<A>
  {List.uncons(A, model(A, q)) == pop.model(A, pop(A, q)) : List.Step<&2, A, List<&2, A>>}

def pop_model(A, q):
  match q:
    case Queue{Nil{}, r}:
      pop_model.rot(A, List.reverse(&2, A, r))
    case Queue{h <> t, r}:
      {==}
