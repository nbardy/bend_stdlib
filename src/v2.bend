import Base
import ./class.bend as C
import ./u32.bend as U32

# v2.bend: 2D integer vectors with wrapping + and -.
#
#   import ./v2.bend as V2
#   V2.V2{x, y}, V2.group()

type V2 is Data:
  V2{x: U32, y: U32}

def add(a: V2, b: V2) -> V2:
  match a b:
    case V2{ax, ay} V2{bx, by}:
      V2{U32.add(ax, bx), U32.add(ay, by)}

def sub(a: V2, b: V2) -> V2:
  match a b:
    case V2{ax, ay} V2{bx, by}:
      V2{U32.sub(ax, bx), U32.sub(ay, by)}

law sub_add:
  for a: V2
  for b: V2
  {a == sub(add(a, b), b) : V2}

def sub_add(a, b):
  match a b:
    case V2{+ax, +ay} V2{+bx, +by}:
      %U32.sub_add(ax, bx) : {V2{ax, ay} == V2{_, U32.sub(U32.add(ay, by), by)} : V2}
      %U32.sub_add(ay, by) : {V2{ax, ay} == V2{ax, _} : V2}
      {==}

law add_sub:
  for a: V2
  for b: V2
  {a == add(sub(a, b), b) : V2}

def add_sub(a, b):
  match a b:
    case V2{+ax, +ay} V2{+bx, +by}:
      %U32.add_sub(ax, bx) : {V2{ax, ay} == V2{_, U32.add(U32.sub(ay, by), by)} : V2}
      %U32.add_sub(ay, by) : {V2{ax, ay} == V2{ax, _} : V2}
      {==}

def group() -> C.Group<V2>:
  C.Group{add, sub, sub_add, add_sub}
