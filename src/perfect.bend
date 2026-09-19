import Base

# The missing Array invariant (audit T4): Array admits ragged trees
# while size/get walk as if perfect. Every Array law takes Perfect
# first. Sizing is stated via dbl (structural doubling) — connecting
# dbl to U32.pow needs Word-level shl==mul2 theory (staked, NOT
# stated: a law without its proof would be an axiom).
#
# RECORDED BARRIER (2026-09-19): full induction over Array.size is
# blocked by linearity composition — relating size(ANode) to an IH
# about size(xs) mentions xs twice (once to compute, once for the
# IH), `+` is impossible on Type, and clone-dup fails because
# clone(xs) is only propositionally (not definitionally) xs.
# What lands instead: one-level composition laws (size_node_shl),
# which suffice for fixed-depth unrolling. A general escape for
# linear induction composition is an open problem, not a gap.

law Perfect:
  for -T: Type
  for d: Nat
  for a: Array<T>
  Type

def Perfect(T, d, a):
  match d a:
    case 0n ALeaf{x}:
      Unit
    case 0n ANode{xs, ys}:
      Empty
    case 1n+p ALeaf{x}:
      Empty
    case 1n+p ANode{xs, ys}:
      Perfect(T, p, xs) & Perfect(T, p, ys)

# Pair second projection (Base only destructures; no snd call exists
# anywhere — this names it so laws can state pair equations).
def snd_size(-T: Type, p: Array<T> & U32) -> U32:
  (a, n) = p
  n

# Doubling spec of Array.size (size walks the left spine doubling).
def dbl(d: Nat) -> U32:
  match d:
    case 0n:
      1
    case 1n+p:
      U32.shl(dbl(p))

# One-level size algebra: size.node's output in terms of its input.
# Proved by matching the pair param (Base's own destructure idiom).
law size_node_snd:
  for -T: Type
  for ys: Array<T>
  for r: Array<T> & U32
  {snd_size(T, Array.size.node(T, ys, r)) == U32.shl(snd_size(T, r)) : U32}

def size_node_snd(T, ys, r):
  (xa, xb) = r
  {==}

# Composed one level: size of a node via shl of the left size.
# Exact use-count: xs once, ys once — the most composition linear
# affinity permits without the (open) induction escape.
law size_node_shl:
  for -T: Type
  for xs: Array<T>
  for ys: Array<T>
  {snd_size(T, Array.size(T, ANode{xs, ys})) == U32.shl(snd_size(T, Array.size(T, xs))) : U32}

def size_node_shl(T, xs, ys):
  size_node_snd(T, ys, Array.size(T, xs))

# Array.new builds perfect trees. Needs +d/+v (both subtrees take
# the same IH) — hence Data-only, exactly like List.replicate.
law perfect_new:
  for -T: Data
  for +d: Nat
  for +v: T
  Perfect(T, d, Array.new(T, d, v))

def perfect_new(T, d, v):
  match d:
    case 0n:
      Unit{}
    case 1n+p:
      (perfect_new(T, p, v), perfect_new(T, p, v))

def main() -> U32:
  dbl(3n)
