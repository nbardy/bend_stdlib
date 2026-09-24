import Base
import ../src/float/sf32.bend as SF32
import ../src/float/f32.bend as F32

# sf32_gpu.bend: Base's F32.add, F32.mul, F32.is_lt and F32.neg run
# inside `!` calls, which the native binary sends to the GPU (Metal on
# macOS, CUDA on Linux), against the bit-level specs in src/float.
#
# On the CPU lanes these match IEEE 754 exactly. On an Apple M4 (Metal,
# MTLMathModeSafe) add, mul and < flush subnormal inputs and results to
# zero of the same sign; negation is exact, NaNs included. See
# notes/metal_floats.md. The output below counts results that match
# neither IEEE 754 nor IEEE 754 with flush-to-zero, so it is the same on
# every lane.

type Bad is Data:
  Bad{op: U32, a: U32, b: U32, hw: U32, sw: U32}

type Res is Data:
  Res{add: U32, mul: U32, lt: U32, neg: U32, fadd: U32, fmul: U32, flt: U32, nneg: U32, bad: List<&2, Bad>}

def is_nan(+x: F32) -> Bool:
  Bool.and(U32.is_eq(U32.and(SF32.bits(x), 2139095040), 2139095040), U32.is_ne(U32.and(SF32.bits(x), 8388607), 0))

def same(+a: F32, +b: F32) -> Bool:
  Bool.or(U32.is_eq(SF32.bits(a), SF32.bits(b)), Bool.and(is_nan(a), is_nan(b)))

def miss(ok: Bool) -> U32:
  match ok:
    case True{}:
      0
    case False{}:
      1

def b2u(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

def one(ok: Bool, op: U32, a: U32, b: U32, hw: U32, sw: U32) -> List<&2, Bad>:
  match ok:
    case True{}:
      []
    case False{}:
      [Bad{op, a, b, hw, sw}]

def cat(x: List<&2, Bad>, y: List<&2, Bad>) -> List<&2, Bad>:
  List.append(&2, Bad, x, y)

def is_sub(+x: F32) -> Bool:
  Bool.and(U32.is_eq(U32.and(SF32.bits(x), 2139095040), 0), U32.is_ne(U32.and(SF32.bits(x), 8388607), 0))

# flush a subnormal to zero of the same sign
def ftz(+x: F32) -> F32:
  Bool.pick(F32, is_sub(x), SF32.of_bits(U32.and(SF32.bits(x), 2147483648)), x)

def leaf(+x: F32, +y: F32) -> Res:
  +ha = F32.add(x, y)
  +sa = SF32.add(x, y)
  +za = ftz(SF32.add(ftz(x), ftz(y)))
  +hm = F32.mul(x, y)
  +sm = SF32.mul(x, y)
  +zm = ftz(SF32.mul(ftz(x), ftz(y)))
  +hl = F32.is_lt(x, y)
  +sl = F32.lt_bits(x, y)
  +zl = F32.lt_bits(ftz(x), ftz(y))
  +hn = F32.neg(x)
  +sn = F32.neg_bits(x)
  +oa = Bool.or(same(ha, sa), same(ha, za))
  +om = Bool.or(same(hm, sm), same(hm, zm))
  +ol = Bool.or(Bool.not(Bool.xor(hl, sl)), Bool.not(Bool.xor(hl, zl)))
  +on = Bool.or(U32.is_eq(SF32.bits(hn), SF32.bits(sn)), is_nan(x))
  +xb = SF32.bits(x)
  +yb = SF32.bits(y)
  Res{miss(same(ha, sa)), miss(same(hm, sm)), miss(Bool.not(Bool.xor(hl, sl))), miss(on),
    miss(oa), miss(om), miss(ol), miss(Bool.or(Bool.not(is_nan(x)), U32.is_eq(SF32.bits(hn), SF32.bits(sn)))),
    cat(one(oa, 0, xb, yb, SF32.bits(ha), SF32.bits(za)),
      cat(one(om, 1, xb, yb, SF32.bits(hm), SF32.bits(zm)),
        cat(one(ol, 2, xb, yb, b2u(hl), b2u(zl)), one(on, 3, xb, 0, SF32.bits(hn), SF32.bits(sn)))))}

def join(r: Res, s: Res) -> Res:
  match r s:
    case Res{a1, m1, l1, n1, fa1, fm1, fl1, nn1, b1} Res{a2, m2, l2, n2, fa2, fm2, fl2, nn2, b2}:
      Res{U32.add(a1, a2), U32.add(m1, m2), U32.add(l1, l2), U32.add(n1, n2),
        U32.add(fa1, fa2), U32.add(fm1, fm2), U32.add(fl1, fl2), U32.add(nn1, nn2), cat(b1, b2)}

def none() -> Res:
  Res{0, 0, 0, 0, 0, 0, 0, 0, []}

def next(x: U32) -> U32:
  U32.add(U32.mul(x, 1664525), 1013904223)

# Random bit patterns: every exponent, NaNs, infinities, subnormals.
def rand.leaf(+i: U32) -> Res:
  +s1 = next(U32.mul(i, 2654435761))
  +s2 = next(s1)
  leaf(SF32.of_bits(s1), SF32.of_bits(s2))

def rand(d: Nat, +lo: U32) -> Res:
  match d:
    case 0n:
      rand.leaf(lo)
    case 1n++k:
      r s = rand(k, U32.mul(lo, 2)) rand(k, U32.add(U32.mul(lo, 2), 1))
      join(r, s)

# Subnormal-heavy: x has exponent field 0 or 1 (subnormal or the smallest
# normals); y is in [0.5, 1), so x + y is ordinary but x * y is often
# subnormal.
def sub.leaf(+i: U32) -> Res:
  +s1 = next(U32.mul(i, 2246822519))
  +s2 = next(s1)
  leaf(SF32.of_bits(U32.and(s1, 2164260863)), SF32.of_bits(U32.or(U32.and(s2, 2155872255), 1056964608)))

def sub(d: Nat, +lo: U32) -> Res:
  match d:
    case 0n:
      sub.leaf(lo)
    case 1n++k:
      r s = sub(k, U32.mul(lo, 2)) sub(k, U32.add(U32.mul(lo, 2), 1))
      join(r, s)

# the edge cases of examples/sf32.bend, every pair
def edges() -> List<&2, F32>:
  [0.0, SF32.of_bits(2147483648), 1.0, SF32.of_bits(3212836864), 0.1, 0.2, 0.3, 3.0, 16777216.0, 16777217.0, 0.5, 1.5, 2.5,
   SF32.of_bits(1), SF32.of_bits(8388607), SF32.of_bits(8388608), SF32.of_bits(2139095039), SF32.of_bits(4286578687),
   SF32.of_bits(2139095040), SF32.of_bits(4286578688), SF32.of_bits(2143289344), 1.0000001, 0.9999999, 33554430.0]

def at(xs: List<&2, F32>, i: Nat) -> F32:
  match xs i:
    case Nil{} _:
      0.0
    case h <> t 0n:
      h
    case h <> t 1n+j:
      at(t, j)

def edge.go(inside: Bool, +j: Nat) -> Res:
  match inside:
    case True{}:
      leaf(at(edges(), Nat.div(j, 24n)), at(edges(), Nat.mod(j, 24n)))
    case False{}:
      none()

def edge.leaf(+i: U32) -> Res:
  +j = U32.to_nat(U32.sub(i, 1024))
  edge.go(Nat.is_lt(j, 576n), j)

def edge(d: Nat, +lo: U32) -> Res:
  match d:
    case 0n:
      edge.leaf(lo)
    case 1n++k:
      r s = edge(k, U32.mul(lo, 2)) edge(k, U32.add(U32.mul(lo, 2), 1))
      join(r, s)

def op_name(+op: U32) -> String:
  Bool.pick(String, U32.is_eq(op, 0), "add", Bool.pick(String, U32.is_eq(op, 1), "mul", Bool.pick(String, U32.is_eq(op, 2), "lt ", "neg")))

def show_bad(b: Bad) -> String:
  match b:
    case Bad{+op, a, b, hw, sw}:
      "  " ++ op_name(op) ++ " a=" ++ U32.show(a) ++ " b=" ++ U32.show(b) ++ " hw=" ++ U32.show(hw) ++ " spec=" ++ U32.show(sw)

def show_bads(n: Nat, bs: List<&2, Bad>) -> String:
  match n bs:
    case 0n _:
      ""
    case 1n+k Nil{}:
      ""
    case 1n+k h <> t:
      "\n" ++ show_bad(h) ++ show_bads(k, t)

def report(name: String, r: Res) -> String:
  match r:
    case Res{a, m, l, n, fa, fm, fl, nn, bad}:
      name ++ " neither IEEE nor flush-to-zero: add " ++ U32.show(fa) ++ " mul " ++ U32.show(fm) ++ " lt " ++ U32.show(fl) ++ " neg " ++ U32.show(n) ++ show_bads(12n, bad)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(report("edges ", edge!(10n, 1)))
    IO.print(report("random", rand!(12n, 1)))
    IO.print(report("subnrm", sub!(12n, 1)))

#|edges  neither IEEE nor flush-to-zero: add 0 mul 0 lt 0 neg 0
#|random neither IEEE nor flush-to-zero: add 0 mul 0 lt 0 neg 0
#|subnrm neither IEEE nor flush-to-zero: add 0 mul 0 lt 0 neg 0
