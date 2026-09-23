# Probe for agent_notes/bend_float_facts.md: functions of a float's bits
# compute on literals. (F32 arithmetic does not: the law
# {F32.add(1.0, 1.0) == 2.0 : F32} fails with "expected F32.add(1.0,
# 1.0), observed 2.0".) Mantissa and exponent stay U32: converting them
# to unary Nat overflows the checker.
import Base

def bits(x: F32) -> U32:
  match x:
    case F32{w}:
      U32{w}

# the exact value of a normal float: (-1)^sign * (2^23 + mantissa) * 2^(exponent - 150)
type Dyadic is Data:
  Dyadic{neg: Bool, m: U32, e: U32}

def decode(+x: F32) -> Dyadic:
  Dyadic{U32.is_ne(U32.shrn(bits(x), 31n), 0),
         U32.add(U32.and(bits(x), 8388607), 8388608),
         U32.and(U32.shrn(bits(x), 23n), 255)}

# 1.5 = 12582912 * 2^(127-150)
law decode_1_5:
  {decode(1.5) == Dyadic{False{}, 12582912, 127} : Dyadic}

def decode_1_5():
  {==}

