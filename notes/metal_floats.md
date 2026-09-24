# F32 on the Metal lane

Measured 2026-09-25 on an Apple M4 (macOS 15.5, Metal 3) with Bend
2.0.27. Bend builds the GPU program with `MTLMathModeSafe` and the CPU
program with `fp contract(off)`. A `!` call runs on the GPU; `--gpu off`
runs the same binary's `!` calls on the CPU pool.

Probe: `examples/sf32_gpu.bend` (and a larger scratch version). Base's
`F32.add`, `F32.mul`, `F32.is_lt` and `F32.neg` run inside `!` calls;
each lane compares them with `SF32.add`, `SF32.mul`, `F32.lt_bits` and
`F32.neg_bits`. Inputs: the 576 edge pairs of `examples/sf32.bend`,
32768 random bit patterns, and 32768 subnormal-heavy pairs.

## Result

| | CPU pool (`--gpu off`) | Metal GPU |
|---|---|---|
| add, mul vs IEEE 754 | 0 mismatches | 44 add, 24300 mul |
| `<` vs IEEE 754 | 0 | 6 |
| neg vs sign flip | 0 | 0, NaNs included |
| add, mul, `<` vs IEEE 754 with flush-to-zero | (differs, as expected) | 0 mismatches |

Every Metal mismatch is flush-to-zero, and nothing else: subnormal
inputs are read as zero of the same sign (DAZ), and subnormal results
are returned as zero of the same sign (FTZ). Examples: `0 + 2^-149 = 0`,
`1.0 * 2^-149 = 0`, `0 < 2^-149` is false. Rounding of normal results is
IEEE's (no mismatch outside subnormals). `MTLMathModeSafe` does not turn
this off.

## What it means for the hypotheses

- `NegOk`: holds on Metal (sign flip on every value, NaNs too).
- `LtOk`: fails on Metal when an operand is subnormal. It holds when
  neither operand is.
- `SF32.HardOk` (correct rounding of `+` and `*`): fails on Metal when
  an input or the exact result is subnormal. It holds otherwise.
- The clamp laws do not hold on the GPU for subnormal inputs:
  `F32.clamp(-2^-149, 0.0, 216.0)` returns `-2^-149` (bits `0x80000001`)
  on Metal, below `lo`; the CPU returns `+0`. So `lo_le_clamp`'s
  conclusion fails for code run under `!`. The apps are unaffected: they
  make no `!` calls.

A Metal-lane hypothesis would be the IEEE one with flush-to-zero (the
model the probe checks). The simplest law-level fix for clamping is to
state hypotheses and results on non-subnormal values, or to flush
subnormals in the spec (`ftz` in the probe) and prove the clamp laws
against that. Not done yet. CUDA was not checked (no NVIDIA GPU here).
