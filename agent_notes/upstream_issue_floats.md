# Draft feature issue: laws about float code

For HigherOrderCO/Bend, as a Feature issue. Not filed yet.

---

**Title:** Laws about F32 code: make float operations computable in the checker

### What Bend should do

Let a law state and prove facts about float results:

```python
law sum_tenths:
  {F32.add(0.1, 0.2) == 0.3 : F32}   # true in binary32: both are 0x3E99999A
```

Today every `F32` operation in Base is an unfilled law, so this does not
check, and a user file cannot add axioms. Integer and fixed-point code
has laws; float code has none.

### Why

Games and simulations keep state in floats. Laws such as "a physics
step stays within ε of exact arithmetic", "this replay stays in the
arena", or "this result is bit-identical on C, CUDA, Metal and JS" have
no way in.

It works in a library, without a Base change:
<https://github.com/nbardy/bend_stdlib/tree/stdlib-rewrite/src/float>.
binary32 is implemented in software over `Word(32n)`, as the IEEE
definition (the exact result, then round to nearest even), so the
checker computes it. `0.1 + 0.2` is proven bit-exact against hardware,
and `add`/`mul` match hardware on C and JS on every edge and random
case tried. Hardware `F32` enters only as a named hypothesis
(`HardOk`): a law that needs it takes it as a `~` argument.

The one step a library cannot take: Base giving `F32.add`, `sub`, `mul`,
`div`, `sqrt` bodies ("exact, then round") while the compiler keeps the
machine instruction, as it already does for `U32.add` (`Word.adc` to the
checker, one instruction at run time). Then floats compute in the
checker and the hypothesis goes away. `+ - * /` and `sqrt` are correctly
rounded on the C lane (contraction off) and the JS lane (`Math.fround`
of a float64 operation equals the float32 result for these); Metal and
CUDA would need checking; transcendental functions would stay laws.

This is the step CompCert took in 1.12, replacing axiomatized floats with
Flocq's executable, proven IEEE model; related work we drew on:
VCFloat2 (Appel, Kellison), Numerical Fuzz (Kellison, Hsu), Bean.
Design notes:
<https://github.com/nbardy/bend_stdlib/blob/stdlib-rewrite/agent_notes/float_system.md>.

Is this something you want in Base, somewhere else, or left to
libraries? The library can stay as it is either way.
