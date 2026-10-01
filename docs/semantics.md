# Semantics

Every representation gin handles — the Lean model, the core IR, the
normal form, the netlist and the generated HDL — must agree with the
definitions on this page. The reference simulators (`Gin.Sim`) are a
direct transcription of them.

## Cycles

A circuit is observed at cycles `t = 0, 1, 2, …`.

- The value of an input port at cycle `t` is row `t` of the vectors.
- A register with initial value `v` and argument signal `s` satisfies
  `reg(0) = v` and `reg(t+1) = s(t)`.
- Everything else is combinational within a cycle.
- Output row `t` is the value of the output ports at cycle `t`.

In Lean, `Signal dom α := Nat → α`, with

```
register v s = fun t => if t = 0 then v else s (t - 1)
mealy f v i  = o, where st(0) = v and (st(t+1), o(t)) = f (st t) (i t)
```

## Primitives

`n` is the operand width. Every bit-vector result lies in `[0, 2^w)`
for its width `w`; arithmetic wraps around.

| Primitive                 | Meaning                                    |
| ------------------------- | ------------------------------------------ |
| `bool.and/or/xor/not`     | standard; `bool.eq a b = (a == b)`         |
| `bv.add a b`              | `(a + b) mod 2^n`                          |
| `bv.sub a b`              | `(a - b) mod 2^n`                          |
| `bv.mul a b`              | `(a * b) mod 2^n`                          |
| `bv.neg a`                | `(2^n - a) mod 2^n`                        |
| `bv.and/or/xor`           | bitwise                                    |
| `bv.not a`                | `2^n - 1 - a`                              |
| `bv.shl k a`              | `(a * 2^k) mod 2^n` (0 when `k >= n`)      |
| `bv.lshr k a`             | `a div 2^k` (0 when `k >= n`)              |
| `bv.eq/ult/ule`           | unsigned comparison, result `Bool`         |
| `bv.concat a b`           | `a * 2^(width b) + b`                      |
| `bv.extract hi lo a`      | `(a div 2^lo) mod 2^(hi - lo + 1)`         |
| `bv.zext m a`             | `a`, at width `m`                          |
| `bv.ofBool b`             | `1` if `b` else `0`, width 1               |
| `if c t e`                | `t` if `c` else `e`                        |
| `sig.pure x`              | `fun t => x`                               |
| `sig.lift k f s1 … sk`    | `fun t => f (s1 t) … (sk t)`               |

## Hardware mapping

- `Bool` is a single bit, `1` meaning true. `BitVec n` is an unsigned
  `n`-bit vector with bit `n-1` most significant.
- Every module has a clock port `clk` (rising edge) and a reset port
  `rst` (synchronous, active-high), even if it has no registers.
  Registers load their initial value when `rst` is high at a rising
  edge.

## Testbench protocol

Every backend's generated testbench follows the same protocol, so the
HDL simulation can be compared cycle for cycle with the reference
simulators:

1. Time unit 1 ns; clock period 10 ns; the clock starts low.
2. Assert reset (`rst = 1`) and drive every input to 0/false.
3. Apply one rising edge, so registers load their initial values. With
   the clock low again, deassert reset.
4. For `t = 0 … N-1`: with the clock low, drive row `t`'s inputs; wait
   1 ns; compare every output with row `t`'s expected value, printing
   one `GIN-MISMATCH` line per differing port; then apply one rising
   edge and return the clock low.
5. Print exactly one final line, `GIN-PASS cycles=<N>` if there were no
   mismatches and `GIN-FAIL mismatches=<k>` otherwise, then finish the
   simulation.

A run passes if and only if some output line contains `GIN-PASS` and no
line contains `GIN-FAIL` or `GIN-MISMATCH`. Lines are matched by
substring because simulators may prefix report output (nvc prints
`** Note:`).

## Multiple outputs

A top entity with outputs `o1 … on` (n ≥ 2) returns the right-nested
binary product `o1 × (o2 × … × (o(n-1) × on))`, the shape of Lean's
`o1 × o2 × … × on`. Output `j` is the `j`-th component along that spine.
