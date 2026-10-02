import Gin
import Gin.Export.Vectors

/-!
The input generator is SplitMix64, reproducible from its seed, and the
vector sources pair inputs with the outputs of the Lean definition.
-/

open Gin Gin.Export

namespace GinTest.Vectors

-- Reference values of SplitMix64 seeded with 0.
#guard (Prod.fst <$> [(Rng.mk 0).next, ((Rng.mk 0).next.2).next]) ==
  [0xE220A8397B1DCDAF, 0x6E789E6AA1B965F4]

-- Wide samples combine several 64-bit words and stay below 2^n.
#guard ((Rng.mk 5).bits 100).1 < 2 ^ 100
#guard ((Rng.mk 5).bits 100).1 ≥ 2 ^ 64
#guard ((Rng.mk 5).bits 1).1 < 2

-- Inputs are reproducible from the seed, and different seeds differ.
#guard (VectorSource.of1 Counter.counter).rows 9 10 == (VectorSource.of1 Counter.counter).rows 9 10
#guard (VectorSource.of1 Counter.counter).rows 9 10 != (VectorSource.of1 Counter.counter).rows 8 10
#guard ((VectorSource.of1 Counter.counter).rows 9 10).size == 10

/-- Two outputs: the input and its negation. -/
def twoOutputs (b : Signal System Bool) : Signal System (Bool × BitVec 3) :=
  lift (fun b => (!b, if b then 5 else 2)) b

-- A product result is split into one value per output port, in order.
#guard (VectorSource.of1 twoOutputs).outputs == [.bool, .bv 3]
#guard ((VectorSource.of1 twoOutputs).rows 1 4).all fun c =>
  match c.inputs, c.outputs with
  | [.bool b], [.bool nb, .bv 3 v] => nb == !b && v == (if b then 5 else 2)
  | _, _ => false

-- Mac draws x then y in each cycle, and its first output is the reset value.
#guard (VectorSource.of2 Mac.mac).inputs == [.bv 8, .bv 8]
#guard ((VectorSource.of2 Mac.mac).rows 2 1).map (·.outputs) == #[[.bv 16 0]]

end GinTest.Vectors
