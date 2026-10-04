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

/-- A counter without inputs. -/
def ticks : Signal System (BitVec 4) := mealy (fun (s : BitVec 4) (_ : Bool) => (s + 1, s)) 0 (Signal.pure true)

-- A circuit without inputs has no input values; its outputs follow the clock.
#guard (VectorSource.of0 ticks).inputs == []
#guard ((VectorSource.of0 ticks).rows 1 3).map (fun c => (c.inputs, c.outputs)) ==
  #[([], [.bv 4 0]), ([], [.bv 4 1]), ([], [.bv 4 2])]

/-- Three inputs. -/
def pick (a : Signal System Bool) (x y : Signal System (BitVec 3)) : Signal System (BitVec 3) :=
  lift3 (fun a x y => if a then x else y) a x y

-- Three inputs are drawn in order and the output follows them.
#guard (VectorSource.of3 pick).inputs == [.bool, .bv 3, .bv 3]
#guard ((VectorSource.of3 pick).rows 5 16).all fun c =>
  match c.inputs, c.outputs with
  | [.bool a, x, y], [o] => o == if a then x else y
  | _, _ => false

-- The biased generators produce exactly `n` samples, reproducibly.
#guard ((enableRuns 1024 ⟨1⟩).1.size, (patternBits 1024 ⟨1⟩).1.size) == (1024, 1024)
#guard ((largeOperands (w := 8) (v := 8) 1024 ⟨1⟩).1.size) == 1024
#guard (enableRuns 50 ⟨4⟩).1 == (enableRuns 50 ⟨4⟩).1
#guard (enableRuns 0 ⟨4⟩).1.size == 0

-- Enable runs include a high run longer than 255 cycles.
#guard ((enableRuns 1024 ⟨1⟩).1.foldl (fun (best, cur) b =>
  let cur := if b then cur + 1 else 0; (max best cur, cur)) (0, 0)).1 > 255

-- Most operands have their top bit set.
#guard ((largeOperands (w := 8) (v := 8) 1024 ⟨2⟩).1.filter fun (x, _) => x.toNat ≥ 128).size > 640

-- A biased generator replaces the uniform one in a vector source.
#guard ((VectorSource.of1 Counter.counter enableRuns).rows 1 1024).size == 1024

end GinTest.Vectors
