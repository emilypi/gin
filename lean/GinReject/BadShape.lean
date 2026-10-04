import Gin.Signal

/-!
# Reject fixture: theorems without the refinement shape

Not part of the default build. Each theorem below is proved, but none
says that the implementation meets an independent specification at every
cycle for every input, so the exporter must refuse each one, naming the
theorem. `scripts/export-examples.sh --check-rejects` checks that it does
and that nothing is written.
-/

open Gin

namespace BadShape

/-- The enable counter of `Gin.Examples.Counter`. -/
def bad (en : Signal System Bool) : Signal System (BitVec 8) :=
  mealy (fun s e => (if e then s + 1 else s, s)) 0 en

/-- A tautology: the implementation equals itself. -/
theorem tautology : ∀ en t, bad en t = bad en t := fun _ _ => rfl

/-- A claim about cycle 0 only. -/
theorem at_zero : ∀ en, bad en 0 = 0 := fun _ => rfl

/-- A "specification" that calls the implementation. -/
def spec (en : Signal System Bool) (t : Nat) : BitVec 8 := bad en t

/-- Compared with a specification that calls the implementation. -/
theorem calls_impl : ∀ en t, bad en t = spec en t := fun _ _ => rfl

/-- A claim weakened by a disjunction. -/
theorem or_true : ∀ en t, bad en t = BitVec.ofNat 8 t ∨ True := fun _ _ => .inr trivial

end BadShape
