import Gin.Signal

/-!
# Enable counter

An 8-bit counter that increments on every cycle its enable input is high.
The output during cycle `t` is the count before cycle `t`'s increment.
-/

open Gin

namespace Counter

/-- The implementation: one Mealy machine whose state is the count. -/
def counter (en : Signal System Bool) : Signal System (BitVec 8) :=
  mealy (fun s e => (if e then s + 1 else s, s)) 0 en

/-- The specification: the number of enabled cycles strictly before `t`,
modulo 2^8. -/
def spec (en : Signal System Bool) (t : Nat) : BitVec 8 :=
  BitVec.ofNat 8 ((List.range t).countP (fun i => en i))

theorem state_eq (en : Signal System Bool) (t : Nat) :
    mealyState (fun (s : BitVec 8) (e : Bool) => (if e then s + 1 else s, s)) 0 en t
      = BitVec.ofNat 8 ((List.range t).countP (fun i => en i)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [mealyState_succ, ih, List.range_succ, List.countP_append]
    cases h : en t <;> simp [h, BitVec.ofNat_add]

/-- The refinement theorem: the counter meets its specification at every
cycle, for every input stream. -/
theorem counter_correct : ∀ en t, counter en t = spec en t := by
  intro en t
  simp only [counter, spec, mealy_apply, state_eq]

end Counter
