import Gin.Signal

/-!
# Reject fixture: a design module that runs code when loaded

Not part of the default build. The design and its proof are sound, but
the module declares an `initialize`, which runs whenever the module is
loaded, including inside the exporter. The exporter must refuse the
module, naming it, before any of its code runs.
`scripts/export-examples.sh --check-rejects` checks that it does and that
nothing is written.
-/

open Gin

namespace BadInit

/-- Runs whenever the module is loaded. -/
initialize loaded : IO.Ref Bool ← IO.mkRef true

/-- The enable counter of `Gin.Examples.Counter`. -/
def bad (en : Signal System Bool) : Signal System (BitVec 8) :=
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

/-- A sound refinement theorem. -/
theorem bad_correct : ∀ en t, bad en t = spec en t := by
  intro en t
  simp only [bad, spec, mealy_apply, state_eq]

end BadInit
