import Gin.Signal

/-!
# "101" sequence detector

A Mealy machine that raises its output in the cycle that completes the bit
pattern `1 0 1` on its input. Matches may overlap: `1 0 1 0 1` hits twice.
-/

open Gin

namespace Detector

/-- One step of the detector. State 0: nothing matched; state 1: the last
input was `1`; state 2: the last two inputs were `1 0`. -/
def step (s : BitVec 2) (i : Bool) : BitVec 2 × Bool :=
  if s = 0 then (if i then 1 else 0, false)
  else if s = 1 then (if i then 1 else 2, false)
  else (if i then 1 else 0, i)

/-- The implementation: `step` run as a Mealy machine from state 0. -/
def detector (b : Signal System Bool) : Signal System Bool :=
  mealy step 0 b

/-- The specification: the inputs at cycles `t-2`, `t-1` and `t` are
`1 0 1`. -/
def spec (b : Signal System Bool) (t : Nat) : Bool :=
  decide (t ≥ 2) && b (t - 2) && !b (t - 1) && b t

/-- Closed form of the state register, used in the proof. -/
def stateSpec (b : Signal System Bool) : Nat → BitVec 2
  | 0 => 0
  | t + 1 => if b t then 1 else if t ≥ 1 ∧ b (t - 1) then 2 else 0

theorem state_eq (b : Signal System Bool) (t : Nat) :
    mealyState step 0 b t = stateSpec b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [mealyState_succ, ih]
    cases t with
    | zero => cases h : b 0 <;> simp [step, stateSpec, h]
    | succ t =>
      cases h1 : b (t + 1) <;> cases h0 : b t <;>
        by_cases hc : 1 ≤ t ∧ b (t - 1) = true <;> simp_all [step, stateSpec]

/-- The refinement theorem: the detector meets its specification at every
cycle, for every input stream. -/
theorem detector_correct : ∀ b t, detector b t = spec b t := by
  intro b t
  simp only [detector, mealy_apply, state_eq]
  match t with
  | 0 => cases h : b 0 <;> simp [step, stateSpec, spec, h]
  | 1 => cases h0 : b 0 <;> cases h1 : b 1 <;> simp [step, stateSpec, spec, h0, h1]
  | t + 2 =>
    cases h0 : b t <;> cases h1 : b (t + 1) <;> cases h2 : b (t + 2) <;>
      simp [step, stateSpec, spec, h0, h1, h2]

end Detector
