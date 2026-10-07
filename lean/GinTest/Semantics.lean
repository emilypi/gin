import Gin.Signal

/-!
Checks that the signal combinators satisfy the equations of
`docs/semantics.md`, both symbolically and on concrete streams. These
equations are the operational semantics of the circuit: every
representation gin handles (the Lean model, IR, normal form, netlist and
HDL) must agree with them.
-/

open Gin

namespace GinTest.Semantics

variable {dom : Domain} {α σ ι ο : Type}

-- [lean-semantics] `reg(0) = v`.
example (v : α) (s : Signal dom α) : register v s 0 = v := rfl

-- [lean-semantics] `reg(t+1) = s(t)`.
example (v : α) (s : Signal dom α) (t : Nat) : register v s (t + 1) = s t := rfl

-- [lean-semantics] `mealy f v i = o` where `st(0) = v` and
-- `(st(t+1), o(t)) = f (st t) (i t)`: such a state sequence exists ...
example (f : σ → ι → σ × ο) (v : σ) (i : Signal dom ι) :
    ∃ st : Nat → σ, st 0 = v ∧ ∀ t, (st (t + 1), mealy f v i t) = f (st t) (i t) :=
  ⟨mealyState f v i, rfl, fun _ => rfl⟩

-- [lean-semantics] ... and any sequence satisfying the equations determines
-- the same outputs, so the equations characterise `mealy` completely.
theorem mealy_unique (f : σ → ι → σ × ο) (v : σ) (i : Signal dom ι) (st : Nat → σ)
    (h0 : st 0 = v) (hs : ∀ t, st (t + 1) = (f (st t) (i t)).1) (t : Nat) :
    mealy f v i t = (f (st t) (i t)).2 := by
  have hst : ∀ t, mealyState f v i t = st t := by
    intro t
    induction t with
    | zero => exact h0.symm
    | succ t ih => rw [mealyState_succ, ih, hs]
  rw [mealy_apply, hst]

/-- `10 * t` at cycle `t`. -/
def tens : Signal System Nat := fun t => 10 * t

-- [lean-semantics] A register delays by exactly one cycle.
#guard (List.range 5).map (register 7 tens) == [7, 0, 10, 20, 30]

-- [lean-semantics] A Mealy machine whose output is its state before the step:
-- running sums of the earlier inputs.
#guard (List.range 6).map (mealy (fun s x => (s + x, s)) 0 tens) == [0, 0, 10, 30, 60, 100]

-- [lean-semantics] A Mealy machine whose output is its state after the step.
#guard (List.range 4).map (mealy (fun s x => (s + x, s + x)) 1 tens) == [1, 11, 31, 61]

-- [lean-semantics] Combinational lifting is pointwise.
#guard (List.range 3).map (lift2 (· + ·) tens (Signal.pure 1)) == [1, 11, 21]
#guard (List.range 3).map (lift (· * 2) tens) == [0, 20, 40]
#guard (List.range 3).map (lift3 (fun a b c => a + b + c) tens tens (Signal.pure 5)) == [5, 25, 45]

end GinTest.Semantics
