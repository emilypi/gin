import Gin.Signal

/-!
# Reject fixture: compiled code that is not the definition

Not part of the default build. The design and its proof are sound, but
the increment it uses is `@[implemented_by]` a function that adds two, so
its compiled code, which would compute the vectors, does not compute what
the trace (`Certificate` in the code, `"certificate"` in the JSON) and the
IR describe. `gin-check-export` must refuse it, naming the constant, and
so must `gin-export`. `scripts/export-examples.sh --check-rejects` checks
the refusals and that nothing is written.
-/

open Gin

namespace BadImplementedBy

/-- The code that runs in place of `inc`. -/
def incOther (s : BitVec 8) : BitVec 8 := s + 2

/-- Adds one, but its compiled code adds two. -/
@[implemented_by incOther] def inc (s : BitVec 8) : BitVec 8 := s + 1

/-- The enable counter of `Gin.Examples.Counter`, incrementing with `inc`. -/
def bad (en : Signal System Bool) : Signal System (BitVec 8) :=
  mealy (fun s e => (if e then inc s else s, s)) 0 en

/-- The specification: the number of enabled cycles strictly before `t`,
modulo 2^8. -/
def spec (en : Signal System Bool) (t : Nat) : BitVec 8 :=
  BitVec.ofNat 8 ((List.range t).countP (fun i => en i))

theorem state_eq (en : Signal System Bool) (t : Nat) :
    mealyState (fun (s : BitVec 8) (e : Bool) => (if e then inc s else s, s)) 0 en t
      = BitVec.ofNat 8 ((List.range t).countP (fun i => en i)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [mealyState_succ, ih, List.range_succ, List.countP_append]
    cases h : en t <;> simp [h, inc, BitVec.ofNat_add]

/-- A sound refinement theorem. -/
theorem bad_correct : ∀ en t, bad en t = spec en t := by
  intro en t
  simp only [bad, spec, mealy_apply, state_eq]

end BadImplementedBy
