import Gin.Signal

/-!
# Reject fixture: a clock domain that reduces by running code

Not part of the default build. The name of the design's clock domain
reduces only through `Lean.reduceBool`, which Lean's reduction evaluates by
running the compiled code of `hook`: the translator would run code of the
design. `gin-check-export` must refuse it, naming the domain, and so must
`gin-export`, before translating it. (Its theorem also depends on the axiom
`Lean.trustCompiler`, through the definition of `Lean.reduceBool`; the
native reduction check runs first and gives the reason.)
`scripts/export-examples.sh --check-rejects` checks the refusals and that
nothing is written.
-/

open Gin

namespace BadReduceBool

/-- Code that `Lean.reduceBool` would run. -/
def hook : Bool := true

set_option linter.deprecated false in
/-- A domain whose name reduces only by running `hook`. -/
def hooked : Domain := ⟨cond (Lean.reduceBool hook) "System" "System", 10000⟩

/-- The enable counter of `Gin.Examples.Counter`, in the domain `hooked`. -/
def bad (en : Signal hooked Bool) : Signal hooked (BitVec 8) :=
  mealy (fun s e => (if e then s + 1 else s, s)) 0 en

/-- The specification: the number of enabled cycles strictly before `t`,
modulo 2^8. -/
def spec (en : Signal hooked Bool) (t : Nat) : BitVec 8 :=
  BitVec.ofNat 8 ((List.range t).countP (fun i => en i))

theorem state_eq (en : Signal hooked Bool) (t : Nat) :
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

end BadReduceBool
