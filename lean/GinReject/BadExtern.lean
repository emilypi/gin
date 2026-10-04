import Gin.Signal

/-!
# Reject fixture: foreign code in a design module

Not part of the default build. The design and its proof are sound, and
nothing in the module is `unsafe`, but it declares `foreign`, an
`@[extern]` constant, and `cached`, a closed term that calls it and that no
design uses. Lean evaluates the closed terms of every module linked into an
executable when it starts, so linked into `gin-export` the foreign code
would run before any check (with `lean_io_remove_file` it could delete or,
with other runtime functions, write files). `gin-check-export` must refuse
the module, naming the constant, and so must `gin-export`.
`scripts/export-examples.sh --check-rejects` checks the refusals and that
nothing is written. The symbol does not exist: the module is never linked.
-/

open Gin

namespace BadExtern

/-- Foreign code. -/
@[extern "gin_reject_bad_extern"] opaque foreign : @& String → Unit → Nat

/-- Calls `foreign` when evaluated: at start-up, in an executable that links
this module. -/
def cached : Nat := foreign "examples/counter/counter.gin.json" ()

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

end BadExtern
