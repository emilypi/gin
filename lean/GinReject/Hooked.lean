import Gin.Signal

/-!
# Reject fixture: an initializer in a module the exporter links

Not part of the default build. The design and its proof are sound, but
the module declares an `initialize` that writes a marker file (the path in
`GIN_HOOK_MARKER`, when set), and the executable `gin-export-hooked`
(`GinReject/HookedExport.lean`) is `gin-export` with this design linked
in to compute its vectors. A linked `initialize` runs when the executable
starts, before any check of `gin-export`; it could write forged files and
exit. `scripts/export-examples.sh --check-rejects` checks that the
initializer does run when `gin-export-hooked` starts, and that the export
pipeline, which runs `gin-check-export` (which links no design) first,
refuses the circuit without starting `gin-export-hooked`: the marker is
not written. I run the checker first because once `gin-export-hooked`
has started, a refusal would come too late.
-/

open Gin

namespace Hooked

/-- Runs whenever the module is loaded, and when an executable that links it
starts. -/
initialize do
  if let some path ← IO.getEnv "GIN_HOOK_MARKER" then
    IO.FS.writeFile path "the initializer of GinReject.Hooked ran\n"

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

end Hooked
