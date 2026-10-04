import Gin.Signal

/-!
# Reject fixture: an `unsafe` closed term in a design module

Not part of the default build. The design and its proof are sound, but
the module also declares `cached`, an `unsafe` closed term that no design
uses and that runs IO through `unsafeIO`. Lean evaluates the closed terms
of every module linked into an executable when it starts, so linked into
`gin-export` it would run before any check and could write a forged
certificate (here it only writes a marker, at the path in
`GIN_HOOK_MARKER`). `gin-check-export` must refuse the module, naming the
constant, and so must `gin-export`. `scripts/export-examples.sh
--check-rejects` checks the refusals and that nothing is written.
-/

open Gin

namespace BadUnsafeIO

/-- Writes a marker file when `GIN_HOOK_MARKER` is set. -/
def mark : IO Nat := do
  if let some path ← IO.getEnv "GIN_HOOK_MARKER" then
    IO.FS.writeFile path "the closed term of GinReject.BadUnsafeIO ran\n"
  return 0

/-- Runs `mark` when evaluated: at start-up, in an executable that links this
module. -/
unsafe def cached : Nat :=
  match unsafeIO mark with
  | .ok n => n
  | .error _ => 1

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

end BadUnsafeIO
