import Lean
import Gin.Signal

/-!
# Reject fixture: a lemma the kernel never checked

Not part of the default build. `set_option debug.skipKernelTC true` lets a
declaration into the environment without the kernel type-checking it. Here
a meta command adds a "proof" of `False` that way, and the refinement
theorem is derived from it. `collectAxioms` sees no axiom at all, so only
replaying the module through the kernel (`leanchecker`) catches it;
`scripts/export-examples.sh --check-rejects` checks that the kernel replay
of the modules `gin-check-export --list-modules bad_kernel` lists fails and names
this module. It lives outside the `Gin` namespace and the `Gin` module tree
on purpose: the replay covers every module an export loads, whatever its
name.
-/

open Gin Lean Elab Command

namespace BadKernel

/-- The enable counter of `Gin.Examples.Counter`. -/
def bad (en : Signal System Bool) : Signal System (BitVec 8) :=
  mealy (fun s e => (if e then s + 1 else s, s)) 0 en

/-- A false specification: the count ignores the enable input. -/
def spec (_en : Signal System Bool) (t : Nat) : BitVec 8 := BitVec.ofNat 8 t

set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl <| .thmDecl {
  name := `BadKernel.unchecked, levelParams := [], type := mkConst ``False
  value := mkConst ``True.intro }

/-- The false claim, "proved" from the unchecked lemma `BadKernel.unchecked`. -/
theorem bad_correct : ∀ en t, bad en t = spec en t := fun _ _ => unchecked.elim

end BadKernel
