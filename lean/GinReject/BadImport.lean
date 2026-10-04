import Gin.Signal
import GinReject.Unchecked

/-!
# Reject fixture: a design that imports an unchecked module

Not part of the default build. Written like a shipped example (namespace
`Gin.Examples.Forged`), but its refinement theorem follows from
`GinReject.Unchecked.lemma`, a proof of `False` that the kernel never
checked in a separate module. `collectAxioms` sees no axiom, and the
module itself replays cleanly; only replaying every module the export
loads catches it. `scripts/export-examples.sh --check-rejects` checks that
the kernel replay of the modules listed by `gin-export --list-modules
bad_import` fails on `GinReject.Unchecked`, and that the same design, not
marked as a reject fixture (`forged`), is refused for loading `GinReject`
modules.
-/

open Gin

namespace Gin.Examples.Forged

/-- The enable counter of `Gin.Examples.Counter`. -/
def counter (en : Signal System Bool) : Signal System (BitVec 8) :=
  mealy (fun s e => (if e then s + 1 else s, s)) 0 en

/-- A false specification: the count ignores the enable input. -/
def spec (_en : Signal System Bool) (t : Nat) : BitVec 8 := BitVec.ofNat 8 t

/-- The false claim, "proved" from the unchecked lemma. -/
theorem counter_correct : ∀ en t, counter en t = spec en t :=
  fun _ _ => GinReject.Unchecked.lemma.elim

end Gin.Examples.Forged
