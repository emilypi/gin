import Gin.Signal

/-!
# Reject fixture: a proof by `sorry`

Not part of the default build. The exporter must refuse this design and
name `sorryAx`; `scripts/export-examples.sh --check-rejects` checks that it
does and that nothing is written.
-/

open Gin

namespace Bad

/-- The enable counter of `Gin.Examples.Counter`. -/
def bad (en : Signal System Bool) : Signal System (BitVec 8) :=
  mealy (fun s e => (if e then s + 1 else s, s)) 0 en

/-- A false claim (the count does not ignore the enable input), "proved"
with `sorry`. -/
theorem bad_correct : ∀ en t, bad en t = BitVec.ofNat 8 t := by sorry

end Bad
