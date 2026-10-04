import Lean
import Gin.Signal

/-!
# Fixture: a specification disguised by an unexpander

Not part of the default build. The theorem compares the implementation
with `specR`, which says the output is always 0, but an `app_unexpander`
makes Lean's pretty printer show `specR en t` as `BadUnexpander.spec en t`,
the honest enable-counter specification. The exporter does not refuse
this design: its certificate is rendered by a printer that ignores
unexpanders, so it names `specR` and lists `specR`'s definition, and a
reviewer sees the real claim. `GinReject.UnexpanderCheck` checks this.
-/

open Gin

namespace BadUnexpander

/-- An implementation that ignores its input and always outputs 0. -/
def bad (en : Signal System Bool) : Signal System (BitVec 8) :=
  lift (fun _ => (0 : BitVec 8)) en

/-- The specification a reader expects: the number of enabled cycles
strictly before `t`, modulo 2^8. -/
def spec (en : Signal System Bool) (t : Nat) : BitVec 8 :=
  BitVec.ofNat 8 ((List.range t).countP (fun i => en i))

/-- The specification actually proved: always 0. -/
def specR (_en : Signal System Bool) (_t : Nat) : BitVec 8 := 0

open Lean PrettyPrinter in
/-- Makes Lean's pretty printer show `specR` as `spec`. -/
@[app_unexpander specR] def unexpandSpecR : Unexpander
  | `($_ $a $b) => `($(mkIdent `BadUnexpander.spec) $a $b)
  | _ => throw ()

/-- Pretty-printed, this reads `bad en t = BadUnexpander.spec en t`. -/
theorem bad_correct : ∀ en t, bad en t = specR en t := fun _ _ => rfl

end BadUnexpander
