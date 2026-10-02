import Lean

/-!
Helpers shared by the exporter tests.
-/

open Lean Meta

namespace GinTest

/-- Does `s` contain `needle`? -/
def containsStr (s needle : String) : Bool := (s.splitOn needle).length > 1

/-- Run `x`, expecting it to fail with a message containing every string
in `needles`. -/
def expectError {α : Type} (x : MetaM α) (needles : List String) : MetaM Unit := do
  let r ← try
      discard x
      pure none
    catch e => pure (some (← e.toMessageData.toString))
  match r with
  | none => throwError "expected an error mentioning {needles}, but it succeeded"
  | some msg =>
    for n in needles do
      unless containsStr msg n do
        throwError "the error does not mention {n}:\n{msg}"

end GinTest
