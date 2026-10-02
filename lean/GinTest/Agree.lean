import Lean
import Gin.Export.Encode
import Gin.Export.Program
import GinTest.IrEval

/-!
Translation validation for tests: translate a circuit, compute its vectors
by running the Lean definition, and check the reference evaluator agrees.
-/

open Lean Meta Gin.Export

namespace GinTest

/-- An entry for a test circuit. Its theorem is never looked at by
`translateTop`. -/
def testEntry (top : Name) (inputs outputs : List String) (src : VectorSource)
    (defs : List Name := [top]) (seed : UInt64 := 7) : Entry :=
  { name := "dut", module := .anonymous, top, defs, theorem_ := .anonymous,
    inputs, outputs, vectors := some src, seed }

/-- Translate an entry, compute its vectors by running the Lean definition,
and check that the reference evaluator agrees with them on every cycle. -/
def checkAgrees (e : Entry) : MetaM Unit := do
  let (top, defs) ← translateTop e
  let vecs ← ofExcept (exportVectors e top)
  match IrEval.agrees top defs vecs with
  | .ok () => pure ()
  | .error msg => throwError "{e.top}: IR and Lean disagree: {msg}"

/-- The compact IR of a translated definition. -/
def irOf (n : Name) (exported : List Name := []) : MetaM String := do
  let d ← translateDef n (exported.foldl NameSet.insert {})
  return d.body.toDoc.compact

end GinTest
