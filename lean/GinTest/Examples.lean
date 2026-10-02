import Gin.Export.Table
import GinTest.Agree
import GinTest.Util

/-!
The shipped export table: each example certifies, translates to IR that
agrees with its Lean vectors on all 64 cycles, and has the interface the
rest of gin expects. Also covers the top-entity checks.
-/

open Lean Meta Gin.Export GinTest

namespace GinTest.Examples

/-- The entry of the export table with the given name. -/
def entry (n : String) : MetaM Entry := do
  let some e := table.find? (·.name == n) | throwError "no table entry {n}"
  return e

/-- A port as `(name, type)`. -/
def portSig (p : Port) : String × Ty := (p.name, p.type)

end GinTest.Examples

open GinTest.Examples in
run_meta do
  unless defaultExports == ["counter", "detector", "mac"] do
    throwError "unexpected default exports {defaultExports}"
  for n in defaultExports do
    let e ← entry n
    let p ← exportProgram e
    let v ← ofExcept (exportVectors e p.top)
    -- the IR computes what the Lean definition computes
    match IrEval.agrees p.top p.defs v with
    | .ok () => pure ()
    | .error msg => throwError "{n}: {msg}"
    unless v.cycles.size == 64 && p.top.name == n && v.top == n do
      throwError "{n}: wrong name or cycle count"
    unless p.top.domain == { name := "System", periodPs := 10000 } do
      throwError "{n}: wrong domain"
    unless p.producer.tool == "gin-export" && p.producer.leanVersion == Lean.versionString do
      throwError "{n}: wrong producer"

-- Names and ports are exactly the ones the Haskell side and the HDL interface
-- expect.
run_meta do
  let expect (n : String) (defs : List String) (thm : String) (ins outs : List (String × Ty)) :
      MetaM Unit := do
    let p ← exportProgram (← GinTest.Examples.entry n)
    unless p.defs.map (·.name) == defs && p.top.def_ == defs.getLast! do
      throwError "{n}: definitions {p.defs.map (·.name)}"
    unless p.certificate.theorem_ == thm do throwError "{n}: theorem {p.certificate.theorem_}"
    unless p.top.inputs.map GinTest.Examples.portSig == ins do throwError "{n}: inputs"
    unless p.top.outputs.map GinTest.Examples.portSig == outs do throwError "{n}: outputs"
  expect "counter" ["Counter.counter"] "Counter.counter_correct" [("en", .bool)] [("count", .bv 8)]
  expect "detector" ["Detector.step", "Detector.detector"] "Detector.detector_correct"
    [("b", .bool)] [("hit", .bool)]
  expect "mac" ["Mac.mac"] "Mac.mac_correct" [("x", .bv 8), ("y", .bv 8)] [("acc", .bv 16)]

-- The seeded inputs exercise the interesting behaviour: both enable values,
-- several detector hits including an overlapping one, and accumulator
-- wrap-around.
run_meta do
  let rows (n : String) : MetaM (Array Cycle) := do
    let e ← GinTest.Examples.entry n
    return (← ofExcept (exportVectors e (← exportProgram e).top)).cycles
  let counter ← rows "counter"
  unless counter.any (·.inputs == [.bool true]) && counter.any (·.inputs == [.bool false]) do
    throwError "counter inputs are constant"
  let detector ← rows "detector"
  let hits := (List.range 64).filter fun t => detector[t]!.outputs == [.bool true]
  unless hits.length ≥ 3 && (hits.zip hits.tail).any (fun (a, b) => b == a + 2) do
    throwError "detector hits {hits}: expected at least three, two of them overlapping"
  let acc := (← rows "mac").map fun c => match c.outputs with | [.bv _ v] => v | _ => 0
  unless (List.range 63).any fun t => acc[t + 1]! < acc[t]! do
    throwError "the accumulator never wraps around"

-- Hardware identifiers.
#guard isLegalIdent "counter" && isLegalIdent "a1_b2" && isLegalIdent "x"
#guard !isLegalIdent "" && !isLegalIdent "Counter" && !isLegalIdent "1a" && !isLegalIdent "a__b"
#guard !isLegalIdent "a_" && !isLegalIdent "gin_x" && !isLegalIdent "a-b"
#guard !isLegalIdent (String.ofList (List.replicate 65 'a')) && isLegalIdent (String.ofList (List.replicate 64 'a'))

-- Output products are split along the right-nested spine.
#guard splitOutputs 1 (.prod [.bool, .bool]) == some [.prod [.bool, .bool]]
#guard splitOutputs 2 (.prod [.bool, .bv 3]) == some [.bool, .bv 3]
#guard splitOutputs 3 (.prod [.bool, .prod [.bv 3, .bool]]) == some [.bool, .bv 3, .bool]
#guard splitOutputs 3 (.prod [.prod [.bool, .bv 3], .bool]) == none
#guard splitOutputs 0 .bool == none

-- Interface errors in an entry are refused, naming the problem.
run_meta do
  let base ← GinTest.Examples.entry "counter"
  expectError (translateTop { base with name := "Counter" }) ["top name", "Counter"]
  expectError (translateTop { base with inputs := ["clk"] }) ["clk"]
  expectError (translateTop { base with outputs := ["en"] }) ["not pairwise distinct"]
  expectError (translateTop { base with inputs := [] }) ["takes 1 signals but 0 input names"]
  expectError (translateTop { base with outputs := ["a", "b"] }) ["does not have 2 output components"]
  expectError (translateTop { base with defs := [``Mac.mac] }) ["do not include the top definition"]
  let p ← exportProgram base
  -- a vector source for another interface is refused
  match exportVectors { base with vectors := some (.of2 Mac.mac) } p.top with
  | .ok _ => throwError "a mismatched vector source was accepted"
  | .error msg => unless containsStr msg "does not match the port types" do throwError msg
  match exportVectors { base with vectors := none } p.top with
  | .ok _ => throwError "an entry without a vector source was exported"
  | .error msg => unless containsStr msg "no vector source" do throwError msg
