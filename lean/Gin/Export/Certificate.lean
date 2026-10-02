import Lean
import Gin.Export.Ir

/-!
# Proof certificates

The exporter only writes a design whose refinement theorem, and every
exported definition, depends on no axioms beyond the three standard ones of
Lean's logic. In particular it refuses proofs that use `sorry` (`sorryAx`)
and proofs by `native_decide` or `bv_decide`, which trust the compiler
through `Lean.ofReduceBool` or generated `<theorem>._native.*` axioms.

`collectAxioms` reads proof terms but cannot tell whether the kernel
actually checked them (`set_option debug.skipKernelTC`), so the export
script also replays every module through `leanchecker` before exporting.
-/

open Lean Meta

namespace Gin.Export

/-- The axioms a certified design may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Why an axiom outside the allowed list typically shows up. -/
def axiomHint (a : Name) : String :=
  if a == ``sorryAx then " (the proof is incomplete: it uses sorry)"
  else if (a.toString.splitOn "._native.").length > 1 || a == ``Lean.ofReduceBool
      || a == ``Lean.ofReduceNat || a == ``Lean.trustCompiler then
    " (native_decide and bv_decide trust the compiler, not the kernel)"
  else ""

/-- The axioms `n` depends on, sorted; an error naming every axiom outside
`allowedAxioms`. -/
def checkedAxioms (what : String) (n : Name) : MetaM (Array Name) := do
  let axs := (← collectAxioms n).qsort (·.toString < ·.toString)
  let bad := axs.filter (!allowedAxioms.contains ·)
  unless bad.isEmpty do
    let names := ", ".intercalate (bad.toList.map fun a => a.toString ++ axiomHint a)
    throwError "{what} {n} depends on disallowed axioms: {names}; only propext, Classical.choice and Quot.sound are allowed"
  return axs

/-- The certificate for refinement theorem `thm` about the top definition
`top`, whose implementation consists of `defs`. Fails if any of them uses
a disallowed axiom, if the theorem's statement does not mention `top`, or
if the statement does not pretty-print in full. -/
def certify (thm top : Name) (defs : List Name) : MetaM Certificate := do
  let some ci := (← getEnv).find? thm | throwError "unknown theorem {thm}"
  let .thmInfo _ := ci | throwError "{thm} is not a theorem"
  let axs ← checkedAxioms "theorem" thm
  let mut impl : Array Name := #[]
  for d in defs do
    impl := impl ++ (← checkedAxioms "definition" d)
  unless ci.type.getUsedConstants.contains top do
    throwError "theorem {thm} does not mention {top}: its statement must be about the exported design"
  let statement := toString (← ppExpr ci.type)
  if statement.contains '⋯' then
    throwError "the statement of {thm} pretty-prints with elided terms (⋯), so it cannot be reviewed: {statement}"
  let implAxioms := (impl.qsort (·.toString < ·.toString)).toList.eraseDups
  return {
    theorem_ := thm.toString
    statement
    axioms := axs.toList.map (·.toString)
    implAxioms := implAxioms.map (·.toString) }

end Gin.Export
