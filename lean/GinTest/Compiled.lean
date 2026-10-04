import Gin.Export.Program
import GinTest.Fixture.NativeReduction
import GinTest.Fixture.Overrides
import GinTest.Util

/-!
The exporter refuses a design whose compiled code, which computes the
vectors, may differ from its definitions: a project constant it runs is
`@[implemented_by]` or `@[extern]`, or a project `@[csimp]` theorem
rewrites a constant it may reach. It also refuses, before translating, a
design whose reduction would run compiled code (`Lean.reduceBool`,
`Lean.reduceNat`).
-/

open Lean Meta Gin.Export GinTest

namespace GinTest.Compiled

/-- An entry for the one-input design `top` of the fixture. -/
def entry (top : Name) : Entry :=
  { name := "dut", module := `GinTest.Fixture.Overrides
    top := `GinTest.Fixture.Overrides ++ top, defs := [`GinTest.Fixture.Overrides ++ top]
    theorem_ := .anonymous, inputs := ["x"], outputs := ["y"], vectors := none }

run_meta do
  expectError (translateTop (entry `viaImplementedBy))
    ["GinTest.Fixture.Overrides.incImpl is marked @[implemented_by]"]
  expectError (translateTop (entry `viaExtern))
    ["GinTest.Fixture.Overrides.incExtern is marked @[extern]"]
  expectError (translateTop (entry `viaCsimp))
    ["GinTest.Fixture.Overrides.incSlow_eq_incFast replaces GinTest.Fixture.Overrides.incSlow"]
  expectError (translateTop (entry `viaCoreCsimp))
    ["GinTest.Fixture.Overrides.bvNot_eq replaces BitVec.not"]
  discard <| translateTop (entry `plain)

-- the same refusals, read as `gin-check-export` reads the modules
run_meta do
  let env ← importModules #[{ module := `GinTest.Fixture.Overrides }] {} (loadExts := false)
  let reasons (top : Name) := compiledOverrides env #[`GinTest.Fixture.Overrides ++ top]
  unless (reasons `viaImplementedBy).size == 1 && (reasons `viaExtern).size == 1 &&
      (reasons `viaCsimp).size == 1 && (reasons `viaCoreCsimp).size == 1 &&
      (reasons `plain).isEmpty do
    throwError "compiledOverrides on the imported fixture: {[`viaImplementedBy, `viaExtern,
      `viaCsimp, `viaCoreCsimp, `plain].map reasons}"

/-- An entry for the one-input design `top` of the native reduction
fixture. -/
def nativeEntry (top : Name) : Entry :=
  { entry .anonymous with
    module := `GinTest.Fixture.NativeReduction
    top := `GinTest.Fixture.NativeReduction ++ top
    defs := [`GinTest.Fixture.NativeReduction ++ top] }

run_meta do
  expectError (translateTop (nativeEntry `viaReduceBool))
    ["GinTest.Fixture.NativeReduction.boolDomain refers to Lean.reduceBool"]
  expectError (translateTop (nativeEntry `viaReduceNat))
    ["GinTest.Fixture.NativeReduction.natDomain refers to Lean.reduceNat"]

-- the same, read as `gin-check-export` reads the modules
run_meta do
  let env ← importModules #[{ module := `GinTest.Fixture.NativeReduction }] {} (loadExts := false)
  let found (top : Name) := nativeReductions env #[`GinTest.Fixture.NativeReduction ++ top]
  unless found `viaReduceBool == #[(`GinTest.Fixture.NativeReduction.boolDomain, ``Lean.reduceBool)]
      && found `viaReduceNat == #[(`GinTest.Fixture.NativeReduction.natDomain, ``Lean.reduceNat)] do
    throwError "nativeReductions on the imported fixture: {found `viaReduceBool}, {found `viaReduceNat}"

end GinTest.Compiled
