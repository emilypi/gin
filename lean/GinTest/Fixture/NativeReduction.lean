import Gin.Signal

/-!
Fixture for `GinTest.Compiled`: designs whose clock domain reduces only by
running compiled code, through `Lean.reduceBool` and `Lean.reduceNat`.
-/

open Gin

namespace GinTest.Fixture.NativeReduction

/-- Code that `Lean.reduceBool` runs. -/
def boolHook : Bool := true

set_option linter.deprecated false in
/-- A domain whose name reduces only by running `boolHook`. -/
def boolDomain : Domain := ⟨cond (Lean.reduceBool boolHook) "Hooked" "Hooked", 10000⟩

/-- A design in `boolDomain`. -/
def viaReduceBool (x : Signal boolDomain (BitVec 8)) : Signal boolDomain (BitVec 8) :=
  lift (· + 1) x

/-- Code that `Lean.reduceNat` runs. -/
def natHook : Nat := 10000

set_option linter.deprecated false in
/-- A domain whose period reduces only by running `natHook`. -/
def natDomain : Domain := ⟨"Hooked", Lean.reduceNat natHook⟩

/-- A design in `natDomain`. -/
def viaReduceNat (x : Signal natDomain (BitVec 8)) : Signal natDomain (BitVec 8) :=
  lift (· + 1) x

end GinTest.Fixture.NativeReduction
