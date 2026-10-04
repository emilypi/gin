import Gin.Signal

/-!
Fixture for `GinTest.Compiled`: designs whose compiled code differs from
their definitions, through `@[implemented_by]`, `@[extern]` and `@[csimp]`.
-/

open Gin

namespace GinTest.Fixture.Overrides

/-- The code `incImpl` runs instead of its definition. -/
def incOther (x : BitVec 8) : BitVec 8 := x + 2

/-- Adds one, but its code adds two. -/
@[implemented_by incOther] def incImpl (x : BitVec 8) : BitVec 8 := x + 1

/-- Calls `incImpl` through a project helper. -/
def incHelper (x : BitVec 8) : BitVec 8 := incImpl x

/-- Uses `incImpl`, indirectly. -/
def viaImplementedBy (x : Signal System (BitVec 8)) : Signal System (BitVec 8) :=
  lift incHelper x

/-- Adds one, but its code is foreign. -/
@[extern "gin_test_inc"] def incExtern (x : BitVec 8) : BitVec 8 := x + 1

/-- Uses `incExtern`. -/
def viaExtern (x : Signal System (BitVec 8)) : Signal System (BitVec 8) := lift incExtern x

/-- Adds one. -/
def incSlow (x : BitVec 8) : BitVec 8 := x + 1

/-- Also adds one. -/
def incFast (x : BitVec 8) : BitVec 8 := x + 1

/-- Replaces `incSlow` by `incFast` in code compiled after it. -/
@[csimp] theorem incSlow_eq_incFast : @incSlow = @incFast := rfl

/-- Uses `incSlow`. -/
def viaCsimp (x : Signal System (BitVec 8)) : Signal System (BitVec 8) := lift incSlow x

/-- `BitVec.not`, under another name. -/
def bvNot {n : Nat} (x : BitVec n) : BitVec n := BitVec.not x

/-- Replaces a constant of Lean's core library in code compiled after it. -/
@[csimp] theorem bvNot_eq : @BitVec.not = @bvNot := rfl

/-- Reaches `BitVec.not` only through the core library's `~~~` instance. -/
def viaCoreCsimp (x : Signal System (BitVec 8)) : Signal System (BitVec 8) :=
  lift (fun a => ~~~a) x

/-- Uses none of them. -/
def plain (x : Signal System (BitVec 8)) : Signal System (BitVec 8) := lift (· + 1) x

end GinTest.Fixture.Overrides
