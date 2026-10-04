/-!
Fixture for `GinTest.Compiled`: code that may run arbitrary IO when a
program linking this module starts, although no design uses it. Nothing
here runs: GinTest is never linked into an executable.
-/

namespace GinTest.Fixture.LinkedCode

/-- Would run IO when evaluated, as a closed term, at start-up. -/
unsafe def viaUnsafeIO : Nat :=
  match unsafeIO (IO.getEnv "GIN_TEST_LINKED_CODE") with
  | .ok _ => 0
  | .error _ => 1

/-- Foreign code, declared without `unsafe`. -/
@[extern "gin_test_linked_code"] opaque foreign : @& String → Unit → Nat

/-- A safe closed term that calls foreign code. -/
def viaExtern : Nat := foreign "x" ()

/-- Runs a function other than its definition. -/
def other (n : Nat) : Nat := n + 1

/-- Implemented by `other`. -/
@[implemented_by other] def viaImplementedBy (n : Nat) : Nat := n

/-- A `partial` definition, implemented by an `unsafe` twin. -/
partial def viaPartial (n : Nat) : Nat := if n = 0 then 0 else viaPartial (n - 1)

/-- Structural recursion: compiled from an `_unsafe_rec` twin, but not
`partial`. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => n + 1 + sumTo n

/-- None of them. -/
def plain : Nat := 3

end GinTest.Fixture.LinkedCode
