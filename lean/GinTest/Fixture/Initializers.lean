/-!
Fixture for `GinTest.Modules`: one declaration for every way a module can
register an IO initializer. The initializers do nothing but allocate.
-/

namespace GinTest.Fixture.Initializers

/-- `initialize` with a result. -/
initialize viaInitialize : IO.Ref Nat ← IO.mkRef 0

/-- `builtin_initialize` with a result. -/
builtin_initialize viaBuiltinInitialize : IO.Ref Nat ← IO.mkRef 0

/-- The action of the attribute forms below. -/
def mkZero : IO Nat := pure 0

/-- Registered after its declaration by `attribute [init]`. -/
opaque viaAttribute : Nat

attribute [init mkZero] viaAttribute

/-- `@[init act]`. -/
@[init mkZero] opaque viaAtInit : Nat

/-- `@[init]` on an `IO Unit` action. -/
@[init] def viaAtInitUnit : IO Unit := pure ()

/-- `@[builtin_init act]`. -/
@[builtin_init mkZero] opaque viaAtBuiltinInit : Nat

end GinTest.Fixture.Initializers
