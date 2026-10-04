module

/-!
Fixture for `GinTest.Modules`: IO initializers in a module of the module
system, where a module's own declarations are private unless marked
`public`. The initializers do nothing but allocate.
-/

namespace GinTest.Fixture.InitializersModule

/-- A private `initialize`. -/
initialize viaPrivate : IO.Ref Nat ← IO.mkRef 0

/-- A public `initialize`. -/
public initialize viaPublic : IO.Ref Nat ← IO.mkRef 0

/-- A private `builtin_initialize`. -/
builtin_initialize viaPrivateBuiltin : IO.Ref Nat ← IO.mkRef 0

/-- A public `builtin_initialize`. -/
public builtin_initialize viaPublicBuiltin : IO.Ref Nat ← IO.mkRef 0

end GinTest.Fixture.InitializersModule
