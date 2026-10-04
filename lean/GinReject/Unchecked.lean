import Lean

/-!
# Reject fixture: a helper module the kernel never checked

Not part of the default build. A meta command adds a "proof" of `False`
under `debug.skipKernelTC`, so the kernel never type-checks it.
`GinReject.BadImport` derives a refinement theorem from it; only replaying
this module, which the design imports, through the kernel catches it.
-/

open Lean Elab Command

set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl <| .thmDecl {
  name := `GinReject.Unchecked.lemma, levelParams := [], type := mkConst ``False
  value := mkConst ``True.intro }
