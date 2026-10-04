import Gin.Export.Main
import Gin.Export.Table
import GinReject.Hooked

/-! Root of `gin-export-hooked`, a reject fixture: `gin-export` with the
design of `GinReject.Hooked`, whose module declares an `initialize`,
linked in to compute its vectors (see `GinReject/Hooked.lean`). -/

open Gin.Export

/-- Entry point of `lake exe gin-export-hooked`. -/
unsafe def main (args : List String) : IO UInt32 :=
  Gin.Export.main (withVectors entries (vectorSources ++ [("hooked", .of1 Hooked.bad enableRuns)]))
    defaultExports args
