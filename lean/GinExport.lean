import Gin.Export.Main
import Gin.Export.Table

/-! Root of `gin-export`. It links every design (`Gin.Export.Table`); run
`gin-check-export` first (`scripts/export-examples.sh`). -/

/-- Entry point of `lake exe gin-export`. -/
unsafe def main (args : List String) : IO UInt32 :=
  Gin.Export.main Gin.Export.table Gin.Export.defaultExports args
