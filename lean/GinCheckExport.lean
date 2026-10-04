import Gin.Export.Entries
import Gin.Export.Main

/-! Root of `gin-check-export`. It imports no design, so no code of a design
is linked into it or runs in it. -/

/-- Entry point of `lake exe gin-check-export`. -/
def main (args : List String) : IO UInt32 :=
  Gin.Export.checkMain Gin.Export.entries Gin.Export.defaultExports args
