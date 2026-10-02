import Gin.Export.Main
import Gin.Export.Table

/-- Entry point of `lake exe gin-export`. -/
unsafe def main (args : List String) : IO UInt32 :=
  Gin.Export.main Gin.Export.table Gin.Export.defaultExports args
