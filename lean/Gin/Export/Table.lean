import Gin
import Gin.Export.Entries

/-!
# Export table

`entries` with their vector sources. Computing vectors runs the compiled
designs, so this module links every design into `gin-export`, and their
`initialize` declarations run when it starts; `scripts/export-examples.sh`
therefore runs `gin-check-export`, which links no design, first.
-/

namespace Gin.Export

/-- Attach vector sources to entries by name. -/
def withVectors (es : List Entry) (sources : List (String × VectorSource)) : List Entry :=
  es.map fun e => { e with vectors := sources.lookup e.name }

/-- The vector source of each shipped example. -/
def vectorSources : List (String × VectorSource) := [
  ("counter", .of1 Counter.counter enableRuns),
  ("detector", .of1 Detector.detector patternBits),
  ("mac", .of2 Mac.mac largeOperands)]

/-- Every exportable circuit. -/
def table : List Entry := withVectors entries vectorSources

end Gin.Export
