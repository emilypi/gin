import Gin
import Gin.Export.Program

/-!
# Export table

The circuits `gin-export` knows about. Port names are given here explicitly
rather than taken from Lean binder names: they are part of the generated
hardware interface.

The two reject fixtures are listed so the refusal path can be exercised
(`scripts/export-examples.sh --check-rejects`); their modules are not part
of the default build and they have no vector source, so they can never be
written.
-/

namespace Gin.Export

/-- Every exportable circuit. -/
def table : List Entry := [
  { name := "counter", module := `Gin
    top := ``Counter.counter, defs := [``Counter.counter]
    theorem_ := ``Counter.counter_correct
    inputs := ["en"], outputs := ["count"]
    vectors := some (.of1 Counter.counter), seed := 1 },
  { name := "detector", module := `Gin
    top := ``Detector.detector, defs := [``Detector.step, ``Detector.detector]
    theorem_ := ``Detector.detector_correct
    inputs := ["b"], outputs := ["hit"]
    vectors := some (.of1 Detector.detector), seed := 3 },
  { name := "mac", module := `Gin
    top := ``Mac.mac, defs := [``Mac.mac]
    theorem_ := ``Mac.mac_correct
    inputs := ["x", "y"], outputs := ["acc"]
    vectors := some (.of2 Mac.mac), seed := 2 },
  { name := "bad", module := `Gin.Examples.Bad
    top := `Bad.bad, defs := [`Bad.bad]
    theorem_ := `Bad.bad_correct
    inputs := ["en"], outputs := ["count"]
    vectors := none },
  { name := "bad_native", module := `Gin.Examples.BadNative
    top := `BadNative.bad, defs := [`BadNative.bad]
    theorem_ := `BadNative.bad_correct
    inputs := ["en"], outputs := ["count"]
    vectors := none }]

/-- The circuits exported when no names are given. -/
def defaultExports : List String := ["counter", "detector", "mac"]

end Gin.Export
