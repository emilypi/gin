import Gin
import Gin.Export.Program

/-!
# Export table

The circuits `gin-export` knows about. Port names are given here explicitly
rather than taken from Lean binder names: they are part of the generated
hardware interface.

The reject fixtures (`GinReject`) are listed so the refusal paths can be
exercised (`scripts/export-examples.sh --check-rejects`); their modules are
not part of the default build and they have no vector source, so they can
never be written. Only an entry marked `fixture` may load a `GinReject`
module.
-/

namespace Gin.Export

/-- Every exportable circuit. -/
def table : List Entry := [
  { name := "counter", module := `Gin
    top := ``Counter.counter, defs := [``Counter.counter]
    theorem_ := ``Counter.counter_correct
    inputs := ["en"], outputs := ["count"]
    vectors := some (.of1 Counter.counter enableRuns), seed := 1 },
  { name := "detector", module := `Gin
    top := ``Detector.detector, defs := [``Detector.step, ``Detector.detector]
    theorem_ := ``Detector.detector_correct
    inputs := ["b"], outputs := ["hit"]
    vectors := some (.of1 Detector.detector patternBits), seed := 3 },
  { name := "mac", module := `Gin
    top := ``Mac.mac, defs := [``Mac.mac]
    theorem_ := ``Mac.mac_correct
    inputs := ["x", "y"], outputs := ["acc"]
    vectors := some (.of2 Mac.mac largeOperands), seed := 2 },
  { name := "bad", module := `GinReject.Bad
    top := `Bad.bad, defs := [`Bad.bad]
    theorem_ := `Bad.bad_correct
    inputs := ["en"], outputs := ["count"]
    vectors := none, fixture := true },
  { name := "bad_native", module := `GinReject.BadNative
    top := `BadNative.bad, defs := [`BadNative.bad]
    theorem_ := `BadNative.bad_correct
    inputs := ["en"], outputs := ["count"]
    vectors := none, fixture := true },
  { name := "bad_init", module := `GinReject.BadInit
    top := `BadInit.bad, defs := [`BadInit.bad]
    theorem_ := `BadInit.bad_correct
    inputs := ["en"], outputs := ["count"]
    vectors := none, fixture := true },
  { name := "bad_tautology", module := `GinReject.BadShape
    top := `BadShape.bad, defs := [`BadShape.bad]
    theorem_ := `BadShape.tautology
    inputs := ["en"], outputs := ["count"]
    vectors := none, fixture := true },
  { name := "bad_at_zero", module := `GinReject.BadShape
    top := `BadShape.bad, defs := [`BadShape.bad]
    theorem_ := `BadShape.at_zero
    inputs := ["en"], outputs := ["count"]
    vectors := none, fixture := true },
  { name := "bad_calls_impl", module := `GinReject.BadShape
    top := `BadShape.bad, defs := [`BadShape.bad]
    theorem_ := `BadShape.calls_impl
    inputs := ["en"], outputs := ["count"]
    vectors := none, fixture := true },
  { name := "bad_or_true", module := `GinReject.BadShape
    top := `BadShape.bad, defs := [`BadShape.bad]
    theorem_ := `BadShape.or_true
    inputs := ["en"], outputs := ["count"]
    vectors := none, fixture := true },
  { name := "bad_kernel", module := `GinReject.BadKernel
    top := `BadKernel.bad, defs := [`BadKernel.bad]
    theorem_ := `BadKernel.bad_correct
    inputs := ["en"], outputs := ["count"]
    vectors := none, fixture := true },
  { name := "bad_import", module := `GinReject.BadImport
    top := `Gin.Examples.Forged.counter, defs := [`Gin.Examples.Forged.counter]
    theorem_ := `Gin.Examples.Forged.counter_correct
    inputs := ["en"], outputs := ["count"]
    vectors := none, fixture := true },
  -- the same design, not marked as a reject fixture: refused for importing
  -- GinReject modules
  { name := "forged", module := `GinReject.BadImport
    top := `Gin.Examples.Forged.counter, defs := [`Gin.Examples.Forged.counter]
    theorem_ := `Gin.Examples.Forged.counter_correct
    inputs := ["en"], outputs := ["count"]
    vectors := none }]

/-- The circuits exported when no names are given. -/
def defaultExports : List String := ["counter", "detector", "mac"]

end Gin.Export
