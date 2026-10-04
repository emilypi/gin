import Gin.Export.Modules
import GinTest.Fixture.Initializers
import GinTest.Fixture.InitializersModule

/-!
`initializers` finds every form of IO initializer in a project module, read
as `gin-check-export` reads it (imported without its extensions), and
`shadowedCoreModules` refuses toolchain-named modules loaded from anywhere
but the toolchain's library directory.
-/

open Lean Gin.Export

namespace GinTest.Modules

/-- The fixture module without the module system. -/
def fixture : Name := `GinTest.Fixture.Initializers

/-- The fixture module of the module system, whose private declarations
have private names. -/
def fixtureModule : Name := `GinTest.Fixture.InitializersModule

/-- The initializers found in the fixture modules and the modules they
import (Lean's `Init`, whose own initializers must not be reported), with
the declarations sorted. -/
def fixtureInitializers : IO (Array (Name × Array Name)) := do
  let imports := #[fixture, fixtureModule].map ({ module := · })
  let env ← importModules imports {} (loadExts := false)
  return (initializers env).map fun (m, ds) => (m, ds.qsort Name.lt)

/-- The private name of `n` in the module `m` of the module system. -/
def privateName (m n : Name) : Name := mkPrivateNameCore m (m ++ n)

run_meta do
  let found ← fixtureInitializers
  let expected : Array (Name × Array Name) := #[
    (fixture, #[`viaInitialize, `viaBuiltinInitialize, `viaAttribute, `viaAtInit, `viaAtInitUnit,
      `viaAtBuiltinInit].map (fixture ++ ·)),
    (fixtureModule, #[privateName fixtureModule `viaPrivate, fixtureModule ++ `viaPublic,
      privateName fixtureModule `viaPrivateBuiltin, fixtureModule ++ `viaPublicBuiltin])]
  let expected := expected.map fun (m, ds) => (m, ds.qsort Name.lt)
  unless found == expected do
    throwError "initializers reported {found}, expected {expected}"

/-- The toolchain's library directory, in the synthetic inputs below. -/
def libDir : System.FilePath := "/toolchain/lib/lean"

-- toolchain modules loaded from the toolchain pass; project modules pass
-- wherever they come from
#guard shadowedCoreModules libDir #[
    (`Init.Core, "/toolchain/lib/lean/Init/Core.olean"),
    (`Std.Data, "/toolchain/lib/lean/Std/Data.olean"),
    (`Lean.Meta, "/toolchain/lib/lean/Lean/Meta.olean"),
    (`Lake.Build, "/toolchain/lib/lean/Lake/Build.olean"),
    (`Gin.Signal, "/project/.lake/build/lib/lean/Gin/Signal.olean"),
    (`Initial, "/project/.lake/build/lib/lean/Initial.olean")] == #[]

-- every toolchain root, loaded from the project, is refused
#guard shadowedCoreModules libDir #[
    (`Init.Evil, "/project/.lake/build/lib/lean/Init/Evil.olean"),
    (`Std, "/project/.lake/build/lib/lean/Std.olean"),
    (`Lean.Evil, "/project/.lake/build/lib/lean/Lean/Evil.olean"),
    (`Lake.Evil, "/project/.lake/build/lib/lean/Lake/Evil.olean")] ==
  #[`Init.Evil, `Std, `Lean.Evil, `Lake.Evil]

-- a sibling directory whose name extends the library directory's is not it
#guard shadowedCoreModules libDir #[
    (`Init.Core, "/toolchain/lib/lean2/Init/Core.olean"),
    (`Init.Data, "/toolchain/lib/leanInit/Data.olean")] == #[`Init.Core, `Init.Data]

end GinTest.Modules
