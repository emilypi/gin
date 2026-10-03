import Lean

/-!
# Which module a constant comes from

The exporter treats the modules of an imported environment in three groups:

* the Lean toolchain: modules under `Init`, `Std`, `Lean` and `Lake`, which
  must be loaded from the toolchain's own library directory;
* gin's signal DSL, the module `Gin.Signal`;
* everything else, the project: the designs, their specifications and any
  helper modules they import.

The certificate leaves out the definitions of Lean's core library (`Init`,
`Std`, `Lean`) and of the DSL, and shows every other definition a
specification depends on. A project module named like a core module could
therefore hide a definition from the reviewer; `shadowedCoreModules` finds
such modules so that the exporter can refuse them.

Building a design runs its code: `#eval` and macros run during `lake build`,
and the `initialize` declarations of every module linked into `gin-export`
run when it starts. `initializers` lists the IO initializers that project
modules register, so that the exporter can refuse to export a design that
has any (see `lean/README.md`, "Trust").
-/

open Lean

namespace Gin.Export

/-- Top-level namespaces of the modules shipped with Lean. -/
def toolchainRoots : List Name := [`Init, `Std, `Lean, `Lake]

/-- Top-level namespaces of Lean's core library, whose definitions the
certificate does not show. -/
def coreLibraryRoots : List Name := [`Init, `Std, `Lean]

/-- Is `m` named like a module shipped with Lean? -/
def isToolchainModule (m : Name) : Bool := toolchainRoots.contains m.getRoot

/-- Is `m` a module of Lean's core library? -/
def isCoreLibraryModule (m : Name) : Bool := coreLibraryRoots.contains m.getRoot

/-- The module of gin's signal DSL. -/
def dslModule : Name := `Gin.Signal

/-- The module that declares `c`, or `none` for a constant of the current
module (which is part of the project). -/
def moduleOf? (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).bind fun i => env.header.moduleNames[i.toNat]?

/-- Is `c` declared in Lean's core library? -/
def isCoreLibraryConst (env : Environment) (c : Name) : Bool :=
  (moduleOf? env c).any isCoreLibraryModule

/-- Is `c` declared in gin's signal DSL? -/
def isDslConst (env : Environment) (c : Name) : Bool :=
  moduleOf? env c == some dslModule

/-- Project modules named like toolchain modules, given each imported
module with the file it was loaded from. A toolchain module must come from
`libDir`, the toolchain's library directory. -/
def shadowedCoreModules (libDir : System.FilePath) (modules : Array (Name × System.FilePath)) :
    Array Name :=
  let prefix_ := libDir.toString ++ "/"
  modules.filterMap fun (m, file) =>
    if isToolchainModule m && !file.toString.startsWith prefix_ then some m else none

/-- The IO initializers (`initialize`, `builtin_initialize`, `@[init]`,
`@[builtin_init]`) that each imported project module registers, in import
order. Reads the entries the modules exported, so it works on an
environment imported without loading its extensions, in which no
initializer has run. -/
def initializers (env : Environment) : Array (Name × Array Name) := Id.run do
  let mut out := #[]
  for h : i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if isToolchainModule m then continue
    let idx : ModuleIdx := i
    let mut decls : Array Name := #[]
    for attr in [regularInitAttr, builtinInitAttr] do
      for (d, _) in attr.ext.getModuleEntries env idx ++ attr.ext.getModuleIREntries env idx do
        unless decls.contains d do
          decls := decls.push d
    unless decls.isEmpty do
      out := out.push (m, decls)
  return out

end Gin.Export
