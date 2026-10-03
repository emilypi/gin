import Lean
import Gin.Export.Encode
import Gin.Export.Modules
import Gin.Export.Program

/-!
# The `gin-export` command

Imports the compiled Lean environment, exports each requested circuit in
memory, and writes the files only once every circuit has passed every
check, including the limits gin enforces on the files it reads, so a
refusal never leaves partial output behind.

The environment is imported twice. The first import reads the modules as
data, without loading environment extensions: no initializer of an imported
module runs, and no delaborator, unexpander or other code a module
registers is available. The exporter refuses project modules that register
IO initializers or are named like toolchain modules, then checks and
renders every certificate in this environment; `collectAxioms` walks the
proofs themselves here instead of trusting axiom summaries stored by the
modules. Only then are the modules imported again with their extensions,
which the translator needs (instances, pattern-match compilation), and the
designs translated. Messages are printed raw (`pp.raw`), so that no
delaborator of a design runs while an error is reported.
-/

open Lean Meta System

namespace Gin.Export

/-- Command-line help. -/
def usage : String :=
  "usage: lake exe gin-export [--out DIR] [NAME ...]\n\n" ++
  "Writes DIR/NAME/NAME.gin.json and DIR/NAME/NAME.vectors.json for each named circuit\n" ++
  "(default: the shipped examples; DIR defaults to examples). Run it through `lake exe`\n" ++
  "so that the Lean search path is set. Nothing is written unless every named circuit\n" ++
  "exports successfully."

/-- Parsed command line. -/
structure CliOptions where
  /-- Output directory. -/
  out : FilePath := "examples"
  /-- Circuits to export; empty means the defaults. -/
  names : List String := []
  /-- Print usage and exit. -/
  help : Bool := false

/-- Parse the command line. -/
def parseArgs : List String → CliOptions → Except String CliOptions
  | [], o => .ok { o with names := o.names.reverse }
  | "--out" :: dir :: rest, o => parseArgs rest { o with out := dir }
  | ["--out"], _ => .error "--out needs a directory"
  | "--help" :: rest, o | "-h" :: rest, o => parseArgs rest { o with help := true }
  | a :: rest, o =>
    if a.startsWith "-" then .error s!"unknown option {a}"
    else parseArgs rest { o with names := a :: o.names }

/-- Run a `MetaM` computation in an imported environment, with messages
printed raw. -/
def runMeta {α : Type} (env : Environment) (x : MetaM α) : IO α := do
  let opts := pp.raw.set {} true
  let (a, _, _) ← x.toIO { fileName := "gin-export", fileMap := default, options := opts } { env }
  return a

/-- Refuse an environment with a project module named like a toolchain
module (it could hide definitions from the certificate) or a project module
that registers IO initializers (`lean/README.md`, "Trust"). -/
def checkModules (env : Environment) : IO Unit := do
  let libDir := (← findSysroot) / "lib" / "lean"
  let files ← env.header.moduleNames.filter isToolchainModule |>.mapM fun m =>
    return (m, ← findOLean m)
  for m in shadowedCoreModules libDir files do
    throw <| IO.userError s!"module {m} is named like a module of the Lean toolchain but was not \
      loaded from {libDir}; refusing to export, because the certificate trusts such modules"
  for (m, decls) in initializers env do
    let names := ", ".intercalate (decls.toList.map toString)
    throw <| IO.userError s!"module {m} registers IO initializers ({names}), which run code \
      whenever the module is loaded; refusing to export it (see lean/README.md, \"Trust\")"

/-- Write a file by renaming a temporary sibling into place. -/
def writeAtomically (path : FilePath) (contents : String) : IO Unit := do
  let tmp := path.addExtension "tmp"
  IO.FS.writeFile tmp contents
  IO.FS.rename tmp path

/-- Export the named circuits of `table` (or `defaults`) as the command
line says. Exit code 0 on success, 1 if any circuit is refused, 2 on a
usage error. -/
unsafe def main (table : List Entry) (defaults : List String) (args : List String) :
    IO UInt32 := do
  let opts ← match parseArgs args {} with
    | .ok o => pure o
    | .error msg =>
      IO.eprintln s!"gin-export: {msg}\n{usage}"
      return 2
  if opts.help then
    IO.println usage
    return 0
  let names := (if opts.names.isEmpty then defaults else opts.names).eraseDups
  let mut entries := #[]
  for n in names do
    match table.find? (·.name == n) with
    | some e => entries := entries.push e
    | none =>
      IO.eprintln s!"gin-export: unknown circuit {n}; known: {" ".intercalate (table.map (·.name))}"
      return 2
  let mut writing := false
  try
    initSearchPath (← findSysroot)
    let imports := (entries.map (·.module)).toList.eraseDups.toArray.map ({ module := · })
    -- the modules as data: no initializer runs, no extension is loaded
    let data ← importModules imports {} (loadExts := false)
    checkModules data
    let mut certificates := #[]
    for e in entries do
      try
        certificates := certificates.push (← runMeta data (certifyEntry e))
      catch err =>
        throw <| IO.userError s!"{e.name}: {err}"
    -- the modules with their extensions, for the translator
    enableInitializersExecution
    let env ← importModules imports {} (loadExts := true)
    let mut outputs := #[]
    for e in entries, certificate in certificates do
      try
        let (top, defs) ← runMeta env (translateTop e)
        let prog : Program := { producer, top, defs, certificate }
        let vecs ← IO.ofExcept (exportVectors e prog.top)
        let docs := [(s!"{e.name}.gin.json", prog.toDoc), (s!"{e.name}.vectors.json", vecs.toDoc)]
        let files ← docs.mapM fun (file, doc) =>
          match renderFile doc with
          | .ok text => pure (file, text)
          | .error msg => throw <| IO.userError s!"{file}: {msg}"
        outputs := outputs.push (e, files)
      catch err =>
        throw <| IO.userError s!"{e.name}: {err}"
    writing := true
    for (e, files) in outputs do
      let dir := opts.out / e.name
      IO.FS.createDirAll dir
      for (file, text) in files do
        writeAtomically (dir / file) text
        IO.println s!"gin-export: wrote {dir / file}"
    return 0
  catch err =>
    IO.eprintln s!"gin-export: error: {err}"
    unless writing do
      IO.eprintln "gin-export: nothing was written"
    return 1

end Gin.Export
