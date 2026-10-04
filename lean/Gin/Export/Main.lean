import Lean
import Gin.Export.Encode
import Gin.Export.Modules
import Gin.Export.Program

/-!
# The `gin-check-export` and `gin-export` commands

`gin-check-export` is the gate: it links only the exporter and the DSL, no
design, and reads the modules as data, without loading environment
extensions, so no code of a design runs in it (no initializer, no
delaborator, unexpander or other code a module registers). It refuses
project modules that register IO initializers or are named like toolchain
modules, in the modules the named circuits load and in those `gin-export`
links (its root module, `--exporter`), and then checks and renders every
certificate; `collectAxioms` walks the proofs themselves instead of
trusting axiom summaries stored by the modules.

`gin-export` links the designs, to compute vectors by running them. Their
`initialize` declarations run when it starts, before any check, so
`scripts/export-examples.sh` runs it only after `gin-check-export` has
passed. It repeats the same checks (defence in depth), then imports the
modules again with their extensions, which the translator needs (instances,
pattern-match compilation), translates the designs, and writes the files
only once every circuit has passed every check, including the limits gin
enforces on the files it reads, so a refusal never leaves partial output
behind. Messages are printed raw (`pp.raw`), so that no delaborator of a
design runs while an error is reported.
-/

open Lean Meta System

namespace Gin.Export

/-- Command-line help of `gin-export`. -/
def usage : String :=
  "usage: lake exe gin-export [--out DIR] [NAME ...]\n\n" ++
  "Writes DIR/NAME/NAME.gin.json and DIR/NAME/NAME.vectors.json for each named circuit\n" ++
  "(default: the shipped examples; DIR defaults to examples). Run it through `lake exe`\n" ++
  "so that the Lean search path is set, and only after `lake exe gin-check-export` has\n" ++
  "accepted the same circuits: the designs linked into gin-export run their initializers\n" ++
  "when it starts. Nothing is written unless every named circuit exports successfully."

/-- Command-line help of `gin-check-export`. -/
def checkUsage : String :=
  "usage: lake exe gin-check-export [--exporter MODULE] [--list-modules] [NAME ...]\n\n" ++
  "Checks, without running any code of a design, what gin-export checks before it\n" ++
  "translates the named circuits (default: the shipped examples): the modules they load\n" ++
  "and the modules of the exporter MODULE (default GinExport, the root of gin-export)\n" ++
  "register no IO initializer and do not shadow toolchain modules, no circuit that is\n" ++
  "not a reject fixture loads one, and every certificate passes the axiom policy and\n" ++
  "the shape check. Exit code 0 when all pass.\n\n" ++
  "--list-modules prints, after those checks, the modules outside the Lean toolchain\n" ++
  "that the circuits and the exporter load, one per line: the modules the kernel replay\n" ++
  "(scripts/export-examples.sh) must check."

/-- Parsed command line. -/
structure CliOptions where
  /-- Output directory (`gin-export`). -/
  out : FilePath := "examples"
  /-- Circuits to export; empty means the defaults. -/
  names : List String := []
  /-- Print usage and exit. -/
  help : Bool := false
  /-- Print the project modules loaded instead of passing (`gin-check-export`). -/
  listModules : Bool := false
  /-- Root module of the exporter whose linked modules are checked
  (`gin-check-export`). -/
  exporter : Name := `GinExport

/-- Parse the command line; `check` selects the options of
`gin-check-export`, otherwise those of `gin-export`. -/
def parseArgs (check : Bool) : List String → CliOptions → Except String CliOptions
  | [], o => .ok { o with names := o.names.reverse }
  | "--out" :: dir :: rest, o =>
    if check then .error "unknown option --out" else parseArgs check rest { o with out := dir }
  | ["--out"], _ => .error (if check then "unknown option --out" else "--out needs a directory")
  | "--list-modules" :: rest, o =>
    if check then parseArgs check rest { o with listModules := true }
    else .error "unknown option --list-modules (see gin-check-export)"
  | "--exporter" :: m :: rest, o =>
    if check then parseArgs check rest { o with exporter := m.toName }
    else .error "unknown option --exporter"
  | ["--exporter"], _ => .error "--exporter needs a module name"
  | "--help" :: rest, o | "-h" :: rest, o => parseArgs check rest { o with help := true }
  | a :: rest, o =>
    if a.startsWith "-" then .error s!"unknown option {a}"
    else parseArgs check rest { o with names := a :: o.names }

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

/-- Refuse a circuit that loads a reject fixture module (`lean/GinReject`)
unless it is a reject fixture itself: the reject fixtures contain
declarations the kernel never checked, and only the modules a circuit loads
are replayed. -/
def checkRejectImports (env : Environment) (e : Entry) : IO Unit := do
  if let some m := rejectImport? e.fixture (importClosure env e.module) then
    throw <| IO.userError s!"{e.name}: module {e.module} imports the reject fixture module {m}; \
      refusing to export a circuit that is not a reject fixture and loads one"

/-- Write a file by renaming a temporary sibling into place. -/
def writeAtomically (path : FilePath) (contents : String) : IO Unit := do
  let tmp := path.addExtension "tmp"
  IO.FS.writeFile tmp contents
  IO.FS.rename tmp path

/-- Parse the command line and look up the named circuits of `table` (or
`defaults`), or the exit code after printing usage or an error. -/
def parseCommand (tool : String) (check : Bool) (table : List Entry) (defaults : List String)
    (args : List String) : IO (Except UInt32 (CliOptions × Array Entry)) := do
  let help := if check then checkUsage else usage
  let opts ← match parseArgs check args {} with
    | .ok o => pure o
    | .error msg =>
      IO.eprintln s!"{tool}: {msg}\n{help}"
      return .error 2
  if opts.help then
    IO.println help
    return .error 0
  let names := (if opts.names.isEmpty then defaults else opts.names).eraseDups
  let mut entries := #[]
  for n in names do
    match table.find? (·.name == n) with
    | some e => entries := entries.push e
    | none =>
      IO.eprintln s!"{tool}: unknown circuit {n}; known: {" ".intercalate (table.map (·.name))}"
      return .error 2
  return .ok (opts, entries)

/-- The modules `entries` load, followed by `linked`, as imports. -/
def importsOf (entries : Array Entry) (linked : Array Name := #[]) : Array Import :=
  ((entries.map (·.module)).toList ++ linked.toList).eraseDups.toArray.map ({ module := · })

/-- The checks that need no code of a design: import the modules of
`entries` and `linked` as data (no initializer runs, no extension is
loaded), refuse shadowed toolchain modules and IO initializers, refuse a
circuit that is not a reject fixture but loads one, and check and render
every certificate. Returns the data environment and the certificates. -/
def gate (entries : Array Entry) (linked : Array Name := #[]) :
    IO (Environment × Array Certificate) := do
  initSearchPath (← findSysroot)
  let data ← importModules (importsOf entries linked) {} (loadExts := false)
  checkModules data
  for e in entries do
    checkRejectImports data e
  let mut certificates := #[]
  for e in entries do
    try
      certificates := certificates.push (← runMeta data (certifyEntry e))
    catch err =>
      throw <| IO.userError s!"{e.name}: {err}"
  return (data, certificates)

/-- `gin-check-export`: run `gate` on the named circuits of `table` (or
`defaults`) and on the modules of the exporter, without loading or running
any design. Exit code 0 when every check passes, 1 if any circuit is
refused, 2 on a usage error. -/
def checkMain (table : List Entry) (defaults : List String) (args : List String) :
    IO UInt32 := do
  let (opts, entries) ← match ← parseCommand "gin-check-export" true table defaults args with
    | .ok r => pure r
    | .error code => return code
  try
    let (data, _) ← gate entries #[opts.exporter]
    if opts.listModules then
      for m in data.header.moduleNames do
        unless isToolchainModule m do
          IO.println m
    else
      for e in entries do
        IO.println s!"gin-check-export: {e.name} ok"
    return 0
  catch err =>
    IO.eprintln s!"gin-check-export: error: {err}"
    return 1

/-- `gin-export`: export the named circuits of `table` (or `defaults`) as
the command line says, repeating the checks of `gate` first. Exit code 0 on
success, 1 if any circuit is refused, 2 on a usage error. -/
unsafe def main (table : List Entry) (defaults : List String) (args : List String) :
    IO UInt32 := do
  let (opts, entries) ← match ← parseCommand "gin-export" false table defaults args with
    | .ok r => pure r
    | .error code => return code
  let mut writing := false
  try
    let (_, certificates) ← gate entries
    -- the modules with their extensions, for the translator
    enableInitializersExecution
    let env ← importModules (importsOf entries) {} (loadExts := true)
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
