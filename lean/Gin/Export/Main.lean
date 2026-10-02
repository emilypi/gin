import Lean
import Gin.Export.Encode
import Gin.Export.Program

/-!
# The `gin-export` command

Imports the compiled Lean environment, exports each requested circuit in
memory, and writes the files only once every circuit has passed every
check, so a refusal never leaves partial output behind.
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

/-- Run a `MetaM` computation in an imported environment. -/
def runMeta {α : Type} (env : Environment) (x : MetaM α) : IO α := do
  let (a, _, _) ← x.toIO { fileName := "gin-export", fileMap := default } { env }
  return a

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
    enableInitializersExecution
    let modules := (entries.map (·.module)).toList.eraseDups.toArray
    let env ← importModules (modules.map ({ module := · })) {} (loadExts := true)
    let mut outputs := #[]
    for e in entries do
      try
        let prog ← runMeta env (exportProgram e)
        let vecs ← IO.ofExcept (exportVectors e prog.top)
        outputs := outputs.push (e, prog, vecs)
      catch err =>
        throw <| IO.userError s!"{e.name}: {err}"
    writing := true
    for (e, prog, vecs) in outputs do
      let dir := opts.out / e.name
      IO.FS.createDirAll dir
      for (file, doc) in [(s!"{e.name}.gin.json", prog.toDoc), (s!"{e.name}.vectors.json", vecs.toDoc)] do
        writeAtomically (dir / file) doc.render
        IO.println s!"gin-export: wrote {dir / file}"
    return 0
  catch err =>
    IO.eprintln s!"gin-export: error: {err}"
    unless writing do
      IO.eprintln "gin-export: nothing was written"
    return 1

end Gin.Export
