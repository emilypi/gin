import Lean
import Gin.Export.Certificate
import Gin.Export.Modules

/-!
# Code the compiler substitutes for a definition

The exporter reads the IR and the certificate from the kernel definitions
of a design, but computes its vectors by running the design's compiled
code. Three attributes let the compiled code differ from the definition:

* `@[implemented_by f]` runs `f` instead of the definition, unchecked;
* `@[extern]` runs foreign code instead of the definition;
* a `@[csimp]` theorem `@f = @g` replaces `f` by `g` in the code of every
  definition compiled after it. Its proof may use `sorry` or an unsound
  axiom, which the certificate never sees, as it is not part of any
  specification.

The toolchain's uses of these attributes are trusted like the rest of the
toolchain. `compiledOverrides` finds the project's: an `implemented_by` or
`extern` on a project constant the design's code runs, and a project
`csimp` theorem that rewrites any constant the design's code may reach,
including constants of Lean's core library that the compiler may inline
into the design. The exporter refuses a design with any of them, so its
vectors are computed from the code its definitions describe.

The translator itself must not run code of a design either. Lean's
`whnf` and `isDefEq` evaluate `Lean.reduceBool c` and `Lean.reduceNat c` by
running the compiled code of `c`, so `nativeReductions` finds the
constants a design reaches that refer to them, and the exporter refuses
the design before translating it.
-/

open Lean

namespace Gin.Export

/-- The project constants whose code a design runs: the ones reachable
from `roots` through definitions, without theorems, gin's signal DSL and
Lean's core library (see `specClosure`). -/
def implementationClosure (env : Environment) (roots : Array Name) : Array Name :=
  specClosure env roots (fun _ => false)

/-- Every constant reachable from `roots` through definitions, including
those of Lean's core library and the DSL. Theorems are reached but not
entered: the compiler never runs a proof. -/
def reachableConstants (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots.toList
  while true do
    match todo with
    | [] => break
    | c :: rest =>
      todo := rest
      let c := closureNode env c
      if seen.contains c then continue
      seen := seen.insert c
      match env.find? c with
      | some (.thmInfo _) => continue
      | _ => todo := (closureEdges env c).1.toList ++ todo
  return seen

/-- Does `attr` hold for `c`, in any entry the module of `c` exported (to
its `.olean` or to its `.ir`)? -/
def hasParamAttr {α : Type} [Inhabited α] (attr : ParametricAttribute α) (env : Environment)
    (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some i => (attr.ext.getModuleEntries env i ++ attr.ext.getModuleIREntries env i).any (·.1 == c)
  | none => (attr.getParam? env c).isSome

/-- The `csimp` theorems of project modules (and of the current module), as
`(theorem, rewritten constant)`. -/
def projectCsimps (env : Environment) : Array (Name × Name) := Id.run do
  let ext := Compiler.CSimp.ext.ext
  let entry : ScopedEnvExtension.Entry Compiler.CSimp.Entry → Name × Name
    | .global e | .scoped _ e => (e.thmName, e.fromDeclName)
  let mut out := #[]
  for h : i in [0:env.header.moduleNames.size] do
    if isToolchainModule env.header.moduleNames[i] then continue
    let idx : ModuleIdx := i
    out := out ++ (ext.getModuleEntries env idx ++ ext.getModuleIREntries env idx).map entry
  out := out ++ (ext.getState env).newEntries.toArray.map entry
  return out.toList.eraseDups.toArray

/-- Why the compiled code of the definitions `roots` may differ from the
definitions, one message per reason; empty if it cannot. -/
def compiledOverrides (env : Environment) (roots : Array Name) : Array String := Id.run do
  let mut out := #[]
  for c in implementationClosure env roots do
    if hasParamAttr Compiler.implementedByAttr env c then
      out := out.push s!"{c} is marked @[implemented_by]"
    if hasParamAttr externAttr env c then
      out := out.push s!"{c} is marked @[extern]"
  let csimps := projectCsimps env
  unless csimps.isEmpty do
    let reached := reachableConstants env roots
    for (thm, f) in csimps do
      if reached.contains f then
        out := out.push s!"the @[csimp] theorem {thm} replaces {f} in compiled code"
  return out

/-- The constants that Lean's reduction evaluates by running compiled
code. -/
def nativeReductionConsts : List Name := [``Lean.reduceBool, ``Lean.reduceNat]

/-- The constants reachable from `roots` through definitions (see
`reachableConstants`) that refer to `Lean.reduceBool` or `Lean.reduceNat`,
with the one they refer to. Reducing a term built from them may run
compiled code. -/
def nativeReductions (env : Environment) (roots : Array Name) : Array (Name × Name) := Id.run do
  let mut out := #[]
  for c in (reachableConstants env roots).toArray.qsort Name.lt do
    if let some (.thmInfo _) := env.find? c then continue
    for r in nativeReductionConsts do
      if (closureEdges env c).1.contains r then
        out := out.push (c, r)
  return out

/-- Refuse the definitions `roots` if reducing them may run compiled code
(see `nativeReductions`). The translator reduces the definitions of a
design, so this check must come first. -/
def checkNoNativeReduction (roots : Array Name) : MetaM Unit := do
  let found := nativeReductions (← getEnv) roots
  unless found.isEmpty do
    let uses := found.toList.map fun (c, r) => s!"{c} refers to {r}"
    throwError "reducing {roots} may run compiled code: {"; ".intercalate uses}; refusing to \
      translate it"

/-- Refuse the definitions `roots` if their compiled code, which computes
the vectors, may differ from them (see `compiledOverrides`). -/
def checkCompiledCode (roots : Array Name) : MetaM Unit := do
  let reasons := compiledOverrides (← getEnv) roots
  unless reasons.isEmpty do
    throwError "the compiled code of {roots} may differ from its definitions, which the \
      certificate and the IR describe: {"; ".intercalate reasons.toList}; refusing to export"

end Gin.Export
