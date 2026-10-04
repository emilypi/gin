import Lean
import Gin.Export.Certificate
import Gin.Export.Compiled
import Gin.Export.Reserved
import Gin.Export.Translate
import Gin.Export.Vectors

/-!
# Assembling a program and its vectors

An `Entry` says what to export for one circuit: its definitions, its
refinement theorem, its port names and how to compute its vectors.
`exportProgram` checks the certificate, translates the definitions and
derives the top entity; `exportVectors` evaluates the circuit.
-/

open Lean Meta

namespace Gin.Export

/-- Number of cycles of every exported vector file. -/
def vectorCycles : Nat := 1024

/-- Upper bound on cycles × summed port widths of a vector file. -/
def maxVectorPayloadBits : Nat := 2 ^ 18

/-- What to export for one circuit. -/
structure Entry where
  /-- Name of the generated hardware module, of the output directory and of
  the files in it. -/
  name : String
  /-- The module whose environment contains the circuit. -/
  module : Name
  /-- The definition implementing the circuit. Its type must be
  `Signal d i₁ → … → Signal d iₖ → Signal d o`. -/
  top : Name
  /-- The definitions to emit, in order; must include `top`. Calls to these
  become `global` references; every other definition is inlined. -/
  defs : List Name
  /-- The refinement theorem; its statement must mention `top`. -/
  theorem_ : Name
  /-- Input port names, one per argument of `top`. -/
  inputs : List String
  /-- Output port names: one, or one per component of the right-nested
  product `o`. -/
  outputs : List String
  /-- How to compute vectors, or `none` for designs that exist only to test
  that the exporter refuses them. -/
  vectors : Option VectorSource
  /-- Seed of the pseudo-random inputs. -/
  seed : UInt64 := 1
  /-- Number of vector cycles; every exported circuit uses `vectorCycles`. -/
  cycles : Nat := vectorCycles
  /-- A reject fixture (`lean/GinReject`): a design that exists to test that
  the exporter or the kernel replay refuses it. Only a reject fixture may
  import a `GinReject` module. -/
  fixture : Bool := false

/-- Producer recorded in every file. -/
def producer : Producer := { tool := "gin-export", leanVersion := Lean.versionString }

/-- A legal hardware identifier: lower-case ASCII letter first, then
lower-case letters, digits and single underscores, not ending in `_`, at
most 64 characters, no `gin_` prefix, and not one of gin's
`reservedWords` (HDL keywords and names the tools reject). Generated modules
also reserve the port names `clk` and `rst`. -/
def isLegalIdent (s : String) : Bool :=
  match s.toList with
  | c :: rest =>
    c.isLower && rest.all (fun x => x.isLower || x.isDigit || x == '_') && s.length ≤ 64
      && (s.splitOn "__").length == 1 && !s.endsWith "_" && !s.startsWith "gin_"
      && !reservedWords.contains s
  | [] => false

/-- The clock domain of every `Signal` occurring in `ty`. -/
partial def signalDomains (ty : Lean.Expr) : TrM (List DomainInfo) := do
  let ty := (← instantiateMVars ty).consumeMData
  match_expr ty with
  | Gin.Signal d a => return (← domainInfo d) :: (← signalDomains a)
  | Prod a b => return (← signalDomains a) ++ (← signalDomains b)
  | _ =>
    match ty with
    | .forallE _ a b _ => return (← signalDomains a) ++ (← signalDomains b)
    | _ =>
      match ← unfoldReducible? ty with
      | some ty' => signalDomains ty'
      | none => return []

/-- Split the right-nested output product into `n` components. -/
def splitOutputs : Nat → Ty → Option (List Ty)
  | 0, _ => none
  | 1, t => some [t]
  | n + 2, .prod [a, b] => (a :: ·) <$> splitOutputs (n + 1) b
  | _, _ => none

/-- Translate an entry's definitions and derive its top entity. Does not
look at the theorem; see `exportProgram`. -/
def translateTop (e : Entry) : MetaM (Top × List Def) := do
  unless e.defs.contains e.top do
    throwError "the definitions to export do not include the top definition {e.top}"
  unless isLegalIdent e.name do
    throwError "top name {repr e.name} is not a legal hardware identifier"
  let ports := e.inputs ++ e.outputs
  for p in ports do
    unless isLegalIdent p && p != "clk" && p != "rst" do
      throwError "port name {repr p} is not a legal hardware identifier (clk and rst are reserved)"
  unless ports.eraseDups.length == ports.length do
    throwError "port names {ports} are not pairwise distinct"
  checkCompiledCode e.defs.toArray
  checkNoNativeReduction e.defs.toArray
  let exported := e.defs.foldl NameSet.insert {}
  let defs ← e.defs.mapM (translateDef · exported)
  let topName ← irName e.top
  let some topDef := defs.find? (·.name == topName) | unreachable!
  -- the top type: `Signal d i₁ → … → Signal d iₖ → Signal d o`
  let (args, res) := splitFuns topDef.type
  unless args.length == e.inputs.length do
    throwError "{e.top} takes {args.length} signals but {e.inputs.length} input names are given"
  let some topCi := (← getEnv).find? e.top | unreachable!
  let domains ← runTr e.top exported (signalDomains topCi.type)
  let some domain := domains.head? | throwError "{e.top} has no Signal in its type"
  unless domains.all (· == domain) do
    throwError "{e.top} mixes clock domains {repr domains.eraseDups}; one domain is supported"
  let inputs ← (e.inputs.zip args).mapM fun (n, t) => do
    let .signal _ ty := t | throwError "input {n} of {e.top} is not a Signal"
    unless ty.isScalar do throwError "input {n} of {e.top} is not Bool or BitVec"
    return { name := n, type := ty : Port }
  let .signal _ resTy := res | throwError "the result of {e.top} is not a Signal"
  let some outTys := splitOutputs e.outputs.length resTy
    | throwError "the result type of {e.top} does not have {e.outputs.length} output components"
  let outputs ← (e.outputs.zip outTys).mapM fun (n, ty) => do
    unless ty.isScalar do throwError "output {n} of {e.top} is not Bool or BitVec"
    return { name := n, type := ty : Port }
  return ({ name := e.name, domain, inputs, outputs, def_ := topName }, defs)
where
  splitFuns : Ty → List Ty × Ty
    | .fn a r => let (as, res) := splitFuns r; (a :: as, res)
    | t => ([], t)

/-- Certify an entry's theorem. -/
def certifyEntry (e : Entry) : MetaM Certificate := certify e.theorem_ e.top e.defs

/-- Certify an entry's theorem, then translate it, in one environment.
`gin-export` does the two in separate imports (`Gin.Export.Main`). -/
def exportProgram (e : Entry) : MetaM Program := do
  let certificate ← certifyEntry e
  let (top, defs) ← translateTop e
  return { producer, top, defs, certificate }

/-- Compute an entry's vectors and check them against the program's ports. -/
def exportVectors (e : Entry) (top : Top) : Except String Vectors := do
  let some src := e.vectors | throw s!"{e.name} has no vector source"
  unless src.inputs == top.inputs.map (·.type) && src.outputs == top.outputs.map (·.type) do
    throw s!"the vector source of {e.name} does not match the port types of {e.top}"
  let cycles := src.rows e.seed e.cycles
  for c in cycles do
    unless c.inputs.map (·.ty) == src.inputs && c.outputs.map (·.ty) == src.outputs do
      throw s!"a vector row of {e.name} does not match its port types"
  let widthOf : Ty → Nat := fun | .bv w => w | _ => 1
  let payload := cycles.size * ((top.inputs ++ top.outputs).map (widthOf ·.type)).sum
  unless payload ≤ maxVectorPayloadBits do
    throw s!"the vectors of {e.name} carry {payload} bits, more than {maxVectorPayloadBits}"
  return { top := top.name, inputs := top.inputs, outputs := top.outputs, cycles }

end Gin.Export
