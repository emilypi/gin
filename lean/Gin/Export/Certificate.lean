import Lean
import Gin.Export.Ir
import Gin.Export.Modules
import Gin.Export.Print

/-!
# Proof traces

This module builds the trace (`Certificate` in the code, `"certificate"` in
the JSON). The exporter only writes a design whose refinement theorem has
the expected shape and, like every exported definition, depends on no
axioms beyond the three standard ones of Lean's logic. In particular it
refuses proofs that use `sorry` (`sorryAx`) and proofs by `native_decide`
or `bv_decide`, which trust the compiler through `Lean.ofReduceBool` or
generated `<theorem>._native.*` axioms.

`collectAxioms` reads proof terms but cannot tell whether the kernel
actually checked them (`set_option debug.skipKernelTC`), so the export
script also replays every module the export loads through `leanchecker`
before exporting. Does the proof check? The kernel decides that, not this
module.

## The refinement shape

I want the theorem to say one thing: the implementation equals its
specification at every cycle and for every input stream. Concretely, it
must state

    ∀ i₁ … iₖ (t : Nat), top i₁ … iₖ t = S i₁ … iₖ t

where `top` is the exported top definition, the `iⱼ` are the bound inputs
passed straight through, `S` is a constant other than `top`, and `S` does
not refer to `top`, directly or through other definitions. This rules out
tautologies (`top i t = top i t`), claims about some cycles only
(`top i 0 = …`), weaker statements (`… ∨ True`) and specifications that
call the implementation. A specification that copies the implementation's
body without naming it cannot be told apart mechanically; the trace shows
its definition so that you can.

## What the trace shows

`statement` is the theorem's type and `specDefinitions` every constant it
depends on, rendered by the fixed printer of `Gin.Export.Print`. The
definitions are collected transitively through the types and values of
definitions, stopping at the top definition, at gin's signal DSL (the
module `Gin.Signal`) and at Lean's core library (modules under `Init`,
`Std` and `Lean`). They are listed in dependency order, ties broken by name.

* Definitions and opaque constants are shown as `name : type := value`.
  The kernel never unfolds an opaque constant, so the theorem holds
  whatever its value is.
* Inductive types and their constructors are shown as `name : type`; an
  inductive type brings all its constructors along. A recursor stands for
  its inductive type, which determines it.
* Theorems are left out, and so is everything only they refer to: by proof
  irrelevance the meaning of a definition does not depend on which proof it
  contains. The axioms of those proofs are still checked, because
  `collectAxioms` on the refinement theorem reaches them.
* An axiom in the closure is shown as `name : type`; any axiom outside the
  allowed three has already been refused.

Every name in the trace (the theorem, the axioms, the constants and
binders of the statement and of the definitions, and the `name` of each
definition) is printed by `Print.name` (with `_root_.` where Lean would
read the name as an alias, `Print.globalName`), which never gives two names
the same text and prints only ASCII. The export is refused if a name cannot
be printed that way (a name with macro scopes or a numeric component, an
inaccessible name, a component containing `»`), if two definitions print
the same name, or if a bound variable prints like a constant of its term.
Every field is printable ASCII by construction of the printer; the export
is refused if one is not (`checkAscii`), so that no text in a trace can
hide a character you do not see.
-/

open Lean Meta

namespace Gin.Export

/-- The axioms a certified design may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The sentence that ends every axiom error. Tools that look for the name
of the offending axiom in an error should ignore it. -/
def allowedNote : String :=
  "Allowed axioms: " ++ ", ".intercalate (allowedAxioms.map (·.toString)) ++ "."

/-- Why an axiom outside the allowed list typically shows up. -/
def axiomHint (a : Name) : String :=
  if a == ``sorryAx then " (the proof is incomplete: it uses sorry)"
  else if (a.toString.splitOn "._native.").length > 1 || a == ``Lean.ofReduceBool
      || a == ``Lean.ofReduceNat || a == ``Lean.trustCompiler then
    " (native_decide and bv_decide trust the compiler, not the kernel)"
  else ""

/-- The axioms `n` depends on, sorted; an error naming every axiom outside
`allowedAxioms`. -/
def checkedAxioms (what : String) (n : Name) : MetaM (Array Name) := do
  let axs := (← collectAxioms n).qsort (·.toString < ·.toString)
  let bad := axs.filter (!allowedAxioms.contains ·)
  unless bad.isEmpty do
    let names := ", ".intercalate (bad.toList.map fun a => a.toString ++ axiomHint a)
    throwError "{what} {n} depends on disallowed axioms: {names}. {allowedNote}"
  return axs

/-- The refinement shape, for error messages. -/
def refinementShape : String := "∀ i₁ … iₖ (t : Nat), top i₁ … iₖ t = S i₁ … iₖ t"

/-- The constant a closure reaches when it reaches `c`: the inductive type
of a recursor, which determines it, and `c` itself otherwise. -/
def closureNode (env : Environment) (c : Name) : Name :=
  match env.find? c with
  | some (.recInfo v) => v.getMajorInduct
  | _ => c

/-- The constants a closure goes on to from `c`, and the ones `c` must be
listed after. They differ for an inductive type, which brings its
constructors along but is listed before them. -/
def closureEdges (env : Environment) (c : Name) : Array Name × Array Name :=
  match env.find? c with
  | some (.defnInfo v) => let d := v.type.getUsedConstants ++ v.value.getUsedConstants; (d, d)
  | some (.opaqueInfo v) => let d := v.type.getUsedConstants ++ v.value.getUsedConstants; (d, d)
  | some (.inductInfo v) => (v.type.getUsedConstants ++ v.ctors.toArray, v.type.getUsedConstants)
  | some ci => (ci.type.getUsedConstants, ci.type.getUsedConstants)
  | none => (#[], #[])

/-- The constants reachable from `roots` through definitions (see the module
documentation), without the ones `stop` holds for, theorems, gin's signal
DSL and Lean's core library. -/
partial def specClosure (env : Environment) (roots : Array Name) (stop : Name → Bool) :
    Array Name := Id.run do
  let excluded (c : Name) : Bool :=
    stop c || isDslConst env c || isCoreLibraryConst env c ||
      (match env.find? c with | some (.thmInfo _) => true | _ => false)
  let mut seen : NameSet := {}
  let mut out := #[]
  let mut todo := roots.toList
  while true do
    match todo with
    | [] => break
    | c :: rest =>
      todo := rest
      let c := closureNode env c
      if seen.contains c || excluded c then continue
      seen := seen.insert c
      out := out.push c
      todo := (closureEdges env c).1.toList ++ todo
  return out

/-- `nodes` in dependency order (every constant after the ones it refers
to), ties and cycles broken by the least name. -/
def dependencyOrder (env : Environment) (nodes : Array Name) : Array Name := Id.run do
  let inSet : NameSet := nodes.foldl NameSet.insert {}
  let deps (c : Name) : NameSet :=
    ((closureEdges env c).2.map (closureNode env)).foldl
      (fun s d => if d != c && inSet.contains d then s.insert d else s) {}
  let mut remaining := nodes.qsort (·.toString < ·.toString)
  let mut done : NameSet := {}
  let mut out := #[]
  while !remaining.isEmpty do
    let next := (remaining.find? fun c => (deps c).toList.all done.contains).getD remaining[0]!
    out := out.push next
    done := done.insert next
    remaining := remaining.filter (· != next)
  return out

/-- Lift a printer refusal into `MetaM`. -/
def printed {α : Type} (what : String) (x : Except String α) : MetaM α :=
  match x with
  | .ok a => pure a
  | .error e => throwError "cannot print {what} unambiguously: {e}; refusing to export"

/-- Refuse a trace in which two specification definitions print the
same name. -/
def checkDistinctNames (names : List String) : Except String Unit :=
  match Print.firstDuplicate? names with
  | some n => throw s!"two specification definitions print the same name {n}"
  | none => pure ()

/-- Refuse a trace with a field that is not printable ASCII
(`0x20`–`0x7E`): a non-ASCII character could pass for another one, and a
control character could hide text. -/
def checkAscii (c : Certificate) : Except String Unit := do
  let fields := [("theorem", c.theorem_), ("statement", c.statement)] ++
    (c.axioms ++ c.implAxioms).map ("axiom", ·) ++
    c.specDefinitions.flatMap fun d => [("specification definition name", d.name),
      ("specification definition", d.body)]
  for (what, text) in fields do
    unless Print.isPrintableAscii text do
      throw s!"the {what} {text.quote} contains a character that is not printable ASCII"

/-- The specification definitions of a statement, rendered. -/
def specDefinitions (env : Environment) (statement : Lean.Expr) (top : Name) :
    MetaM (List SpecDef) := do
  let nodes := specClosure env statement.getUsedConstants (· == top)
  let aliases := Print.aliases env
  let defs ← (dependencyOrder env nodes).toList.filterMapM fun c => do
    let some ci := env.find? c | return none
    return some {
      name := ← printed s!"the name of {c}" (Print.globalName aliases c)
      body := ← printed s!"the definition of {c}"
        (Print.decl env c ci.levelParams ci.type (ci.value? (allowOpaque := true))) }
  printed "the specification definitions" (checkDistinctNames (defs.map (·.name)))
  return defs

/-- Does `c` refer to `target`, directly or through the definitions it
depends on (see `specClosure`)? -/
def refersTo (env : Environment) (c target : Name) : Bool :=
  (specClosure env #[c] (· == target)).any fun d =>
    ((closureEdges env d).1.map (closureNode env)).contains target

/-- Refuse `thm` for not having the refinement shape. -/
def shapeError {α : Type} (thm top : Name) (why : MessageData) : MetaM α :=
  throwError "theorem {thm} does not have the refinement shape {refinementShape} \
    with top = {top}: {why}"

/-- Check that `thmType`, the type of `thm`, has the refinement shape for
the top definition `top` (see the module documentation); return `S`. -/
def checkShape (thm top : Name) (thmType : Lean.Expr) : MetaM Name := do
  let env ← getEnv
  forallTelescope thmType fun xs body => do
    let some t := xs.back? | shapeError thm top m!"it does not quantify over a cycle t : Nat"
    let tTy := (← instantiateMVars (← inferType t)).consumeMData
    unless tTy.isConstOf ``Nat do
      shapeError thm top m!"its last quantified variable is not a cycle t : Nat"
    let body := (← instantiateMVars body).consumeMData
    let some (_, lhs, rhs) := body.eq? | shapeError thm top m!"its conclusion is not an equation"
    let lhs := lhs.consumeMData
    let rhs := rhs.consumeMData
    let passes (e : Lean.Expr) : Bool :=
      e.getAppArgs.size == xs.size &&
        (e.getAppArgs.zip xs).all fun (a, x) => a.consumeMData == x
    unless lhs.getAppFn.consumeMData.isConstOf top && passes lhs do
      shapeError thm top
        m!"the left-hand side is not {top} applied to the quantified inputs and t, in order"
    let .const spec _ := rhs.getAppFn.consumeMData
      | shapeError thm top
          m!"the right-hand side is not a constant applied to the quantified inputs and t"
    unless passes rhs do
      shapeError thm top
        m!"the right-hand side is not {spec} applied to the quantified inputs and t, in order"
    if spec == top then
      shapeError thm top m!"both sides are {top}, so the statement says nothing"
    if refersTo env spec top then
      shapeError thm top
        m!"the specification {spec} refers to {top}, the implementation it is compared with"
    return spec

/-- The trace for refinement theorem `thm` about the top definition
`top`, whose implementation consists of `defs`. Fails if any of them uses a
disallowed axiom or if the theorem does not have the refinement shape. -/
def certify (thm top : Name) (defs : List Name) : MetaM Certificate := do
  let env ← getEnv
  let some ci := env.find? thm | throwError "unknown theorem {thm}"
  let .thmInfo _ := ci | throwError "{thm} is not a theorem"
  let axs ← checkedAxioms "theorem" thm
  let mut impl : Array Name := #[]
  for d in defs do
    impl := impl ++ (← checkedAxioms "definition" d)
  discard <| checkShape thm top ci.type
  let implAxioms := (impl.qsort (·.toString < ·.toString)).toList.eraseDups
  let aliases := Print.aliases env
  let names (ns : List Name) := printed "the axioms" (ns.mapM (Print.globalName aliases))
  let c : Certificate := {
    theorem_ := ← printed s!"the name of {thm}" (Print.globalName aliases thm)
    statement := ← printed s!"the statement of {thm}" (Print.expr env ci.type)
    axioms := ← names axs.toList
    implAxioms := ← names implAxioms
    specDefinitions := ← specDefinitions env ci.type top }
  printed "the certificate" (checkAscii c)
  return c

end Gin.Export
