import Lean

/-!
# A fixed printer for kernel terms

Certificates show a reviewer the refinement theorem and every definition it
depends on (`docs/file-formats.md`, "Certificate"). They are rendered by this
printer, not by Lean's pretty printer: the pretty printer consults
delaborators, unexpanders and notation that any imported module can declare,
so a design could make the printed statement differ from the term the kernel
checked. (An `app_unexpander` can, for instance, print a call of `specR` as
`Counter.spec`.) This printer reads only the term itself and the types and
values of the constants it mentions; nothing in the environment can change
its output.

## ASCII

Every printed text is printable ASCII (`0x20`–`0x7E`), so that nothing in
it can pass for something else that looks alike: a confusable letter
(`spe\u{3F2}`, with a Greek lunate sigma, for `spec`), an invisible
character or a bidirectional override. The fixed syntax is written in its
ASCII forms (`forall`, `->`, `{{x : α}}` for a strict-implicit binder),
names are escaped as below, and in a string literal every character outside
printable ASCII, and `"` and `\`, is written `\u{XXXX}` (its code point in
upper-case hexadecimal, at least four digits), so that `"on\u{200B}"` does
not read as `"on"`. The certificate checks the result again.

## Names

Two different names never print the same text. `Name.toString` does not
guarantee this: it turns escaping off for inaccessible names and names with
macro scopes, so the root constant `«A.spec✝»` and the constant `spec✝` in
namespace `A` both print `A.spec✝`.

* A name component is printed bare if it is a plain ASCII identifier
  (`[A-Za-z_][A-Za-z0-9_']*`) and not one of `keywords`; otherwise it is
  printed `<<…>>` (standing for Lean's `«…»`), with every character other
  than an ASCII letter, digit, `_` or `'` written `\u{XXXX}` (so `.`, `<`,
  `>`, `\` and every non-ASCII character are escaped). A string component
  that consists of digits is not a plain identifier, so it is printed
  `<<…>>`. Components are joined with `.`.
* Names with a numeric component (`A.1`, which reads as a projection, or
  the root `1`, which reads as a numeral), names with macro scopes and
  inaccessible names (a component containing `✝` or equal to
  `_inaccessible`) of constants and universe parameters are refused, and so
  is a component that contains `»`: such names are not written by hand, and
  their meaning depends on what the printer does not show.
* A constant whose name Lean source would resolve through an alias
  (`export`), such as a root constant `true`, which is not `Bool.true`, is
  printed `_root_.true`; `_root_` itself is a keyword, so a constant named
  `_root_.true` prints `<<_root_>>.true`.
* A bound variable's name has its macro scopes erased and is printed as one
  component (a multi-component binder name has its `.`s escaped), so that it
  cannot read as a constant or a projection.

## Rules

* Constants are printed with their full names. Universe arguments are
  printed, as `c.{u, v}`, unless they are all `0`.
* Applications print every argument, including implicit and instance
  arguments. An applied constant or variable is written `@c` unless its type,
  with definitions unfolded as needed, is seen to take explicit binders for
  all the arguments and to have no non-explicit binder after them; so the
  text denotes the same application even when the binders are hidden behind
  a definition (`g : F` with `F := {n : Nat} -> Nat -> Nat`) and Lean would
  not insert an implicit argument after the last one. By the same rule an
  unapplied constant or variable whose type starts with a non-explicit
  binder is written `@c`.
* `@Eq α a b` is printed `a = b` (the type `α` is not shown).
* A non-dependent explicit `forall` is printed `α -> β`, and is
  right-associative; every other `forall` is printed `forall (x : α), β`,
  with `{x : α}`, `{{x : α}}` and `[x : α]` for the other binder kinds.
  Consecutive binders share one `forall`, and consecutive lambdas one
  `fun (x : α) (y : β) => b`.
* `let x : α := v; b`, and `have x : α := v; b` for a non-dependent `let`.
* Numerals: `@OfNat.ofNat Nat n (instOfNatNat n)` is printed `n`, so a bare
  number is always a `Nat`; `@OfNat.ofNat (BitVec w) n (BitVec.instOfNat w n)`
  and `BitVec.ofNat w n` for a numeral `n` are printed `(n : BitVec w)`.
  Numerals at any other instance are printed as ordinary applications. A raw
  literal is printed `nat_lit n`, and a string literal in quotes, escaped as
  above.
* Sorts: `Prop`, `Type`, `Type u`, `Sort u`. A structure projection is
  printed `e.i`, with `i` counted from 1; since no constant name has a
  numeric component, `A.1` is always a projection.
* Bound variables keep their names, except that a name already bound in an
  enclosing scope, or equal to a constant of the term or a prefix of one,
  gets the least suffix `_k` (`k ≥ 1`) that makes it fresh. After printing,
  `expr` and `decl` check again that no bound variable prints like a
  constant of the term or a prefix of one.
* An argument that is not an atom is parenthesised; so are the operands of
  `=` that are not applications or atoms, the left operand of `->` that is an
  arrow or a binder, and any binder that is not at the end of the enclosing
  term (the body of a binder and the right operand of `->` are at the end).
-/

open Lean

namespace Gin.Export.Print

/-! ## Names -/

/-- Words that a plain identifier must not be, because the printed term or
Lean source gives them another meaning. -/
def keywords : Std.HashSet String := Std.HashSet.ofList
  ["_", "Prop", "Sort", "Type", "abbrev", "at", "axiom", "by", "calc", "class", "def", "deriving",
   "do", "else", "end", "example", "exists", "forall", "from", "fun", "have", "if", "import", "in",
   "inductive", "instance", "let", "match", "mut", "namespace", "nat_lit", "noncomputable",
   "opaque", "open", "partial", "private", "protected", "return", "section", "show", "sorry",
   "structure", "suffices", "then", "theorem", "universe", "unsafe", "variable", "where", "with",
   "_root_"]

/-- May `c` appear in a printed component without escaping? -/
def plainChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

/-- Is `s` a plain ASCII identifier, `[A-Za-z_][A-Za-z0-9_']*`, and not a
keyword? -/
def isPlainIdent (s : String) : Bool :=
  match s.toList with
  | c :: cs => (c.isAlpha || c == '_') && cs.all plainChar && !keywords.contains s
  | [] => false

/-- `\u{XXXX}`: the code point of `c` in upper-case hexadecimal, at least
four digits. -/
def unicodeEscape (c : Char) : String :=
  let hex := String.ofList ((Nat.toDigits 16 c.toNat).map Char.toUpper)
  "\\u{" ++ "".pushn '0' (4 - hex.length) ++ hex ++ "}"

/-- A name component: bare if it is a plain identifier, otherwise `<<…>>`
with every character that is not `plainChar` escaped. A component containing
`»` is refused. -/
def component (s : String) : Except String String := do
  if s.contains '»' then throw s!"the name component {s.quote} contains »"
  if isPlainIdent s then return s
  return "<<" ++ s.foldl (fun acc c => if plainChar c then acc.push c else acc ++ unicodeEscape c) ""
    ++ ">>"

/-- A string literal in quotes, with every character outside printable
ASCII (`0x20`–`0x7E`), and `"` and `\`, written `\u{XXXX}`. -/
def stringLit (s : String) : String :=
  let plain (c : Char) := 0x20 ≤ c.toNat && c.toNat ≤ 0x7E && c != '"' && c != '\\'
  "\"" ++ s.foldl (fun acc c => if plain c then acc.push c else acc ++ unicodeEscape c) "" ++ "\""

/-- Is every character of `s` printable ASCII (`0x20`–`0x7E`)? -/
def isPrintableAscii (s : String) : Bool :=
  s.all fun c => 0x20 ≤ c.toNat && c.toNat ≤ 0x7E

/-- The printed form of a constant's or universe parameter's name (see the
module documentation). Refuses anonymous names, names with macro scopes,
names with a numeric component and inaccessible names. -/
def name (n : Name) : Except String String := do
  if n.isAnonymous then throw "an anonymous name"
  if n.hasMacroScopes then throw s!"the name {n} has macro scopes"
  let rec go : Name → Except String (List String)
    | .anonymous => pure []
    | .num .. => throw s!"the name {n} has a numeric component"
    | .str p s => do
      if s.contains '✝' || s == "_inaccessible" then
        throw s!"the name {n} is inaccessible"
      return (← go p) ++ [← component s]
  return ".".intercalate (← go n)

/-- Names that Lean source resolves to another constant through an alias
(`export`): those of `env`, read from its imported modules' entries as well
as from its state (the state is empty when the modules were imported
without extensions), and `true` and `false`. -/
def aliases (env : Environment) : NameSet := Id.run do
  let mut s : NameSet := NameSet.empty |>.insert `true |>.insert `false
  for (a, _) in (getAliasState env).toList do
    s := s.insert a
  for i in [0:env.header.moduleNames.size] do
    for (a, _) in aliasExtension.getModuleEntries env i do
      s := s.insert a
  return s

/-- The printed form of a constant's name in a term or as a declaration's
name: `name`, prefixed by `_root_.` if Lean source would resolve the bare
text through an alias (`true` for the root constant `true`, which is not
`Bool.true`). -/
def globalName (aliases : NameSet) (n : Name) : Except String String := do
  let s ← name n
  return if aliases.contains n then "_root_." ++ s else s

/-- The text of a bound variable's name, before escaping: macro scopes
erased, components joined with `.`; `x` for an anonymous name. -/
def binderText (n : Name) : String :=
  let n := n.eraseMacroScopes
  if n.isAnonymous then "x" else
  ".".intercalate (n.components.map fun
    | .str _ s => s
    | .num _ k => toString k
    | .anonymous => "")

/-- The first text that occurs twice in `names`, if any. -/
def firstDuplicate? (names : List String) : Option String := Id.run do
  let mut seen : Std.HashSet String := {}
  for n in names do
    if seen.contains n then return some n
    seen := seen.insert n
  return none

/-- Refuse a printed term in which a bound variable prints like a constant
of the term or a prefix of one. -/
def checkBound (reserved : Std.HashSet String) (bound : Array String) : Except String Unit :=
  match bound.find? reserved.contains with
  | some x => throw s!"the bound variable {x} prints like a constant of the term"
  | none => pure ()

/-! ## Terms -/

/-- Precedence of printed text: what may appear where without parentheses. -/
inductive Prec where
  /-- `forall`, `fun`, `let`, `have`: extend as far to the right as possible. -/
  | binder
  /-- `α -> β`. -/
  | arrow
  /-- `a = b`. -/
  | eq
  /-- `f a b`, `Sort u`, `nat_lit n`. -/
  | app
  /-- Names, numerals, parenthesised terms, projections. -/
  | atom
  deriving BEq, Inhabited

/-- The rank of a precedence, for comparisons. -/
def Prec.rank : Prec → Nat
  | .binder => 0
  | .arrow => 1
  | .eq => 2
  | .app => 3
  | .atom => 4

/-- Printed text with its precedence. -/
structure Doc where
  /-- The text. -/
  text : String
  /-- Its precedence. -/
  prec : Prec
  deriving Inhabited

/-- The text of `d`, parenthesised unless its precedence is at least `p`. -/
def Doc.paren (d : Doc) (p : Prec) : String :=
  if d.prec.rank ≥ p.rank then d.text else "(" ++ d.text ++ ")"

/-- Read-only context of the printer. -/
structure Ctx where
  /-- Where the types and values of constants are looked up, to decide on
  `@`. -/
  env : Environment
  /-- The bound variables, innermost first: printed name and type. -/
  locals : List (String × Expr) := []
  /-- Names a bound variable must not take: every constant of the printed
  term, and every prefix of one, as printed. -/
  reserved : Std.HashSet String := {}
  /-- Names printed with `_root_.` (see `globalName`). -/
  aliases : NameSet := {}

/-- The printer's monad: it records every bound variable's printed name and
can refuse a name. -/
abbrev M := StateT (Array String) (Except String)

/-- Lift a refusal into the printer. -/
def liftName (x : Except String String) : M String :=
  match x with
  | .ok s => pure s
  | .error e => throw e

/-- `(l, k)` such that the level is `l` plus `k` successors, `l` not a
successor. -/
def peelSucc : Level → Nat → Level × Nat
  | .succ l, k => peelSucc l (k + 1)
  | l, k => (l, k)

mutual

/-- A level, as `0`, `u`, `u+1`, `max u v` or `imax u v`. -/
partial def level (l : Level) : Except String String :=
  match l with
  | .zero => pure "0"
  | .param n => name n
  | .mvar _ => pure "?u"
  | .max a b => return s!"max {← levelArg a} {← levelArg b}"
  | .imax a b => return s!"imax {← levelArg a} {← levelArg b}"
  | .succ _ =>
    match peelSucc l 0 with
    | (.zero, k) => pure (toString k)
    | (base, k) => return s!"{← levelArg base}+{k}"

/-- A level as an operand of `max`, `imax`, `+`, `Type` or `Sort`. -/
partial def levelArg (l : Level) : Except String String :=
  match l with
  | .max .. | .imax .. => return "(" ++ (← level l) ++ ")"
  | .succ _ => do
    let s ← level l
    return if (peelSucc l 0).1 == .zero then s else "(" ++ s ++ ")"
  | _ => level l

end

/-- A sort: `Prop`, `Type`, `Type u` or `Sort u`. -/
def sort (u : Level) : Except String Doc :=
  match u with
  | .zero => pure ⟨"Prop", .atom⟩
  | .succ .zero => pure ⟨"Type", .atom⟩
  | .succ l => return ⟨"Type " ++ (← levelArg l), .app⟩
  | l => return ⟨"Sort " ++ (← levelArg l), .app⟩

/-- A constant with its universe arguments (omitted when all are `0`). -/
def constName (aliases : NameSet) (c : Name) (us : List Level) : Except String String := do
  let n ← globalName aliases c
  if us.all (· == .zero) then return n
  return n ++ ".{" ++ ", ".intercalate (← us.mapM level) ++ "}"

/-- Does a function of type `ty`, applied to `args`, possibly have a
non-explicit binder, among those its arguments fill or after them? Lean
source would then fill or insert the argument itself, so the application is
printed with `@`. The type is walked binder by binder, instantiating each
with its argument while arguments remain; when it is not a `∀`, its head
definition is unfolded. It has no further binders if it is then a sort, a
variable or headed by an inductive type, an axiom or an opaque constant
(and all arguments are used). Otherwise the answer is `true`, so that `@` is
printed whenever explicit binders are not seen. -/
partial def needsAt (env : Environment) (ty : Expr) (args : Array Expr) (i : Nat := 0)
    (fuel : Nat := 256) : Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 =>
    match ty.consumeMData.headBeta with
    | .forallE _ _ b bi =>
      !bi.isExplicit || needsAt env (if h : i < args.size then b.instantiate1 args[i] else b) args
        (i + 1) fuel
    | .letE _ _ v b _ => needsAt env (b.instantiate1 v) args i fuel
    | .sort _ => i < args.size
    | t =>
      match t.getAppFn.consumeMData with
      | .const c us =>
        match env.find? c with
        | some ci@(.defnInfo _) =>
          if ci.levelParams.length != us.length then true else
          needsAt env ((ci.instantiateValueLevelParams! us).beta t.getAppArgs) args i fuel
        | some (.inductInfo _) | some (.axiomInfo _) | some (.opaqueInfo _) => i < args.size
        | _ => true
      | .bvar _ => i < args.size
      | _ => true

/-- `n` if `e` is a raw natural-number literal. -/
def rawNat? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | _ => none

/-- `n` if `e` is `@OfNat.ofNat Nat n (instOfNatNat n)`. -/
def natNumeral? (e : Expr) : Option Nat := do
  let e := e.consumeMData
  guard (e.isAppOfArity ``OfNat.ofNat 3)
  let args := e.getAppArgs
  guard (args[0]!.consumeMData.isConstOf ``Nat)
  let n ← rawNat? args[1]!
  let inst := args[2]!.consumeMData
  guard (inst.isAppOfArity ``instOfNatNat 1 && rawNat? inst.appArg! == some n)
  return n

/-- A numeral of a `BitVec` type: `(width, n)` if `e` is
`@OfNat.ofNat (BitVec w) n (BitVec.instOfNat w n)` or `BitVec.ofNat w n`
for a numeral or raw literal `n`. -/
def bvNumeral? (e : Expr) : Option (Expr × Nat) := do
  let e := e.consumeMData
  if e.isAppOfArity ``BitVec.ofNat 2 then
    let n ← natNumeral? e.appArg! <|> rawNat? e.appArg!
    return (e.appFn!.appArg!, n)
  guard (e.isAppOfArity ``OfNat.ofNat 3)
  let args := e.getAppArgs
  let ty := args[0]!.consumeMData
  guard (ty.isAppOfArity ``BitVec 1)
  let n ← rawNat? args[1]!
  let inst := args[2]!.consumeMData
  guard (inst.isAppOfArity ``BitVec.instOfNat 2)
  guard (inst.appFn!.appArg!.consumeMData == ty.appArg!.consumeMData)
  guard (rawNat? inst.appArg! == some n)
  return (ty.appArg!, n)

/-- A fresh printed name for a binder named `n`, recorded as bound. -/
def freshName (ctx : Ctx) (n : Name) : M String := do
  let base := binderText n
  let taken (s : String) := ctx.reserved.contains s || ctx.locals.any (·.1 == s)
  let mut x ← liftName (component base)
  let mut k := 1
  -- terminates: only finitely many names are taken
  for _ in [0:ctx.locals.length + ctx.reserved.size + 1] do
    if !taken x then break
    x ← liftName (component s!"{base}_{k}")
    k := k + 1
  modify (·.push x)
  return x

/-- Enter a binder. -/
def Ctx.bind (ctx : Ctx) (name : String) (ty : Expr) : Ctx :=
  { ctx with locals := (name, ty) :: ctx.locals }

/-- The opening and closing brackets of a binder. -/
def brackets : BinderInfo → String × String
  | .default => ("(", ")")
  | .implicit => ("{", "}")
  | .strictImplicit => ("{{", "}}")
  | .instImplicit => ("[", "]")

mutual

/-- Print a term. -/
partial def doc (ctx : Ctx) (e : Expr) : M Doc := do
  match e with
  | .mdata _ e => doc ctx e
  | .bvar i =>
    match ctx.locals[i]? with
    | some (x, ty) => return ⟨(if needsAt ctx.env ty #[] then "@" else "") ++ x, .atom⟩
    | none => return ⟨s!"#{i}", .atom⟩
  | .fvar fv => return ⟨s!"?fvar.{fv.name}", .atom⟩
  | .mvar mv => return ⟨s!"?mvar.{mv.name}", .atom⟩
  | .sort u => liftDoc (sort u)
  | .const c us =>
    let atSign := match ctx.env.find? c with
      | some ci => if needsAt ctx.env ci.type #[] then "@" else ""
      | none => "@"
    return ⟨atSign ++ (← liftName (constName ctx.aliases c us)), .atom⟩
  | .lit (.natVal n) => return ⟨s!"nat_lit {n}", .app⟩
  | .lit (.strVal s) => return ⟨stringLit s, .atom⟩
  | .proj _ i s => return ⟨(← doc ctx s).paren .atom ++ "." ++ toString (i + 1), .atom⟩
  | .app .. => app ctx e
  | .lam .. => lam ctx e #[]
  | .forallE .. => pi ctx e
  | .letE n t v b nondep =>
    let x ← freshName ctx n
    let kw := if nondep then "have" else "let"
    return ⟨s!"{kw} {x} : {(← doc ctx t).text} := {(← doc ctx v).text}; \
      {(← doc (ctx.bind x t) b).text}", .binder⟩

/-- Lift a printed sort into the printer. -/
partial def liftDoc (x : Except String Doc) : M Doc :=
  match x with
  | .ok d => pure d
  | .error e => throw e

/-- Print an application. -/
partial def app (ctx : Ctx) (e : Expr) : M Doc := do
  if let some n := natNumeral? e then return ⟨toString n, .atom⟩
  if let some (w, n) := bvNumeral? e then
    return ⟨s!"({n} : BitVec {(← doc ctx w).paren .atom})", .atom⟩
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if fn.isConstOf ``Eq && args.size == 3 then
    return ⟨(← doc ctx args[1]!).paren .app ++ " = " ++ (← doc ctx args[2]!).paren .app, .eq⟩
  let head ← match fn with
    | .const c us => do
      let atSign := match ctx.env.find? c with
        | some ci => if needsAt ctx.env ci.type args then "@" else ""
        | none => "@"
      pure (atSign ++ (← liftName (constName ctx.aliases c us)))
    | .bvar i =>
      match ctx.locals[i]? with
      | some (x, ty) => pure ((if needsAt ctx.env ty args then "@" else "") ++ x)
      | none => pure s!"#{i}"
    | _ => do pure ((← doc ctx fn).paren .atom)
  let args ← args.toList.mapM fun a => return (← doc ctx a).paren .atom
  return ⟨" ".intercalate (head :: args), .app⟩

/-- Print a block of lambdas. -/
partial def lam (ctx : Ctx) (e : Expr) (binders : Array String) : M Doc := do
  match e with
  | .lam n t b bi =>
    let x ← freshName ctx n
    let (o, c) := brackets bi
    lam (ctx.bind x t) b (binders.push s!"{o}{x} : {(← doc ctx t).text}{c}")
  | .mdata _ e => lam ctx e binders
  | body => return ⟨"fun " ++ " ".intercalate binders.toList ++ " => " ++ (← doc ctx body).text, .binder⟩

/-- Print a `∀`: an arrow if it is non-dependent and explicit, otherwise a
block of binders. -/
partial def pi (ctx : Ctx) (e : Expr) : M Doc := do
  match e with
  | .forallE _ t b .default =>
    if b.hasLooseBVar 0 then piBlock ctx e #[] else
    return ⟨(← doc ctx t).paren .eq ++ " -> " ++ (← doc (ctx.bind "_" t) b).text, .arrow⟩
  | _ => piBlock ctx e #[]

/-- Print consecutive dependent or non-explicit binders as one `∀`. -/
partial def piBlock (ctx : Ctx) (e : Expr) (binders : Array String) : M Doc := do
  match e with
  | .forallE n t b bi =>
    if bi.isExplicit && !b.hasLooseBVar 0 && !binders.isEmpty then
      finish ctx e binders
    else
      let x ← freshName ctx n
      let (o, c) := brackets bi
      piBlock (ctx.bind x t) b (binders.push s!"{o}{x} : {(← doc ctx t).text}{c}")
  | .mdata _ e => piBlock ctx e binders
  | body => finish ctx body binders

/-- Close a block of `∀` binders. -/
partial def finish (ctx : Ctx) (body : Expr) (binders : Array String) : M Doc := do
  return ⟨"forall " ++ " ".intercalate binders.toList ++ ", " ++ (← doc ctx body).text, .binder⟩

end

/-- Every constant of `es` and every prefix of one, as printed (also without
`_root_.`). -/
def reservedNames (es : List Expr) : Except String (Std.HashSet String) := do
  let mut s : Std.HashSet String := {}
  for e in es do
    for c in e.getUsedConstants do
      let mut n := c
      while !n.isAnonymous do
        s := s.insert (← name n)
        n := n.getPrefix
  return s

/-- Print the terms `es` in a context whose reserved names are those of
`es` and `extra`; refuse if a bound variable prints like a reserved name. -/
def run (env : Environment) (es : List Expr) (extra : List Expr := []) :
    Except String (List String) := do
  let reserved ← reservedNames (es ++ extra)
  let ctx : Ctx := { env, reserved, aliases := aliases env }
  let (texts, bound) ← (es.mapM fun e => return (← doc ctx e).text).run #[]
  checkBound reserved bound
  return texts

/-- Print a closed term. -/
def expr (env : Environment) (e : Expr) : Except String String := do
  let texts ← run env [e]
  return texts.headD ""

/-- Print a declaration as `name : type := value`, or `name : type` for a
declaration without a value. Universe parameters are written
`name.{u, v}`. -/
def decl (env : Environment) (n : Name) (levelParams : List Name) (type : Expr)
    (value : Option Expr) : Except String String := do
  let texts ← run env (type :: value.toList)
  let mut head ← globalName (aliases env) n
  unless levelParams.isEmpty do
    head := head ++ ".{" ++ ", ".intercalate (← levelParams.mapM name) ++ "}"
  match texts with
  | [ty, v] => return head ++ " : " ++ ty ++ " := " ++ v
  | ty :: _ => return head ++ " : " ++ ty
  | [] => return head

end Gin.Export.Print
