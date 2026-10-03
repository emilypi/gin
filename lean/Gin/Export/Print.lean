import Lean

/-!
# A fixed printer for kernel terms

Certificates show a reviewer the refinement theorem and every definition it
depends on (`docs/file-formats.md`, "Certificate"). They are rendered by this
printer, not by Lean's pretty printer: the pretty printer consults
delaborators, unexpanders and notation that any imported module can declare,
so a design could make the printed statement differ from the term the kernel
checked. (An `app_unexpander` can, for instance, print a call of `specR` as
`Counter.spec`.) This printer reads only the term itself and the types of
the constants it mentions; nothing in the environment can change its output.

## Rules

* Constants are printed with their full names (escaped with `«»` where
  needed). Universe arguments are printed, as `c.{u, v}`, unless they are
  all `0`.
* Applications print every argument, including implicit and instance
  arguments. A constant whose applied binders include an implicit,
  strict-implicit or instance binder is written `@c`, so that the text
  denotes the same application.
* `@Eq α a b` is printed `a = b` (the type `α` is not shown).
* A non-dependent explicit `∀` is printed `α → β`, and is right-associative;
  every other `∀` is printed `∀ (x : α), β`, with `{x : α}`, `⦃x : α⦄` and
  `[x : α]` for the other binder kinds. Consecutive binders share one `∀`,
  and consecutive lambdas one `fun (x : α) (y : β) => b`.
* `let x : α := v; b`, and `have x : α := v; b` for a non-dependent `let`.
* Numerals: `@OfNat.ofNat Nat n (instOfNatNat n)` is printed `n`, so a bare
  number is always a `Nat`; `@OfNat.ofNat (BitVec w) n (BitVec.instOfNat w n)`
  and `BitVec.ofNat w n` for a numeral `n` are printed `(n : BitVec w)`.
  Numerals at any other instance are printed as ordinary applications. A raw
  literal is printed `nat_lit n`, and a string literal in quotes.
* Sorts: `Prop`, `Type`, `Type u`, `Sort u`. A structure projection is
  printed `e.i`, with `i` counted from 1.
* Bound variables keep their names, except that a name already bound in an
  enclosing scope, or equal to a constant of the term or a prefix of one,
  gets the least suffix `_k` (`k ≥ 1`) that makes it fresh.
* An argument that is not an atom is parenthesised; so are the operands of
  `=` that are not applications or atoms, the left operand of `→` that is an
  arrow or a binder, and any binder that is not at the end of the enclosing
  term (the body of a binder and the right operand of `→` are at the end).
-/

open Lean

namespace Gin.Export.Print

/-- Precedence of printed text: what may appear where without parentheses. -/
inductive Prec where
  /-- `∀`, `fun`, `let`, `have`: extend as far to the right as possible. -/
  | binder
  /-- `α → β`. -/
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
  /-- Where the types of constants are looked up, to decide on `@`. -/
  env : Environment
  /-- The bound variables, innermost first: printed name and type. -/
  locals : List (String × Expr) := []
  /-- Names a bound variable must not take: every constant of the printed
  term, and every prefix of one. -/
  reserved : Std.HashSet String := {}

/-- `(l, k)` such that the level is `l` plus `k` successors, `l` not a
successor. -/
def peelSucc : Level → Nat → Level × Nat
  | .succ l, k => peelSucc l (k + 1)
  | l, k => (l, k)

mutual

/-- A level, as `0`, `u`, `u+1`, `max u v` or `imax u v`. -/
partial def level (l : Level) : String :=
  match l with
  | .zero => "0"
  | .param n => n.toString
  | .mvar _ => "?u"
  | .max a b => s!"max {levelArg a} {levelArg b}"
  | .imax a b => s!"imax {levelArg a} {levelArg b}"
  | .succ _ =>
    match peelSucc l 0 with
    | (.zero, k) => toString k
    | (base, k) => s!"{levelArg base}+{k}"

/-- A level as an operand of `max`, `imax`, `+`, `Type` or `Sort`. -/
partial def levelArg (l : Level) : String :=
  match l with
  | .max .. | .imax .. => "(" ++ level l ++ ")"
  | .succ _ => if (peelSucc l 0).1 == .zero then level l else "(" ++ level l ++ ")"
  | _ => level l

end

/-- A sort: `Prop`, `Type`, `Type u` or `Sort u`. -/
def sort (u : Level) : Doc :=
  match u with
  | .zero => ⟨"Prop", .atom⟩
  | .succ .zero => ⟨"Type", .atom⟩
  | .succ l => ⟨"Type " ++ levelArg l, .app⟩
  | l => ⟨"Sort " ++ levelArg l, .app⟩

/-- A constant with its universe arguments (omitted when all are `0`). -/
def constName (c : Name) (us : List Level) : String :=
  if us.all (· == .zero) then c.toString
  else c.toString ++ ".{" ++ ", ".intercalate (us.map level) ++ "}"

/-- Does `ty` have a non-explicit binder among its first `n` binders? Only
syntactic `∀`s are inspected; arguments past them are explicit. -/
def hasImplicitBinder (ty : Expr) (n : Nat) : Bool :=
  match n, ty.consumeMData with
  | k + 1, .forallE _ _ b bi => !bi.isExplicit || hasImplicitBinder b k
  | _, _ => false

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

/-- A fresh printed name for a binder named `n`. -/
def freshName (ctx : Ctx) (n : Name) : String :=
  let n := n.eraseMacroScopes
  let base := if n.isAnonymous then "x" else n.toString
  let taken (s : String) := ctx.reserved.contains s || ctx.locals.any (·.1 == s)
  if !taken base then base else Id.run do
    let mut k := 1
    -- terminates: only finitely many names are taken
    for _ in [0:ctx.locals.length + ctx.reserved.size + 1] do
      if !taken s!"{base}_{k}" then break
      k := k + 1
    return s!"{base}_{k}"

/-- Enter a binder. -/
def Ctx.bind (ctx : Ctx) (name : String) (ty : Expr) : Ctx :=
  { ctx with locals := (name, ty) :: ctx.locals }

/-- The opening and closing brackets of a binder. -/
def brackets : BinderInfo → String × String
  | .default => ("(", ")")
  | .implicit => ("{", "}")
  | .strictImplicit => ("⦃", "⦄")
  | .instImplicit => ("[", "]")

mutual

/-- Print a term. -/
partial def doc (ctx : Ctx) (e : Expr) : Doc :=
  match e with
  | .mdata _ e => doc ctx e
  | .bvar i => ⟨(ctx.locals[i]?.map (·.1)).getD s!"#{i}", .atom⟩
  | .fvar fv => ⟨s!"?fvar.{fv.name}", .atom⟩
  | .mvar mv => ⟨s!"?mvar.{mv.name}", .atom⟩
  | .sort u => sort u
  | .const c us => ⟨constName c us, .atom⟩
  | .lit (.natVal n) => ⟨s!"nat_lit {n}", .app⟩
  | .lit (.strVal s) => ⟨s.quote, .atom⟩
  | .proj _ i s => ⟨(doc ctx s).paren .atom ++ "." ++ toString (i + 1), .atom⟩
  | .app .. => app ctx e
  | .lam .. => lam ctx e #[]
  | .forallE .. => pi ctx e
  | .letE n t v b nondep =>
    let x := freshName ctx n
    let kw := if nondep then "have" else "let"
    ⟨s!"{kw} {x} : {(doc ctx t).text} := {(doc ctx v).text}; {(doc (ctx.bind x t) b).text}", .binder⟩

/-- Print an application. -/
partial def app (ctx : Ctx) (e : Expr) : Doc :=
  if let some n := natNumeral? e then ⟨toString n, .atom⟩ else
  if let some (w, n) := bvNumeral? e then ⟨s!"({n} : BitVec {(doc ctx w).paren .atom})", .atom⟩ else
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if fn.isConstOf ``Eq && args.size == 3 then
    ⟨(doc ctx args[1]!).paren .app ++ " = " ++ (doc ctx args[2]!).paren .app, .eq⟩
  else
    let head := match fn with
      | .const c us =>
        let atSign := match ctx.env.find? c with
          | some ci => if hasImplicitBinder ci.type args.size then "@" else ""
          | none => ""
        atSign ++ constName c us
      | .bvar i =>
        match ctx.locals[i]? with
        | some (x, ty) => (if hasImplicitBinder ty args.size then "@" else "") ++ x
        | none => s!"#{i}"
      | _ => (doc ctx fn).paren .atom
    ⟨" ".intercalate (head :: args.toList.map fun a => (doc ctx a).paren .atom), .app⟩

/-- Print a block of lambdas. -/
partial def lam (ctx : Ctx) (e : Expr) (binders : Array String) : Doc :=
  match e with
  | .lam n t b bi =>
    let x := freshName ctx n
    let (o, c) := brackets bi
    lam (ctx.bind x t) b (binders.push s!"{o}{x} : {(doc ctx t).text}{c}")
  | .mdata _ e => lam ctx e binders
  | body => ⟨"fun " ++ " ".intercalate binders.toList ++ " => " ++ (doc ctx body).text, .binder⟩

/-- Print a `∀`: an arrow if it is non-dependent and explicit, otherwise a
block of binders. -/
partial def pi (ctx : Ctx) (e : Expr) : Doc :=
  match e with
  | .forallE _ t b .default =>
    if b.hasLooseBVar 0 then piBlock ctx e #[] else
    ⟨(doc ctx t).paren .eq ++ " → " ++ (doc (ctx.bind "_" t) b).text, .arrow⟩
  | _ => piBlock ctx e #[]

/-- Print consecutive dependent or non-explicit binders as one `∀`. -/
partial def piBlock (ctx : Ctx) (e : Expr) (binders : Array String) : Doc :=
  match e with
  | .forallE n t b bi =>
    if bi.isExplicit && !b.hasLooseBVar 0 && !binders.isEmpty then
      finish ctx e binders
    else
      let x := freshName ctx n
      let (o, c) := brackets bi
      piBlock (ctx.bind x t) b (binders.push s!"{o}{x} : {(doc ctx t).text}{c}")
  | .mdata _ e => piBlock ctx e binders
  | body => finish ctx body binders

/-- Close a block of `∀` binders. -/
partial def finish (ctx : Ctx) (body : Expr) (binders : Array String) : Doc :=
  ⟨"∀ " ++ " ".intercalate binders.toList ++ ", " ++ (doc ctx body).text, .binder⟩

end

/-- Every constant of `es` and every prefix of one, as strings. -/
def reservedNames (es : List Expr) : Std.HashSet String := Id.run do
  let mut s : Std.HashSet String := {}
  for e in es do
    for c in e.getUsedConstants do
      let mut n := c
      while !n.isAnonymous do
        s := s.insert n.toString
        n := n.getPrefix
  return s

/-- Print a closed term. -/
def expr (env : Environment) (e : Expr) : String :=
  (doc { env, reserved := reservedNames [e] } e).text

/-- Print a declaration as `name : type := value`, or `name : type` for a
declaration without a value. Universe parameters are written
`name.{u, v}`. -/
def decl (env : Environment) (n : Name) (levelParams : List Name) (type : Expr)
    (value : Option Expr) : String :=
  let ctx : Ctx := { env, reserved := reservedNames (type :: value.toList) }
  let name := if levelParams.isEmpty then n.toString
    else n.toString ++ ".{" ++ ", ".intercalate (levelParams.map toString) ++ "}"
  let head := name ++ " : " ++ (doc ctx type).text
  match value with
  | some v => head ++ " := " ++ (doc ctx v).text
  | none => head

end Gin.Export.Print
