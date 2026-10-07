import Lean
import Gin
import Gin.Export.Certificate
import Gin.Export.Translate
import GinTest.Util

/-!
The trace (`Certificate` in the code, `"certificate"` in the JSON) is
unambiguous: two different names never print the same text, every printed
text is printable ASCII (names, string literals and the fixed syntax), names
that hide their meaning (macro scopes, inaccessible names, numeric
components) are refused, names Lean reads as aliases get `_root_.`, and `@`
is printed whenever a binder of a head's type is not seen to be explicit.
An ambiguous trace could have you review a specification other than the
one the kernel checked.

The attacks below were found in review. Each passed every check of the
exporter: the first two while names were printed with `Name.toString`, the
third while string literals were printed with `String.quote`.
-/

open Lean Meta Gin

/-! ## Attack: a confusable letter

The theorem proves the buggy counter equal to `Atk.speϲ` (with U+03F2, Greek
lunate sigma), which always returns 0; a reducible type drags the honest
`Atk.spec` into the listed definitions, so that a reader sees both and takes
the statement to be about the honest one. -/

namespace Atk

/-- Buggy implementation: always 0. -/
def counter (en : Signal System Bool) : Signal System (BitVec 8) :=
  lift (fun _ => (0 : BitVec 8)) en

/-- Honest-looking specification (Latin c). -/
def spec (en : Signal System Bool) (t : Nat) : BitVec 8 :=
  BitVec.ofNat 8 ((List.range t).countP (fun i => en i))

/-- Output type that drags the honest `spec` into the closure. -/
@[reducible] def Out : Type := (fun (_ : Signal System Bool → Nat → BitVec 8) => BitVec 8) spec

/-- The specification actually proved; its last letter is Greek ϲ (U+03F2). -/
def speϲ (_en : Signal System Bool) (_t : Nat) : Out := (0 : BitVec 8)

/-- Refinement theorem against the confusable name. -/
theorem counter_correct : ∀ en t, counter en t = speϲ en t := fun _ _ => rfl

end Atk

/-! ## Attack: an unescaped inaccessible name

`Name.toString` does not escape a name whose last component contains `✝`,
so the honest `Atk2.«spec✝»` and the root constant `«Atk2.spec✝»`, which
always returns 0 and is the one the theorem is about, both printed
`Atk2.spec✝`. -/

namespace Atk2

/-- Buggy implementation. -/
def counter (en : Signal System Bool) : Signal System (BitVec 8) :=
  lift (fun _ => (0 : BitVec 8)) en

/-- Honest-looking, printed `Atk2.spec✝` by `Name.toString`. -/
def «spec✝» (en : Signal System Bool) (t : Nat) : BitVec 8 :=
  BitVec.ofNat 8 ((List.range t).countP (fun i => en i))

/-- Drags `Atk2.«spec✝»` in. -/
@[reducible] def Out : Type := (fun (_ : Signal System Bool → Nat → BitVec 8) => BitVec 8) «spec✝»

end Atk2

/-- The real spec, a single-component name, also printed `Atk2.spec✝` by
`Name.toString`. -/
def «Atk2.spec✝» (_en : Signal System Bool) (_t : Nat) : Atk2.Out := (0 : BitVec 8)

namespace Atk2

/-- Refinement theorem against the colliding name. -/
theorem counter_correct : ∀ en t, counter en t = «Atk2.spec✝» en t := fun _ _ => rfl

end Atk2

/-! ## Attack: an invisible character in a string literal

`spec` reads as `if "on" = "on" then <count> else 0`, the honest count, but
the second literal ends in a zero-width space (U+200B), so the condition is
false and `spec` is 0, like the buggy counter. -/

namespace Atk5

/-- Buggy implementation: always 0. -/
def counter (en : Signal System Bool) : Signal System (BitVec 8) :=
  lift (fun _ => (0 : BitVec 8)) en

/-- Looks like the honest count; is 0. -/
def spec (en : Signal System Bool) (t : Nat) : BitVec 8 :=
  if "on" = "on\u200B" then BitVec.ofNat 8 ((List.range t).countP (fun i => en i)) else 0

/-- Refinement theorem. -/
theorem counter_correct : ∀ en t, counter en t = spec en t := by
  intro en t; simp [spec, counter, lift]

end Atk5

/-! ## Implicit binders hidden behind a definition -/

namespace GinTest.Names

/-- A function type whose first binder is implicit. -/
def F : Type := {_n : Nat} → Nat → Nat

/-- A function of that type. -/
def g : F := fun {n} m => n - m

/-- `g` applied to its implicit argument `5` and to `3`. -/
def useG : Nat := @g 5 3

/-- An implicit binder after the explicit ones. -/
def h (a : Nat) {_n : Nat} : Nat := a

/-- `h` applied to its explicit argument only. -/
def partialH : {_n : Nat} → Nat := @h 1

/-- `id` unapplied. -/
def unappliedId := @id

/-- An exported definition with a confusable name (Greek ϲ). -/
def cϲ (en : Signal System Bool) : Signal System Bool := en

/-- An exported definition with an inaccessible name. -/
def «c✝» (en : Signal System Bool) : Signal System Bool := en

/-- A reference to it. -/
def useInaccessible (en : Signal System Bool) : Signal System Bool := «c✝» en

/-- An unwrapped `Except String String`, or the error as a string. -/
def text : Except String String → String
  | .ok s => s
  | .error e => "error: " ++ e

/-- Is `x` a refusal mentioning `needle`? -/
def refused (x : Except String String) (needle : String) : Bool :=
  match x with
  | .ok _ => false
  | .error e => GinTest.containsStr e needle

end GinTest.Names

open GinTest.Names
open Gin.Export.Print (name component expr decl stringLit)

/-- A trace of theorem `T` with the statement and definitions given. -/
def cert (statement : String) (defs : List (String × String)) : Gin.Export.Certificate :=
  { theorem_ := "T", statement, axioms := [], implAxioms := [],
    specDefinitions := defs.map fun (name, body) => { name, body } }

/-- Every field of `c` is printable ASCII. -/
def asciiCertificate (c : Gin.Export.Certificate) : Bool :=
  (Gin.Export.checkAscii c) matches .ok _

-- [lean-names] The confusable letter is escaped: the statement names
-- `Atk.<<spe\u{03F2}>>`, and the two definitions print differently.
run_meta do
  let c ← Gin.Export.certify ``Atk.counter_correct ``Atk.counter [``Atk.counter]
  unless c.statement ==
      "forall (en : Gin.Signal Gin.System Bool) (t : Nat), Atk.counter en t = Atk.<<spe\\u{03F2}>> en t" do
    throwError "statement {c.statement}"
  let names := c.specDefinitions.map (·.name)
  unless names == ["Atk.spec", "Atk.Out", "Atk.<<spe\\u{03F2}>>"] do
    throwError "spec definitions {names}"
  unless asciiCertificate c do throwError "the certificate is not ASCII"

-- [lean-names] The invisible character is escaped: the spec definition shows
-- `"on\u{200B}"`, so the condition does not read as `"on" = "on"`.
run_meta do
  let c ← Gin.Export.certify ``Atk5.counter_correct ``Atk5.counter [``Atk5.counter]
  let some d := c.specDefinitions.find? (·.name == "Atk5.spec") | throwError "no Atk5.spec"
  unless GinTest.containsStr d.body "(\"on\" = \"on\\u{200B}\")" do
    throwError "printed {d.body}"
  unless asciiCertificate c do throwError "the certificate is not ASCII"

-- [lean-names] String literals: everything outside printable ASCII, and the
-- quote and backslash, is written `\u{XXXX}`; a bidirectional override
-- (U+202E) cannot reorder the text around it.
#guard stringLit "on\u200B" == "\"on\\u{200B}\""
#guard stringLit "a\u202Eb" == "\"a\\u{202E}b\""
#guard stringLit "q\"b\\n\n\t\x7f~ " == "\"q\\u{0022}b\\u{005C}n\\u{000A}\\u{0009}\\u{007F}~ \""
#guard stringLit "𝔹" == "\"\\u{1D539}\""
run_meta do
  let s := text (expr (← getEnv) (mkStrLit "a\u202Eb"))
  unless s == "\"a\\u{202E}b\"" do throwError "printed {s}"

-- [lean-names] A trace with a field that is not printable ASCII is
-- refused, whichever field it is.
#guard asciiCertificate (cert "forall (t : Nat), t = t" [("S", "S : Nat := 0")])
#guard !asciiCertificate (cert "∀ (t : Nat), t = t" [])
#guard !asciiCertificate (cert "s" [("S", "S : String := \"on\u200B\"")])
#guard !asciiCertificate (cert "s" [("S\n", "S : Nat := 0")])
#guard !asciiCertificate { cert "s" [] with axioms := ["prop\u202Eext"] }

-- [lean-names] The inaccessible name is refused, so the colliding
-- trace is never written.
run_meta do
  GinTest.expectError (Gin.Export.certify ``Atk2.counter_correct ``Atk2.counter [``Atk2.counter])
    ["cannot print", "inaccessible", "refusing to export"]

-- [lean-names] Escaped components never collide with bare ones or with each
-- other: a `.` inside a component, digits, keywords, the printer's own
-- pseudo-syntax (`#0`, `?u`, `_`, `<<`) and non-ASCII letters are all
-- escaped.
#guard text (name (Name.mkStr1 "Atk2.spec")) == "<<Atk2\\u{002E}spec>>"
#guard text (name `Atk2.spec) == "Atk2.spec"
#guard text (name (Name.mkStr1 "#0")) == "<<\\u{0023}0>>"
#guard text (name (Name.mkStr1 "?u")) == "<<\\u{003F}u>>"
#guard text (name (Name.mkStr2 "A" "0")) == "A.<<0>>"
#guard text (name (Name.mkStr2 "A" "fun")) == "A.<<fun>>"
#guard text (name (Name.mkStr1 "_")) == "<<_>>"
#guard text (name (Name.mkStr2 "_root_" "true")) == "<<_root_>>.true"
#guard text (name `α) == "<<\\u{03B1}>>"
#guard text (name (Name.mkStr1 "a\\b")) == "<<a\\u{005C}b>>"
#guard text (name (Name.mkStr1 "a«b")) == "<<a\\u{00AB}b>>"
#guard text (name (Name.mkStr1 "<<a>>")) == "<<\\u{003C}\\u{003C}a\\u{003E}\\u{003E}>>"
#guard text (name `x'_1) == "x'_1"

-- [lean-names] Names that cannot be printed unambiguously are refused:
-- a component containing `»`, inaccessible names and macro scopes.
#guard refused (component "a»b") "»"
#guard refused (name (Name.mkStr2 "A" "spec✝")) "inaccessible"
#guard refused (name (Name.mkStr2 "A" "_inaccessible")) "inaccessible"
#guard refused (name (addMacroScope `M `x 3)) "macro scopes"
#guard refused (name .anonymous) "anonymous"

-- [lean-names] Numeric components are refused, so `A.1` is always a
-- projection, a bare `1` always a numeral and `Type 0` always level 0: the
-- constant `A.1` and the projection `.proj Prod 0 A` would both print
-- `A.1`, the root constant `1` and the numeral `1` both `1`, and a
-- universe parameter named `0` would print like the level `0`.
#guard refused (name (Name.mkNum `A 1)) "numeric"
#guard refused (name (Name.mkNum .anonymous 1)) "numeric"
#guard refused (name (Name.mkNum .anonymous 0)) "numeric"
#guard refused (name (Name.mkStr (Name.mkNum `A 1) "b")) "numeric"
run_meta do
  let env ← getEnv
  unless text (expr env (.proj ``Prod 0 (mkConst ``useG))) == "GinTest.Names.useG.1" do
    throwError "projection"
  unless refused (expr env (mkConst (Name.mkNum ``useG 1))) "numeric" do
    throwError "useG.1 printed"
  unless text (expr env (mkNatLit 1)) == "1" do throwError "numeral"
  unless refused (expr env (mkConst (Name.mkNum .anonymous 1))) "numeric" do
    throwError "root 1 printed"
  let zero := Name.mkNum .anonymous 0
  unless refused (expr env (.sort (.succ (.param zero)))) "numeric" do throwError "Type 0 printed"
  unless refused (expr env (mkConst ``List [.param zero])) "numeric" do
    throwError "List with level parameter 0 printed"
  unless refused (decl env `A [zero] (.sort (.param zero)) none) "numeric" do
    throwError "A with level parameter 0 printed"

-- [lean-names] A root constant named like a core alias reads as the alias in
-- Lean source (`true` is `Bool.true`), so it is printed with `_root_.`, in
-- terms and as a declaration's name.
run_meta do
  withoutModifyingEnv do
    addDecl (.defnDecl (mkDefinitionValEx `true [] (mkConst ``Bool) (mkConst ``Bool.false)
      .abbrev .safe []))
    let env ← getEnv
    let e := Expr.lam `b (mkConst ``Bool)
      (mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) (.bvar 0) (mkConst `true)) .default
    let s := text (expr env e)
    unless s == "fun (b : Bool) => b = _root_.true" do throwError "printed {s}"
    let d := text (decl env `true [] (mkConst ``Bool) (mkConst ``Bool.false))
    unless d == "_root_.true : Bool := Bool.false" do throwError "printed {d}"
    unless text (expr env (mkConst ``Bool.true)) == "Bool.true" do throwError "Bool.true"
-- the aliases of modules imported without extensions are read from their
-- entries (`some` is `Option.some` through `export Option (none some)`)
run_meta do
  let env ← importModules #[{ module := `Init }] {} (loadExts := false)
  unless (Gin.Export.Print.aliases env).contains `some do throwError "alias some not found"
  unless text (expr env (mkConst `some)) == "@_root_.some" do throwError "some"

-- [lean-names] A binder name cannot inject text: it is one escaped
-- component, whatever it contains.
run_meta do
  let env ← getEnv
  let nm := Name.mkStr2 "t) (h : False) (y" "✝"
  let e := Expr.lam nm (mkConst ``Nat) (.bvar 0) .default
  let s := text (expr env e)
  let x := "<<t\\u{0029}\\u{0020}\\u{0028}h\\u{0020}\\u{003A}\\u{0020}False\\u{0029}\\u{0020}" ++
    "\\u{0028}y\\u{002E}\\u{271D}>>"
  unless s == s!"fun ({x} : Nat) => {x}" do throwError "printed {s}"
  -- a binder named like a projection of a bound variable
  let nm2 := Name.mkStr2 "t" "succ"
  let e2 := Expr.lam `t (mkConst ``Nat) (.lam nm2 (mkConst ``Nat) (.bvar 0) .default) .default
  let s2 := text (expr env e2)
  unless s2 == "fun (t : Nat) (<<t\\u{002E}succ>> : Nat) => <<t\\u{002E}succ>>" do
    throwError "printed {s2}"

-- [lean-names] The trace is refused if two definitions print the same
-- name, or a bound variable prints like a constant of its term.
#guard (Gin.Export.checkDistinctNames ["A.s", "B.s", "A.s"]) matches .error _
#guard (Gin.Export.checkDistinctNames ["A.s", "B.s"]) matches .ok _
#guard (Gin.Export.Print.checkBound (Std.HashSet.ofList ["A", "A.s"]) #["x", "A"]) matches .error _
#guard (Gin.Export.Print.checkBound (Std.HashSet.ofList ["A", "A.s"]) #["x"]) matches .ok _

-- [lean-names] `@` is decided by walking the type with definitions unfolded:
-- `g : F` hides an implicit binder behind `F`, so `@g 5 3` keeps its `@`.
run_meta do
  let ci ← getConstInfo ``useG
  let s := text (decl (← getEnv) ``useG [] ci.type ci.value?)
  unless s == "GinTest.Names.useG : Nat := @GinTest.Names.g 5 3" do throwError "printed {s}"

-- [lean-names] `@` is printed when a binder after the last argument is
-- implicit (Lean would insert that argument), for an unapplied constant
-- whose type starts with an implicit binder, and for such a variable.
run_meta do
  let env ← getEnv
  let ci ← getConstInfo ``partialH
  let s := text (decl env ``partialH [] ci.type ci.value?)
  unless s == "GinTest.Names.partialH : forall {_n : Nat}, Nat := @GinTest.Names.h 1" do
    throwError "printed {s}"
  let ci ← getConstInfo ``unappliedId
  let s := text (decl env ``unappliedId ci.levelParams ci.type ci.value?)
  unless s == "GinTest.Names.unappliedId.{u_1} : forall {<<\\u{03B1}>> : Sort u_1}, " ++
      "<<\\u{03B1}>> -> <<\\u{03B1}>> := @id.{u_1}" do
    throwError "printed {s}"
  let fTy := Expr.forallE `n (mkConst ``Nat) (mkConst ``Nat) .implicit
  let s := text (expr env (.lam `f fTy (.bvar 0) .default))
  unless s == "fun (f : forall {n : Nat}, Nat) => @f" do throwError "printed {s}"
  -- explicit binders throughout: no `@`
  let s := text (expr env (mkConst ``Nat.succ))
  unless s == "Nat.succ" do throwError "printed {s}"

-- [lean-names] IR definition names and references go through the same
-- escaper: the confusable name is escaped and the inaccessible one refused,
-- as a definition and as a reference.
run_meta do
  let d ← Gin.Export.translateDef ``cϲ (NameSet.empty.insert ``cϲ)
  unless d.name == "GinTest.Names.<<c\\u{03F2}>>" do throwError "IR name {d.name}"
  GinTest.expectError (Gin.Export.translateDef ``«c✝» (NameSet.empty.insert ``«c✝»))
    ["inaccessible"]
  GinTest.expectError
    (Gin.Export.translateDef ``useInaccessible ((NameSet.empty.insert ``useInaccessible).insert ``«c✝»))
    ["inaccessible"]
