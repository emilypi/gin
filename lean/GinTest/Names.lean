import Lean
import Gin
import Gin.Export.Certificate
import GinTest.Util

/-!
Names in certificates are unambiguous: two different names never print the
same text, every printed name is ASCII, names that hide their meaning
(macro scopes, inaccessible names) are refused, and `@` is printed whenever
an application's binders are not all seen to be explicit.

The two attacks below were found in review. Each passed every check of the
exporter while names were printed with `Name.toString`.
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

/-! ## Implicit binders hidden behind a definition -/

namespace GinTest.Names

/-- A function type whose first binder is implicit. -/
def F : Type := {_n : Nat} → Nat → Nat

/-- A function of that type. -/
def g : F := fun {n} m => n - m

/-- `g` applied to its implicit argument `5` and to `3`. -/
def useG : Nat := @g 5 3

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
open Gin.Export.Print (name component expr decl)

-- [lean-names] The confusable letter is escaped: the statement names
-- `Atk.«spe\u{03F2}»`, and the two definitions print differently.
run_meta do
  let c ← Gin.Export.certify ``Atk.counter_correct ``Atk.counter [``Atk.counter]
  unless c.statement ==
      "∀ (en : Gin.Signal Gin.System Bool) (t : Nat), Atk.counter en t = Atk.«spe\\u{03F2}» en t" do
    throwError "statement {c.statement}"
  let names := c.specDefinitions.map (·.name)
  unless names == ["Atk.spec", "Atk.Out", "Atk.«spe\\u{03F2}»"] do
    throwError "spec definitions {names}"
  unless (c.specDefinitions.map (·.body)).all
      (·.all fun (ch : Char) => ch.toNat < 128 || "∀→⦃⦄«»".contains ch) do
    throwError "a definition prints a non-ASCII name"

-- [lean-names] The inaccessible name is refused, so the colliding
-- certificate is never written.
run_meta do
  GinTest.expectError (Gin.Export.certify ``Atk2.counter_correct ``Atk2.counter [``Atk2.counter])
    ["cannot print", "inaccessible", "refusing to export"]

-- [lean-names] Escaped components never collide with bare ones or with each
-- other: a `.` inside a component, digits, keywords, the printer's own
-- pseudo-syntax (`#0`, `?u`, `_`) and non-ASCII letters are all escaped.
#guard text (name (Name.mkStr1 "Atk2.spec")) == "«Atk2\\u{002E}spec»"
#guard text (name `Atk2.spec) == "Atk2.spec"
#guard text (name (Name.mkStr1 "#0")) == "«\\u{0023}0»"
#guard text (name (Name.mkStr1 "?u")) == "«\\u{003F}u»"
#guard text (name (Name.mkStr2 "A" "0")) == "A.«0»"
#guard text (name (Name.mkNum `A 0)) == "A.0"
#guard text (name (Name.mkStr2 "A" "fun")) == "A.«fun»"
#guard text (name (Name.mkStr1 "_")) == "«_»"
#guard text (name `α) == "«\\u{03B1}»"
#guard text (name (Name.mkStr1 "a\\b")) == "«a\\u{005C}b»"
#guard text (name (Name.mkStr1 "a«b")) == "«a\\u{00AB}b»"
#guard text (name `x'_1) == "x'_1"

-- [lean-names] Names that cannot be printed unambiguously are refused:
-- a component containing `»`, inaccessible names and macro scopes.
#guard refused (component "a»b") "»"
#guard refused (name (Name.mkStr2 "A" "spec✝")) "inaccessible"
#guard refused (name (Name.mkStr2 "A" "_inaccessible")) "inaccessible"
#guard refused (name (addMacroScope `M `x 3)) "macro scopes"
#guard refused (name .anonymous) "anonymous"

-- [lean-names] A binder name cannot inject text: it is one escaped
-- component, whatever it contains.
run_meta do
  let env ← getEnv
  let nm := Name.mkStr2 "t) (h : False) (y" "✝"
  let e := Expr.lam nm (mkConst ``Nat) (.bvar 0) .default
  let s := text (expr env e)
  let x := "«t\\u{0029}\\u{0020}\\u{0028}h\\u{0020}\\u{003A}\\u{0020}False\\u{0029}\\u{0020}" ++
    "\\u{0028}y\\u{002E}\\u{271D}»"
  unless s == s!"fun ({x} : Nat) => {x}" do throwError "printed {s}"
  -- a binder named like a projection of a bound variable
  let nm2 := Name.mkStr2 "t" "succ"
  let e2 := Expr.lam `t (mkConst ``Nat) (.lam nm2 (mkConst ``Nat) (.bvar 0) .default) .default
  let s2 := text (expr env e2)
  unless s2 == "fun (t : Nat) («t\\u{002E}succ» : Nat) => «t\\u{002E}succ»" do
    throwError "printed {s2}"

-- [lean-names] The certificate is refused if two definitions print the same
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
