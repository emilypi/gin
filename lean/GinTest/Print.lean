import Lean
import Gin
import Gin.Export.Print
import GinTest.Util

/-!
The fixed printer of the trace (`Certificate` in the code, `"certificate"`
in the JSON): full names, every argument, numerals as values, binders with
their types, and nothing a design declares (notation, unexpanders,
delaborators) can change its output.
You answer the first question (does the specification say what I want?)
by reading this text, so I want it to show the term the kernel checked.
-/

open Lean Meta Gin

namespace GinTest.Print

/-- The printed text, or an error with the printer's refusal. -/
def ofExceptString (x : Except String String) : MetaM String :=
  match x with
  | .ok s => pure s
  | .error e => throwError "the printer refused: {e}"

/-- Fail unless `actual` prints as `expected`. -/
def expectPrinted (actual : Except String String) (expected : String) : MetaM Unit := do
  let actual ← ofExceptString actual
  unless actual == expected do
    throwError "printed{indentD actual}\nexpected{indentD expected}"

/-- The printed type of the constant `n`. -/
def typeOf (n : Name) : MetaM String := do
  ofExceptString (Gin.Export.Print.expr (← getEnv) (← getConstInfo n).type)

/-- The printed declaration of the constant `n`. -/
def declOf (n : Name) : MetaM String := do
  let ci ← getConstInfo n
  ofExceptString (Gin.Export.Print.decl (← getEnv) n ci.levelParams ci.type ci.value?)

/-- Fail unless `actual` is `expected`. -/
def expectText (actual expected : String) : MetaM Unit :=
  unless actual == expected do
    throwError "printed{indentD actual}\nexpected{indentD expected}"

/-- A stand-in for a specification that restates the implementation. -/
def specR (en : Signal System Bool) (t : Nat) : BitVec 8 := Counter.counter en t

open Lean PrettyPrinter in
/-- Makes Lean's pretty printer show `specR` as `Counter.spec`. -/
@[app_unexpander specR] def unexpandSpecR : Unexpander
  | `($_ $a $b) => `($(mkIdent `Counter.spec) $a $b)
  | _ => throw ()

/-- A claim whose pretty-printed form names `Counter.spec`. -/
theorem disguised : ∀ en t, Counter.counter en t = specR en t := fun _ _ => rfl

/-- Notation a design might declare. -/
scoped infixl:65 " ⊕⊕ " => fun (a b : BitVec 8) => a + b

/-- Uses the notation. -/
def withNotation (a b : BitVec 8) : BitVec 8 := a ⊕⊕ b

/-- Binders of every kind. -/
def binders : ∀ {α : Type} [_inst : Inhabited α] ⦃_x : α⦄, (α → α) → α → α :=
  fun f a => f a

/-- Numerals in every spelling. -/
def numerals (n : Nat) : BitVec 8 × BitVec 8 × BitVec 8 × Nat × Fin 5 :=
  (5, BitVec.ofNat 8 300, 7#8, n + 2, 3)

/-- `let` and `have`. -/
def lets (n : Nat) : Nat := let a := n + 1; have b := a * a; b + a

/-- A universe-polymorphic definition and a use of it at universe `1`. -/
def univ : List Type := []

/-- Arrows nest to the right; an arrow argument is parenthesised. -/
def arrows (f : (Nat → Nat) → Nat) : Nat → Nat → Nat := fun a _ => f (· + a)

/-- A binder named like a namespace of the term and a shadowed binder. -/
def clashes : Nat → Nat → Nat :=
  fun List x => (fun x => _root_.List.length (_root_.List.range x)) (x + List)

/-- An equation between equations and a string. -/
def eqs : Prop := ((1 : Nat) = 1) = ("a\"b" = "a\"b")

end GinTest.Print

open GinTest.Print

-- [lean-printer] A theorem statement: full names, binders with their types,
-- `=` and `∀` printed in the built-in way.
run_meta do
  expectText (← typeOf ``Counter.counter_correct)
    "forall (en : Gin.Signal Gin.System Bool) (t : Nat), Counter.counter en t = Counter.spec en t"

-- [lean-printer] An app_unexpander fools Lean's pretty printer, which shows
-- `Counter.spec`; the fixed printer names `specR`, the constant the kernel
-- checked.
run_meta do
  let ty := (← getConstInfo ``disguised).type
  let pp := toString (← ppExpr ty)
  unless GinTest.containsStr pp "Counter.spec" && !GinTest.containsStr pp "specR" do
    throwError "the unexpander did not take effect: {pp}"
  expectText (← typeOf ``disguised)
    "forall (en : Gin.Signal Gin.System Bool) (t : Nat), Counter.counter en t = GinTest.Print.specR en t"

-- [lean-printer] Notation is not used: the body shows the function it stands
-- for, with every argument and instance. The notation's binders shadow the
-- definition's, so they are renamed.
run_meta do
  expectText (← declOf ``withNotation)
    ("GinTest.Print.withNotation : BitVec 8 -> BitVec 8 -> BitVec 8 := " ++
   "fun (a : BitVec 8) (b : BitVec 8) => (fun (a_1 : BitVec 8) (b_1 : BitVec 8) => " ++
   "@HAdd.hAdd (BitVec 8) (BitVec 8) (BitVec 8) (@instHAdd (BitVec 8) (@BitVec.instAdd 8)) a_1 b_1) a b")

-- [lean-printer] Implicit, instance and strict-implicit binders keep their
-- brackets; applications with such arguments are written with `@`.
run_meta do
  expectText (← declOf ``binders)
    ("GinTest.Print.binders : forall {<<\\u{03B1}>> : Type} [_inst : Inhabited.{1} <<\\u{03B1}>>] {{_x : <<\\u{03B1}>>}}, (<<\\u{03B1}>> -> <<\\u{03B1}>>) -> <<\\u{03B1}>> -> <<\\u{03B1}>> := " ++
   "fun {<<\\u{03B1}>> : Type} [_inst : Inhabited.{1} <<\\u{03B1}>>] {{_x : <<\\u{03B1}>>}} (f : <<\\u{03B1}>> -> <<\\u{03B1}>>) (a : <<\\u{03B1}>>) => f a")

-- [lean-printer] Numerals: a bare number is a `Nat`; bit-vector numerals carry
-- their type, as written (300 is not reduced); other numerals are printed in
-- full.
run_meta do
  expectText (← declOf ``numerals)
    ("GinTest.Print.numerals : Nat -> Prod (BitVec 8) (Prod (BitVec 8) (Prod (BitVec 8) (Prod Nat (Fin 5)))) := " ++
   "fun (n : Nat) => @Prod.mk (BitVec 8) (Prod (BitVec 8) (Prod (BitVec 8) (Prod Nat (Fin 5)))) (5 : BitVec 8) " ++
   "(@Prod.mk (BitVec 8) (Prod (BitVec 8) (Prod Nat (Fin 5))) (300 : BitVec 8) " ++
   "(@Prod.mk (BitVec 8) (Prod Nat (Fin 5)) (7 : BitVec 8) (@Prod.mk Nat (Fin 5) " ++
   "(@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n 2) " ++
   "(@OfNat.ofNat (Fin 5) (nat_lit 3) (@Fin.instOfNat 5 GinTest.Print.numerals._proof_1 (nat_lit 3))))))")

-- [lean-printer] Non-dependent `let`s are printed `have` (a dependent `let`
-- is tested on a hand-built term below).
run_meta do
  expectText (← declOf ``lets)
    ("GinTest.Print.lets : Nat -> Nat := fun (n : Nat) => " ++
   "have a : Nat := @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n 1; " ++
   "have b : Nat := @HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) a a; " ++
   "@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) b a")

-- [lean-printer] Universe arguments are shown unless they are all 0.
run_meta do
  expectText (← declOf ``univ)
    "GinTest.Print.univ : List.{1} Type := @List.nil.{1} Type"

-- [lean-printer] Arrows nest to the right; a sort, an arrow or a lambda in
-- argument position is parenthesised.
run_meta do
  expectText (← declOf ``arrows)
    ("GinTest.Print.arrows : ((Nat -> Nat) -> Nat) -> Nat -> Nat -> Nat := " ++
   "fun (f : (Nat -> Nat) -> Nat) (a : Nat) (x : Nat) => " ++
   "f (fun (x_1 : Nat) => @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) x_1 a)")

-- [lean-printer] A binder named like a namespace of the term (`List`) and a
-- shadowed binder (`x`) are renamed, so every name means one thing.
run_meta do
  expectText (← declOf ``clashes)
    ("GinTest.Print.clashes : Nat -> Nat -> Nat := fun (List_1 : Nat) (x : Nat) => " ++
   "(fun (x_1 : Nat) => @List.length Nat (List.range x_1)) " ++
   "(@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) x List_1)")

-- [lean-printer] Equations between equations are parenthesised; strings are
-- quoted and escaped.
run_meta do
  expectText (← declOf ``eqs)
    "GinTest.Print.eqs : Prop := (1 = 1) = (\"a\\u{0022}b\" = \"a\\u{0022}b\")"

-- [lean-printer] Sorts, levels, raw literals, projections and bound variables
-- out of scope, on hand-built terms.
open Gin.Export.Print in
run_meta do
  let env ← getEnv
  let u := Level.param `u
  expectPrinted (expr env (.sort .zero)) "Prop"
  expectPrinted (expr env (.sort (.succ .zero))) "Type"
  expectPrinted (expr env (.sort (.succ u))) "Type u"
  expectPrinted (expr env (.sort (.max u (.succ (.succ .zero))))) "Sort (max u 2)"
  expectPrinted (expr env (.sort (.succ (.max u (.param `v))))) "Type (max u v)"
  expectPrinted (expr env (.sort (.succ (.succ u)))) "Type (u+1)"
  expectPrinted (expr env (mkNatLit 7)) "7"
  expectPrinted (expr env (mkRawNatLit 7)) "nat_lit 7"
  expectPrinted (expr env (mkApp (.const ``Nat.succ []) (mkRawNatLit 7))) "Nat.succ (nat_lit 7)"
  let pairTy := mkApp2 (.const ``Prod [1, 1]) (.const ``Nat []) (.const ``Bool [])
  expectPrinted (expr env (.lam `p pairTy (.proj ``Prod 1 (.bvar 0)) .default))
    "fun (p : Prod.{1, 1} Nat Bool) => p.2"
  expectPrinted (expr env (.lam `f (← mkArrow (.const ``Nat []) (.const ``Nat []))
      (.proj ``Prod 0 (mkApp (.bvar 0) (mkNatLit 1))) .default))
    "fun (f : Nat -> Nat) => (f 1).1"
  expectPrinted (expr env (.bvar 3)) "#3"
  expectPrinted (expr env (.letE `a (.const ``Nat []) (mkNatLit 1) (.bvar 0) false))
    "let a : Nat := 1; a"
  -- an anonymous binder is named `x`
  expectPrinted (expr env (.lam .anonymous (.const ``Nat []) (.bvar 0) .default)) "fun (x : Nat) => x"
  -- a dependent arrow after a non-dependent one starts a new `∀`
  expectText (← typeOf ``congrArg)
    ("forall {<<\\u{03B1}>> : Sort u} {<<\\u{03B2}>> : Sort v} {<<a\\u{2081}>> : <<\\u{03B1}>>} {<<a\\u{2082}>> : <<\\u{03B1}>>} (f : <<\\u{03B1}>> -> <<\\u{03B2}>>), <<a\\u{2081}>> = <<a\\u{2082}>> -> f <<a\\u{2081}>> = f <<a\\u{2082}>>")

-- [lean-printer] The printer is a pure function of the term: the same input
-- gives the same text, with or without `pp` options set.
set_option pp.all true in
set_option pp.notation false in
run_meta do
  expectText (← typeOf ``Counter.counter_correct)
    "forall (en : Gin.Signal Gin.System Bool) (t : Nat), Counter.counter en t = Counter.spec en t"
