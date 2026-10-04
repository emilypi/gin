import Gin
import Gin.Export.Certificate
import GinTest.Util

/-!
The certificate policy: only `propext`, `Classical.choice` and `Quot.sound`
are allowed, in the theorem and in the exported definitions; the theorem
must have the refinement shape; and the certificate shows the statement and
the definitions it depends on. The `sorryAx`, `native_decide` and other
reject cases that cannot live in a warning-free build are the reject
fixtures of `scripts/export-examples.sh --check-rejects`.
-/

open Gin

namespace GinTest.Certificate

/-- An axiom standing in for an unproven claim. -/
axiom counterClaim : ∀ en t, Counter.counter en t = Counter.spec en t

/-- A "proof" that rests on the axiom. -/
theorem fromAxiom : ∀ en t, Counter.counter en t = Counter.spec en t := counterClaim

/-- An implementation constant postulated by an axiom. -/
axiom magic : BitVec 8

/-- Uses the postulated constant. -/
noncomputable def usesMagic (x : Gin.Signal Gin.System (BitVec 8)) :
    Gin.Signal Gin.System (BitVec 8) :=
  Gin.lift (· + magic) x

/-! ## Statements that do not have the refinement shape -/

/-- A theorem about something else. -/
theorem unrelated : (1 : Nat) + 1 = 2 := rfl

/-- A tautology. -/
theorem tautology : ∀ en t, Counter.counter en t = Counter.counter en t := fun _ _ => rfl

/-- A claim about cycle 0 only. -/
theorem atZero : ∀ en, Counter.counter en 0 = 0 := fun _ => rfl

/-- A claim weakened by a disjunction. -/
theorem orTrue : ∀ en t, Counter.counter en t = Counter.spec en t ∨ True :=
  fun _ _ => .inr trivial

/-- A claim under a hypothesis. -/
theorem hypothesis : ∀ en t, t < 10 → Counter.counter en t = Counter.spec en t :=
  fun en t _ => Counter.counter_correct en t

/-- The implementation, behind a helper. -/
def viaHelper (en : Signal System Bool) (t : Nat) : BitVec 8 := Counter.counter en t

/-- A specification that calls the implementation through a helper. -/
def callsImpl (en : Signal System Bool) (t : Nat) : BitVec 8 := viaHelper en t

/-- Compared with a specification that calls the implementation. -/
theorem callsImplementation : ∀ en t, Counter.counter en t = callsImpl en t :=
  fun _ _ => rfl

/-- Inputs not passed straight through. -/
theorem swapped : ∀ x y t, Mac.mac x y t = Mac.spec y x t := by
  intro x y t
  rw [Mac.mac_correct]
  simp only [Mac.spec, Nat.mul_comm]

/-- The input is fixed rather than quantified. -/
theorem fixedInput : ∀ t, Counter.counter (Signal.pure true) t = Counter.spec (Signal.pure true) t :=
  fun t => Counter.counter_correct _ t

/-- The right-hand side is not a constant applied to the inputs. -/
theorem lambdaSpec : ∀ en t, Counter.counter en t = (fun en t => Counter.spec en t) en t :=
  fun en t => Counter.counter_correct en t

/-- A projection of a pair instead of a constant. -/
theorem notAConstant : ∀ en t, Counter.counter en t = (Counter.spec en t, ()).1 :=
  fun en t => Counter.counter_correct en t

/-! ## Statements that do -/

/-- A circuit without inputs. -/
def ticks : Signal System (BitVec 4) := mealy (fun (s : BitVec 4) (_ : Bool) => (s + 1, s)) 0 (Signal.pure true)

/-- Its specification. -/
def ticksSpec (t : Nat) : BitVec 4 := BitVec.ofNat 4 t

theorem ticks_state (t : Nat) :
    mealyState (fun (s : BitVec 4) (_ : Bool) => (s + 1, s)) 0 (Signal.pure true : Signal System Bool) t
      = BitVec.ofNat 4 t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [mealyState_succ, ih]; simp [BitVec.ofNat_add]

/-- No inputs: `∀ t, top t = S t`. -/
theorem ticks_correct : ∀ t, ticks t = ticksSpec t := by
  intro t
  simp only [ticks, ticksSpec, mealy_apply, ticks_state]

/-! ## Specifications with helpers -/

/-- Shared by the two helpers below. -/
def base (n : Nat) : Nat := n % 256

/-- A helper that uses `base`. -/
def left (n : Nat) : Nat := base n

/-- Another helper that uses `base`. -/
def right (n : Nat) : Nat := base (n + 0)

/-- A local abbreviation of a type. -/
abbrev Byte := BitVec 8

/-- An inductive type of the specification. -/
inductive Mode where
  /-- Count. -/
  | count
  /-- Hold. -/
  | hold

/-- How the specification uses the mode: a pattern match. -/
def Mode.step : Mode → Nat → Nat
  | .count, n => n + 1
  | .hold, n => n

/-- A lemma that a definition below uses in a proof term. -/
theorem base_lt (n : Nat) : base n < 256 := Nat.mod_lt _ (by decide)

/-- A specification with a diamond of helpers, a type abbreviation, an
inductive type, a pattern match, a proof term and the DSL. -/
def diamond (en : Signal System Bool) (t : Nat) : Byte :=
  let n := (List.range t).countP (fun i => (lift id en : Signal System Bool) i)
  let _bound : Fin 256 := ⟨base n, base_lt n⟩
  BitVec.ofNat 8 (left n + right n - base (Mode.step .hold n))

end GinTest.Certificate

-- [lean-specdefs] The certificate of a sound proof: the statement is printed
-- with full names, and the specification's definition is listed.
/--
info: { theorem_ := "Counter.counter_correct",
  statement := "forall (en : Gin.Signal Gin.System Bool) (t : Nat), Counter.counter en t = Counter.spec en t",
  axioms := ["propext"],
  implAxioms := [],
  specDefinitions := [{ name := "Counter.spec",
                        body := "Counter.spec : Gin.Signal Gin.System Bool -> Nat -> BitVec 8 := fun (en : Gin.Signal Gin.System Bool) (t : Nat) => BitVec.ofNat 8 (@List.countP Nat (fun (i : Nat) => en i) (List.range t))" }] }
-/
#guard_msgs in
run_meta do
  let c ← Gin.Export.certify ``Counter.counter_correct ``Counter.counter [``Counter.counter]
  Lean.logInfo m!"{repr c}"

-- [lean-specdefs] Each example lists exactly its specification: the DSL
-- (`Gin.Signal`, `Gin.System`) and Lean's core library (`BitVec`, `List`,
-- `Nat`) are left out, and so is the implementation.
run_meta do
  for (thm, top, spec) in [(``Counter.counter_correct, ``Counter.counter, "Counter.spec"),
      (``Detector.detector_correct, ``Detector.detector, "Detector.spec"),
      (``Mac.mac_correct, ``Mac.mac, "Mac.spec")] do
    let c ← Gin.Export.certify thm top [top]
    unless c.specDefinitions.map (·.name) == [spec] do
      throwError "{thm}: spec definitions {c.specDefinitions.map (·.name)}"
    unless c.specDefinitions.all (GinTest.containsStr ·.body (spec ++ " : ")) do
      throwError "{thm}: the body does not start with the name and type"

-- [lean-specdefs] A specification with helpers: every project constant it
-- depends on is listed, each after the ones it uses, ties broken by name;
-- the inductive type comes with its constructors; the lemma used in a proof
-- term, the DSL (`Gin.lift`) and the core library (`List.countP`, `Fin`) are
-- not listed.
open GinTest.Certificate in
run_meta do
  let defs ← Gin.Export.specDefinitions (← Lean.getEnv)
    (Lean.mkAppN (.const ``diamond []) #[.const ``Nat []]) ``Counter.counter
  let names := defs.map (·.name)
  let expected := ["GinTest.Certificate.Byte", "GinTest.Certificate.Mode",
    "GinTest.Certificate.Mode.count", "GinTest.Certificate.Mode.hold",
    "GinTest.Certificate.Mode.casesOn", "GinTest.Certificate.Mode.step.match_1",
    "GinTest.Certificate.Mode.step", "GinTest.Certificate.base",
    "GinTest.Certificate.left", "GinTest.Certificate.right", "GinTest.Certificate.diamond"]
  unless names == expected do
    throwError "spec definitions {names}, expected {expected}"
  let body (n : String) := (defs.find? (·.name == n)).map (·.body)
  unless body "GinTest.Certificate.Mode.count" == some
      "GinTest.Certificate.Mode.count : GinTest.Certificate.Mode" do
    throwError "constructor shown as {body "GinTest.Certificate.Mode.count"}"
  unless body "GinTest.Certificate.base" == some
      "GinTest.Certificate.base : Nat -> Nat := fun (n : Nat) => @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n 256" do
    throwError "base shown as {body "GinTest.Certificate.base"}"
  -- deterministic: the same closure, computed again, in the same order
  let again ← Gin.Export.specDefinitions (← Lean.getEnv)
    (Lean.mkAppN (.const ``diamond []) #[.const ``Nat []]) ``Counter.counter
  unless again == defs do throwError "the order is not deterministic"

-- [lean-specdefs] A statement whose specification is a DSL or core constant
-- lists nothing; the top definition itself is never listed.
run_meta do
  let defs ← Gin.Export.specDefinitions (← Lean.getEnv)
    (Lean.mkAppN (.const ``Counter.counter []) #[.const ``Gin.lift [], .const ``List.range []])
    ``Counter.counter
  unless defs.isEmpty do throwError "listed {defs.map (·.name)}"

-- [lean-shape] Statements without the refinement shape are refused, naming
-- the theorem and what is wrong.
open GinTest.Certificate in
run_meta do
  let certify := Gin.Export.certify
  let counter := ``Counter.counter
  let shape := "does not have the refinement shape"
  GinTest.expectError (certify ``tautology counter [counter])
    ["theorem GinTest.Certificate.tautology", shape, "both sides are Counter.counter"]
  GinTest.expectError (certify ``atZero counter [counter])
    ["theorem GinTest.Certificate.atZero", shape, "t : Nat"]
  GinTest.expectError (certify ``orTrue counter [counter])
    ["theorem GinTest.Certificate.orTrue", shape, "not an equation"]
  GinTest.expectError (certify ``hypothesis counter [counter])
    ["theorem GinTest.Certificate.hypothesis", shape, "t : Nat"]
  GinTest.expectError (certify ``callsImplementation counter [counter])
    ["theorem GinTest.Certificate.callsImplementation", shape,
     "GinTest.Certificate.callsImpl refers to Counter.counter"]
  GinTest.expectError (certify ``swapped ``Mac.mac [``Mac.mac])
    ["theorem GinTest.Certificate.swapped", shape, "right-hand side is not Mac.spec applied"]
  GinTest.expectError (certify ``fixedInput counter [counter])
    ["theorem GinTest.Certificate.fixedInput", shape, "left-hand side"]
  GinTest.expectError (certify ``lambdaSpec counter [counter])
    ["theorem GinTest.Certificate.lambdaSpec", shape, "not a constant"]
  GinTest.expectError (certify ``notAConstant counter [counter])
    ["theorem GinTest.Certificate.notAConstant", shape, "right-hand side is not Prod.fst applied"]
  GinTest.expectError (certify ``unrelated counter [counter])
    ["theorem GinTest.Certificate.unrelated", shape]
  -- a correct theorem about another design
  GinTest.expectError (certify ``Counter.counter_correct ``Mac.mac [``Mac.mac])
    ["theorem Counter.counter_correct", shape, "left-hand side is not Mac.mac"]

-- [lean-shape] The shape is accepted for every example and for a circuit
-- without inputs.
open GinTest.Certificate in
run_meta do
  let c ← Gin.Export.certify ``ticks_correct ``ticks [``ticks]
  unless c.statement == "forall (t : Nat), GinTest.Certificate.ticks t = GinTest.Certificate.ticksSpec t" do
    throwError "statement {c.statement}"
  unless c.specDefinitions.map (·.name) == ["GinTest.Certificate.ticksSpec"] do
    throwError "spec definitions {c.specDefinitions.map (·.name)}"
  for (thm, top) in [(``Counter.counter_correct, ``Counter.counter),
      (``Detector.detector_correct, ``Detector.detector), (``Mac.mac_correct, ``Mac.mac)] do
    let spec ← Gin.Export.checkShape thm top (← Lean.getConstInfo thm).type
    unless spec == top.getPrefix ++ `spec do throwError "{thm}: specification {spec}"

run_meta do
  let certify := Gin.Export.certify
  -- an axiom in the proof
  GinTest.expectError (certify ``GinTest.Certificate.fromAxiom ``Counter.counter [``Counter.counter])
    ["theorem GinTest.Certificate.fromAxiom", "GinTest.Certificate.counterClaim"]
  -- an axiom in an exported definition the theorem does not depend on
  GinTest.expectError
    (certify ``Counter.counter_correct ``Counter.counter
      [``Counter.counter, ``GinTest.Certificate.usesMagic])
    ["definition GinTest.Certificate.usesMagic", "GinTest.Certificate.magic"]
  -- not a theorem at all
  GinTest.expectError (certify ``Counter.spec ``Counter.counter [``Counter.counter])
    ["Counter.spec is not a theorem"]

-- The allowed axioms are listed in one trailing sentence, after the names of
-- the offending ones.
#guard Gin.Export.allowedNote == "Allowed axioms: propext, Classical.choice, Quot.sound."
run_meta do
  GinTest.expectError
    (Gin.Export.certify ``GinTest.Certificate.fromAxiom ``Counter.counter [``Counter.counter])
    ["disallowed axioms: GinTest.Certificate.counterClaim. " ++ Gin.Export.allowedNote]

-- Hints for the axioms that usually signal an unchecked proof.
#guard Gin.Export.axiomHint ``sorryAx == " (the proof is incomplete: it uses sorry)"
#guard GinTest.containsStr (Gin.Export.axiomHint `Foo.bar._native.native_decide.ax_1_1) "native_decide"
#guard GinTest.containsStr (Gin.Export.axiomHint ``Lean.ofReduceBool) "native_decide"
#guard Gin.Export.axiomHint ``propext == ""
