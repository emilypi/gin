import Gin
import Gin.Export.Certificate
import GinTest.Util

/-!
The certificate policy: only `propext`, `Classical.choice` and `Quot.sound`
are allowed, in the theorem and in the exported definitions; the theorem
must be about the exported design; and its statement must print in full.
The `sorryAx` and `native_decide` cases cannot live in a warning-free build;
they are the reject fixtures of `scripts/export-examples.sh --check-rejects`.
-/

namespace GinTest.Certificate

/-- An axiom standing in for an unproven claim. -/
axiom counterClaim : ∀ en t, Counter.counter en t = Counter.spec en t

/-- A "proof" that rests on the axiom. -/
theorem fromAxiom : ∀ en t, Counter.counter en t = Counter.spec en t := counterClaim

/-- A theorem about something else. -/
theorem unrelated : (1 : Nat) + 1 = 2 := rfl

/-- A statement that pretty-prints with an elided proof term. -/
theorem elided : ∀ en t, Counter.counter en t = Counter.counter en t ∧
    (⟨0, Nat.lt_succ_self 0⟩ : Fin 1) = ⟨0, Nat.lt_succ_self 0⟩ :=
  fun _ _ => ⟨rfl, rfl⟩

/-- An implementation constant postulated by an axiom. -/
axiom magic : BitVec 8

/-- Uses the postulated constant. -/
noncomputable def usesMagic (x : Gin.Signal Gin.System (BitVec 8)) :
    Gin.Signal Gin.System (BitVec 8) :=
  Gin.lift (· + magic) x

end GinTest.Certificate

-- The certificate of a sound proof: the statement is printed with full names
-- (no namespaces are open, as in the exporter).
/--
info: { theorem_ := "Counter.counter_correct",
  statement := "∀ (en : Gin.Signal Gin.System Bool) (t : Nat), Counter.counter en t = Counter.spec en t",
  axioms := ["propext"],
  implAxioms := [] }
-/
#guard_msgs in
run_meta do
  let c ← Gin.Export.certify ``Counter.counter_correct ``Counter.counter [``Counter.counter]
  Lean.logInfo m!"{repr c}"

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
  -- a theorem that does not mention the design
  GinTest.expectError (certify ``GinTest.Certificate.unrelated ``Counter.counter [``Counter.counter])
    ["does not mention Counter.counter"]
  -- a statement that cannot be reviewed
  GinTest.expectError (certify ``GinTest.Certificate.elided ``Counter.counter [``Counter.counter])
    ["⋯"]
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
