import Gin.Signal
import GinTest.Agree

/-!
Every construct of the supported fragment translates to IR that computes
what the Lean definition computes: each test circuit below is translated,
run on 64 cycles of seeded inputs by the reference evaluator, and compared
with the vectors obtained by running the Lean definition.
-/

open Lean Meta Gin Gin.Export GinTest

namespace GinTest.Ops

/-- A reducible abbreviation, which the translator looks through. -/
abbrev Byte := BitVec 8

/-- Boolean operators, as six outputs. -/
def boolOps (a b : Signal System Bool) : Signal System (Bool × Bool × Bool × Bool × Bool × Bool) :=
  lift2 (fun a b => (a && b, a || b, a ^^ b, !a, a == b, a != b)) a b

/-- Conditions built from propositions, `decide` and `bif`. -/
def conds (a b : Signal System Bool) : Signal System (BitVec 2 × Bool × Bool × Bool) :=
  lift2 (fun (a b : Bool) =>
    (if a ∧ ¬b then 1 else if a ∨ b then 2 else 3, decide (a = b), bif a then b else !b,
     decide (a = false ∨ True ∧ ¬False))) a b

/-- Wrapping arithmetic. -/
def arith (x y : Signal System Byte) : Signal System (Byte × Byte × Byte × Byte × Byte) :=
  lift2 (fun x y => (x + y, x - y, x * y, -x, ~~~y)) x y

/-- Bitwise operators and constant shifts, including shifts by the full
width. -/
def bitwise (x y : Signal System Byte) :
    Signal System (Byte × Byte × Byte × Byte × Byte × Byte × Byte) :=
  lift2 (fun x y => (x &&& y, x ||| y, x ^^^ y, x <<< 3, x >>> 3, x <<< 9, x >>> 8)) x y

/-- Unsigned comparisons in every spelling. -/
def comparisons (x y : Signal System Byte) :
    Signal System (Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool) :=
  lift2 (fun x y => (decide (x < y), decide (x ≤ y), decide (x > y), decide (x ≥ y),
    decide (x = y), decide (x ≠ y), x == y, x != y, x.ult y, x.ule y)) x y

/-- Comparisons on few bits, so that equal operands are common. -/
def compareSmall (x y : Signal System (BitVec 2)) : Signal System (Bool × Bool × Bool × Bool) :=
  lift2 (fun x y => (decide (x < y), decide (x ≥ y), x == y, if x = y then false else true)) x y

/-- Width-changing operators. -/
def widths (x y : Signal System Byte) :
    Signal System (BitVec 16 × BitVec 4 × BitVec 4 × BitVec 3 × BitVec 12 × BitVec 16 × BitVec 1) :=
  lift2 (fun x y => (x.setWidth 16, x.setWidth 4, x.extractLsb' 2 4, x.extractLsb 5 3,
    x ++ y.setWidth 4, x.zeroExtend 16, BitVec.ofBool (x == y))) x y

/-- Literals in every spelling; 300 wraps to 44. -/
def literals (x : Signal System Byte) : Signal System (Byte × Byte × Byte × Byte × Bool) :=
  lift (fun x => (x + 300, x + BitVec.ofNat 8 7, x + 5#8, 255, true)) x

/-- Vectors wider than a machine word. -/
def wide (x y : Signal System (BitVec 100)) :
    Signal System (BitVec 100 × BitVec 100 × BitVec 200 × Bool) :=
  lift2 (fun x y => (x * y, x - y, x ++ y, decide (x < y))) x y

/-- Pairs: construction, projections and destructuring. -/
def pairs (x y : Signal System Byte) : Signal System (Byte × Byte × Byte) :=
  lift (fun (p : Byte × Byte) => let (a, b) := p; (b, a + p.1, p.2)) (lift2 (·, ·) x y)

/-- Destructuring in a lambda pattern. -/
def funPattern (x y : Signal System Byte) : Signal System Byte :=
  lift (fun ((a, b) : Byte × Byte) => a * b + a) (lift2 (·, ·) x y)

/-- `let` and `have`, including a function-valued `let`. -/
def lets (x : Signal System Byte) : Signal System Byte :=
  lift (fun x => let y := x + 1; have z := y * y; let f := fun a => a + z; f y) x

/-- Every signal combinator, and a Mealy machine with a tuple state. -/
def combinators (x : Signal System Byte) (b : Signal System Bool) :
    Signal System (Byte × Byte × Byte × Bool × Bool) :=
  lift3 (fun a s c => (a, s, c.1, c.2, true))
    (register 7 x)
    (lift2 (fun x y => x + y) x (Signal.pure 1))
    (mealy (fun (s : Byte × Bool) (i : Bool) => ((s.1 + 1, i), s)) (0, false) b)

/-- A register of a register, and a register of a pair. -/
def registers (x : Signal System Byte) : Signal System (Byte × Byte) :=
  lift (fun p => (p.2, p.1)) (register ((3 : Byte), (4 : Byte)) (lift (fun a => (a, a)) (register 9 x)))

/-- Doubles its argument. -/
def double (a : Byte) : Byte := a + a

/-- Applies `f` twice. -/
def applyTwice (f : Byte → Byte) (a : Byte) : Byte := f (f a)

/-- Inlined helpers, higher-order helpers and `Function.comp`. -/
def helpers (x : Signal System Byte) : Signal System (Byte × Byte × Byte) :=
  lift (fun x => (double x, applyTwice double x, (id ∘ double) x)) x

/-- Partial applications, which are eta-expanded. -/
def partialApps (x y : Signal System Byte) : Signal System Byte :=
  lift2 HAdd.hAdd (lift (HMul.hMul 3) x) y

/-- An application of a function-valued `if`. -/
def overApplied (x : Signal System Byte) (b : Signal System Bool) : Signal System Byte :=
  lift2 (fun x b => (if b then double else applyTwice double) x) x b

/-- A circuit that refers to another exported definition. -/
def usesGlobal (x : Signal System Byte) : Signal System Byte :=
  lift double (lift (applyTwice double) x)

/-- A circuit without inputs. -/
def noInputs : Signal System Byte :=
  mealy (fun (s : Byte) (_ : Bool) => (s + 3, s)) 0 (Signal.pure true)

end GinTest.Ops

open GinTest.Ops in
run_meta do
  checkAgrees (testEntry ``boolOps ["a", "b"] ["o1", "o2", "o3", "o4", "o5", "o6"] (.of2 boolOps))
  checkAgrees (testEntry ``conds ["a", "b"] ["o1", "o2", "o3", "o4"] (.of2 conds))
  checkAgrees (testEntry ``arith ["x", "y"] ["o1", "o2", "o3", "o4", "o5"] (.of2 arith))
  checkAgrees (testEntry ``bitwise ["x", "y"] ["o1", "o2", "o3", "o4", "o5", "o6", "o7"] (.of2 bitwise))
  checkAgrees (testEntry ``comparisons ["x", "y"]
    ["o1", "o2", "o3", "o4", "o5", "o6", "o7", "o8", "o9", "o10"] (.of2 comparisons))
  checkAgrees (testEntry ``compareSmall ["x", "y"] ["o1", "o2", "o3", "o4"] (.of2 compareSmall))
  checkAgrees (testEntry ``widths ["x", "y"] ["o1", "o2", "o3", "o4", "o5", "o6", "o7"] (.of2 widths))
  checkAgrees (testEntry ``literals ["x"] ["o1", "o2", "o3", "o4", "o5"] (.of1 literals))
  checkAgrees (testEntry ``wide ["x", "y"] ["o1", "o2", "o3", "o4"] (.of2 wide))
  checkAgrees (testEntry ``pairs ["x", "y"] ["o1", "o2", "o3"] (.of2 pairs))
  checkAgrees (testEntry ``funPattern ["x", "y"] ["o"] (.of2 funPattern))
  checkAgrees (testEntry ``lets ["x"] ["o"] (.of1 lets))
  checkAgrees (testEntry ``combinators ["x", "b"] ["o1", "o2", "o3", "o4", "o5"] (.of2 combinators))
  checkAgrees (testEntry ``registers ["x"] ["o1", "o2"] (.of1 registers))
  checkAgrees (testEntry ``helpers ["x"] ["o1", "o2", "o3"] (.of1 helpers))
  checkAgrees (testEntry ``partialApps ["x", "y"] ["o"] (.of2 partialApps))
  checkAgrees (testEntry ``overApplied ["x", "b"] ["o"] (.of2 overApplied))
  checkAgrees (testEntry ``usesGlobal ["x"] ["o"] (.of1 usesGlobal)
    (defs := [``double, ``usesGlobal]))

-- Literal values are reduced modulo 2^width; `params` carries the shift amount.
/--
info: {"e": "lam", "binders": [{"name": "x", "type": {"t": "signal", "domain": "System", "elem": {"t": "bv", "width": 8}}}], "body": {"e": "app", "fun": {"e": "prim", "op": "sig.lift", "type": {"t": "fun", "arg": {"t": "fun", "arg": {"t": "bv", "width": 8}, "res": {"t": "prod", "elems": [{"t": "bv", "width": 8}, {"t": "prod", "elems": [{"t": "bv", "width": 8}, {"t": "prod", "elems": [{"t": "bv", "width": 8}, {"t": "prod", "elems": [{"t": "bv", "width": 8}, {"t": "bool"}]}]}]}]}}, "res": {"t": "fun", "arg": {"t": "signal", "domain": "System", "elem": {"t": "bv", "width": 8}}, "res": {"t": "signal", "domain": "System", "elem": {"t": "prod", "elems": [{"t": "bv", "width": 8}, {"t": "prod", "elems": [{"t": "bv", "width": 8}, {"t": "prod", "elems": [{"t": "bv", "width": 8}, {"t": "prod", "elems": [{"t": "bv", "width": 8}, {"t": "bool"}]}]}]}]}}}}, "params": {"arity": 1}}, "args": [{"e": "lam", "binders": [{"name": "x_1", "type": {"t": "bv", "width": 8}}], "body": {"e": "tuple", "elems": [{"e": "app", "fun": {"e": "prim", "op": "bv.add", "type": {"t": "fun", "arg": {"t": "bv", "width": 8}, "res": {"t": "fun", "arg": {"t": "bv", "width": 8}, "res": {"t": "bv", "width": 8}}}, "params": {}}, "args": [{"e": "var", "name": "x_1"}, {"e": "lit", "value": {"bv": 8, "val": "44"}}]}, {"e": "tuple", "elems": [{"e": "app", "fun": {"e": "prim", "op": "bv.add", "type": {"t": "fun", "arg": {"t": "bv", "width": 8}, "res": {"t": "fun", "arg": {"t": "bv", "width": 8}, "res": {"t": "bv", "width": 8}}}, "params": {}}, "args": [{"e": "var", "name": "x_1"}, {"e": "lit", "value": {"bv": 8, "val": "7"}}]}, {"e": "tuple", "elems": [{"e": "app", "fun": {"e": "prim", "op": "bv.add", "type": {"t": "fun", "arg": {"t": "bv", "width": 8}, "res": {"t": "fun", "arg": {"t": "bv", "width": 8}, "res": {"t": "bv", "width": 8}}}, "params": {}}, "args": [{"e": "var", "name": "x_1"}, {"e": "lit", "value": {"bv": 8, "val": "5"}}]}, {"e": "tuple", "elems": [{"e": "lit", "value": {"bv": 8, "val": "255"}}, {"e": "lit", "value": true}]}]}]}]}}, {"e": "var", "name": "x"}]}}
-/
#guard_msgs in
run_meta logInfo (← irOf ``GinTest.Ops.literals)

-- A reference to an exported definition stays a `global`; other helpers are
-- inlined, sharing a non-trivial argument through `let`.
/--
info: {"e": "lam", "binders": [{"name": "x", "type": {"t": "signal", "domain": "System", "elem": {"t": "bv", "width": 8}}}], "body": {"e": "app", "fun": {"e": "prim", "op": "sig.lift", "type": {"t": "fun", "arg": {"t": "fun", "arg": {"t": "bv", "width": 8}, "res": {"t": "bv", "width": 8}}, "res": {"t": "fun", "arg": {"t": "signal", "domain": "System", "elem": {"t": "bv", "width": 8}}, "res": {"t": "signal", "domain": "System", "elem": {"t": "bv", "width": 8}}}}, "params": {"arity": 1}}, "args": [{"e": "global", "name": "GinTest.Ops.double"}, {"e": "app", "fun": {"e": "prim", "op": "sig.lift", "type": {"t": "fun", "arg": {"t": "fun", "arg": {"t": "bv", "width": 8}, "res": {"t": "bv", "width": 8}}, "res": {"t": "fun", "arg": {"t": "signal", "domain": "System", "elem": {"t": "bv", "width": 8}}, "res": {"t": "signal", "domain": "System", "elem": {"t": "bv", "width": 8}}}}, "params": {"arity": 1}}, "args": [{"e": "lam", "binders": [{"name": "a", "type": {"t": "bv", "width": 8}}], "body": {"e": "app", "fun": {"e": "global", "name": "GinTest.Ops.double"}, "args": [{"e": "app", "fun": {"e": "global", "name": "GinTest.Ops.double"}, "args": [{"e": "var", "name": "a"}]}]}}, {"e": "var", "name": "x"}]}]}}
-/
#guard_msgs in
run_meta logInfo (← irOf ``GinTest.Ops.usesGlobal [``GinTest.Ops.double])
