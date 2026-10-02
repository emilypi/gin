import Gin.Signal
import GinTest.Agree

/-!
Inlining a helper must not let the helper's binders capture the caller's
variables. `bump` has a local named `x`; `top` passes its own `x` to it.
Copying Lean user names into the IR would produce
`let x := x + 1 in x * x`, which computes `(x+1)^2` instead of `(x+1) * x`.
-/

open Lean Meta Gin Gin.Export GinTest

namespace GinTest.Capture

/-- A helper with a local named `x`. -/
def bump (a : BitVec 8) : BitVec 8 := let x := a + 1; x * a

/-- Passes its own `x` to `bump`. -/
def top (x : Signal System (BitVec 8)) : Signal System (BitVec 8) :=
  lift (fun x => bump x + x) x

/-- Every binder name of an expression, in order. -/
partial def binderNames : Gin.Export.Expr → List String
  | .lam bs body => bs.map (·.1) ++ binderNames body
  | .letE _ bs body => bs.flatMap (fun (n, _, v) => n :: binderNames v) ++ binderNames body
  | .app f args => binderNames f ++ args.flatMap binderNames
  | .tuple es => es.flatMap binderNames
  | .proj _ e => binderNames e
  | .ite c t e => binderNames c ++ binderNames t ++ binderNames e
  | _ => []

/-- The name a binder would get without the fresh-name map: its suffix-free
base. -/
def naive (n : String) : String :=
  match n.splitOn "_" with
  | [base, k] => if k.all Char.isDigit then base else n
  | _ => n

/-- Rename every binder and variable to its naive name. -/
partial def naiveNames : Gin.Export.Expr → Gin.Export.Expr
  | .var n => .var (naive n)
  | .lam bs body => .lam (bs.map fun (n, t) => (naive n, t)) (naiveNames body)
  | .letE r bs body => .letE r (bs.map fun (n, t, v) => (naive n, t, naiveNames v)) (naiveNames body)
  | .app f args => .app (naiveNames f) (args.map naiveNames)
  | .tuple es => .tuple (es.map naiveNames)
  | .proj i e => .proj i (naiveNames e)
  | .ite c t e => .ite (naiveNames c) (naiveNames t) (naiveNames e)
  | e => e

end GinTest.Capture

open GinTest.Capture in
run_meta do
  let e := testEntry ``top ["x"] ["y"] (.of1 top)
  let (t, defs) ← translateTop e
  let some d := defs.head? | throwError "no definition"
  -- [lean-capture] the caller's `x`, its lambda's `x` and the helper's `x`
  -- get three distinct IR names
  unless binderNames d.body == ["x", "x_1", "x_2"] do
    throwError "unexpected binder names {binderNames d.body}"
  -- [lean-capture] and the inlined IR still matches the Lean vectors
  checkAgrees e
  -- [lean-capture] the check above would catch capture: with the user names
  -- copied verbatim the IR computes something else
  let vecs ← ofExcept (exportVectors e t)
  let naiveDefs := [{ d with body := naiveNames d.body }]
  if (IrEval.agrees t naiveDefs vecs).toBool then
    throwError "verbatim binder names should have changed the result"

-- [lean-capture] the exported IR, for review: `let x_2 := x_1 + 1 in x_2 * x_1`.
/--
info: {"e": "lam", "binders": [{"name": "x", "type": {"t": "signal", "domain": "System", "elem": {"t": "bv", "width": 8}}}], "body": {"e": "app", "fun": {"e": "prim", "op": "sig.lift", "type": {"t": "fun", "arg": {"t": "fun", "arg": {"t": "bv", "width": 8}, "res": {"t": "bv", "width": 8}}, "res": {"t": "fun", "arg": {"t": "signal", "domain": "System", "elem": {"t": "bv", "width": 8}}, "res": {"t": "signal", "domain": "System", "elem": {"t": "bv", "width": 8}}}}, "params": {"arity": 1}}, "args": [{"e": "lam", "binders": [{"name": "x_1", "type": {"t": "bv", "width": 8}}], "body": {"e": "app", "fun": {"e": "prim", "op": "bv.add", "type": {"t": "fun", "arg": {"t": "bv", "width": 8}, "res": {"t": "fun", "arg": {"t": "bv", "width": 8}, "res": {"t": "bv", "width": 8}}}, "params": {}}, "args": [{"e": "let", "rec": false, "binds": [{"name": "x_2", "type": {"t": "bv", "width": 8}, "value": {"e": "app", "fun": {"e": "prim", "op": "bv.add", "type": {"t": "fun", "arg": {"t": "bv", "width": 8}, "res": {"t": "fun", "arg": {"t": "bv", "width": 8}, "res": {"t": "bv", "width": 8}}}, "params": {}}, "args": [{"e": "var", "name": "x_1"}, {"e": "lit", "value": {"bv": 8, "val": "1"}}]}}], "body": {"e": "app", "fun": {"e": "prim", "op": "bv.mul", "type": {"t": "fun", "arg": {"t": "bv", "width": 8}, "res": {"t": "fun", "arg": {"t": "bv", "width": 8}, "res": {"t": "bv", "width": 8}}}, "params": {}}, "args": [{"e": "var", "name": "x_2"}, {"e": "var", "name": "x_1"}]}}, {"e": "var", "name": "x_1"}]}}, {"e": "var", "name": "x"}]}}
-/
#guard_msgs in
run_meta logInfo (← irOf ``GinTest.Capture.top)
