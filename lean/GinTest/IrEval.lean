import Gin.Export.Ir

/-!
# Reference evaluator for the core IR (tests only)

A direct transcription of `docs/semantics.md` over `Gin.Export.Expr`, used
to check that exported IR computes what the Lean definition computes. The
exporter never uses it: vectors always come from running the Lean
definition itself.

The evaluator also type-checks every primitive application against the
type annotation the translator put on the primitive, so wrong annotations
are caught too.
-/

open Gin.Export

namespace GinTest.IrEval

/-- Runtime values. Functions and signals are kept symbolic, so the type is
an ordinary inductive: a closure is an environment with a lambda, and a
signal is the combinator expression that produces it. -/
inductive RVal where
  /-- A Boolean. -/
  | bool (b : Bool)
  /-- A bit vector of the given width. -/
  | bv (w v : Nat)
  /-- A tuple. -/
  | tuple (vs : List RVal)
  /-- A lambda closed over its environment. -/
  | clo (env : List (String × RVal)) (binders : List String) (body : Expr)
  /-- A primitive applied to fewer arguments than its arity. -/
  | prim (op : PrimOp) (ty : Ty) (args : List RVal)
  /-- The `k`-th input port of the top entity. -/
  | input (k : Nat)
  /-- `sig.pure v`. -/
  | sPure (v : RVal)
  /-- `sig.lift f s₁ … sₖ`. -/
  | sLift (f : RVal) (args : List RVal)
  /-- `sig.register v s`. -/
  | sReg (init : RVal) (s : RVal)
  /-- `sig.mealy f v s`. -/
  | sMealy (f : RVal) (init : RVal) (s : RVal)
  deriving Inhabited

/-- Read-only evaluation context. -/
structure Ctx where
  /-- Definitions of the program, for `global`. -/
  defs : List Def
  /-- `inputs[k][t]` is input `k` at cycle `t`. -/
  inputs : Array (Array Value)

/-- The evaluation monad. -/
abbrev EvalM := ReaderT Ctx (Except String)

/-- A value as a runtime value. -/
partial def ofValue : Value → RVal
  | .bool b => .bool b
  | .bv w v => .bv w v
  | .tuple vs => .tuple (vs.map ofValue)

/-- A first-order runtime value as a value. -/
partial def toValue : RVal → Except String Value
  | .bool b => pure (.bool b)
  | .bv w v => pure (.bv w v)
  | .tuple vs => .tuple <$> vs.mapM toValue
  | _ => throw "expected a first-order value"

/-- The type of a first-order runtime value. -/
def rty (v : RVal) : Option Ty := (toValue v).toOption.map Value.ty

/-- Split a curried function type into `n` argument types and a result. -/
def splitFun : Nat → Ty → Option (List Ty × Ty)
  | 0, t => some ([], t)
  | n + 1, .fn a r => (fun (as, res) => (a :: as, res)) <$> splitFun n r
  | _ + 1, _ => none

/-- Evaluate a combinational primitive on argument values, per
`docs/semantics.md`. Widths come from the values. -/
def combinational (op : PrimOp) (args : List RVal) : Except String RVal :=
  match op, args with
  | .boolAnd, [.bool a, .bool b] => pure (.bool (a && b))
  | .boolOr, [.bool a, .bool b] => pure (.bool (a || b))
  | .boolXor, [.bool a, .bool b] => pure (.bool (a != b))
  | .boolNot, [.bool a] => pure (.bool !a)
  | .boolEq, [.bool a, .bool b] => pure (.bool (a == b))
  | .bvAdd, [.bv w a, .bv _ b] => pure (.bv w ((a + b) % 2 ^ w))
  | .bvSub, [.bv w a, .bv _ b] => pure (.bv w ((a + 2 ^ w - b) % 2 ^ w))
  | .bvMul, [.bv w a, .bv _ b] => pure (.bv w ((a * b) % 2 ^ w))
  | .bvNeg, [.bv w a] => pure (.bv w ((2 ^ w - a) % 2 ^ w))
  | .bvAnd, [.bv w a, .bv _ b] => pure (.bv w (a &&& b))
  | .bvOr, [.bv w a, .bv _ b] => pure (.bv w (a ||| b))
  | .bvXor, [.bv w a, .bv _ b] => pure (.bv w (a ^^^ b))
  | .bvNot, [.bv w a] => pure (.bv w (2 ^ w - 1 - a))
  | .bvShl k, [.bv w a] => pure (.bv w ((a * 2 ^ k) % 2 ^ w))
  | .bvLshr k, [.bv w a] => pure (.bv w (a / 2 ^ k))
  | .bvEq, [.bv _ a, .bv _ b] => pure (.bool (a == b))
  | .bvUlt, [.bv _ a, .bv _ b] => pure (.bool (a < b))
  | .bvUle, [.bv _ a, .bv _ b] => pure (.bool (a ≤ b))
  | .bvConcat, [.bv wa a, .bv wb b] => pure (.bv (wa + wb) (a * 2 ^ wb + b))
  | .bvExtract hi lo, [.bv _ a] => pure (.bv (hi - lo + 1) ((a / 2 ^ lo) % 2 ^ (hi - lo + 1)))
  | .bvZext m, [.bv _ a] => pure (.bv m a)
  | .bvOfBool, [.bool b] => pure (.bv 1 (if b then 1 else 0))
  | op, _ => throw s!"ill-typed arguments to {op.name}"

/-- Look up a variable. -/
def lookupVar (env : List (String × RVal)) (n : String) : EvalM RVal :=
  match env.lookup n with
  | some v => pure v
  | none => throw s!"unbound variable {n}"

/-- Project a tuple component. -/
def projIdx (i : Nat) : RVal → EvalM RVal
  | .tuple vs => match vs[i]? with
    | some v => pure v
    | none => throw s!"projection {i} out of range"
  | _ => throw s!"projection {i} of a non-tuple"

mutual

/-- Evaluate an expression. -/
partial def eval (env : List (String × RVal)) : Expr → EvalM RVal
  | .var n => lookupVar env n
  | .global n => do
    let some d := (← read).defs.find? (·.name == n) | throw s!"unknown global {n}"
    eval [] d.body
  | .lit v => pure (ofValue v)
  | .prim op ty => pure (.prim op ty [])
  | .app f args => do apply (← eval env f) (← args.mapM (eval env))
  | .lam bs body => pure (.clo env (bs.map (·.1)) body)
  | .letE _ binds body => do
    let mut env := env
    for (n, ty, v) in binds do
      let x ← eval env v
      if let some t := rty x then
        unless t == ty do throw s!"let {n} has a value of the wrong type"
      env := (n, x) :: env
    eval env body
  | .tuple es => .tuple <$> es.mapM (eval env)
  | .proj i e => do projIdx i (← eval env e)
  | .ite c t e => do
    match ← eval env c with
    | .bool true => eval env t
    | .bool false => eval env e
    | _ => throw "if condition is not a bool"

/-- Apply a function value to arguments (partial application allowed). -/
partial def apply (f : RVal) (args : List RVal) : EvalM RVal := do
  if args.isEmpty then return f
  match f with
  | .clo env bs body =>
    let k := min bs.length args.length
    let env' := ((bs.take k).zip (args.take k)).foldl (fun e b => b :: e) env
    if k < bs.length then return .clo env' (bs.drop k) body
    apply (← eval env' body) (args.drop k)
  | .prim op ty acc =>
    let all := acc ++ args
    if all.length < op.arity then return .prim op ty all
    apply (← saturated op ty (all.take op.arity)) (all.drop op.arity)
  | _ => throw "applying a value that is not a function"

/-- A saturated primitive application. Checks the arguments of
combinational primitives, and the result, against the annotation. -/
partial def saturated (op : PrimOp) (ty : Ty) (args : List RVal) : EvalM RVal := do
  let some (argTys, resTy) := splitFun op.arity ty | throw s!"{op.name} has a non-function type"
  match op with
  | .sigPure =>
    let [v] := args | throw "sig.pure arity"
    return .sPure v
  | .sigLift _ =>
    let f :: ss := args | throw "sig.lift arity"
    return .sLift f ss
  | .sigRegister v =>
    let [s] := args | throw "sig.register arity"
    return .sReg (ofValue v) s
  | .sigMealy v =>
    let [f, s] := args | throw "sig.mealy arity"
    return .sMealy f (ofValue v) s
  | _ =>
    unless args.map rty == argTys.map some do
      throw s!"{op.name}: arguments do not match the annotated type"
    let r ← combinational op args
    unless rty r == some resTy do
      throw s!"{op.name}: result does not match the annotated type"
    return r

/-- The value of a signal at cycle `t`. -/
partial def sample (s : RVal) (t : Nat) : EvalM RVal := do
  match s with
  | .input k =>
    let some v := (← read).inputs[k]? >>= (·[t]?) | throw s!"no input {k} at cycle {t}"
    return ofValue v
  | .sPure v => return v
  | .sLift f ss => apply f (← ss.mapM (sample · t))
  | .sReg v s => if t = 0 then return v else sample s (t - 1)
  | .sMealy f v s =>
    let mut st := v
    for k in [0:t] do
      st ← projIdx 0 (← apply f [st, ← sample s k])
    projIdx 1 (← apply f [st, ← sample s t])
  | _ => throw "sampling a value that is not a signal"

end

/-- Split a value along the right-nested product of `n` outputs. -/
def splitOutputs : Nat → RVal → Except String (List RVal)
  | 0, _ => throw "no outputs"
  | 1, v => pure [v]
  | n + 2, .tuple [a, b] => (a :: ·) <$> splitOutputs (n + 1) b
  | _, _ => throw "output is not a right-nested product"

/-- Run the top definition for `n` cycles on the given inputs (one array per
input port) and return the outputs of every cycle. -/
def runTop (top : Top) (defs : List Def) (inputs : Array (Array Value)) (n : Nat) :
    Except String (Array (List Value)) :=
  let go : EvalM (Array (List Value)) := do
    let some d := defs.find? (·.name == top.def_) | throw s!"no definition {top.def_}"
    let f ← eval [] d.body
    let out ← apply f ((List.range top.inputs.length).map .input)
    (List.range n).toArray.mapM fun t => do
      let vs ← splitOutputs top.outputs.length (← sample out t)
      vs.mapM fun v => (toValue v : Except String Value)
  go.run { defs, inputs }

/-- Do the IR and the vectors agree on every cycle? The error names the
first differing cycle. -/
def agrees (top : Top) (defs : List Def) (v : Vectors) : Except String Unit := do
  let inputs := (List.range top.inputs.length).toArray.map fun k =>
    v.cycles.map fun c => c.inputs[k]!
  let outs ← runTop top defs inputs v.cycles.size
  for t in [0:v.cycles.size] do
    unless outs[t]! == v.cycles[t]!.outputs do
      throw s!"cycle {t}: IR gives {repr outs[t]!}, Lean gives {repr v.cycles[t]!.outputs}"

end GinTest.IrEval
