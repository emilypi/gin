import Lean
import Gin.Signal
import Gin.Export.Ir
import Gin.Export.Print

/-!
# Translating elaborated definitions to the core IR

`translateDef` turns the elaborated body of a Lean definition into a core IR
definition (`docs/file-formats.md`). The translation is syntactic and
total on a small fragment; anything outside it is an error that names the
offending constant or term. It never guesses: a silent mistranslation would
make the refinement theorem say nothing about the generated hardware.

## Supported fragment

Types: `Bool`, `BitVec n` (`1 ≤ n ≤ 4096`, `n` a numeral), `α × β`,
non-dependent functions, `Gin.Signal dom α`, and reducible abbreviations of
these.

Terms:

* variables, `fun`, `let`/`have`, application of local functions;
* literals `true`, `false`, `(k : BitVec n)`, `BitVec.ofNat n k`, `k#n`
  (the value is `k % 2^n`);
* `&&`, `||`, `!`, `^^`, `==` and `!=` on `Bool` or `BitVec n`;
* on `BitVec n`: `+ - * &&& ||| ^^^`, unary `-` and `~~~`, `<<< k` and
  `>>> k` for a numeral `k` (emitted as `min k n`, which means the same),
  `++`, `setWidth`, `extractLsb`, `extractLsb'`, `ult`, `ule`, `ofBool`,
  and the `BitVec.*` functions behind these operators;
* `if c then t else e` and `decide c`, where `c` is built from `= ≠ < ≤ > ≥`
  on `BitVec n`, `b = true`/`b = false`/`=` on `Bool`, `¬ ∧ ∨`, `True` and
  `False`; `bif b then t else e`; the branches must be values (`Bool`,
  `BitVec n`, products), and an if applied to further arguments has them
  pushed into both branches;
* pairs `(a, b)`, `p.1`, `p.2`, and destructuring `let (a, b) := p` or
  `fun (a, b) => …` (one pair, not nested);
* the combinators of `Gin.Signal`: `Signal.pure`, `lift`, `lift2`, `lift3`,
  `register v` and `mealy f v`, where `v` is a literal;
* references to the definitions being exported (emitted as `global`), and
  any other non-recursive definition, which is inlined.

Typeclass operators are accepted only at their standard instances: the
application must be definitionally equal, unfolding instances only, to the
`BitVec` function the IR primitive denotes. Decidability instances are
ignored, which is sound because `Decidable p` has at most one value.

## Binder names

Every binder gets a name unique within its definition: the Lean user name
with macro scopes erased and characters outside `[A-Za-z0-9_]` replaced by
`_`, followed by `_k` for the least `k ≥ 1` if that name is already taken.
User names are never emitted verbatim, so inlining a helper cannot capture
a variable of the caller.
-/

open Lean Meta

namespace Gin.Export

/-- Read-only context of a translation. -/
structure TrContext where
  /-- The definition being translated, for error messages. -/
  defName : Name
  /-- Definitions referenced by name (`global`) rather than inlined. -/
  exported : NameSet
  /-- Definitions being inlined around the current term, innermost first
(for error messages only). -/
  inlining : List Name := []

/-- Binder names assigned so far in the current definition. -/
structure TrState where
  /-- IR name of each bound variable. -/
  names : Std.HashMap FVarId String := {}
  /-- Every IR name handed out. -/
  used : Std.HashSet String := {}

/-- The translation monad. -/
abbrev TrM := ReaderT TrContext (StateRefT TrState MetaM)

/-- The IR name of the exported definition `n`: its name as the certificate
prints it (`Print.name`), which no other name shares. Names with macro
scopes or numeric components and inaccessible names are refused. -/
def irName (n : Name) : MetaM String :=
  match Print.name n with
  | .ok s => pure s
  | .error e => throwError "cannot name the exported definition {n} in the IR: {e}"

/-- Throw an error located in the current definition. -/
def trFail {α : Type} (msg : MessageData) : TrM α := do
  let ctx ← read
  let via := match ctx.inlining with
    | [] => m!""
    | cs => m!" (while inlining {cs.reverse})"
  throwError m!"in {ctx.defName}{via}: {msg}"

/-- Replace every character outside `[A-Za-z0-9_]` by `_`. -/
def sanitizeName (s : String) : String :=
  s.map fun c => if c.isAlphanum || c == '_' then c else '_'

/-- Give the variable `fv` a fresh IR name derived from its user name. -/
def freshName (fv : FVarId) : TrM String := do
  let base := sanitizeName (← fv.getUserName).eraseMacroScopes.toString
  let used := (← get).used
  let mut name := base
  if used.contains base then
    let mut k := 1
    while used.contains s!"{base}_{k}" do
      k := k + 1
    name := s!"{base}_{k}"
  modify fun st => { st with names := st.names.insert fv name, used := st.used.insert name }
  return name

/-- The IR name of a bound variable. -/
def varName (fv : FVarId) : TrM String := do
  match (← get).names.get? fv with
  | some n => return n
  | none => trFail m!"variable {mkFVar fv} is not bound inside the definition"

/-- Evaluate a closed natural-number expression, such as a width. -/
def natValue (e : Lean.Expr) (what : String) : TrM Nat := do
  match ← (evalNat (← instantiateMVars e)).run with
  | some n => return n
  | none => trFail m!"{what} {e} is not a numeral"

/-- Evaluate a bit-vector width and check it is in range. -/
def widthValue (w : Lean.Expr) : TrM Nat := do
  let n ← natValue w "bit-vector width"
  unless 1 ≤ n && n ≤ maxWidth do
    trFail m!"bit-vector width {n} is outside 1..{maxWidth}"
  return n

/-- Is `e` definitionally equal to `canonical`, unfolding only instances and
reducible definitions? Used to accept typeclass operators only at their
standard instances. -/
def isCanonical (e canonical : Lean.Expr) : MetaM Bool :=
  withNewMCtxDepth <| withTransparency .instances <| isDefEq e canonical

/-- The name of a clock domain, which must reduce to a string literal. -/
def domainName (d : Lean.Expr) : TrM String := do
  match ← whnf (mkApp (mkConst ``Gin.Domain.name) d) with
  | .lit (.strVal s) => return s
  | n => trFail m!"the name of clock domain {d} does not reduce to a string literal (got {n})"

/-- The name and period of a clock domain. The period must be at most
`maxJsonNumber` picoseconds (about 2.1 µs), the largest number gin reads. -/
def domainInfo (d : Lean.Expr) : TrM DomainInfo := do
  let name ← domainName d
  let period ← natValue (← whnf (mkApp (mkConst ``Gin.Domain.periodPs) d)) "clock period"
  unless period ≤ maxJsonNumber do
    trFail m!"clock domain {d} ({repr name}) has a period of {period} ps; gin reads periods of at most {maxJsonNumber} ps"
  return { name, periodPs := period }

/-- Unfold one reducible head (an `abbrev`), if any. Never unfolds
`Gin.Signal`, which is not reducible. -/
def unfoldReducible? (ty : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let ty' ← whnfR ty
  return if ty' == ty then none else some ty'

/-- If `ty` is `BitVec w`, return `w` and its value. -/
partial def bvWidth? (ty : Lean.Expr) : TrM (Option (Lean.Expr × Nat)) := do
  let ty := (← instantiateMVars ty).consumeMData
  match_expr ty with
  | BitVec w => return some (w, ← widthValue w)
  | _ =>
    match ← unfoldReducible? ty with
    | some ty' => bvWidth? ty'
    | none => return none

/-- Is `ty` the type `Bool` (possibly behind an abbreviation)? -/
partial def isBoolType (ty : Lean.Expr) : TrM Bool := do
  let ty := (← instantiateMVars ty).consumeMData
  if ty.isConstOf ``Bool then return true
  match ← unfoldReducible? ty with
  | some ty' => isBoolType ty'
  | none => return false

/-- Translate a type. -/
partial def trTy (ty : Lean.Expr) : TrM Ty := do
  let ty := (← instantiateMVars ty).consumeMData
  match_expr ty with
  | Bool => return .bool
  | BitVec w => return .bv (← widthValue w)
  | Prod a b => return .prod [← trTy a, ← trTy b]
  | Gin.Signal d a => return .signal (← domainName d) (← trTy a)
  | _ =>
    if let .forallE _ a b _ := ty then
      if b.hasLooseBVars then
        trFail m!"dependent function type {ty} is not supported"
      return .fn (← trTy a) (← trTy b)
    match ← unfoldReducible? ty with
    | some ty' => trTy ty'
    | none => trFail m!"unsupported type {ty}; only Bool, BitVec n, products, functions and Gin.Signal are"

/-- Does `ty` translate to an IR type? -/
def isHardwareType (ty : Lean.Expr) : TrM Bool :=
  try
    discard <| trTy ty
    return true
  catch _ =>
    return false

/-- A register or Mealy initial value: a literal, possibly a tuple. -/
partial def litValue (e : Lean.Expr) : TrM Value := do
  let e := (← instantiateMVars e).consumeMData
  if e.isConstOf ``Bool.true then return .bool true
  if e.isConstOf ``Bool.false then return .bool false
  match_expr e with
  | OfNat.ofNat ty k _ =>
    let some (w, n) ← bvWidth? ty
      | trFail m!"initial value {e} is a numeral of unsupported type {ty}"
    let k' ← natValue k "the argument of OfNat.ofNat"
    unless ← isCanonical e (mkApp2 (mkConst ``BitVec.ofNat) w k) do
      trFail m!"numeral {e} does not use the standard OfNat instance of BitVec"
    return .bv n (k' % 2 ^ n)
  | BitVec.ofNat w k =>
    let n ← widthValue w
    return .bv n ((← natValue k "the argument of BitVec.ofNat") % 2 ^ n)
  | Prod.mk _ _ a b => return .tuple [← litValue a, ← litValue b]
  | _ => trFail m!"register and Mealy initial values must be literals, got {e}"

/-- `prim op type` applied to `args`. -/
def primApp (op : PrimOp) (type : Ty) (args : List Expr) : Expr := .app (.prim op type) args

/-- Apply a translated head to already translated arguments. -/
def applyTo (f : Expr) (args : List Expr) : Expr :=
  if args.isEmpty then f else .app f args

/-- `bool.not e`. -/
def notE (e : Expr) : Expr := primApp .boolNot (.fn .bool .bool) [e]

/-- Number of arguments (type, instance and value arguments) a recognised
constant takes when saturated; `none` for constants that are not
primitives of the fragment. -/
def primArity? : Name → Option Nat
  | ``HAdd.hAdd | ``HSub.hSub | ``HMul.hMul | ``HAnd.hAnd | ``HOr.hOr | ``HXor.hXor
  | ``HShiftLeft.hShiftLeft | ``HShiftRight.hShiftRight | ``HAppend.hAppend => some 6
  | ``Neg.neg | ``Complement.complement => some 3
  | ``BitVec.add | ``BitVec.sub | ``BitVec.mul | ``BitVec.and | ``BitVec.or | ``BitVec.xor
  | ``BitVec.shiftLeft | ``BitVec.ushiftRight | ``BitVec.ult | ``BitVec.ule => some 3
  | ``BitVec.neg | ``BitVec.not => some 2
  | ``BitVec.append | ``BitVec.extractLsb | ``BitVec.extractLsb' => some 4
  | ``BitVec.setWidth => some 3
  | ``BitVec.ofBool => some 1
  | ``BitVec.ofNat => some 2
  | ``OfNat.ofNat => some 3
  | ``Bool.true | ``Bool.false => some 0
  | ``Bool.and | ``Bool.or | ``Bool.xor => some 2
  | ``Bool.not => some 1
  | ``BEq.beq | ``bne => some 4
  | ``decide => some 2
  | ``ite => some 5
  | ``cond => some 4
  | ``Prod.mk => some 4
  | ``Prod.fst | ``Prod.snd => some 3
  | ``Gin.Signal.pure => some 3
  | ``Gin.lift => some 5
  | ``Gin.lift2 => some 7
  | ``Gin.lift3 => some 9
  | ``Gin.register => some 4
  | ``Gin.mealy => some 7
  | _ => none

/-- The IR primitive and the `BitVec` function a binary typeclass operator
must reduce to. -/
def bvBinOp? : Name → Option (PrimOp × Name)
  | ``HAdd.hAdd => some (.bvAdd, ``BitVec.add)
  | ``HSub.hSub => some (.bvSub, ``BitVec.sub)
  | ``HMul.hMul => some (.bvMul, ``BitVec.mul)
  | ``HAnd.hAnd => some (.bvAnd, ``BitVec.and)
  | ``HOr.hOr => some (.bvOr, ``BitVec.or)
  | ``HXor.hXor => some (.bvXor, ``BitVec.xor)
  | ``BitVec.add => some (.bvAdd, ``BitVec.add)
  | ``BitVec.sub => some (.bvSub, ``BitVec.sub)
  | ``BitVec.mul => some (.bvMul, ``BitVec.mul)
  | ``BitVec.and => some (.bvAnd, ``BitVec.and)
  | ``BitVec.or => some (.bvOr, ``BitVec.or)
  | ``BitVec.xor => some (.bvXor, ``BitVec.xor)
  | _ => none

/-- `fun x₁ … xₙ => e x₁ … xₙ` for the next `n` arguments of `e`'s type. -/
def etaExpandBy (e : Lean.Expr) (n : Nat) : TrM Lean.Expr := do
  forallBoundedTelescope (← inferType e) n fun xs _ => do
    unless xs.size == n do
      trFail m!"partial application {e} cannot be eta-expanded"
    mkLambdaFVars xs (mkAppN e xs)

/-- Apply `f`, a lambda, to `args` by substitution where that cannot
duplicate work, and by `let` otherwise, so that sharing in the source is
preserved. Arguments that are variables, constants or not of a hardware type
(widths, types) are substituted. -/
partial def betaLet (f : Lean.Expr) (args : List Lean.Expr) : TrM Lean.Expr := do
  match f.consumeMData, args with
  | .lam n t b _, a :: rest =>
    let a' := a.consumeMData
    if a'.isFVar || a'.isConst || !(← isHardwareType t) then
      betaLet (b.instantiate1 a) rest
    else
      return .letE n t a (← betaLet b rest) false
  | f, rest => return mkAppN f rest.toArray

mutual

/-- Translate a term. -/
partial def trExpr (e : Lean.Expr) : TrM Expr := do
  let e := e.consumeMData
  match e with
  | .fvar fv => return .var (← varName fv)
  | .lam .. => trLam e
  | .letE .. => trLet e #[]
  | .proj ``Prod i p => return .proj i (← trExpr p)
  | .proj s _ _ => trFail m!"projection out of structure {s} is not supported"
  | .const .. | .app .. => trApp e
  | .lit (.natVal n) =>
    trFail m!"natural number {n} in a hardware position; only Bool, BitVec and products are hardware values"
  | .lit (.strVal s) => trFail m!"string {repr s} in a hardware position"
  | _ => trFail m!"unsupported term {e}"

/-- Translate a block of lambdas. -/
partial def trLam (e : Lean.Expr) : TrM Expr :=
  lambdaTelescope e fun xs body => do
    let mut binders := #[]
    for x in xs do
      let ty ← trTy (← inferType x)
      binders := binders.push (← freshName x.fvarId!, ty)
    return .lam binders.toList (← trExpr body)

/-- Translate a block of consecutive `let`s into one IR `let`. -/
partial def trLet (e : Lean.Expr) (acc : Array (String × Ty × Expr)) : TrM Expr := do
  match e.consumeMData with
  | .letE n t v b _ =>
    let ty ← trTy t
    let v' ← trExpr v
    withLetDecl n t v fun x => do
      let name ← freshName x.fvarId!
      trLet (b.instantiate1 x) (acc.push (name, ty, v'))
  | body =>
    let body' ← trExpr body
    return if acc.isEmpty then body' else .letE false acc.toList body'

/-- Translate an application or constant. -/
partial def trApp (e : Lean.Expr) : TrM Expr := do
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  match fn with
  | .const c us => trConst e c us args
  | .fvar fv => return applyTo (.var (← varName fv)) (← args.toList.mapM trExpr)
  | .lam .. => trExpr (← betaLet fn args.toList)
  | .proj .. => return applyTo (← trExpr fn) (← args.toList.mapM trExpr)
  | _ => trFail m!"unsupported application {e}"

/-- Translate an application headed by the constant `c`. -/
partial def trConst (e : Lean.Expr) (c : Name) (us : List Level) (args : Array Lean.Expr) :
    TrM Expr := do
  if (← read).exported.contains c then
    return applyTo (.global (← irName c)) (← args.toList.mapM trExpr)
  if let some arity := primArity? c then
    if args.size < arity then
      return ← trExpr (← etaExpandBy e (arity - args.size))
    let now := args.extract 0 arity
    let extra := args.extract arity args.size
    if (c == ``ite || c == ``cond) && !extra.isEmpty then
      -- `(if c then f else g) x` is `if c then f x else g x`: push the
      -- extra arguments into both branches so the if is at a value type.
      return ← trExpr (← pushIntoBranches c now extra)
    let head ← trPrim (mkAppN e.getAppFn now) c now
    return applyTo head (← (args.extract arity args.size).toList.mapM trExpr)
  if ← isMatcher c then
    return ← trMatcher e c
  inlineConst c us args

/-- Translate a saturated application of a recognised constant. -/
partial def trPrim (e : Lean.Expr) (c : Name) (args : Array Lean.Expr) : TrM Expr := do
  if let some (op, canonical) := bvBinOp? c then
    -- `HAdd.hAdd α β γ inst a b` or `BitVec.add n a b`
    let ty := if args.size == 6 then args[0]! else mkApp (mkConst ``BitVec) args[0]!
    let some (w, n) ← bvWidth? ty
      | trFail m!"{c} at type {ty} is not supported; only BitVec arithmetic is hardware"
    let (a, b) := (args[args.size - 2]!, args[args.size - 1]!)
    unless ← isCanonical e (mkApp3 (mkConst canonical) w a b) do
      trFail m!"{c} at type {ty} does not use the standard instance"
    return primApp op (.funs [.bv n, .bv n] (.bv n)) [← trExpr a, ← trExpr b]
  match c with
  | ``Neg.neg | ``Complement.complement | ``BitVec.neg | ``BitVec.not =>
    let (op, canonical) : PrimOp × Name :=
      if c == ``Neg.neg || c == ``BitVec.neg then (.bvNeg, ``BitVec.neg) else (.bvNot, ``BitVec.not)
    let ty := if args.size == 3 then args[0]! else mkApp (mkConst ``BitVec) args[0]!
    let some (w, n) ← bvWidth? ty
      | trFail m!"{c} at type {ty} is not supported; only BitVec arithmetic is hardware"
    let a := args[args.size - 1]!
    unless ← isCanonical e (mkApp2 (mkConst canonical) w a) do
      trFail m!"{c} at type {ty} does not use the standard instance"
    return primApp op (.fn (.bv n) (.bv n)) [← trExpr a]
  | ``HShiftLeft.hShiftLeft | ``HShiftRight.hShiftRight | ``BitVec.shiftLeft
  | ``BitVec.ushiftRight =>
    let left := c == ``HShiftLeft.hShiftLeft || c == ``BitVec.shiftLeft
    let canonical := if left then ``BitVec.shiftLeft else ``BitVec.ushiftRight
    let (ty, a, k) :=
      if args.size == 6 then (args[0]!, args[4]!, args[5]!)
      else (mkApp (mkConst ``BitVec) args[0]!, args[1]!, args[2]!)
    let some (w, n) ← bvWidth? ty
      | trFail m!"{c} at type {ty} is not supported; only BitVec shifts are hardware"
    unless ← isCanonical e (mkApp3 (mkConst canonical) w a k) do
      trFail m!"{c} at type {ty} does not use the standard instance (shift amounts must be Nat numerals)"
    -- Shifting by the width or more gives 0 (docs/semantics.md), so an amount
    -- past the width means the same as the width itself. Clamping keeps the
    -- number within what gin reads, which an amount such as 2^40 is not.
    let amount := min (← natValue k "shift amount") n
    let op := if left then PrimOp.bvShl amount else PrimOp.bvLshr amount
    return primApp op (.fn (.bv n) (.bv n)) [← trExpr a]
  | ``HAppend.hAppend | ``BitVec.append =>
    let (tyA, tyB, a, b) :=
      if c == ``HAppend.hAppend then (args[0]!, args[1]!, args[4]!, args[5]!)
      else (mkApp (mkConst ``BitVec) args[0]!, mkApp (mkConst ``BitVec) args[1]!, args[2]!, args[3]!)
    let some (wa, na) ← bvWidth? tyA
      | trFail m!"{c} at type {tyA} is not supported; only BitVec concatenation is hardware"
    let some (wb, nb) ← bvWidth? tyB
      | trFail m!"{c} at type {tyB} is not supported; only BitVec concatenation is hardware"
    unless ← isCanonical e (mkApp4 (mkConst ``BitVec.append) wa wb a b) do
      trFail m!"{c} at type {tyA} does not use the standard instance"
    unless na + nb ≤ maxWidth do
      trFail m!"concatenation width {na + nb} exceeds {maxWidth}"
    return primApp .bvConcat (.funs [.bv na, .bv nb] (.bv (na + nb))) [← trExpr a, ← trExpr b]
  | ``BitVec.setWidth =>
    let n ← widthValue args[0]!
    let m ← widthValue args[1]!
    let x ← trExpr args[2]!
    if n ≤ m then
      return primApp (.bvZext m) (.fn (.bv n) (.bv m)) [x]
    else
      return primApp (.bvExtract (m - 1) 0) (.fn (.bv n) (.bv m)) [x]
  | ``BitVec.extractLsb =>
    let n ← widthValue args[0]!
    let hi ← natValue args[1]! "extract bound"
    let lo ← natValue args[2]! "extract bound"
    unless lo ≤ hi && hi < n do
      trFail m!"extractLsb {hi} {lo} of a {n}-bit vector needs {n} > hi ≥ lo"
    return primApp (.bvExtract hi lo) (.fn (.bv n) (.bv (hi - lo + 1))) [← trExpr args[3]!]
  | ``BitVec.extractLsb' =>
    let n ← widthValue args[0]!
    let start ← natValue args[1]! "extract start"
    let len ← widthValue args[2]!
    unless start + len ≤ n do
      trFail m!"extractLsb' {start} {len} of a {n}-bit vector reads past bit {n - 1}"
    return primApp (.bvExtract (start + len - 1) start) (.fn (.bv n) (.bv len)) [← trExpr args[3]!]
  | ``BitVec.ult | ``BitVec.ule =>
    let n ← widthValue args[0]!
    let op := if c == ``BitVec.ult then PrimOp.bvUlt else PrimOp.bvUle
    return primApp op (.funs [.bv n, .bv n] .bool) [← trExpr args[1]!, ← trExpr args[2]!]
  | ``BitVec.ofBool => return primApp .bvOfBool (.fn .bool (.bv 1)) [← trExpr args[0]!]
  | ``BitVec.ofNat | ``OfNat.ofNat =>
    if c == ``OfNat.ofNat && (← bvWidth? args[0]!).isNone then
      trFail m!"numeral {e} has type {args[0]!}; only Bool, BitVec and products are hardware values"
    return .lit (← litValue e)
  | ``Bool.true => return .lit (.bool true)
  | ``Bool.false => return .lit (.bool false)
  | ``Bool.and | ``Bool.or | ``Bool.xor =>
    let op := if c == ``Bool.and then PrimOp.boolAnd else if c == ``Bool.or then .boolOr else .boolXor
    return primApp op (.funs [.bool, .bool] .bool) [← trExpr args[0]!, ← trExpr args[1]!]
  | ``Bool.not => return notE (← trExpr args[0]!)
  | ``BEq.beq | ``bne =>
    let inst := (← instantiateMVars args[1]!).consumeMData
    unless inst.isAppOfArity ``instBEqOfDecidableEq 2 do
      trFail m!"{c} at type {args[0]!} must use the BEq instance derived from DecidableEq, got {inst}"
    let eq ← trEq args[0]! args[2]! args[3]!
    return if c == ``bne then notE eq else eq
  | ``decide => trProp args[0]!
  | ``ite =>
    checkIfType e args[0]!
    return .ite (← trProp args[1]!) (← trExpr args[3]!) (← trExpr args[4]!)
  | ``cond =>
    checkIfType e args[0]!
    return .ite (← trExpr args[1]!) (← trExpr args[2]!) (← trExpr args[3]!)
  | ``Prod.mk => return .tuple [← trExpr args[2]!, ← trExpr args[3]!]
  | ``Prod.fst => return .proj 0 (← trExpr args[2]!)
  | ``Prod.snd => return .proj 1 (← trExpr args[2]!)
  | ``Gin.Signal.pure =>
    let d ← domainName args[0]!
    let a ← trTy args[1]!
    return primApp .sigPure (.fn a (.signal d a)) [← trExpr args[2]!]
  | ``Gin.lift | ``Gin.lift2 | ``Gin.lift3 =>
    let k := (args.size - 3) / 2
    let d ← domainName args[0]!
    let tys ← (args.extract 1 (k + 2)).toList.mapM trTy
    let ins := tys.take k
    let res := tys.getLast!
    let sig := Ty.signal d
    let type := Ty.fn (.funs ins res) (.funs (ins.map sig) (sig res))
    let vals ← (args.extract (k + 2) args.size).toList.mapM trExpr
    return primApp (.sigLift k) type vals
  | ``Gin.register =>
    let d ← domainName args[0]!
    let a ← trTy args[1]!
    let init ← litValue args[2]!
    unless init.ty == a do
      trFail m!"register initial value {args[2]!} does not have type {args[1]!}"
    return primApp (.sigRegister init) (.fn (.signal d a) (.signal d a)) [← trExpr args[3]!]
  | ``Gin.mealy =>
    let d ← domainName args[0]!
    let s ← trTy args[1]!
    let i ← trTy args[2]!
    let o ← trTy args[3]!
    let init ← litValue args[5]!
    unless init.ty == s do
      trFail m!"Mealy initial state {args[5]!} does not have type {args[1]!}"
    let type := Ty.fn (.funs [s, i] (.prod [s, o])) (.fn (.signal d i) (.signal d o))
    return primApp (.sigMealy init) type [← trExpr args[4]!, ← trExpr args[6]!]
  | _ => trFail m!"internal error: no translation for {c}"

/-- An if (`ite` or `cond`) must choose between values: Booleans, bit
vectors or products of these. One choosing between functions that is not
applied, or between signals, has no IR form. -/
partial def checkIfType (e ty : Lean.Expr) : TrM Unit := do
  let rec valueTy : Ty → Bool
    | .bool | .bv _ => true
    | .prod ts => ts.all valueTy
    | _ => false
  let t ← trTy ty
  unless valueTy t do
    trFail m!"if-then-else {e} chooses between values of type {ty}; only Bool, BitVec and products of these can be chosen (apply a function-typed if to its arguments, and choose inside `lift` rather than between signals)"

/-- `ite`/`cond` applied to more arguments than it takes: rebuild it with
the extra arguments applied (and beta-reduced) in each branch, at the
branches' result type. -/
partial def pushIntoBranches (c : Name) (now extra : Array Lean.Expr) : TrM Lean.Expr := do
  let (tIdx, eIdx) := if c == ``ite then (3, 4) else (2, 3)
  let t := (mkAppN now[tIdx]! extra).headBeta
  let f := (mkAppN now[eIdx]! extra).headBeta
  let ty ← inferType t
  let lvl ← getLevel ty
  if c == ``ite then
    return mkApp5 (mkConst ``ite [lvl]) ty now[1]! now[2]! t f
  else
    return mkApp4 (mkConst ``cond [lvl]) ty now[1]! t f

/-- `a = b` (or `a == b`) at type `ty`, as a Boolean expression. -/
partial def trEq (ty a b : Lean.Expr) : TrM Expr := do
  if ← isBoolType ty then
    let b' := b.consumeMData
    if b'.isConstOf ``Bool.true then return ← trExpr a
    if b'.isConstOf ``Bool.false then return notE (← trExpr a)
    return primApp .boolEq (.funs [.bool, .bool] .bool) [← trExpr a, ← trExpr b]
  let some (_, n) ← bvWidth? ty
    | trFail m!"equality at type {ty} is not supported; only Bool and BitVec are hardware"
  return primApp .bvEq (.funs [.bv n, .bv n] .bool) [← trExpr a, ← trExpr b]

/-- A decidable proposition, as the Boolean expression `decide p`. -/
partial def trProp (p : Lean.Expr) : TrM Expr := do
  let p := (← instantiateMVars p).consumeMData
  if p.isConstOf ``True then return .lit (.bool true)
  if p.isConstOf ``False then return .lit (.bool false)
  match_expr p with
  | Eq ty a b => trEq ty a b
  | Ne ty a b => return notE (← trEq ty a b)
  | Not q => return notE (← trProp q)
  | And q r => return primApp .boolAnd (.funs [.bool, .bool] .bool) [← trProp q, ← trProp r]
  | Or q r => return primApp .boolOr (.funs [.bool, .bool] .bool) [← trProp q, ← trProp r]
  | LT.lt ty _ a b => trCompare p ty ``LT.lt ``instLTBitVec .bvUlt a b
  | LE.le ty _ a b => trCompare p ty ``LE.le ``instLEBitVec .bvUle a b
  | GT.gt ty _ a b => trCompare p ty ``GT.gt ``instLTBitVec .bvUlt b a (swap := true)
  | GE.ge ty _ a b => trCompare p ty ``GE.ge ``instLEBitVec .bvUle b a (swap := true)
  | _ => trFail m!"unsupported condition {p}"

/-- An unsigned comparison `lhs op rhs` on `BitVec n`, at the standard
order instance. With `swap`, `p` is `rhs > lhs` (or `≥`) as written. -/
partial def trCompare (p ty : Lean.Expr) (rel inst : Name) (op : PrimOp) (lhs rhs : Lean.Expr)
    (swap : Bool := false) : TrM Expr := do
  let some (w, n) ← bvWidth? ty
    | trFail m!"comparison {p} at type {ty} is not supported; only BitVec comparisons are hardware"
  let (a, b) := if swap then (rhs, lhs) else (lhs, rhs)
  let canonical :=
    mkApp4 (mkConst rel [Level.zero]) (mkApp (mkConst ``BitVec) w) (mkApp (mkConst inst) w) a b
  unless ← isCanonical p canonical do
    trFail m!"comparison {p} does not use the standard order on BitVec"
  return primApp op (.funs [.bv n, .bv n] .bool) [← trExpr lhs, ← trExpr rhs]

/-- Destructuring of one pair (`let (a, b) := p`, `fun (a, b) => …`):
the alternative applied to the two projections. Any other pattern match
is an error naming the matcher. -/
partial def trMatcher (e : Lean.Expr) (c : Name) : TrM Expr := do
  let unsupported : TrM Expr :=
    trFail m!"pattern match {c} is not supported; only destructuring one pair, `let (a, b) := p`, is"
  let some m ← matchMatcherApp? e | unsupported
  unless m.discrs.size == 1 && m.alts.size == 1 && m.altNumParams == #[2] do
    return ← unsupported
  let discr := m.discrs[0]!
  let dty := (← instantiateMVars (← inferType discr)).consumeMData
  unless dty.isAppOfArity ``Prod 2 do
    return ← unsupported
  let lvls := dty.getAppFn.constLevels!
  let (α, β) := (dty.appFn!.appArg!, dty.appArg!)
  let fst := mkApp3 (mkConst ``Prod.fst lvls) α β discr
  let snd := mkApp3 (mkConst ``Prod.snd lvls) α β discr
  let candidate := mkAppN m.alts[0]! (#[fst, snd] ++ m.remaining)
  -- The matcher must reduce to its alternative on the projections (by
  -- structure eta), which pins down its meaning.
  unless ← withNewMCtxDepth (isDefEq e candidate) do
    return ← unsupported
  trExpr (← betaLet m.alts[0]! ([fst, snd] ++ m.remaining.toList))

/-- Inline a definition. This terminates because the definitions of a Lean
environment cannot refer to themselves: recursion is compiled to recursors
or `WellFounded.fix`, which are rejected. -/
partial def inlineConst (c : Name) (us : List Level) (args : Array Lean.Expr) : TrM Expr := do
  if c == ``dite then
    trFail m!"dependent if-then-else (`if h : c then …`) is not supported; use `if c then …`"
  let env ← getEnv
  if isAuxRecursor env c || isRecCore env c || isCasesOnRecursor env c then
    trFail m!"recursor {c} is not supported (recursive definitions are not hardware)"
  let some ci := env.find? c | trFail m!"unknown constant {c}"
  let .defnInfo d := ci
    | trFail m!"unsupported constant {c}: it has no definition to inline (constructors, opaque definitions, axioms and theorems are not hardware)"
  unless d.safety == .safe do
    trFail m!"unsupported constant {c}: unsafe and partial definitions are not hardware"
  let value := ci.instantiateValueLevelParams! us
  withReader (fun ctx => { ctx with inlining := c :: ctx.inlining }) do
    trExpr (← betaLet value args.toList)

end

/-- Run a translation of the body of `defName`. -/
def runTr {α : Type} (defName : Name) (exported : NameSet) (x : TrM α) : MetaM α :=
  (x.run { defName, exported }).run' {}

/-- Translate the definition `n`. References to the definitions in
`exported` (which may include `n`) become `global`s; every other constant
is a primitive of the fragment or is inlined. -/
def translateDef (n : Name) (exported : NameSet) : MetaM Def := do
  let some ci := (← getEnv).find? n | throwError "unknown definition {n}"
  let .defnInfo d := ci | throwError "{n} is not a definition"
  unless d.safety == .safe do
    throwError "{n} is unsafe or partial"
  unless ci.levelParams.isEmpty do
    throwError "{n} is universe polymorphic"
  runTr n exported do
    let type ← trTy ci.type
    let body ← trExpr d.value
    return { name := ← irName n, type, body }

end Gin.Export
