/-!
# Core IR

The program representation the exporter emits, mirroring the `gin-ir/1`
and `gin-vectors/1` formats of `docs/file-formats.md` one constructor per
JSON alternative. The JSON encoding lives in `Gin.Export.Encode`.
-/

namespace Gin.Export

/-- Largest bit-vector width the IR admits. -/
def maxWidth : Nat := 4096

/-- Largest number gin reads anywhere in a file, such as a clock period or a
shift amount (`docs/file-formats.md`, "Resource limits"). -/
def maxJsonNumber : Nat := 2 ^ 31 - 1

/-- Deepest nesting of arrays and objects gin reads in a file. -/
def maxJsonDepth : Nat := 4096

/-- Largest file gin reads, in bytes (16 MiB). -/
def maxFileBytes : Nat := 16 * 1024 * 1024

/-- Types of the core IR. -/
inductive Ty where
  /-- A single bit. -/
  | bool
  /-- An unsigned bit vector, `1 ≤ width ≤ maxWidth`. -/
  | bv (width : Nat)
  /-- A product of two or more components. Lean's binary `α × β` always
  maps to a two-element product, so `α × β × γ` is right-nested. -/
  | prod (elems : List Ty)
  /-- A function type. -/
  | fn (arg res : Ty)
  /-- A stream of values in the named clock domain. -/
  | signal (domain : String) (elem : Ty)
  deriving BEq, Repr, Inhabited

/-- `funs [a, b] r = a → b → r`. -/
def Ty.funs (args : List Ty) (res : Ty) : Ty := args.foldr Ty.fn res

/-- Scalars are the only types allowed on top-entity ports. -/
def Ty.isScalar : Ty → Bool
  | .bool => true
  | .bv w => 1 ≤ w && w ≤ maxWidth
  | _ => false

/-- Values: literals, register and Mealy initialisers, and test vectors. -/
inductive Value where
  /-- A Boolean. -/
  | bool (b : Bool)
  /-- `bv width val` with `val < 2 ^ width`. -/
  | bv (width val : Nat)
  /-- A tuple of two or more components. -/
  | tuple (elems : List Value)
  deriving BEq, Repr, Inhabited

/-- The type of a value. -/
partial def Value.ty : Value → Ty
  | .bool _ => .bool
  | .bv w _ => .bv w
  | .tuple vs => .prod (vs.map Value.ty)

/-- Primitive operations; semantics in `docs/semantics.md`. -/
inductive PrimOp where
  /-- `bool.and`. -/
  | boolAnd
  /-- `bool.or`. -/
  | boolOr
  /-- `bool.xor`. -/
  | boolXor
  /-- `bool.not`. -/
  | boolNot
  /-- `bool.eq`. -/
  | boolEq
  /-- `bv.add`, modulo `2^n`. -/
  | bvAdd
  /-- `bv.sub`, modulo `2^n`. -/
  | bvSub
  /-- `bv.mul`, modulo `2^n`. -/
  | bvMul
  /-- `bv.neg`, modulo `2^n`. -/
  | bvNeg
  /-- `bv.and`, bitwise. -/
  | bvAnd
  /-- `bv.or`, bitwise. -/
  | bvOr
  /-- `bv.xor`, bitwise. -/
  | bvXor
  /-- `bv.not`, bitwise. -/
  | bvNot
  /-- `bv.shl` by a constant amount. -/
  | bvShl (amount : Nat)
  /-- `bv.lshr` (logical) by a constant amount. -/
  | bvLshr (amount : Nat)
  /-- `bv.eq`. -/
  | bvEq
  /-- `bv.ult`, unsigned. -/
  | bvUlt
  /-- `bv.ule`, unsigned. -/
  | bvUle
  /-- `bv.concat`; the first argument supplies the most significant bits. -/
  | bvConcat
  /-- `bv.extract hi lo`, both bounds inclusive. -/
  | bvExtract (hi lo : Nat)
  /-- `bv.zext` to the given total width. -/
  | bvZext (width : Nat)
  /-- `bv.ofBool`. -/
  | bvOfBool
  /-- `sig.pure`. -/
  | sigPure
  /-- `sig.lift k`: a `k`-ary combinational function applied pointwise. -/
  | sigLift (arity : Nat)
  /-- `sig.register` with the given initial value. -/
  | sigRegister (init : Value)
  /-- `sig.mealy` with the given initial state. -/
  | sigMealy (init : Value)
  deriving BEq, Repr, Inhabited

/-- The `op` string of a primitive. -/
def PrimOp.name : PrimOp → String
  | .boolAnd => "bool.and"
  | .boolOr => "bool.or"
  | .boolXor => "bool.xor"
  | .boolNot => "bool.not"
  | .boolEq => "bool.eq"
  | .bvAdd => "bv.add"
  | .bvSub => "bv.sub"
  | .bvMul => "bv.mul"
  | .bvNeg => "bv.neg"
  | .bvAnd => "bv.and"
  | .bvOr => "bv.or"
  | .bvXor => "bv.xor"
  | .bvNot => "bv.not"
  | .bvShl _ => "bv.shl"
  | .bvLshr _ => "bv.lshr"
  | .bvEq => "bv.eq"
  | .bvUlt => "bv.ult"
  | .bvUle => "bv.ule"
  | .bvConcat => "bv.concat"
  | .bvExtract _ _ => "bv.extract"
  | .bvZext _ => "bv.zext"
  | .bvOfBool => "bv.ofBool"
  | .sigPure => "sig.pure"
  | .sigLift _ => "sig.lift"
  | .sigRegister _ => "sig.register"
  | .sigMealy _ => "sig.mealy"

/-- Number of value arguments a saturated application takes. -/
def PrimOp.arity : PrimOp → Nat
  | .boolNot | .bvNeg | .bvNot | .bvShl _ | .bvLshr _ | .bvExtract _ _ | .bvZext _
  | .bvOfBool | .sigPure | .sigRegister _ => 1
  | .sigLift k => k + 1
  | _ => 2

/-- Expressions of the core IR. -/
inductive Expr where
  /-- A lambda- or let-bound variable. -/
  | var (name : String)
  /-- A reference to another definition of the program. -/
  | global (name : String)
  /-- A literal. -/
  | lit (value : Value)
  /-- A primitive together with its full instantiated type. -/
  | prim (op : PrimOp) (type : Ty)
  /-- Curried application to one or more arguments. -/
  | app (fn : Expr) (args : List Expr)
  /-- Curried lambda over one or more binders. -/
  | lam (binders : List (String × Ty)) (body : Expr)
  /-- `letE isRec binds body`; each bind is `(name, type, value)`.
  Non-recursive binds scope sequentially. -/
  | letE (isRec : Bool) (binds : List (String × Ty × Expr)) (body : Expr)
  /-- A tuple of two or more components. -/
  | tuple (elems : List Expr)
  /-- Zero-based projection out of a tuple. -/
  | proj (index : Nat) (of : Expr)
  /-- Combinational choice on a `bool` condition. -/
  | ite (cond thenE elseE : Expr)
  deriving BEq, Repr, Inhabited

/-- A named top-level definition. -/
structure Def where
  /-- Fully qualified Lean name. -/
  name : String
  /-- Type of the definition. -/
  type : Ty
  /-- Body of the definition. -/
  body : Expr
  deriving BEq, Repr, Inhabited

/-- A port of the top entity; the type is always scalar. -/
structure Port where
  /-- Port name, part of the generated hardware interface. -/
  name : String
  /-- Port type. -/
  type : Ty
  deriving BEq, Repr, Inhabited

/-- The clock domain of the top entity. -/
structure DomainInfo where
  /-- Domain name, as used in `signal` types. -/
  name : String
  /-- Clock period in picoseconds. -/
  periodPs : Nat
  deriving BEq, Repr, Inhabited

/-- The circuit to synthesise. -/
structure Top where
  /-- Name of the generated hardware module. -/
  name : String
  /-- The single clock domain of the circuit. -/
  domain : DomainInfo
  /-- Input ports, in argument order; may be empty. -/
  inputs : List Port
  /-- Output ports; non-empty. Two or more outputs are read along the
  right-nested product returned by the top definition. -/
  outputs : List Port
  /-- Name of the definition implementing the circuit. -/
  def_ : String
  deriving BEq, Repr, Inhabited

/-- A definition the theorem statement depends on, as a reviewer reads it. -/
structure SpecDef where
  /-- Fully qualified name. -/
  name : String
  /-- `name : type := value`, or `name : type` for a constant without a
  value, rendered by `Gin.Export.Print`. -/
  body : String
  deriving BEq, Repr, Inhabited

/-- The trace (`Certificate` in the code, `"certificate"` in the JSON):
evidence that the implementation was proven against a specification. -/
structure Certificate where
  /-- Fully qualified name of the refinement theorem. -/
  theorem_ : String
  /-- The statement of the theorem, rendered by `Gin.Export.Print`. -/
  statement : String
  /-- Axioms the theorem's proof depends on. -/
  axioms : List String
  /-- Axioms the exported definitions depend on. -/
  implAxioms : List String
  /-- Every definition the statement depends on, other than the top
  definition, the signal DSL and Lean's core library, in dependency order. -/
  specDefinitions : List SpecDef
  deriving BEq, Repr, Inhabited

/-- The tool that wrote a file. -/
structure Producer where
  /-- Tool name. -/
  tool : String
  /-- Version of Lean the tool ran on. -/
  leanVersion : String
  deriving BEq, Repr, Inhabited

/-- A complete `gin-ir/1` program. -/
structure Program where
  /-- Who wrote the file. -/
  producer : Producer
  /-- The circuit to synthesise. -/
  top : Top
  /-- Every definition the top definition refers to, and itself. -/
  defs : List Def
  /-- Trace of the top definition. -/
  certificate : Certificate
  deriving BEq, Repr, Inhabited

/-- One row of test vectors: inputs applied and outputs expected during one
cycle, each in port order. -/
structure Cycle where
  /-- Input values, one per input port. -/
  inputs : List Value
  /-- Output values, one per output port. -/
  outputs : List Value
  deriving BEq, Repr, Inhabited

/-- A complete `gin-vectors/1` file. -/
structure Vectors where
  /-- Equals the program's `top.name`. -/
  top : String
  /-- Equals the program's top inputs. -/
  inputs : List Port
  /-- Equals the program's top outputs. -/
  outputs : List Port
  /-- One row per cycle, starting at cycle 0. -/
  cycles : Array Cycle
  deriving BEq, Repr, Inhabited

end Gin.Export
