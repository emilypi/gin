import Gin.Export.Ir
import Gin.Export.JsonDoc

/-!
# JSON encoding of the core IR

Encodes `Program` and `Vectors` exactly as `docs/file-formats.md`
specifies, with keys in the order the document lists them and `params`
always present on primitives.
-/

namespace Gin.Export

open JsonDoc

/-- Format tag of program files. -/
def irFormat : String := "gin-ir/1"

/-- Format tag of test-vector files. -/
def vectorsFormat : String := "gin-vectors/1"

/-- Encode a type. -/
partial def Ty.toDoc : Ty → JsonDoc
  | .bool => obj [("t", str "bool")]
  | .bv w => obj [("t", str "bv"), ("width", nat w)]
  | .prod es => obj [("t", str "prod"), ("elems", arr (es.map Ty.toDoc))]
  | .fn a r => obj [("t", str "fun"), ("arg", a.toDoc), ("res", r.toDoc)]
  | .signal d e => obj [("t", str "signal"), ("domain", str d), ("elem", e.toDoc)]

/-- Encode a value; bit-vector payloads are decimal strings. -/
partial def Value.toDoc : Value → JsonDoc
  | .bool b => JsonDoc.bool b
  | .bv w v => obj [("bv", nat w), ("val", str (toString v))]
  | .tuple vs => obj [("tuple", arr (vs.map Value.toDoc))]

/-- The `params` object of a primitive. -/
def PrimOp.params : PrimOp → List (String × JsonDoc)
  | .bvShl k | .bvLshr k => [("amount", nat k)]
  | .bvExtract hi lo => [("hi", nat hi), ("lo", nat lo)]
  | .bvZext w => [("width", nat w)]
  | .sigLift k => [("arity", nat k)]
  | .sigRegister v | .sigMealy v => [("init", v.toDoc)]
  | _ => []

/-- Encode an expression. -/
partial def Expr.toDoc : Expr → JsonDoc
  | .var n => obj [("e", str "var"), ("name", str n)]
  | .global n => obj [("e", str "global"), ("name", str n)]
  | .lit v => obj [("e", str "lit"), ("value", v.toDoc)]
  | .prim op ty =>
    obj [("e", str "prim"), ("op", str op.name), ("type", ty.toDoc), ("params", obj op.params)]
  | .app f args => obj [("e", str "app"), ("fun", f.toDoc), ("args", arr (args.map Expr.toDoc))]
  | .lam bs body =>
    obj [("e", str "lam"),
      ("binders", arr (bs.map fun (n, t) => obj [("name", str n), ("type", t.toDoc)])),
      ("body", body.toDoc)]
  | .letE r bs body =>
    obj [("e", str "let"), ("rec", bool r),
      ("binds", arr (bs.map fun (n, t, v) =>
        obj [("name", str n), ("type", t.toDoc), ("value", v.toDoc)])),
      ("body", body.toDoc)]
  | .tuple es => obj [("e", str "tuple"), ("elems", arr (es.map Expr.toDoc))]
  | .proj i e => obj [("e", str "proj"), ("index", nat i), ("of", e.toDoc)]
  | .ite c t e => obj [("e", str "if"), ("cond", c.toDoc), ("then", t.toDoc), ("else", e.toDoc)]

/-- Encode a port. -/
def Port.toDoc (p : Port) : JsonDoc := obj [("name", str p.name), ("type", p.type.toDoc)]

/-- Encode a certificate. -/
def Certificate.toDoc (c : Certificate) : JsonDoc :=
  obj [
    ("theorem", str c.theorem_),
    ("statement", str c.statement),
    ("axioms", arr (c.axioms.map str)),
    ("implAxioms", arr (c.implAxioms.map str)),
    ("specDefinitions", arr (c.specDefinitions.map fun d =>
      obj [("name", str d.name), ("body", str d.body)]))]

/-- Encode a program file. Its last member is the certificate, so that the
file ends in `certificateTail`. -/
def Program.toDoc (p : Program) : JsonDoc :=
  obj [
    ("format", str irFormat),
    ("producer", obj [("tool", str p.producer.tool), ("leanVersion", str p.producer.leanVersion)]),
    ("top", obj [
      ("name", str p.top.name),
      ("domain", obj [("name", str p.top.domain.name), ("periodPs", nat p.top.domain.periodPs)]),
      ("inputs", arr (p.top.inputs.map Port.toDoc)),
      ("outputs", arr (p.top.outputs.map Port.toDoc)),
      ("def", str p.top.def_)]),
    ("defs", arr (p.defs.map fun d =>
      obj [("name", str d.name), ("type", d.type.toDoc), ("body", d.body.toDoc)])),
    ("certificate", p.certificate.toDoc)]

/-- Encode a test-vector file. -/
def Vectors.toDoc (v : Vectors) : JsonDoc :=
  obj [
    ("format", str vectorsFormat),
    ("top", str v.top),
    ("inputs", arr (v.inputs.map Port.toDoc)),
    ("outputs", arr (v.outputs.map Port.toDoc)),
    ("cycles", arr (v.cycles.toList.map fun c =>
      obj [("in", arr (c.inputs.map Value.toDoc)), ("out", arr (c.outputs.map Value.toDoc))]))]

/-- Check a file of `bytes` bytes holding `doc` against the limits gin
enforces on every file it reads (`docs/file-formats.md`, "Resource limits"),
so that the exporter refuses a design instead of writing a file gin rejects.
Widths, value ranges and the vector payload are checked where they arise. -/
def checkLimits (doc : JsonDoc) (bytes : Nat) : Except String Unit := do
  if let some (path, n) := doc.numberAbove? maxJsonNumber then
    throw s!"the number {n} at {path} is larger than {maxJsonNumber}, the largest number gin reads"
  let depth := doc.depth
  unless depth ≤ maxJsonDepth do
    throw s!"arrays and objects are nested {depth} deep, more than the {maxJsonDepth} gin reads"
  unless bytes ≤ maxFileBytes do
    throw s!"the file has {bytes} bytes, more than the {maxFileBytes} gin reads"

/-- The text of a file, or why gin could not read it (`checkLimits`). -/
def renderFile (doc : JsonDoc) : Except String String := do
  let text := doc.render
  checkLimits doc text.utf8ByteSize
  return text

/-- The last bytes of every program file with certificate `c` that
`renderFile` writes: the certificate, the last member of the top-level
object, laid out as `JsonDoc.render` lays it out there, and the closing
brace. `gin-check-export --certificates`, which links no design, writes it
for each circuit, and `scripts/export-examples.sh` refuses a `.gin.json`
file from `gin-export`, which does link designs, unless the file ends in
exactly these bytes (`GinTest/Json.lean` checks the layout). -/
def certificateTail (c : Certificate) : String :=
  let key := JsonDoc.quote "certificate" ++ ": "
  ",\n  " ++ key ++ JsonDoc.prettyAt JsonDoc.width 2 (2 + key.length) c.toDoc ++ "\n}\n"

end Gin.Export
