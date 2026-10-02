import Lean.Data.Json
import Gin.Export.Encode

/-!
The JSON writer produces valid JSON (checked by re-parsing with
`Lean.Json.parse`) and the encoders follow `docs/file-formats.md`.
-/

open Gin.Export

namespace GinTest.Json

/-- The same document as a `Lean.Json`, for comparison with the parser. -/
partial def toLean : JsonDoc → Lean.Json
  | .null => .null
  | .bool b => .bool b
  | .nat n => .num (Lean.JsonNumber.fromNat n)
  | .str s => .str s
  | .arr xs => .arr (xs.map toLean).toArray
  | .obj kvs => Lean.Json.mkObj (kvs.map fun (k, v) => (k, toLean v))

/-- Does the rendered text parse back to the same document? -/
def roundTrips (d : JsonDoc) : Bool :=
  match Lean.Json.parse (JsonDoc.render d) with
  | .ok j => j == toLean d
  | .error _ => false

/-- Strings that need every kind of escape. -/
def awkward : String := "quote\" backslash\\ nl\n cr\r tab\t bell\x07 nul\x00 ü ∀ 𝔹"

-- Escapes: quote, backslash, the named control characters, other control
-- characters as \u00XX; non-ASCII is left as UTF-8.
#guard JsonDoc.quote awkward ==
  "\"quote\\\" backslash\\\\ nl\\n cr\\r tab\\t bell\\u0007 nul\\u0000 ü ∀ 𝔹\""
#guard JsonDoc.quote "" == "\"\""

#guard roundTrips (.str awkward)
#guard roundTrips (.obj [])
#guard roundTrips (.arr [])
#guard roundTrips (.nat (2 ^ 31 - 1))
#guard roundTrips (.obj [("z", .null), ("a", .arr [.bool true, .bool false, .nat 0])])

/-- A document too wide for one line, nested three levels deep. -/
def wide : JsonDoc :=
  .obj [("name", .str "a fairly long string value that does not fit"),
        ("rows", .arr ((List.range 12).map fun i => .obj [("in", .arr [.nat i]), ("out", .arr [.nat (i * i)])])),
        ("empty", .obj [])]

#guard roundTrips wide

-- Rendering is one value per line once a line would exceed 100 columns, and
-- short values stay on one line.
#guard (JsonDoc.render wide).splitOn "\n" ==
  ["{",
   "  \"name\": \"a fairly long string value that does not fit\",",
   "  \"rows\": [",
   "    {\"in\": [0], \"out\": [0]},",
   "    {\"in\": [1], \"out\": [1]},",
   "    {\"in\": [2], \"out\": [4]},",
   "    {\"in\": [3], \"out\": [9]},",
   "    {\"in\": [4], \"out\": [16]},",
   "    {\"in\": [5], \"out\": [25]},",
   "    {\"in\": [6], \"out\": [36]},",
   "    {\"in\": [7], \"out\": [49]},",
   "    {\"in\": [8], \"out\": [64]},",
   "    {\"in\": [9], \"out\": [81]},",
   "    {\"in\": [10], \"out\": [100]},",
   "    {\"in\": [11], \"out\": [121]}",
   "  ],",
   "  \"empty\": {}",
   "}",
   ""]

-- Types, values and expressions use the tags of docs/file-formats.md.
#guard (Ty.toDoc .bool).compact == "{\"t\": \"bool\"}"
#guard (Ty.signal "System" (.prod [.bv 8, .fn .bool .bool])).toDoc.compact ==
  "{\"t\": \"signal\", \"domain\": \"System\", \"elem\": {\"t\": \"prod\", \"elems\": " ++
  "[{\"t\": \"bv\", \"width\": 8}, {\"t\": \"fun\", \"arg\": {\"t\": \"bool\"}, \"res\": {\"t\": \"bool\"}}]}}"
#guard (Value.tuple [.bool false, .bv 4096 (2 ^ 4096 - 1)]).toDoc.compact ==
  "{\"tuple\": [false, {\"bv\": 4096, \"val\": \"" ++ toString (2 ^ 4096 - 1) ++ "\"}]}"
-- `params` is always present, empty when the primitive has none.
#guard (Expr.prim .bvAdd (.funs [.bv 8, .bv 8] (.bv 8))).toDoc.compact ==
  "{\"e\": \"prim\", \"op\": \"bv.add\", \"type\": {\"t\": \"fun\", \"arg\": {\"t\": \"bv\", \"width\": 8}, " ++
  "\"res\": {\"t\": \"fun\", \"arg\": {\"t\": \"bv\", \"width\": 8}, \"res\": {\"t\": \"bv\", \"width\": 8}}}, " ++
  "\"params\": {}}"
#guard (PrimOp.sigMealy (.bv 2 0)).params.map (·.1) == ["init"]
#guard (PrimOp.bvExtract 5 2).params == [("hi", .nat 5), ("lo", .nat 2)]
#guard (PrimOp.bvShl 3).params == [("amount", .nat 3)]
#guard (PrimOp.bvLshr 3).params == [("amount", .nat 3)]
#guard (PrimOp.bvZext 16).params == [("width", .nat 16)]
#guard (PrimOp.sigLift 2).params == [("arity", .nat 2)]
#guard (Expr.letE false [("x", .bool, .lit (.bool true))] (.var "x")).toDoc.compact ==
  "{\"e\": \"let\", \"rec\": false, \"binds\": [{\"name\": \"x\", \"type\": {\"t\": \"bool\"}, " ++
  "\"value\": {\"e\": \"lit\", \"value\": true}}], \"body\": {\"e\": \"var\", \"name\": \"x\"}}"
#guard (Expr.ite (.var "c") (.proj 1 (.var "p")) (.global "M.f")).toDoc.compact ==
  "{\"e\": \"if\", \"cond\": {\"e\": \"var\", \"name\": \"c\"}, \"then\": {\"e\": \"proj\", \"index\": 1, " ++
  "\"of\": {\"e\": \"var\", \"name\": \"p\"}}, \"else\": {\"e\": \"global\", \"name\": \"M.f\"}}"

end GinTest.Json
