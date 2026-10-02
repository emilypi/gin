/-!
# Ordered JSON documents

A minimal JSON tree that keeps object keys in the order they were written,
and a deterministic pretty-printer for it. `Lean.Json` sorts object keys,
which makes generated files harder to read; consumers must not depend on
key order either way.
-/

namespace Gin.Export

/-- A JSON value whose objects keep their keys in insertion order. Numbers
are natural numbers only: the formats gin reads have no other kind. -/
inductive JsonDoc where
  /-- `null`. -/
  | null
  /-- `true` or `false`. -/
  | bool (b : Bool)
  /-- A non-negative integer. -/
  | nat (n : Nat)
  /-- A string. -/
  | str (s : String)
  /-- An array. -/
  | arr (elems : List JsonDoc)
  /-- An object; keys must be distinct. -/
  | obj (fields : List (String × JsonDoc))
  deriving BEq, Repr, Inhabited

namespace JsonDoc

/-- Lower-case hexadecimal digit. -/
private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Escape a string for inclusion between double quotes. Control characters
are written as `\uXXXX`; everything else is emitted as UTF-8. -/
def escape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | c =>
      if c.toNat < 0x20 then
        acc ++ "\\u00" ++ (hexDigit (c.toNat / 16)).toString ++ (hexDigit (c.toNat % 16)).toString
      else acc.push c

/-- A quoted, escaped JSON string. -/
def quote (s : String) : String := "\"" ++ escape s ++ "\""

/-- Single-line rendering, with a space after every `,` and `:`. -/
partial def compact : JsonDoc → String
  | .null => "null"
  | .bool b => toString b
  | .nat n => toString n
  | .str s => quote s
  | .arr xs => "[" ++ ", ".intercalate (xs.map compact) ++ "]"
  | .obj kvs => "{" ++ ", ".intercalate (kvs.map fun (k, v) => quote k ++ ": " ++ compact v) ++ "}"

/-- Render at the given indentation, assuming the cursor is at column `col`.
A value is written on one line when that line stays within `width`
columns; otherwise each element goes on its own line. -/
partial def prettyAt (width indent col : Nat) (d : JsonDoc) : String :=
  let flat := compact d
  if col + flat.length ≤ width then flat else
  let pad := "".pushn ' ' (indent + 2)
  let close := "".pushn ' ' indent
  match d with
  | .arr (x :: xs) =>
    let items := (x :: xs).map fun e => pad ++ prettyAt width (indent + 2) (indent + 2) e
    "[\n" ++ ",\n".intercalate items ++ "\n" ++ close ++ "]"
  | .obj (kv :: kvs) =>
    let items := (kv :: kvs).map fun (k, v) =>
      let key := quote k ++ ": "
      pad ++ key ++ prettyAt width (indent + 2) (indent + 2 + key.length) v
    "{\n" ++ ",\n".intercalate items ++ "\n" ++ close ++ "}"
  | _ => flat

/-- The text of a JSON file: pretty-printed within 100 columns, ending in a
newline. -/
def render (d : JsonDoc) : String := prettyAt 100 0 0 d ++ "\n"

end JsonDoc

end Gin.Export
