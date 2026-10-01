# File formats

gin consumes two JSON files per circuit, both produced by the Lean
exporter:

| File                  | Contents                                    | Format tag      |
| --------------------- | ------------------------------------------- | --------------- |
| `<name>.gin.json`     | The core IR program and its certificate     | `gin-ir/1`      |
| `<name>.vectors.json` | Cycle-by-cycle test vectors from Lean       | `gin-vectors/1` |

Both are UTF-8 JSON. The Haskell types they decode to live in
`Gin.Core.Syntax` and `Gin.Vectors`; the codec is `Gin.Core.Json`.

## Core IR (`gin-ir/1`)

```
Program := {
  "format": "gin-ir/1",
  "producer": {"tool": String, "leanVersion": String},
  "top": {
    "name": Ident,                                     -- legal HDL identifier
    "domain": {"name": String, "periodPs": Nat},
    "inputs":  [ {"name": String, "type": Type} ],     -- may be empty
    "outputs": [ {"name": String, "type": Type} ],     -- non-empty
    "def": String                                      -- one of defs[].name
  },
  "defs": [ {"name": String, "type": Type, "body": Expr} ],
  "certificate": {
    "theorem": String, "statement": String,
    "axioms": [String], "implAxioms": [String]
  }
}

Type :=
    {"t": "bool"}
  | {"t": "bv", "width": Nat}                          -- 1..4096
  | {"t": "prod", "elems": [Type, Type, ...]}          -- length >= 2
  | {"t": "fun", "arg": Type, "res": Type}
  | {"t": "signal", "domain": String, "elem": Type}

Value :=
    true | false
  | {"bv": Nat, "val": DecimalString}                  -- width, 0 <= val < 2^width
  | {"tuple": [Value, Value, ...]}                     -- length >= 2

Expr :=
    {"e": "var",    "name": String}
  | {"e": "global", "name": String}
  | {"e": "lit",    "value": Value}
  | {"e": "prim",   "op": PrimName, "type": Type, "params": Params}
  | {"e": "app",    "fun": Expr, "args": [Expr, ...]}                 -- length >= 1
  | {"e": "lam",    "binders": [{"name": String, "type": Type}, ...],
                    "body": Expr}                                     -- length >= 1
  | {"e": "let",    "rec": Bool,
                    "binds": [{"name": String, "type": Type, "value": Expr}, ...],
                    "body": Expr}
  | {"e": "tuple",  "elems": [Expr, Expr, ...]}                       -- length >= 2
  | {"e": "proj",   "index": Nat, "of": Expr}                         -- zero-based
  | {"e": "if",     "cond": Expr, "then": Expr, "else": Expr}
```

Primitive names and their parameters (`params` may be omitted when
empty):

| `op`                                                                                         | `params`                 |
| -------------------------------------------------------------------------------------------- | ------------------------ |
| `bool.and` `bool.or` `bool.xor` `bool.not` `bool.eq`                                          | `{}`                     |
| `bv.add` `bv.sub` `bv.mul` `bv.neg` `bv.and` `bv.or` `bv.xor` `bv.not`                        | `{}`                     |
| `bv.eq` `bv.ult` `bv.ule` `bv.concat` `bv.ofBool` `sig.pure`                                  | `{}`                     |
| `bv.shl` `bv.lshr`                                                                            | `{"amount": Nat}`        |
| `bv.extract`                                                                                  | `{"hi": Nat, "lo": Nat}` |
| `bv.zext`                                                                                     | `{"width": Nat}`         |
| `sig.lift`                                                                                    | `{"arity": Nat}`         |
| `sig.register` `sig.mealy`                                                                    | `{"init": Value}`        |

Typing rules for each primitive are documented in `Gin.Core.Prim`; the
shape required of the top-level definition is documented on
`Gin.Core.Syntax.TopEntity`.

### Decoding rules

The decoder is strict about structure and lenient about extra keys:

- Unknown object keys are ignored.
- These are decode errors: an unknown `"t"`, `"e"` or `"op"` tag; a
  missing required key; a JSON value of the wrong kind; a format tag
  other than `gin-ir/1`; a width outside 1..4096; a negative or
  non-integral number; a `"val"` that is not a canonical decimal (digits
  only, no sign, no leading zeros except `"0"`) or is out of range for
  its width; tuples, products, applications or lambdas of illegal length.
- Decoding then encoding reproduces the canonical encoding; encoding
  then decoding is the identity. The encoder emits keys in the order
  shown above and always emits `"params"`.

`Ident` is a name accepted by `Gin.Netlist.Types.isLegalIdent`; port
names must be pairwise distinct. Port and top names are part of the
generated hardware interface and are never renamed.

### Resource limits

Input files are untrusted. Each bound below is checked before the work
it guards (constants in `Gin.Limits`):

| Bound                                         | Limit                    |
| --------------------------------------------- | ------------------------ |
| File size                                     | 16 MiB                   |
| JSON nesting depth                            | 4096                     |
| Any JSON number                               | integer, 0 … 2^31 − 1    |
| Length of a `"val"` decimal string            | 1234 digits              |
| Duplicate keys in one JSON object             | rejected                 |
| Bit-vector width                              | 1 … 4096                 |
| Vector cycles                                 | 1 … 100000               |
| Vector payload (cycles × summed port widths)  | 2^18 bits                |
| Normal-form size                              | 65536 bindings           |
| External tool run                             | 300 s (configurable)     |

## Test vectors (`gin-vectors/1`)

```
Vectors := {
  "format": "gin-vectors/1",
  "top": String,                                    -- equals the program's top.name
  "inputs":  [ {"name": String, "type": Type} ],    -- equals top.inputs
  "outputs": [ {"name": String, "type": Type} ],    -- equals top.outputs
  "cycles":  [ {"in": [Value], "out": [Value]} ]    -- 1..100000 entries
}
```

`Type` and `Value` are as above. Row `t` gives the input values applied
during cycle `t` and the output values expected during that cycle, each
in port order (see [semantics.md](semantics.md)).

The decoder rejects a wrong format tag, zero cycles or more than 100000,
a payload over the limit above, rows whose length differs from the port
lists, and values whose type differs from the port type. Commands that
take both files also reject vectors whose `top`, inputs or outputs
(names, types and order) differ from the program's top entity.
