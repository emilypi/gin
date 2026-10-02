# gin Lean package

Circuits are written and proved in Lean; the exporter turns them into the
core IR and test vectors that the Haskell side of gin compiles to HDL
(formats in `docs/file-formats.md`, semantics in `docs/semantics.md`).

| Path                     | Contents                                                        |
| ------------------------ | --------------------------------------------------------------- |
| `Gin/Signal.lean`        | The DSL: `Signal`, `register`, `mealy`, `lift`…                 |
| `Gin/Examples/`          | `counter`, `detector`, `mac` with refinement theorems           |
| `Gin/Examples/Bad*.lean` | Reject fixtures (`sorry`, `native_decide`), not built by default |
| `Gin/Export/`            | Translator, certificate policy, vectors, export table, CLI      |
| `GinExport.lean`         | Root of the `gin-export` executable                             |
| `GinTest/`               | Tests, run by `lake build`                                      |

## Workflow

```sh
lake -d lean build --wfail                  # build and run every test
scripts/export-examples.sh                  # build, leanchecker, regenerate examples/
scripts/export-examples.sh --check-rejects  # unproven designs are refused
```

Files under `examples/` are generated; never edit them by hand. Commit
them together with the Lean change that produced them.

## Adding a circuit

1. Write the implementation with the combinators of `Gin.Signal`, staying
   inside the fragment documented at the top of `Gin/Export/Translate.lean`.
   Register and Mealy initial values must be literals.
2. State a refinement theorem `∀ inputs t, impl inputs t = spec inputs t`
   against an independent specification and prove it with ordinary tactics.
   Only `propext`, `Classical.choice` and `Quot.sound` may appear in the
   proof: no `sorry`, `native_decide` or `bv_decide`.
3. Add an entry to `Gin/Export/Table.lean` with the hardware name, port
   names, the definitions to emit, a vector source and a seed, and list it
   in `defaultExports`.
4. Run `scripts/export-examples.sh`.

## Caveats

- Run the exporter only through `lake exe gin-export`; the bare binary has
  no Lean search path.
- Test vectors come from running the compiled Lean definitions on seeded
  inputs, never from the exported IR. The IR evaluator in
  `GinTest/IrEval.lean` exists only to test the translator.
- `collectAxioms` cannot see proofs that skipped the kernel
  (`debug.skipKernelTC`); that is why the export script runs `leanchecker`
  first. Do not export without it.
- The exporter refuses to write a file gin would reject on reading
  (`docs/file-formats.md`, "Resource limits"): any number above
  2147483647, arrays and objects nested deeper than 4096, or more than
  16 MiB. In particular a clock period must be at most 2147483647 ps
  (about 2.1 µs, a clock of at least about 466 kHz). Constant shifts by
  the width or more are emitted as shifts by the width, which mean the
  same.
- JSON key order in the generated files is not significant.
