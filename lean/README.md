# gin Lean package

Circuits are written and proved in Lean; the exporter turns them into the
core IR and test vectors that the Haskell side of gin compiles to HDL
(formats in `docs/file-formats.md`, semantics in `docs/semantics.md`).

| Path                     | Contents                                                        |
| ------------------------ | --------------------------------------------------------------- |
| `Gin/Signal.lean`        | The DSL: `Signal`, `register`, `mealy`, `lift`…                 |
| `Gin/Examples/`          | `counter`, `detector`, `mac` with refinement theorems           |
| `Gin/Export/`            | Translator, certificate policy, vectors, export table, CLI      |
| `GinCheckExport.lean`    | Root of `gin-check-export`, the checks; links no design         |
| `GinExport.lean`         | Root of `gin-export`, which links the designs                   |
| `GinTest/`               | Tests, run by `lake build`                                      |
| `GinReject/`             | Designs the exporter must refuse, not built by default          |

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
   The exporter checks this shape: the inputs are passed straight through,
   `spec` is a constant other than `impl`, and `impl` does not occur in the
   definitions `spec` depends on.
   Only `propext`, `Classical.choice` and `Quot.sound` may appear in the
   proof: no `sorry`, `native_decide` or `bv_decide`.
3. Add an entry to `Gin/Export/Entries.lean` with the hardware name, port
   names, the definitions to emit and a seed, and list it in
   `defaultExports`; add its vector source to `Gin/Export/Table.lean`.
4. Run `scripts/export-examples.sh`.

## Trust

What a reviewer reads in a certificate is what the kernel checked:

- The statement and every definition it depends on (`specDefinitions`)
  are rendered by the exporter's own printer (`Gin/Export/Print.lean`),
  which prints fully qualified names and explicit applications and never
  consults notation, delaborators or unexpanders declared by a design.
  Names are printed in ASCII and never two alike: a component that is not
  a plain identifier is written `«…»` with `\u{XXXX}` escapes, and names
  with macro scopes, inaccessible names (`✝`) and duplicate definition
  names are refused (`GinTest/Names.lean`).
- The export script replays through the kernel, with `leanchecker`,
  exactly the modules the export loads outside the Lean toolchain
  and the modules `gin-export` links
  (`lake exe gin-check-export --list-modules NAME...`), whatever their names,
  so declarations added under `debug.skipKernelTC` are caught in any
  module a design imports. `leanchecker` runs on a search path holding
  only those modules' `.olean` files, so a stale `.olean` left by a
  deleted source is neither replayed nor imported.
- A circuit that loads a module under `GinReject` is refused unless its
  table entry is marked as a reject fixture.
- The checks run in `gin-check-export`, which links only the exporter
  and the DSL, no design, and imports the environment without its
  extensions, so no code of a design runs while the modules, the axioms
  and the theorem shape are checked and the certificate is rendered. It
  refuses any project module that registers an IO initializer
  (`initialize`, `builtin_initialize`, `@[init]`), among the modules the
  circuits load and those `gin-export` links.
- `gin-export` links the designs to compute vectors, and the
  initializers of linked modules run as soon as it starts, before any of
  its own checks; such code could write forged files. The export script
  therefore runs `gin-check-export` first and never starts `gin-export`
  when it fails (`GinReject/Hooked.lean`). `gin-export` repeats the checks,
  but they cannot stop an initializer that has already run: run it only
  through the script.

`lake build` itself runs code from the sources it builds: `#eval`,
`run_cmd`, macros and elaborators execute at build time with the
builder's privileges. Build and export designs you did not write only in
a sandbox (a container or VM without your credentials).

## Caveats

- Run the exporter only through `scripts/export-examples.sh`, which runs
  `lake exe gin-check-export` before `lake exe gin-export`; the bare
  binaries have no Lean search path.
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
