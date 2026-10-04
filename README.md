# gin

## What gin is

gin compiles synchronous circuits written in Lean 4 to Verilog-2005,
SystemVerilog and VHDL-2008, in the style of Clash: a circuit is an
ordinary Lean function on signals (`Signal dom α`, the stream of values a
wire carries at each clock cycle), built from `register`, `mealy`, `lift`
and combinational functions on `Bool`, `BitVec n` and pairs.

Every circuit comes with a refinement theorem, proved in Lean and checked
by the kernel, stating that the implementation agrees with an independent
specification at every cycle and for every input stream:

```lean
def counter (en : Signal System Bool) : Signal System (BitVec 8) :=
  mealy (fun s e => (if e then s + 1 else s, s)) 0 en

def spec (en : Signal System Bool) (t : Nat) : BitVec 8 :=
  BitVec.ofNat 8 ((List.range t).countP (fun i => en i))

theorem counter_correct : ∀ en t, counter en t = spec en t := by …
```

The Lean exporter translates the implementation to a small typed core IR
and records a certificate: the theorem's name, its statement and the axioms
its proof depends on. It also runs the compiled Lean definition on seeded
inputs to produce test vectors. gin, written in Haskell, checks the
certificate against an axiom policy, normalizes the IR to a first-order
netlist, renders HDL with the theorem statement in every file header, and
generates self-checking testbenches that replay the Lean vectors.

## Why

A circuit is only as trustworthy as the reason to believe it does what it
should. gin moves that reason from the implementation to its
specification. Whether the implementation was written by a hardware
engineer, a contributor you have never met or a language model, a reviewer
answers three small questions about the result, provided it was built
from trusted tooling as described below:

1. Does the specification say what I want? The certificate carries the
   theorem statement and every definition it depends on
   (`specDefinitions`), printed by the exporter's fixed printer into every
   generated HDL file, together with their hash. Review them once, then pin
   the hash with `--spec-hash` so that any later change to the printed claim
   fails.
2. Does the proof check? The Lean kernel decides. The exporter refuses
   proofs that rely on `sorry`, `native_decide`, `bv_decide` or any axiom
   beyond Lean's standard three, and gin checks the same policy again.
3. Does the generated hardware still mean the proven Lean definition?
   Translation validation answers that: the Lean model, gin's normal-form
   simulator and the HDL simulators must produce identical outputs, cycle
   for cycle, on the same vectors, and so must the core IR simulator
   unless its evaluation budget makes it report an inconclusive `SKIP`.

The implementation itself can be as clever or as obscure as it likes: its
behaviour is covered by the proof, so once its theorem is reviewed and
validation passes, you do not need to read its logic to know what it
computes. Building it, however, runs its code: Lean executes `#eval`,
`run_cmd`, macros and elaborators at build time, before and alongside the
kernel replay and the exporter's checks, and the exporter links the
design. A sandbox protects your machine, not the result: code that runs at
build time can forge every output, the certificate, IR and vectors
included, and re-checking the certificate elsewhere would not secure the
IR and vectors, which are not bound to it. For a design you did not write,
a PASS is evidence about the HDL only if its Lean sources were read for
build-time code and the export script, exporter (`lean/Gin/Export/`,
`lean/GinExport.lean`, `lean/GinCheckExport.lean`, including each entry's
vector source), lakefile, DSL and toolchain pin came from a reviewed
revision of gin. The spec hash also does not
cover gin's signal DSL or Lean's core library; changes to
`lean/Gin/Signal.lean` and `lean/lean-toolchain` need review. See
[docs/trust-model.md](docs/trust-model.md).

## Quickstart

### Toolchain

| Tool           | Version        | Used for                                    |
| -------------- | -------------- | ------------------------------------------- |
| GHC            | 9.14.1         | building gin                                |
| cabal-install  | 3.16.1.0       | building and testing gin                    |
| Lean 4         | 4.34.1         | the DSL, proofs and exporter (via `elan`)   |
| Icarus Verilog | 13.0           | Verilog and SystemVerilog lint and runs     |
| Verilator      | 5.052          | Verilog and SystemVerilog lint              |
| nvc            | 1.23.0         | VHDL-2008 analysis and runs                 |
| hlint          | 3.3.4          | linting the Haskell sources                 |

These are the versions gin is tested with. `elan` installs the Lean
version pinned in `lean/lean-toolchain` on first use. The Lean package has
no dependencies outside the Lean distribution.

### Build, test and validate

```sh
cabal build all
GIN_REQUIRE_TOOLS=1 cabal test   # without the variable, tests whose HDL tools are missing are pending
scripts/validate.sh              # the whole pipeline, from the Lean sources to HDL simulation
```

`scripts/validate.sh` builds and tests the Lean package, replays it
through the kernel with `leanchecker`, regenerates `examples/` and checks
that the result is byte for byte what is committed, runs `gin validate` on
every example for all three targets, and checks that designs proved with
`sorry` or `native_decide` are refused. It stops at the first failure. A
missing HDL tool is a failure.

### The `gin` command

Every command takes the IR file the exporter wrote; `testbench`, `sim`
and `validate` also take its vectors.

```sh
gin check     examples/counter/counter.gin.json
gin compile   examples/counter/counter.gin.json -o out              # out/counter.{v,sv,vhd}
gin testbench examples/counter/counter.gin.json --vectors examples/counter/counter.vectors.json -o out
gin sim       examples/counter/counter.gin.json --vectors examples/counter/counter.vectors.json
gin validate  examples/counter/counter.gin.json --vectors examples/counter/counter.vectors.json
```

From a checkout, run them as `cabal run -v0 gin -- check …`.

- `check` decodes and type checks the program and checks its certificate.
- `compile` writes the design for each target; `testbench` also writes
  `<top>_tb.<ext>`. `--target verilog|systemverilog|vhdl` (repeatable)
  selects targets; the default is all three.
- `sim` runs both reference simulators on the vectors and reports the
  first mismatching cycle and port.
- `validate` runs `sim`, then lints each target's design and runs its
  testbench, printing one `<check>: PASS|FAIL|SKIP(…)` line per check.
  `--min-cycles N` fails vectors with fewer than `N` cycles (default 1);
  `--allow-missing-tools` skips checks whose tool is not installed;
  `--tool-timeout SECONDS` bounds each tool run (default 300) and
  `--sim-timeout SECONDS` each reference simulation (default 600).
- `--spec-hash HEX` (every command) fails unless the certificate's spec
  hash, printed in every generated HDL header, is `HEX`.
- `--allow-axiom NAME` admits an extra axiom. `sorryAx`, the
  `Lean.ofReduce*` and `Lean.trustCompiler` axioms and any `._native.`
  axiom are refused regardless.

The exit status is 0 on success, 1 when a check, compile or validation
fails, and 2 on a usage error.

To add a circuit of your own, follow "Adding a circuit" in
[lean/README.md](lean/README.md).

## What is proven, validated and trusted

| Claim | Status | How |
| --- | --- | --- |
| The Lean implementation meets its specification | Proven | The refinement theorem, checked by the Lean kernel, for every cycle and every input stream. `leanchecker` replays every declaration, catching any that was added without kernel checking. |
| The proof takes no unsound shortcuts | Checked | The exporter refuses, and gin by default rejects, any axiom other than `propext`, `Classical.choice` and `Quot.sound`, in the theorem and in the implementation. |
| The specification is the one you meant | Reviewed | By you. The certificate carries the statement and every definition it depends on (`specDefinitions`), rendered by the exporter's fixed printer and printed into every generated HDL file with their hash; `--spec-hash` pins the reviewed version. |
| The core IR means the Lean definition | Validated | The vectors come from running compiled Lean code (the entry's vector source, reviewed to apply the top definition), never from the IR, and gin's core IR simulator must reproduce them unless it reports an inconclusive `SKIP`. |
| Normalization preserves meaning | Validated | The normal-form simulator must reproduce the same vectors, and the normal form is checked against its invariants. |
| The netlist and the generated HDL preserve meaning | Validated | Verilog and SystemVerilog designs must pass Verilator's `-Wall` lint and compile under Icarus Verilog, VHDL designs must analyse under nvc, and every generated testbench must reproduce the vectors under Icarus Verilog or nvc. |
| The exporter's translation and certificate are faithful | Trusted | gin cannot re-check a Lean proof. It trusts that the IR is the definition the theorem is about, and that the certificate's statement, definitions and axiom lists are the theorem's. Validation checks the first point only on the vectors' inputs. |
| The design's code is harmless to run | Trusted | Building a design runs its code, and the exporter links it; the exporter's checks refuse initializers and code that could run at start-up. Designs you did not write belong in a sandbox, which protects your machine but not the result: unless their sources were read for build-time code, their build can forge the certificate, IR and vectors (see `docs/trust-model.md`). |
| The tools are correct | Trusted | The Lean kernel and `leanchecker`, the Lean compiler (the vectors come from compiled code), GHC, the HDL tools, and whatever synthesis tool consumes the generated HDL. |

Validation is evidence, not proof: it shows that every stage agrees with
the Lean model on the vectors' inputs (1024 cycles per example), not on
every input, and neither the proofs nor the testbenches cover asserting
reset in the middle of a run. The meaning every stage must preserve is
defined in [docs/semantics.md](docs/semantics.md).
[docs/trust-model.md](docs/trust-model.md) gives the full trust model: the
trusted base, the threat model and a recommended CI setup.

## Repository layout

| Path | Contents |
| --- | --- |
| `lean/` | The Lean package: the signal DSL, the example circuits and their proofs, the exporter and its tests ([lean/README.md](lean/README.md)) |
| `examples/<name>/` | `<name>.gin.json` and `<name>.vectors.json` exported from Lean, for counter, detector and mac (generated: never edit by hand) |
| `src/Gin/Core/` | The core IR: types, values, primitives, syntax, JSON codec, type checker and normal form |
| `src/Gin/Certificate.hs` | The axiom policy |
| `src/Gin/Normalize*` | Normalization from the core IR to normal form |
| `src/Gin/Netlist/` | The netlist and its construction from the normal form |
| `src/Gin/Backend/` | Verilog, SystemVerilog and VHDL renderers and testbench generators |
| `src/Gin/Sim*` | The two reference simulators, for the core IR and for the normal form |
| `src/Gin/Driver.hs` | The command-line interface; `app/Main.hs` is the `gin` executable |
| `src/Gin/Limits.hs` | Resource bounds on untrusted input |
| `test/` | The hspec suite; `test/Gin/Examples.hs` holds hand-written fixtures at every pipeline level |
| `test/golden/` | Golden netlists and HDL: regenerate with `GIN_ACCEPT=1 cabal test` and review the diff |
| `scripts/export-examples.sh` | Build the Lean package, replay it through the kernel and regenerate `examples/` |
| `scripts/validate.sh` | The whole pipeline, from the Lean sources to HDL simulation |
| `docs/` | The file formats, the semantics every stage implements and the trust model |

## Documentation

- [docs/file-formats.md](docs/file-formats.md): the core IR (`gin-ir/1`)
  and test vector (`gin-vectors/1`) JSON formats, the decoding rules and
  the resource limits on input files.
- [docs/semantics.md](docs/semantics.md): the cycle semantics, the meaning
  of each primitive, the hardware mapping (clock `clk`, synchronous
  active-high reset `rst`) and the testbench protocol.
- [docs/trust-model.md](docs/trust-model.md): what is proved, validated and
  trusted, the threat model and a recommended CI setup.
- [lean/README.md](lean/README.md): the Lean workflow, the supported
  fragment and how to add a circuit.
- The module documentation in `src/`, starting with `Gin.Driver`, which
  describes every command.

## Contributing

Before sending a change, run

```sh
cabal build all --ghc-options=-Werror
GIN_REQUIRE_TOOLS=1 cabal test
hlint src test app
scripts/validate.sh
```

A change to the Lean sources must be committed together with the
`examples/` that `scripts/export-examples.sh` regenerates from it;
`scripts/validate.sh` fails otherwise. A change to generated HDL updates
the golden files under `test/golden/` (`GIN_ACCEPT=1 cabal test`); review
their diff as part of the change.

## Limitations

- Bit vectors are unsigned: there is no signed arithmetic or comparison.
- Shift amounts must be constants; there are no variable shifts.
- There are no memories (RAMs, register files): state lives in individual
  registers and Mealy machines.
- A design has a single clock domain, with one clock and one synchronous,
  active-high reset; there are no multiple clock domains or asynchronous
  resets.
- Ports are `Bool` or `BitVec n` (1 ≤ n ≤ 4096); product-typed ports are
  not supported. A circuit with several outputs returns a tuple, and each
  component becomes its own port.
- Register and Mealy initial values must be literals.
- The exporter is trusted (see the table above), and only the fragment of
  Lean documented in `lean/Gin/Export/Translate.lean` can be exported.
- Validation compares simulations on the exported vectors; it is not an
  equivalence proof between the Lean definition and the generated HDL.

## License

gin is distributed under the BSD-3-Clause license; see
[LICENSE.md](LICENSE.md).
