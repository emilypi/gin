# Circuit portfolios with Yolk

Gin's optional optimizer imports the complete normalized transition function
into Yolk's many-sorted e-graph. Boolean values and every bit-vector width
have distinct sorts. Inputs and current register values are symbolic leaves;
outputs and next-state expressions are extracted together. Shared nodes are
charged once across all roots. Extraction reconstructs a shared normal form
and checks it before HDL generation.

Use sibling checkouts of `gin` and `yolk`; the default `cabal.project` builds
both. Existing compilation remains unchanged unless optimization is requested.

This implementation is tested with Yolk revision
`6aa9b0228ba678dcecd3cf98d289126cce9d07ff` (the companion Pareto extraction
change). Use that revision in the sibling checkout when reproducing the PR.

```sh
cabal run gin -- optimize examples/muxadd/muxadd.gin.json \
  --policy examples/optimization/structural-policy.json \
  --vectors examples/muxadd/muxadd.vectors.json -o out/muxadd-portfolio
```

The output directory must be new. It contains the baseline and extracted
implementations, all requested HDL formats, self-checking testbenches when
vectors were supplied, the normalized policy, and separate search and
simulation reports. Files are generated in a private sibling directory and
published together. Candidate paths are compiler-generated digests.

The example admits one adder/two muxes and two adders/one mux. These are
structural alternatives, not claims about a particular FPGA's mapped resources.
Run `scripts/showcase-optimization.sh NEW_DIRECTORY` to reproduce extraction
and validate the preferred candidate on Verilog, SystemVerilog and VHDL.

## Policy

`gin-policy/1` contains 1–16 named minimization objectives. Each supplies an
optional nonnegative `default` node cost (default 1), an `operators` map,
and `widthWeighted` (default false). Operator names are the core IR names,
plus `mux` and `literal`. Literal costs default to zero. Inputs and register
leaves cost zero; register counts and bits are separately reported on each
final circuit. Width weighting uses the result width (one for Bool), so it
is a configurable heuristic, not a gate or power model.

`upperBounds`, when supplied, is an inclusive final-circuit cost vector in
objective order. `prefer` gives a lexicographic selection order *after*
Pareto search; it does not scalarize the search. Missing names are appended
in objective order. Ties are broken by candidate digest. Unknown fields,
duplicate keys and misspelled operator names are errors.

`search` configures `iterations`, `nodes`, `matches`, `expansions`, `archive`
and equal-vector `witnesses`. `timeoutSeconds` bounds the complete
normalization, saturation, extraction, reconstruction and manifest forcing.
Policy files are limited to 64 KiB; the existing bounded JSON decoder also
rejects excessive nesting, number precision and magnitudes before parsing.
The library exposes bounded options for callers implementing other policies.

## Haskell API conventions

Records keep named selectors and export `fieldNameL` lenses from the defining
module; sum types export constructor prisms. Results describe the compiler's
work when returned. Editing a result record does not rerun extraction, scoring,
or semantic checks.

Policy timeouts, search budgets, weights and upper bounds use checked
`BoundedInt lower upper` values from `Gin.Core.Bounded`. `mkBoundedInt` and
the `boundedInt` prism reject values outside the inclusive interval;
`boundedIntValue` is a getter. The representation has no unchecked setter
or numeric instance, and nominal roles prevent coercion between intervals.
`boundedIntLiteral @n` checks constants at compile time. JSON decoders use
the same smart constructor and keep the existing JSON format.

`mkObjective` and `mkPolicy` check relationships between names, operators,
preferences and objective dimensions. `buildPortfolio` rechecks those
relationships after record updates, without serializing and reparsing a
policy. `PolicySearch` holds the bounded settings; Yolk options are computed
from it and the current objectives, avoiding stale stored dimensions.

`decodePolicy` uses the existing Aeson parsers for typed JSON fields, then
checks the policy through the same smart-construction boundary as `mkPolicy`.
Both stop at the first error and return `Either GinError Policy`. Field paths
identify invalid JSON fields and invalid objective or policy relationships.
`validatePolicy` applies those same checks after record or lens edits.

Collections are capped before traversing their contents. The shared JSON
decoder still rejects malformed syntax, duplicate keys, negative numbers,
and resource-limit violations before parsing policy fields.

`pipelineCircuit` takes a `PipelineDepth`, created with `mkPipelineDepth`
or a checked literal. Reported latency and stage depth are checked values
too. For example, `view (scheduledLatencyL . boundedIntValue) scheduled`
reads the latency as an `Int`.

Objective and preference lists are capped at 16 elements. Circuit bindings
and event logs use sequential traversal or prepend/reverse accumulation;
they retain lists. Yolk's repeatedly combined coordinate vectors use boxed
`Vector Natural` internally. Accumulating left folds in these paths are
strict; no lazy `foldl` or `foldl1` is retained.

All objective arithmetic is exact and nonnegative. Every candidate reports
both its extracted-forest vector and its final vector after newly dead state
and logic have been removed. Policy bounds are applied after cleanup, so
state that will disappear cannot cause premature rejection. Extraction
coverage refers to the former, before this final filtering. The final observed set is a portfolio for further evaluation;
it is not guaranteed to cover all nondominated physical implementations.

The feasible baseline is retained as a fallback. `finalFrontier` identifies
the nondominated final vectors among the evaluated feasible candidates;
`finalFeasibility` reports only whether this portfolio contains a feasible
candidate. Neither promotes the raw extraction status to a whole-circuit
optimality or infeasibility proof.

## Search status and selection

Coverage (`Complete`, `Partial`, `Approximate`), feasibility
(`FeasibleFound`, `NoFeasibleFoundYet`, `ProvenInfeasible`), termination and
witness completeness are separate fields. A zero work budget can still
have a feasible seed. Lack of a feasible incumbent under a work limit is
not a proof of infeasibility. Archive overflow is explicitly approximate,
with no claimed epsilon guarantee.

Completeness covers objective vectors in the frozen visible e-graph under
one representative per e-class. It does not mean saturation discovered all
equivalent circuits, all equally scored witnesses were retained, arbitrary
physical costs were optimized, or a semantic proof has been checked. Scalar
Yolk extraction remains available independently.

```sh
cabal run gin -- compile examples/muxadd/muxadd.gin.json \
  --optimize examples/optimization/structural-policy.json --candidate SHA256 -o out/chosen
```

The same flags apply to `check`, `testbench`, `sim` and `validate`. Omitting
`--candidate` selects according to `prefer`. These commands rebuild the
portfolio from the checked source and policy; they do not trust an imported
manifest, HDL file, claimed validation result or cached proof. A foreign
digest is rejected. Digests identify context and content, not authenticity.

## Timing contracts

The e-graph rewrites preserve every cycle, register initialization and state
identity. Separate pipelining is explicit:

```sh
cabal run gin -- pipeline examples/muxadd/muxadd.gin.json --max-depth 1 \
  --optimize examples/optimization/structural-policy.json \
  --vectors examples/muxadd/muxadd.vectors.json -o out/pipeline
```

Pipelining accepts combinational kernels only. It limits structural logic
levels per stage, inserts and shares delay registers, and aligns all outputs
and reconvergent paths to the same input frame. It accepts one frame per
cycle without backpressure. `timing.json` specifies the latency and warmup:
after reset, output cycle `t + latency` corresponds to source input cycle
`t`. Warmup outputs are outside that contract. Simulation and HDL testbenches
drain the pipeline and compare all post-warmup results with source vectors.

Stage depth is a proxy. A physical toolchain must determine clock frequency,
area, routing and power. Stateful retiming, duplication by use, arbitrary
resource-sharing schedules and clock-domain crossings are not implemented.

## Independent equivalence replay

```sh
cabal run gin -- prove examples/muxadd/muxadd.gin.json \
  --optimize examples/optimization/structural-policy.json -o out/proof
```

The emitter constructs a universally quantified Lean obligation for outputs
and retained next-state values, checks matching initial values, projects
away removed registers, and instantiates a state-induction theorem to lift
the result to all cycles. It uses only generated identifiers, fixed primitive
spellings and checked numeric values. The runner compiles fresh source in a
private directory, inspects the theorem's axioms against Gin's existing
policy, and replays the resulting module with `leanchecker`. It pins the
Lean toolchain and enforces timeouts with process-group cleanup.

Kernel simplification is intentionally incomplete. Small obligations may
use kernel finite enumeration; native decision procedures and added axioms
are not accepted. Failure leaves the source reviewable and reports
`unverified`. The evidence proves stream equality between the two normal forms; it is
not a proof of Gin's source exporter or HDL backend. The source specification
certificate, optimizer evidence, vector simulation and HDL validation remain
distinct records.

## Physical evaluation

No physical target was selected for this implementation. Structural node
weights can encode user-supplied area or switching heuristics, but reports
label them as proxies. Physical timing, power/energy and HBM calibration
remain unavailable until a platform, tool versions, constraints and workload
measurement boundary are supplied. Nothing in the portfolio promotes an
estimate to a measurement or assumes several physical winners must exist.

## Generated memory accelerators

```sh
cabal run gin -- memory examples/memorymap/memorymap.gin.json \
  --words examples/memory-words.json --traffic examples/memory-traffic.json \
  --lanes 1 --lanes 2 --lanes 4 -o out/memory
```

The compiler generates a SystemVerilog read–transform–write accelerator for
each requested lane count. The pure kernel must have one bit-vector input and
one output of the same width. The [memory contract](memory-contract.md)
specifies commands, ready/valid channels, write acknowledgements, reset,
non-overlapping address ranges and completion. This is a generated accelerator;
binding its logical ports to AXI/HBM remains platform work.

With `--optimize`, memory evaluation crosses the circuit portfolio with the
requested lane counts; `--candidate` restricts it to one kernel. Each scenario
specifies channel count, request/response service periods and read/write
latencies. Fair channel arbitration bounds shared bandwidth even when more
lanes are available. `memory-portfolio.json` reports all generated designs,
modeled outputs and a nondominated frontier over per-lane replicated kernel
costs, lane count and completion cycles for each scenario. Lane count is an
explicit overhead proxy, not a transistor or power measurement. Cycle-limited
runs remain visible and are excluded from the completed frontier.

The portfolio is bounded by 128 generated designs, 16 scenarios, 16 million
modeled word bits and 100 million lane/channel/cycle work units. A separate
`--memory-timeout` covers complete model evaluation and report forcing.
