#!/usr/bin/env bash
# Reproduce the whole pipeline, from the Lean sources to HDL simulation.
#
#   scripts/validate.sh
#
# Run from the repository root (the script changes there itself). Needs the
# Lean toolchain, cabal and GHC, and the HDL tools gin validate runs
# (Icarus Verilog, Verilator and nvc); a missing tool is a failure. Steps,
# stopping at the first failure:
#
#   1. scripts/export-examples.sh: build and test the Lean package, replay
#      it through the kernel with leanchecker, and regenerate examples/.
#   2. The regenerated files must be the committed ones: the export is
#      deterministic, so any difference under examples/ or lean/ means the
#      committed examples are stale. Uncommitted changes there fail this
#      step too; commit the Lean change together with its export and rerun.
#   3. gin validate on every example: both reference simulators and the
#      Verilog, SystemVerilog and VHDL testbenches must reproduce the
#      vectors computed in Lean.
#   4. scripts/export-examples.sh --check-rejects: designs proved with
#      sorry or native_decide are refused and nothing is written.
set -euo pipefail

cd "$(dirname "$0")/.."

examples=(counter detector mac)

step() {
  printf '\nvalidate: %s\n' "$*"
}

step "exporting the examples from Lean"
scripts/export-examples.sh

step "checking that the export matches the committed files"
changed=$(git status --porcelain --untracked-files=all -- examples lean)
if [ -n "$changed" ]; then
  printf 'validate: the export differs from the committed files:\n%s\n' "$changed" >&2
  echo "validate: commit the regenerated examples together with the Lean change" >&2
  exit 1
fi

for n in "${examples[@]}"; do
  step "gin validate examples/$n"
  cabal run -v0 gin -- validate "examples/$n/$n.gin.json" --vectors "examples/$n/$n.vectors.json"
done

step "checking that unproven designs are refused"
scripts/export-examples.sh --check-rejects

step "ok: ${examples[*]} validated on every target"
