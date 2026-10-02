#!/usr/bin/env bash
# Regenerate the exported examples from the Lean sources.
#
#   scripts/export-examples.sh                  build, re-check and export
#   scripts/export-examples.sh --check-rejects  check that unproven designs are refused
#
# Run from the repository root. The export builds the Lean package with
# warnings as errors (which runs the Lean tests), replays every module
# through the kernel with leanchecker (catching declarations that were added
# without kernel checking, e.g. under debug.skipKernelTC), and then writes
# examples/<name>/<name>.gin.json and <name>.vectors.json for each example.
# A second export into a temporary directory must reproduce the files byte
# for byte.
#
# --check-rejects builds the two reject fixtures, which are not part of the
# default build, and checks that exporting each one fails with a message
# naming the offending axiom and leaves examples/ untouched.
set -euo pipefail

cd "$(dirname "$0")/.."

examples=(counter detector mac)

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

die() {
  printf 'export-examples: %s\n' "$*" >&2
  exit 1
}

export_examples() {
  lake -d lean build --wfail
  (cd lean && lake env leanchecker Gin)
  lake -d lean exe gin-export --out examples "${examples[@]}"
  # [lean-determinism] a second export reproduces every file byte for byte
  lake -d lean exe gin-export --out "$tmp" "${examples[@]}" >/dev/null
  for n in "${examples[@]}"; do
    diff -r "$tmp/$n" "examples/$n" >/dev/null || die "the export of $n is not deterministic"
  done
  echo "export-examples: exported ${examples[*]}"
}

# Copy the current contents of examples/ to $1.
snapshot() {
  mkdir -p "$1"
  if [ -d examples ]; then cp -R examples/. "$1"; fi
}

# check_reject MODULE NAME AXIOM: MODULE builds, and exporting NAME fails
# with a message that names AXIOM (outside the trailing list of allowed
# axioms).
check_reject() {
  local module=$1 name=$2 axiom=$3 out
  out=$(lake -d lean build "$module" 2>&1) || die "$module does not build:"$'\n'"$out"
  if out=$(lake -d lean exe gin-export "$name" 2>&1); then
    die "gin-export $name succeeded; it must refuse a proof that depends on $axiom"
  fi
  grep -F -- "$axiom" <<<"${out//Allowed axioms: */}" >/dev/null ||
    die "gin-export $name failed without naming $axiom:"$'\n'"$out"
  echo "export-examples: $name refused (depends on $axiom)"
}

check_rejects() {
  # [lean-rejects] both fixtures build, are refused naming the axiom, and
  # nothing under examples/ changes
  snapshot "$tmp/before"
  check_reject Gin.Examples.Bad bad sorryAx
  check_reject Gin.Examples.BadNative bad_native ._native.
  snapshot "$tmp/after"
  diff -r "$tmp/before" "$tmp/after" >/dev/null || die "a refused export changed examples/"
  echo "export-examples: rejects ok"
}

case "${1-}" in
  "") export_examples ;;
  --check-rejects) check_rejects ;;
  *)
    echo "usage: scripts/export-examples.sh [--check-rejects]" >&2
    exit 2
    ;;
esac
