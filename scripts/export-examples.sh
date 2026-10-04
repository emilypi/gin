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
# --check-rejects builds the reject fixtures under lean/GinReject, which are
# not part of the default build, and checks that each one is refused for its
# own reason: an axiom (sorryAx, a ._native. axiom), a kernel replay failure,
# a theorem without the refinement shape, or a module initializer. The
# unexpander fixture is not refused; its check module verifies that the
# certificate shows the real specification. Nothing under examples/ may
# change.
set -euo pipefail

cd "$(dirname "$0")/.."

examples=(counter detector mac)

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

die() {
  printf 'export-examples: %s\n' "$*" >&2
  exit 1
}

# The module roots of the Lean package (lean_lib names, lean_exe roots) from
# lean/lakefile.toml, except the reject fixtures.
module_roots() {
  awk '
    /^\[\[/ { kind = $0; next }
    kind == "[[lean_lib]]" && $1 == "name" { print $3 }
    kind == "[[lean_exe]]" && $1 == "root" { print $3 }
  ' lean/lakefile.toml | tr -d '"' | grep -vx GinReject
}

# The words of gin's reservedWords in src/Gin/Netlist/Types.hs, one per
# line, sorted: the string literals of its definition (up to the first blank
# line), with Haskell string gaps removed.
haskell_reserved_words() {
  sed -n '/^reservedWords =/,/^$/p' src/Gin/Netlist/Types.hs | grep -v '^ *--' | tr '\n' ' ' |
    sed 's/\\ *\\//g' | grep -o '"[^"]*"' | tr -d '"' | tr -s ' ' '\n' | sed '/^$/d' | sort -u
}

# [lean-reserved-words] the exporter refuses exactly the identifiers gin
# reserves: Gin.Export.reservedWords, evaluated by Lean, is the same set as
# gin's list. Needs the Lean package built.
check_reserved_words() {
  local hs lean
  printf '%s\n' 'import Gin.Export.Reserved' \
    'def main : IO Unit := for w in Gin.Export.reservedWords.toList do IO.println w' \
    > "$tmp/reserved.lean"
  hs=$(haskell_reserved_words)
  lean=$(cd lean && lake env lean --run "$tmp/reserved.lean" | sort -u)
  [ -n "$hs" ] || die "no reserved words found in src/Gin/Netlist/Types.hs"
  [ "$hs" = "$lean" ] || die "lean/Gin/Export/Reserved.lean and src/Gin/Netlist/Types.hs reserve different words:"$'\n'"$(diff <(echo "$hs") <(echo "$lean"))"
}

export_examples() {
  local roots
  lake -d lean build --wfail
  check_reserved_words
  # [lean-kernel-replay] every module root except the reject fixtures
  roots=($(module_roots))
  [ "${#roots[@]}" -gt 0 ] || die "no module roots found in lean/lakefile.toml"
  (cd lean && lake env leanchecker "${roots[@]}")
  lake -d lean exe gin-export --out examples "${examples[@]}"
  # [lean-determinism] a second export reproduces every file byte for byte
  lake -d lean exe gin-export --out "$tmp" "${examples[@]}" >/dev/null
  for n in "${examples[@]}"; do
    diff -r "$tmp/$n" "examples/$n" >/dev/null || die "the export of $n is not deterministic"
  done
  echo "export-examples: exported ${examples[*]} (kernel-checked ${roots[*]})"
}

# Copy the current contents of examples/ to $1.
snapshot() {
  mkdir -p "$1"
  if [ -d examples ]; then cp -R examples/. "$1"; fi
}

build_fixture() {
  local out
  out=$(lake -d lean build "$1" 2>&1) || die "$1 does not build:"$'\n'"$out"
}

# check_reject MODULE NAME TEXT REASON: MODULE builds, and exporting NAME
# fails with a message that contains TEXT (outside the trailing list of
# allowed axioms).
check_reject() {
  local module=$1 name=$2 text=$3 reason=$4 out
  build_fixture "$module"
  if out=$(lake -d lean exe gin-export "$name" 2>&1); then
    die "gin-export $name succeeded; it must refuse $reason"
  fi
  grep -F -- "$text" <<<"${out//Allowed axioms: */}" >/dev/null ||
    die "gin-export $name failed without naming $text:"$'\n'"$out"
  echo "export-examples: $name refused ($reason)"
}

# The kernel replay of MODULE fails and names it.
check_kernel_reject() {
  local module=$1 out
  build_fixture "$module"
  if out=$(cd lean && lake env leanchecker "$module" 2>&1); then
    die "leanchecker accepted $module; it must fail on the unchecked declaration"
  fi
  grep -F -- "found a problem in $module" <<<"$out" >/dev/null ||
    die "leanchecker failed on $module without naming it:"$'\n'"$out"
  echo "export-examples: $module refused by the kernel replay"
}

check_rejects() {
  # [lean-rejects] every fixture builds, is refused for its own reason, and
  # nothing under examples/ changes
  snapshot "$tmp/before"
  check_reject GinReject.Bad bad sorryAx "a proof that depends on sorryAx"
  check_reject GinReject.BadNative bad_native ._native. "a proof that depends on a ._native. axiom"
  check_kernel_reject GinReject.BadKernel
  local thm
  for thm in tautology at_zero calls_impl or_true; do
    check_reject GinReject.BadShape "bad_$thm" "theorem BadShape.$thm does not have the refinement shape" \
      "theorem BadShape.$thm without the refinement shape"
  done
  check_reject GinReject.BadInit bad_init "module GinReject.BadInit registers IO initializers" \
    "a module initializer"
  # [lean-printer] not refused: the certificate names specR and lists its body
  build_fixture GinReject.BadUnexpander
  build_fixture GinReject.UnexpanderCheck
  echo "export-examples: GinReject.BadUnexpander certificate shows specR"
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
