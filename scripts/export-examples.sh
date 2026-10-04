#!/usr/bin/env bash
# Regenerate the exported examples from the Lean sources.
#
#   scripts/export-examples.sh                  build, re-check and export
#   scripts/export-examples.sh --check-rejects  check that unproven designs are refused
#
# Run from the repository root. The export builds the Lean package with
# warnings as errors (which runs the Lean tests), replays every module the
# exported circuits load (gin-export --list-modules) through the kernel with
# leanchecker (catching declarations that were added without kernel
# checking, e.g. under debug.skipKernelTC), and then writes
# examples/<name>/<name>.gin.json and <name>.vectors.json for each example.
# A second export into a temporary directory must reproduce the files byte
# for byte.
#
# --check-rejects builds the reject fixtures under lean/GinReject, which are
# not part of the default build, and checks that each one is refused for its
# own reason: an axiom (sorryAx, a ._native. axiom), a kernel replay failure
# (of the design's module, or of an unchecked module it imports), a theorem
# without the refinement shape, a module initializer, or a design that is not
# a reject fixture but loads one. The
# unexpander fixture is not refused; its check module verifies that the
# certificate shows the real specification. Nothing under examples/ may
# change.
set -euo pipefail

cd "$(dirname "$0")/.."

examples=(counter detector mac)

tmp=$(mktemp -d)
# a stale .olean planted by check_stale_olean, removed on exit
stale=lean/.lake/build/lib/lean/Gin/StaleReplayProbe.olean
trap 'rm -rf "$tmp" "$stale"' EXIT

die() {
  printf 'export-examples: %s\n' "$*" >&2
  exit 1
}

# replay DIR MODULE...: replay exactly the named modules through the kernel.
# leanchecker replays every .olean on its search path whose module name
# starts with a target, so it runs on a search path (DIR) that holds copies
# of the named modules' files and nothing else: no other module, and no stale
# .olean of a deleted source, is replayed or can satisfy an import. Every
# module a named module imports must be named too (or be a toolchain module).
replay() {
  local dir=$1 m rel src found path
  shift
  local -a paths
  IFS=: read -r -a paths <<<"$(cd lean && lake env printenv LEAN_PATH)"
  mkdir -p "$dir"
  for m in "$@"; do
    rel=${m//.//}
    found=
    for path in "${paths[@]}"; do
      [ -n "$path" ] && [ -f "$path/$rel.olean" ] || continue
      mkdir -p "$dir/$(dirname "$rel")"
      for src in "$path/$rel".olean "$path/$rel".olean.server "$path/$rel".olean.private; do
        if [ -f "$src" ]; then cp "$src" "$dir/$(dirname "$rel")/"; fi
      done
      found=1
      break
    done
    [ -n "$found" ] || die "no .olean for module $m on the Lean search path"
  done
  (cd lean && lake env env LEAN_PATH="$dir" leanchecker "$@")
}

# The modules outside the Lean toolchain that exporting the named circuits
# loads, one per line, after the exporter's module checks.
loaded_modules() {
  lake -d lean exe gin-export --list-modules "$@"
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
  local mods
  lake -d lean build --wfail
  check_reserved_words
  # [lean-kernel-replay] exactly the modules the export loads
  mods=($(loaded_modules "${examples[@]}")) || die "gin-export --list-modules ${examples[*]} failed"
  [ "${#mods[@]}" -gt 0 ] || die "gin-export --list-modules ${examples[*]} listed no modules"
  replay "$tmp/replay" "${mods[@]}"
  lake -d lean exe gin-export --out examples "${examples[@]}"
  # [lean-determinism] a second export reproduces every file byte for byte
  lake -d lean exe gin-export --out "$tmp" "${examples[@]}" >/dev/null
  for n in "${examples[@]}"; do
    diff -r "$tmp/$n" "examples/$n" >/dev/null || die "the export of $n is not deterministic"
  done
  echo "export-examples: exported ${examples[*]} (kernel-checked ${mods[*]})"
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

# check_kernel_reject MODULE NAME BAD: MODULE builds, and the kernel replay
# of the modules that exporting NAME loads fails and names module BAD.
check_kernel_reject() {
  local module=$1 name=$2 bad=$3 out
  local -a mods
  build_fixture "$module"
  mods=($(loaded_modules "$name")) || die "gin-export --list-modules $name failed"
  if out=$(replay "$tmp/replay-$name" "${mods[@]}" 2>&1); then
    die "leanchecker accepted ${mods[*]}; it must fail on the unchecked declaration in $bad"
  fi
  grep -F -- "found a problem in $bad" <<<"$out" >/dev/null ||
    die "leanchecker failed on ${mods[*]} without naming $bad:"$'\n'"$out"
  echo "export-examples: $name refused by the kernel replay of $bad (replayed ${mods[*]})"
}

# A stale .olean whose source is gone (here a copy of the unchecked
# GinReject.BadKernel, under a name in the Gin tree) is not replayed: the
# replay of the counter's modules still passes.
check_stale_olean() {
  local out
  local -a mods
  build_fixture GinReject.BadKernel
  cp lean/.lake/build/lib/lean/GinReject/BadKernel.olean "$stale"
  mods=($(loaded_modules counter)) || die "gin-export --list-modules counter failed"
  out=$(replay "$tmp/replay-stale" "${mods[@]}" 2>&1) ||
    die "a stale .olean ($stale) broke the kernel replay of ${mods[*]}:"$'\n'"$out"
  rm -f "$stale"
  echo "export-examples: a stale .olean is not replayed"
}

check_rejects() {
  # [lean-rejects] every fixture builds, is refused for its own reason, and
  # nothing under examples/ changes
  snapshot "$tmp/before"
  check_reject GinReject.Bad bad sorryAx "a proof that depends on sorryAx"
  check_reject GinReject.BadNative bad_native ._native. "a proof that depends on a ._native. axiom"
  check_kernel_reject GinReject.BadKernel bad_kernel GinReject.BadKernel
  check_kernel_reject GinReject.BadImport bad_import GinReject.Unchecked
  check_stale_olean
  check_reject GinReject.BadImport forged "imports the reject fixture module GinReject.Unchecked" \
    "a design that is not a reject fixture but imports one"
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
