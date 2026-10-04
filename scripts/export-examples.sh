#!/usr/bin/env bash
# Regenerate the exported examples from the Lean sources.
#
#   scripts/export-examples.sh                  build, re-check and export
#   scripts/export-examples.sh --check-rejects  check that unproven designs are refused
#
# Run from the repository root. The export builds the Lean package with
# warnings as errors (which runs the Lean tests), replays every module the
# exported circuits and the exporter load (gin-check-export --list-modules)
# and every module of the package's module roots (Gin, GinTest, GinExport,
# GinCheckExport; every Lean source outside GinReject must be among them)
# through the kernel with leanchecker (catching declarations that were added
# without kernel checking, e.g. under debug.skipKernelTC), and then writes
# examples/<name>/<name>.gin.json and <name>.vectors.json for each example.
# Every export runs gin-check-export first and stops if it fails:
# gin-export links the design code, which runs as soon as it starts
# (initializers and closed terms of every linked module), so it never starts
# for circuits the checker, which links no design, refuses. The checker's
# certificate is the authority: gin-export writes into a temporary
# directory, and its output is refused unless every certificate in it is,
# byte for byte, the one gin-check-export computed; only then is it copied
# into examples/. Linked design code can still write any file the user can,
# so export designs you did not write only in a sandbox (lean/README.md,
# "Trust"). A second export must reproduce the files byte for byte.
#
# --check-rejects builds the reject fixtures under lean/GinReject, which are
# not part of the default build, and checks that each one is refused for its
# own reason: an axiom (sorryAx, a ._native. axiom), a kernel replay failure
# (of the design's module, or of an unchecked module it imports), a theorem
# without the refinement shape, a module initializer, a module with code
# that may run IO when gin-export starts (@[implemented_by], an unsafe
# closed term, foreign code), a translation that would run compiled code
# (Lean.reduceBool), a design that is not a reject fixture but loads one,
# or a certificate in gin-export's output other than the checker's. The
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
# loads, and those gin-export links, one per line, after the checks of
# gin-check-export.
loaded_modules() {
  lake -d lean exe gin-check-export --list-modules "$@"
}

# check_certificates CERTS OUT NAME...: for each named circuit,
# OUT/NAME/NAME.gin.json ends, byte for byte, in CERTS/NAME.certificate,
# the certificate as gin-check-export rendered it (the last member of the
# top-level object and the closing brace), and no object in the file has a
# key twice, so the file holds no other certificate that a reader could
# take instead.
check_certificates() {
  local certs=$1 out=$2 n
  shift 2
  for n in "$@"; do
    python3 - "$certs/$n.certificate" "$out/$n/$n.gin.json" <<'PY' || return 1
import json, sys

cert_path, gin_path = sys.argv[1], sys.argv[2]

def refuse(why):
    sys.exit(f"export-examples: {gin_path}: {why}; refusing the export")

def unique_keys(pairs):
    keys = [k for k, _ in pairs]
    for k in keys:
        if keys.count(k) > 1:
            refuse(f"the key {k!r} occurs twice in one object")
    return dict(pairs)

with open(cert_path, "rb") as f:
    tail = f.read()
with open(gin_path, "rb") as f:
    data = f.read()
if not (tail.startswith(b',\n  "certificate": ') and tail.endswith(b"\n}\n")):
    refuse(f"{cert_path} is not a certificate written by gin-check-export")
if not data.endswith(tail):
    refuse("the certificate is not the one gin-check-export computed")
try:
    doc = json.loads(data.decode("utf-8"), object_pairs_hook=unique_keys)
except ValueError as err:
    refuse(f"not JSON: {err}")
if not isinstance(doc, dict):
    refuse("not a JSON object")
PY
  done
}

# export_with EXE ROOT OUT NAME...: export the named circuits into OUT with
# the exporter EXE, whose root module is ROOT, only after gin-check-export
# has accepted them and the modules of ROOT, and accept the export only if
# every certificate EXE wrote is, byte for byte, the one gin-check-export
# computed. The checker links no design and runs none of their code; EXE
# links the designs, and their code runs as soon as it starts (initializers,
# closed terms), so it must not start before the checks pass, and its
# certificates are only accepted when they match the checker's.
export_with() {
  local exe=$1 root=$2 out=$3 certs
  shift 3
  certs=$(mktemp -d "$tmp/certificates.XXXXXX")
  lake -d lean exe gin-check-export --exporter "$root" --certificates "$certs" "$@" >/dev/null ||
    return 1
  lake -d lean exe "$exe" --out "$out" "$@" || return 1
  check_certificates "$certs" "$out" "$@"
}

# env_export_with VAR=VALUE EXE ROOT OUT NAME...: export_with, with VAR set
# in the environment of both tools.
env_export_with() {
  (export "${1?}" && shift && export_with "$@")
}

# export_to OUT NAME...: export_with the shipped gin-export.
export_to() {
  local out=$1
  shift
  export_with gin-export GinExport "$out" "$@"
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

# import_closure ROOT...: every module that importing one of the named root
# modules loads, toolchain modules included, one per line. Each root is
# imported on its own (two executable roots both declare main). Needs the
# Lean package built.
import_closure() {
  printf '%s\n' 'import Lean' 'open Lean in' 'def main (roots : List String) : IO Unit := do' \
    '  initSearchPath (← findSysroot)' \
    '  for r in roots do' \
    '    let env ← importModules #[{ module := r.toName }] {} (loadExts := false)' \
    '    for m in env.header.moduleNames do IO.println m' > "$tmp/closure.lean"
  (cd lean && lake env lean --run "$tmp/closure.lean" "$@")
}

# [lean-check-no-design] gin-check-export links no design: outside the Lean
# toolchain, its root module imports only the exporter (Gin.Export.*) and the
# DSL (Gin.Signal). Needs the Lean package built.
check_checker_closure() {
  local mods bad
  mods=$(import_closure GinCheckExport) || die "cannot read the modules of GinCheckExport"
  grep -qx GinCheckExport <<<"$mods" || die "GinCheckExport is not among its own modules"
  bad=$(grep -Ev '^(Init|Std|Lean|Lake)(\.|$)|^Gin\.Export\.|^Gin\.Signal$|^GinCheckExport$' <<<"$mods" || true)
  [ -z "$bad" ] || die "gin-check-export links modules other than the exporter and the DSL:"$'\n'"$bad"
}

# The module roots of the Lean package, other than the reject fixtures: the
# roots of its default libraries and executables.
module_roots=(Gin GinTest GinExport GinCheckExport)

# replay_modules NAME...: the modules the kernel replay covers, one per
# line, sorted: those exporting the named circuits loads and gin-export links
# (gin-check-export --list-modules), and the import closure, outside the Lean
# toolchain, of every module root, so the tests (GinTest) are replayed too.
replay_modules() {
  local listed roots
  listed=$(loaded_modules "$@") || die "gin-check-export --list-modules $* failed"
  roots=$(import_closure "${module_roots[@]}") || die "cannot read the modules of ${module_roots[*]}"
  printf '%s\n%s\n' "$listed" "$roots" | grep -Ev '^(Init|Std|Lean|Lake)(\.|$)|^$' | sort -u
}

# check_replay_covers MODULE...: every Lean source under lean/ outside the
# reject fixtures (GinReject) is one of the named modules, so no module of the
# package escapes the kernel replay.
check_replay_covers() {
  local src m missing=
  while IFS= read -r src; do
    m=${src#lean/}
    m=${m%.lean}
    m=${m//\//.}
    printf '%s\n' "$@" | grep -qxF -- "$m" || missing+="$m"$'\n'
  done < <(find lean -path lean/.lake -prune -o -path lean/GinReject -prune -o \
    -name GinReject.lean -prune -o -name '*.lean' -print)
  [ -z "$missing" ] || die "the kernel replay does not cover these modules:"$'\n'"$missing"
}

export_examples() {
  local mods
  lake -d lean build --wfail
  check_reserved_words
  check_checker_closure
  # [lean-kernel-replay] exactly the modules the export loads and those of
  # every module root, which together are every module of the package
  mods=($(replay_modules "${examples[@]}")) || die "cannot list the modules to replay"
  [ "${#mods[@]}" -gt 0 ] || die "no modules to replay"
  check_replay_covers "${mods[@]}"
  replay "$tmp/replay" "${mods[@]}"
  # [lean-certificate-authority] exported into a temporary directory and
  # copied into examples/ only once every certificate matches the checker's
  export_to "$tmp/export" "${examples[@]}" || die "the export of ${examples[*]} failed"
  for n in "${examples[@]}"; do
    mkdir -p "examples/$n"
    cp "$tmp/export/$n/$n.gin.json" "$tmp/export/$n/$n.vectors.json" "examples/$n/"
  done
  # [lean-determinism] a second export reproduces every file byte for byte
  export_to "$tmp/second" "${examples[@]}" >/dev/null ||
    die "the second export of ${examples[*]} failed"
  for n in "${examples[@]}"; do
    diff -r "$tmp/second/$n" "examples/$n" >/dev/null || die "the export of $n is not deterministic"
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

# expect_refusal TOOL NAME TEXT REASON COMMAND...: COMMAND fails with a
# message that contains TEXT (outside the trailing list of allowed axioms).
expect_refusal() {
  local tool=$1 name=$2 text=$3 reason=$4 out
  shift 4
  if out=$("$@" 2>&1); then
    die "$tool $name succeeded; it must refuse $reason"
  fi
  grep -F -- "$text" <<<"${out//Allowed axioms: */}" >/dev/null ||
    die "$tool $name failed without naming $text:"$'\n'"$out"
}

# check_reject MODULE NAME TEXT REASON: MODULE builds, and exporting NAME
# fails with a message that contains TEXT: gin-check-export refuses NAME, so
# the export pipeline stops there, and gin-export, run directly, refuses NAME
# too.
check_reject() {
  local module=$1 name=$2 text=$3 reason=$4
  build_fixture "$module"
  expect_refusal gin-check-export "$name" "$text" "$reason" lake -d lean exe gin-check-export "$name"
  expect_refusal "the export of" "$name" "$text" "$reason" export_to "$tmp/reject" "$name"
  expect_refusal gin-export "$name" "$text" "$reason" lake -d lean exe gin-export --out "$tmp/reject" "$name"
  echo "export-examples: $name refused ($reason)"
}

# The initializer of GinReject.Hooked, a module that gin-export-hooked links,
# runs as soon as gin-export-hooked starts (it writes GIN_HOOK_MARKER), but
# the export pipeline refuses the circuit in gin-check-export, before
# gin-export-hooked starts: the marker is not written.
check_linked_initializer() {
  local marker=$tmp/hook-ran out
  # built before GIN_HOOK_MARKER is set: building runs the initializer too
  out=$(lake -d lean build gin-export-hooked 2>&1) || die "gin-export-hooked does not build:"$'\n'"$out"
  GIN_HOOK_MARKER=$marker lake -d lean exe gin-export-hooked --help >/dev/null
  [ -f "$marker" ] || die "the initializer of GinReject.Hooked did not run when gin-export-hooked started"
  rm -f "$marker"
  expect_refusal "the export of" hooked "module GinReject.Hooked registers IO initializers" \
    "a module initializer linked into the exporter" \
    env_export_with "GIN_HOOK_MARKER=$marker" gin-export-hooked GinReject.HookedExport "$tmp/reject" hooked
  [ ! -f "$marker" ] || die "gin-export-hooked started (its initializer ran) although gin-check-export refused hooked"
  # the modules the exporter links are checked even when no requested
  # circuit loads them
  expect_refusal gin-check-export GinReject.HookedExport "module GinReject.Hooked registers IO initializers" \
    "a module initializer linked into the exporter" \
    lake -d lean exe gin-check-export --exporter GinReject.HookedExport counter
  echo "export-examples: hooked refused before gin-export-hooked started (a linked module initializer)"
}

# check_kernel_reject MODULE NAME BAD: MODULE builds, and the kernel replay
# of the modules that exporting NAME loads fails and names module BAD.
check_kernel_reject() {
  local module=$1 name=$2 bad=$3 out
  local -a mods
  build_fixture "$module"
  mods=($(loaded_modules "$name")) || die "gin-check-export --list-modules $name failed"
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
  mods=($(loaded_modules counter)) || die "gin-check-export --list-modules counter failed"
  out=$(replay "$tmp/replay-stale" "${mods[@]}" 2>&1) ||
    die "a stale .olean ($stale) broke the kernel replay of ${mods[*]}:"$'\n'"$out"
  rm -f "$stale"
  echo "export-examples: a stale .olean is not replayed"
}

# gin-export-forged changes the certificates it wrote after exporting, as
# code linked into gin-export that gin-check-export does not see could; the
# export pipeline refuses its output, whose certificate is not the one the
# checker computed. A file that ends in the checker's certificate but holds
# a second, forged certificate member earlier is refused too.
check_forged_certificate() {
  local out
  out=$(lake -d lean build gin-export-forged 2>&1) || die "gin-export-forged does not build:"$'\n'"$out"
  expect_refusal "the export of" counter "the certificate is not the one gin-check-export computed" \
    "a certificate other than the checker's" \
    export_with gin-export-forged GinExport "$tmp/forged" counter
  grep -F -- "List.range (t + 1)" "$tmp/forged/counter/counter.gin.json" >/dev/null ||
    die "gin-export-forged did not change the certificate it wrote"
  export_to "$tmp/duplicate" counter >/dev/null || die "the export of counter failed"
  lake -d lean exe gin-check-export --certificates "$tmp/duplicate-certificates" counter >/dev/null ||
    die "gin-check-export counter failed"
  check_certificates "$tmp/duplicate-certificates" "$tmp/duplicate" counter ||
    die "the certificate of an honest export of counter does not match the checker's"
  sed -i.bak '1s/^{$/{"certificate": {"theorem": "Counter.counter_correct", "statement": "True"},/' \
    "$tmp/duplicate/counter/counter.gin.json"
  expect_refusal "the certificate check of" counter "the key 'certificate' occurs twice in one object" \
    "a second certificate member" \
    check_certificates "$tmp/duplicate-certificates" "$tmp/duplicate" counter
  echo "export-examples: certificates other than the checker's refused"
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
  check_linked_initializer
  check_reject GinReject.BadImplementedBy bad_implemented_by \
    "BadImplementedBy.inc is implemented by BadImplementedBy.incOther" \
    "compiled code that is not the definition"
  check_reject GinReject.BadUnsafeIO bad_unsafe_io "BadUnsafeIO.cached is unsafe" \
    "an unsafe closed term, which would run when gin-export starts"
  check_reject GinReject.BadExtern bad_extern "BadExtern.foreign calls foreign code (@[extern])" \
    "foreign code called by a closed term, which would run when gin-export starts"
  check_forged_certificate
  check_reject GinReject.BadReduceBool bad_reduce_bool \
    "BadReduceBool.hooked refers to Lean.reduceBool" "a translation that would run compiled code"
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
