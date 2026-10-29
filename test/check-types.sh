#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
type_check_dir=$(mktemp -d "${TMPDIR:-/tmp}/gin-types.XXXXXX")
trap 'rm -rf "$type_check_dir"' EXIT HUP INT TERM
# A positive control detects a missing package or broken compiler setup.
cabal exec --offline -- ghc -fno-code -XGHC2024 -package gin \
  -outputdir "$type_check_dir" test/compile-pass/BoundedSettings.hs
for fixture in BoundedCoerce BoundedConstructor BoundedUpdate BoundedLiteral \
  BoundedNumber; do
  case "$fixture" in
    BoundedCoerce) expected="Couldn't match type" ;;
    BoundedLiteral) expected="Cannot satisfy: 17 <= 16|Couldn't match type" ;;
    BoundedConstructor|BoundedUpdate) \
      expected='not in scope|out of scope|not a record selector|'\
'Illegal term-level use of the type constructor' ;;
    BoundedNumber) expected='No instance for.*Num' ;;
  esac
  if cabal exec --offline -- ghc -fno-code -XGHC2024 -package gin \
      -outputdir "$type_check_dir" "test/compile-fail/$fixture.hs" > \
        "$type_check_dir/$fixture.log" 2>&1; then
    printf 'FAIL: %s unexpectedly compiled\n' "$fixture"
    exit 1
  fi
  if ! grep -Eiq "$expected" "$type_check_dir/$fixture.log"; then
    cat "$type_check_dir/$fixture.log"
    printf 'FAIL: %s failed for an unexpected reason\n' "$fixture"
    exit 1
  fi
  printf 'PASS: %s rejected at the type boundary\n' "$fixture"
done
