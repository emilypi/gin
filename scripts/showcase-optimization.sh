#!/usr/bin/env bash
# Reproduce the structural search and replay the selected implementation.
set -euo pipefail
cd "$(dirname "$0")/.."
destination=${1:-out/optimization}
policy=examples/optimization/structural-policy.json
source=examples/muxadd/muxadd.gin.json
vectors=examples/muxadd/muxadd.vectors.json
cabal run -v0 gin -- optimize "$source" --policy "$policy" --vectors "$vectors" -o "$destination"
cabal run -v0 gin -- validate "$source" --optimize "$policy" --vectors "$vectors" --min-cycles 1024
cabal run -v0 gin -- prove "$source" --optimize "$policy" -o "$destination/proof"
cabal run -v0 gin -- pipeline "$source" --optimize "$policy" --max-depth 1 \
  --vectors "$vectors" -o "$destination/pipeline"
cabal run -v0 gin -- memory examples/memorymap/memorymap.gin.json --optimize "$policy" \
  --words examples/memory-words.json --traffic examples/memory-traffic.json \
  --lanes 1 --lanes 2 --lanes 4 -o "$destination/memory"
printf 'Portfolio written to %s/portfolio.json\n' "$destination"
