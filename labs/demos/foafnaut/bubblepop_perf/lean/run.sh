#!/usr/bin/env bash
# Compile and run the two measurement programs of this directory with the pinned Lean.
# Usage: labs/demos/foafnaut/bubblepop_perf/lean/run.sh [ITERATIONS]   (default 3000000)
# They are single files with no import: `lean -c` writes C, `leanc -O3 -DNDEBUG` compiles it
# as Lake compiles the library. Output goes to a temporary directory.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../../.." && pwd)
N=${1:-3000000}
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
cd "$ROOT/formal/lean4"   # the directory with lean-toolchain, so elan picks the pinned version
for name in IntConversions VmFloor; do
  lean -R "$HERE" -c "$OUT/$name.c" "$HERE/$name.lean"
  leanc -O3 -DNDEBUG -o "$OUT/$name" "$OUT/$name.c"
  echo "== $name, $N iterations"
  "$OUT/$name" "$N"
done
