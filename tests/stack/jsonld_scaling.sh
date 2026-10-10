#!/usr/bin/env bash
#
# tests/stack/jsonld_scaling.sh -- JSON-LD node map generation, flattening
# and framing scale as n log n in the number of nodes.
#
# Runs `l4jsonld-api --scale` (Harness/JsonLdScale.lean) from the repository
# root. The harness builds five document shapes (one shared hub, one node
# with many references, a blank node chain, many named graphs, one node
# with many properties) at n, 2n, 4n, 8n and 16n, prints the wall time of
# each phase, and checks for the phases node map, flatten and frame core
# that time(4x) stays under 9.0 times max(time(x), 20 ms):
#
#   O(n^2)      predicts time(4x)/time(x) ~= 16
#   O(n log n)  predicts time(4x)/time(x) ~= 4.5
#
# Exit status is the harness's: 0 when every size pair passes, 1 when a pair
# fails (the failing shape, phase and sizes are printed), 124 when the run
# exceeds the time cap. Scores are printed as "N pass, M fail (out of T)".
#
# Usage:  tests/stack/jsonld_scaling.sh [base-n [runs-per-point]]
#         defaults: base-n 250 (sizes 250 to 4000), 3 runs per point.
# Env:    JSONLD_SCALING_TIMEOUT   seconds for the whole run (default 600)
#
# Timing is wall-clock. On a host with other heavy processes, raise the
# runs per point (the minimum of the runs is kept) before reading a failure
# as a regression.
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="$ROOT/formal/lean4/.lake/build/bin/l4jsonld-api"

if [ ! -x "$BIN" ]; then
  echo "tests/stack/jsonld_scaling.sh: $BIN not built (cd formal/lean4 && lake build l4jsonld-api)" >&2
  exit 2
fi

BASE="${1:-250}"
RUNS="${2:-3}"
CAP="${JSONLD_SCALING_TIMEOUT:-600}"

cd "$ROOT" || exit 2
RC=0
timeout "$CAP" "$BIN" --scale "$BASE" "$RUNS" || RC=$?
exit "$RC"
