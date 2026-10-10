#!/usr/bin/env bash
#
# tests/stack/lean_scaling.sh -- the Lean command line scales as n log n on the
# paths that the 2026-10-10 survey found quadratic and that were repaired:
# RDFS closure, TriG parsing, Turtle serialisation, RDFC-1.0 canonicalisation,
# SPARQL GROUP BY, and the process start-up budget.
#
# Runs tests/stack/lean_scaling.py from the repository root against
# formal/lean4/.lake/build/bin/l4factoidal (override with L4_BIN). For each row
# it checks that time(4x) stays under 9.0 times max(time(x), 50 ms). Rows in
# the XFAIL table of lean_scaling.py are known costs with an open issue: they
# count as expected-fail while they fail and as a failure when they pass. Exit
# status: 0 when every row passes or fails as expected, 1 when a row fails or
# an expected failure passes, 2 when the binary is missing, 124 when the run
# exceeds the time cap.
#
# Usage:  tests/stack/lean_scaling.sh [--runs N] [--only ROW[,ROW...]]
# Env:    LEAN_SCALING_TIMEOUT   seconds for the whole run (default 900)
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
cd "$ROOT" || exit 2
RC=0
timeout "${LEAN_SCALING_TIMEOUT:-900}" python3 "$HERE/lean_scaling.py" "$@" || RC=$?
exit "$RC"
