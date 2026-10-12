#!/usr/bin/env bash
#
# tests/stack/owl_real_gate.sh -- OWL reasoning on real ontologies finishes
# under the caps of tools/owl-real-bench.py (600 s wall clock, 6,000,000,000
# bytes of address space per step), with the stated result.
#
# Runs tests/stack/owl_real_gate.py from the repository root against
# formal/lean4/.lake/build/bin/l4factoidal (override the directory with
# L4_BIN_DIR). Rows in its XFAIL table are known shortfalls with an open issue:
# expected-fail while they fail, a failure when they pass. Record:
# docs/designissues/2026-10-10-owl-real-ontologies.md
# (https://github.com/danbri/factoidal/issues/651, plan item 4).
#
# Exit status: 0 when every row passes or fails as expected, 1 when a row
# fails or an expected failure passes, 2 when the binary is missing, 124 when
# the whole run exceeds OWL_REAL_GATE_TIMEOUT seconds (default 3600).
#
# Usage:  tests/stack/owl_real_gate.sh [--only ROW[,ROW...]] [--cap-s S]
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
cd "$ROOT" || exit 2
RC=0
timeout "${OWL_REAL_GATE_TIMEOUT:-3600}" python3 "$HERE/owl_real_gate.py" "$@" || RC=$?
exit "$RC"
