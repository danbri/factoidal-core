#!/usr/bin/env bash
# RIF BLD 2013 on the Lean engine (formal/lean4/L4Factoidal/RIF/Bld.lean):
# the W3C RIF BLD suite (third_party/testing/rif-bld-suite), the corrected
# local copies (tests/rif-bld-local), and every W3C RIF Core entailment case
# through the BLD engine. `l4rif --bld` exits non-zero on a failure, a stale
# exclusion, a failing local case or a Core case that changes its verdict.
# Tracking: https://github.com/danbri/factoidal/issues/1165
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
LEAN="$ROOT/formal/lean4"
(cd "$LEAN" && timeout 1800 lake build l4rif >/dev/null)
cd "$ROOT"
timeout 600 "$LEAN/.lake/build/bin/l4rif" --bld
