#!/usr/bin/env bash
# RIF PRD 2013 on the Lean engine (formal/lean4/L4Factoidal/RIF/Prd.lean):
# the 53 cases of the W3C RIF PRD manifest (third_party/testing/rif-prd-suite:
# 7 cases in PRD_v1.22, 46 shared with the W3C RIF Core suite) and the
# corrected local Core copies (tests/rif-local). `l4rif --prd` exits non-zero
# on a failure, a stale exclusion, a case it cannot read, or a shared Core
# entailment case whose PRD verdict differs from the Core verdict.
# Tracking: https://github.com/danbri/factoidal/issues/1165
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
LEAN="$ROOT/formal/lean4"
(cd "$LEAN" && timeout 1800 lake build l4rif >/dev/null)
cd "$ROOT"
timeout 600 "$LEAN/.lake/build/bin/l4rif" --prd
