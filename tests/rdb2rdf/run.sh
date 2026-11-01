#!/usr/bin/env bash
#
# tests/rdb2rdf/run.sh — the W3C RDB2RDF test cases (R2RML and Direct Mapping
# Test Cases, 2012; third_party/testing/rdb2rdf-tests) against the Lean SQL
# subset (L4Factoidal/SQL/) and the Lean Direct Mapping
# (L4Factoidal/RDB2RDF/DirectMapping.lean). Design record:
# docs/designissues/2026-11-01-r2rml-and-direct-mapping.md.
# Tracking: https://github.com/danbri/factoidal/issues/1165.
#
# Builds l4rdb2rdf in formal/lean4. Prints "N pass, M fail (out of T)"; exits 0
# only when every Direct Mapping case passes. The R2RML cases are counted and
# not run until RDB2RDF/R2RML.lean lands.
set -euo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
LEAN="$ROOT/formal/lean4"
(cd "$LEAN" && timeout 1800 lake build l4rdb2rdf >/dev/null)
timeout 600 "$LEAN/.lake/build/bin/l4rdb2rdf" "$ROOT/third_party/testing/rdb2rdf-tests"
