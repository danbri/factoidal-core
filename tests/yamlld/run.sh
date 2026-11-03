#!/usr/bin/env bash
#
# tests/yamlld/run.sh — YAML-LD 1.0 (JSON-LD WG Editor's Draft) in Lean over the
# vendored suite third_party/testing/yaml-ld (provenance:
# third_party/testing/yaml-ld-PROVENANCE.md; https://github.com/danbri/factoidal/issues/1165).
#
#   1. The manifest: "N pass, M fail (out of T); K excluded (defective test
#      data)". A STALE exclusion (the case passes) fails the run.
#   2. Scale: mappings, sequences and scalars of 100,000 to 400,000 entries load
#      under a 1 MB stack (the loops are tail calls).
#   3. JSON superset: every .jsonld input of the JSON-LD 1.1 suite loads through
#      the YAML 1.2.2 loader as the value the JSON parser gives.
#
# Builds l4yamlld in formal/lean4; exits 0 only when every step passes.
set -euo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
LEAN="$ROOT/formal/lean4"
(cd "$LEAN" && timeout 1800 lake build l4yamlld >/dev/null)
BIN="$LEAN/.lake/build/bin/l4yamlld"
cd "$ROOT"
timeout 600 "$BIN" third_party/testing/yaml-ld/tests
(ulimit -s 1024; timeout 600 "$BIN" --scale 100000)
if [ -d third_party/testing/json-ld/tests ]; then
  timeout 600 "$BIN" --json-superset third_party/testing/json-ld/tests
else
  echo "yamlld: third_party/testing/json-ld/tests is absent; run tools/ensure-test-env.sh" >&2
  exit 2
fi
