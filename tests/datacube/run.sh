#!/usr/bin/env bash
#
# tests/datacube/run.sh — the RDF Data Cube (W3C Recommendation 2014-01-16)
# normalization algorithm and integrity constraints IC-0 to IC-21 in Lean
# (https://github.com/danbri/factoidal/issues/1165).
#
#   1. Drift: regenerate L4Factoidal/DataCube/Queries.lean from spec/ and local/
#      (tools/datacube-gen-queries.py) and fail when it differs from the file.
#   2. Schema: the vocabulary declarations that the theorem phase1_rdfs_sound
#      assumes are in the vendored vocabulary spec/cube.ttl.
#   3. Fixtures: every case of manifest.tsv; each case is normalized by the
#      SPARQL 1.1 Update texts and by the direct Lean functions (must agree), and
#      checked by the SPARQL queries and by the direct functions (must agree).
#
# Builds l4datacube in formal/lean4. Prints "N pass, M fail (out of T)"; exits 0
# only when every step passes.
set -euo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
LEAN="$ROOT/formal/lean4"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/datacube.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT

python3 "$ROOT/tools/datacube-gen-queries.py" "$TMP/Queries.lean"
if ! diff -u "$LEAN/L4Factoidal/DataCube/Queries.lean" "$TMP/Queries.lean"; then
  echo "datacube drift: L4Factoidal/DataCube/Queries.lean differs from tools/datacube-gen-queries.py output" >&2
  exit 1
fi
echo "datacube drift: Queries.lean matches the vendored texts"

(cd "$LEAN" && timeout 1800 lake build l4datacube >/dev/null)
BIN="$LEAN/.lake/build/bin/l4datacube"
timeout 300 "$BIN" --check-schema "$HERE/spec/cube.ttl"
timeout 600 "$BIN" "$HERE/manifest.tsv"
