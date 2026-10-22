#!/usr/bin/env bash
# tools/rdfxml-chunk-differential.sh [DIR...]
#
# The RDF/XML chunk fold of the source layer against the whole-document reader
# (https://github.com/danbri/factoidal/issues/838; the theorem that would make
# this run unnecessary is https://github.com/danbri/factoidal/issues/936, row
# RX-1 of tests/known-defects/run.sh). Every .rdf, .owl and .rdfxml file under
# DIR (default: third_party/testing without the XML conformance suite, and
# third_party/ontologies) goes to `l4rdfxml-chunk-diff`
# (formal/lean4/Harness/RdfXmlChunkDiff.lean), which reads it with two bases and
# chunks of 1, 7, 64 and 65,536 characters.
#
# Exit 0 when every case agrees, 1 when one differs, 2 on a setup error.
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="${L4_RDFXML_CHUNK_DIFF:-$ROOT/formal/lean4/.lake/build/bin/l4rdfxml-chunk-diff}"
[ -x "$BIN" ] || { echo "not built: $BIN (cd formal/lean4 && lake build l4rdfxml-chunk-diff)" >&2; exit 2; }
if [ "$#" -eq 0 ]; then
  set -- "$ROOT/third_party/testing" "$ROOT/third_party/ontologies"
fi
LIST="$(mktemp)"
trap 'rm -f "$LIST"' EXIT
for d in "$@"; do
  find -L "$d" -path '*/third_party/testing/xml' -prune -o \
    \( -name '*.rdf' -o -name '*.owl' -o -name '*.rdfxml' \) -type f -print
done | sort > "$LIST"
n=$(wc -l < "$LIST")
[ "$n" -gt 0 ] || { echo "no RDF/XML file under: $*" >&2; exit 2; }
RC=0
xargs -d '\n' -a "$LIST" "$BIN" || RC=$?
# xargs exits 123 when one invocation exits 1..125.
case "$RC" in
  0) exit 0 ;;
  1|123) exit 1 ;;
  *) exit 2 ;;
esac
