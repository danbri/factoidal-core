#!/usr/bin/env bash
# tools/jsonld-chunk-differential.sh [DIR...]
#
# The JSON-LD chunk fold of the source layer against the whole-document reader
# (https://github.com/danbri/factoidal/issues/839; the theorem that would make
# this run unnecessary is https://github.com/danbri/factoidal/issues/946, row
# JS-1 of tests/known-defects/run.sh). Every .jsonld file under DIR (default:
# third_party/testing/json-ld and tests/sbm11/syntax) goes to `l4jsonld-chunk-diff`
# (formal/lean4/Harness/JsonLdChunkDiff.lean), which reads it, and three wrappings
# of it (an array; an @graph object; an @graph object with the file twice), with
# two bases and chunks of 1, 7, 64 and 65,536 characters.
#
# Exit 0 when every case agrees, 1 when one differs, 2 on a setup error.
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="${L4_JSONLD_CHUNK_DIFF:-$ROOT/formal/lean4/.lake/build/bin/l4jsonld-chunk-diff}"
[ -x "$BIN" ] || { echo "not built: $BIN (cd formal/lean4 && lake build l4jsonld-chunk-diff)" >&2; exit 2; }
if [ "$#" -eq 0 ]; then
  set -- "$ROOT/third_party/testing/json-ld" "$ROOT/tests/sbm11/syntax"
fi
LIST="$(mktemp)"
trap 'rm -f "$LIST"' EXIT
for d in "$@"; do
  find -L "$d" \( -name '*.jsonld' \) -type f -print
done | sort > "$LIST"
n=$(wc -l < "$LIST")
[ "$n" -gt 0 ] || { echo "no JSON-LD file under: $*" >&2; exit 2; }
RC=0
xargs -d '\n' -a "$LIST" "$BIN" || RC=$?
# xargs exits 123 when one invocation exits 1..125.
case "$RC" in
  0) exit 0 ;;
  1|123) exit 1 ;;
  *) exit 2 ;;
esac
