#!/usr/bin/env bash
#
# tests/sbm11/host_compare.sh GEN [QUERY_DIR] — the exit check of KR1 of
# https://github.com/danbri/factoidal/issues/1009: every query of QUERY_DIR
# (default tests/qlvr/queries, the olympics oracle queries) answered on the
# SBM11 generation GEN (a generation directory or a collection root) by
#   1. native `l4sbm11 query GEN --threads 1`, and
#   2. the wasm ops sbm11Open / sbm11Query / sbm11Close through
#      `l4factoidal sbm11-query GEN` (host positioned reads, ffi/l4_hostread.c).
# The two answers must have the same bytes and the same path (ids or
# reference). Prints one line per query with both times, then the totals.
# Exit 0 when every query gives the same bytes and path; 1 otherwise.
#
# Run after `lake build` in formal/lean4. The census of the W3C suites is
# `SBM11_HOST=1 tests/sbm11/census.sh`.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="$ROOT/formal/lean4/.lake/build/bin"
GEN="${1:?usage: host_compare.sh GEN [QUERY_DIR]}"
QDIR="${2:-$ROOT/tests/qlvr/queries}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

ms() { echo $(( ($2 - $1) / 1000000 )); }

same=0; differ=0; n=0
for rq in "$QDIR"/*.rq; do
  name="$(basename "$rq" .rq)"
  n=$((n + 1))
  t0=$(date +%s%N)
  arc=0; timeout 600 "$BIN/l4sbm11" query "$GEN" --file "$rq" --threads 1 >"$TMP/a" 2>"$TMP/a.err" || arc=$?
  t1=$(date +%s%N)
  hrc=0; timeout 600 "$BIN/l4factoidal" sbm11-query "$GEN" --query "$rq" >"$TMP/h" 2>"$TMP/h.err" || hrc=$?
  t2=$(date +%s%N)
  apath=ids; grep -q 'path=reference' "$TMP/a.err" && apath=reference
  hpath=ids; grep -q 'path=reference' "$TMP/h.err" && hpath=reference
  if [ "$arc" -eq 0 ] && [ "$hrc" -eq 0 ] && [ "$apath" = "$hpath" ] && cmp -s "$TMP/a" "$TMP/h"; then
    same=$((same + 1)); verdict=same
  else
    differ=$((differ + 1)); verdict="DIFFER (exit $arc/$hrc, path $apath/$hpath, $(cmp -s "$TMP/a" "$TMP/h" && echo 'same bytes' || echo 'bytes differ'); $(tail -1 "$TMP/h.err" | head -c 160))"
  fi
  printf '%-40s %-9s native %6s ms  host %6s ms  %s\n' "$name" "$apath" "$(ms "$t0" "$t1")" "$(ms "$t1" "$t2")" "$verdict"
done
echo "host_compare: $same same, $differ differ (out of $n queries) on $GEN"
[ "$differ" -eq 0 ]
