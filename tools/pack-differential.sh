#!/usr/bin/env bash
# tools/pack-differential.sh OLD NEW [DIR...]
#
# Differential check of the shard packer `l4block-shard-pack` between two
# binaries, for a change that must not move a byte of any generation (the
# source layer, https://github.com/danbri/factoidal/issues/837). Every .ttl,
# .nt, .nq and .trig file under DIR (default: the W3C RDF 1.1 and 1.2 syntax
# suites, recursively) is packed by OLD and by NEW in each layout that reads it:
#
#   ibk3  .ttl and .nt files (the layout reads Turtle whatever the extension)
#   ibk4  every file
#   ibk5  every file
#
# and, for ibk4 and ibk5 on the files NEW reads in the buffered route, again
# with L4_PACK_BUFFERED=1 (the whole-source route, `PackStream.quadArtifacts`).
#
# A case agrees when the two exit statuses are equal and, when both are 0, the
# generation hashes are equal (the SHA-256 of the sorted per-file SHA-256
# list). When both refuse the input, the message may differ.
#
# Prints one DIFF line per disagreement and the labelled counts. Exit 0 when
# every case agrees, 1 otherwise, 2 on a setup error.
set -uo pipefail
OLD="${1:?usage: pack-differential.sh OLD NEW [DIR...]}"
NEW="${2:?usage: pack-differential.sh OLD NEW [DIR...]}"
shift 2
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
if [ "$#" -eq 0 ]; then
  set -- "$ROOT/third_party/testing/w3c/rdf/rdf11" "$ROOT/third_party/testing/w3c/rdf/rdf12"
fi
for b in "$OLD" "$NEW"; do
  [ -x "$b" ] || { echo "not executable: $b" >&2; exit 2; }
done
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
gen_hash() { (cd "$1" && find . -type f | sort | xargs sha256sum | sha256sum | cut -d' ' -f1); }
cases=0; agree=0; differ=0; both_ok=0; both_refuse=0
run_case() { # file layout buffered(0|1)
  local f="$1" layout="$2" buf="$3" orc=0 nrc=0 oh nh
  rm -rf "$TMP/o" "$TMP/n"
  if [ "$buf" = 1 ]; then
    L4_PACK_BUFFERED=1 timeout 120 "$OLD" "$f" "$TMP/o" "$layout" >/dev/null 2>&1 || orc=$?
    L4_PACK_BUFFERED=1 timeout 120 "$NEW" "$f" "$TMP/n" "$layout" >/dev/null 2>&1 || nrc=$?
  else
    timeout 120 "$OLD" "$f" "$TMP/o" "$layout" >/dev/null 2>&1 || orc=$?
    timeout 120 "$NEW" "$f" "$TMP/n" "$layout" >/dev/null 2>&1 || nrc=$?
  fi
  cases=$((cases + 1))
  if [ "$orc" != "$nrc" ]; then
    differ=$((differ + 1)); echo "DIFF status $layout buffered=$buf $f: old $orc, new $nrc"
  elif [ "$orc" = 0 ]; then
    oh="$(gen_hash "$TMP/o")"; nh="$(gen_hash "$TMP/n")"
    if [ "$oh" = "$nh" ]; then agree=$((agree + 1)); both_ok=$((both_ok + 1))
    else differ=$((differ + 1)); echo "DIFF hash $layout buffered=$buf $f"; fi
  else agree=$((agree + 1)); both_refuse=$((both_refuse + 1)); fi
}
while IFS= read -r f; do
  case "$f" in
    *.ttl|*.nt) run_case "$f" ibk3 0 ;;
  esac
  for layout in ibk4 ibk5; do
    run_case "$f" "$layout" 0
    run_case "$f" "$layout" 1
  done
done < <(find "$@" -type f \( -name '*.ttl' -o -name '*.nt' -o -name '*.nq' -o -name '*.trig' \) | sort)
echo "pack differential: $cases cases, $agree agree ($both_ok packed by both with the same generation hash, $both_refuse refused by both), $differ differ"
[ "$differ" -eq 0 ] && [ "$cases" -gt 0 ]
