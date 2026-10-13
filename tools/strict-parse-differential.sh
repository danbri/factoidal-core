#!/usr/bin/env bash
# tools/strict-parse-differential.sh OLD NEW [DIR...]
#
# Differential check of the strict `l4factoidal parse` between two binaries
# (https://github.com/danbri/factoidal/issues/813): every .nt, .nq and .ttl
# file under DIR (default: the W3C RDF 1.1 and 1.2 suites, RDF/XML excluded)
# is parsed by OLD and NEW, as `parse FILE --format F --out nquads` and as
# `parse FILE --format F` (the count), each with and without `--base`, in the
# RDF 1.1 mode and (files of the RDF 1.2 suites) in the RDF 1.2 mode.
#
# A case agrees when the exit status and the standard error are the same and,
# when OLD exits 0, the standard output is the same byte for byte. When OLD
# exits non-zero, NEW's standard output may hold the lines it wrote before
# the error (the streamed parse writes each chunk before it reads the next)
# and is not compared.
#
# Prints one DIFF line per disagreement and a summary; exit 0 when every case
# agrees, 1 otherwise, 2 on a setup error.
set -uo pipefail
OLD="${1:?usage: strict-parse-differential.sh OLD NEW [DIR...]}"
NEW="${2:?usage: strict-parse-differential.sh OLD NEW [DIR...]}"
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
cases=0; agree=0; differ=0; ok_cases=0; err_cases=0
run_case() { # file format out(nquads|count) base
  local f="$1" fmt="$2" out="$3" base="$4"
  local args=(parse "$f" --format "$fmt")
  [ "$out" = nquads ] && args+=(--out nquads)
  [ -n "$base" ] && args+=(--base "$base")
  local orc=0 nrc=0
  timeout 60 "$OLD" "${args[@]}" > "$TMP/o.out" 2> "$TMP/o.err" || orc=$?
  timeout 60 "$NEW" "${args[@]}" > "$TMP/n.out" 2> "$TMP/n.err" || nrc=$?
  cases=$((cases + 1))
  local why=""
  [ "$orc" = "$nrc" ] || why="exit $orc vs $nrc"
  cmp -s "$TMP/o.err" "$TMP/n.err" || why="$why stderr"
  if [ "$orc" = 0 ]; then
    ok_cases=$((ok_cases + 1))
    cmp -s "$TMP/o.out" "$TMP/n.out" || why="$why stdout"
  else
    err_cases=$((err_cases + 1))
  fi
  if [ -z "$why" ]; then agree=$((agree + 1)); else
    differ=$((differ + 1)); echo "DIFF ($why): ${args[*]}"
  fi
}
while IFS= read -r f; do
  case "$f" in
    */rdf-xml/*) continue ;;
    *.nt) fmts="ntriples" ;;
    *.nq) fmts="nquads" ;;
    *.ttl) fmts="turtle" ;;
    *) continue ;;
  esac
  case "$f" in
    */rdf12/*) case "$fmts" in
        ntriples) fmts="ntriples ntriples12" ;;
        nquads) fmts="nquads nquads12" ;;
        turtle) fmts="turtle turtle12" ;;
      esac ;;
  esac
  for fmt in $fmts; do
    for out in nquads count; do
      run_case "$f" "$fmt" "$out" ""
      run_case "$f" "$fmt" "$out" "http://example.org/base/dir/doc"
    done
  done
done < <(find -L "$@" -type f \( -name '*.nt' -o -name '*.nq' -o -name '*.ttl' \) | sort)
echo "strict-parse-differential: $agree agree, $differ differ (out of $cases cases; old exit 0 in $ok_cases, non-zero in $err_cases)"
[ "$differ" -eq 0 ]
