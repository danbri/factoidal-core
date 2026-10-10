#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
bin="$lean_dir/.lake/build/bin"
run_dir=$(mktemp -d "${TMPDIR:-/tmp}/factoidal-ibk3-direct-select.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT
failures=0

"$bin/l4block-shard-pack" "$lean_dir/Harness/TestData/direct-select-order.ttl" \
  "$run_dir/first" ibk3 >/dev/null
"$bin/l4block-shard-activate" "$run_dir" first >/dev/null

two_pattern='?person <urn:kind> <urn:Person> . ?person <urn:name> ?name .'
three_pattern='?person <urn:kind> ?kind . ?person <urn:name> ?name . ?person <urn:team> ?team .'

check_pair() {
  local label=$1 projection=$2 pattern=$3 modifier=$4 expected_mode=$5
  local actual reference actual_rows reference_rows
  actual=$("$bin/l4block-id-v3-query" "$run_dir" --query \
    "$projection WHERE { $pattern } $modifier")
  reference=$("$bin/l4block-id-v3-query" "$run_dir" --query \
    "$projection WHERE { $pattern FILTER(true) } $modifier")
  printf 'case=%s\n%s\n%s\n' "$label" "$actual" "$reference"
  actual_rows=$(sed -n '/^l4block-id-v3-query rows=/,$p' <<<"$actual")
  reference_rows=$(sed -n '/^l4block-id-v3-query rows=/,$p' <<<"$reference")
  if [[ "$actual_rows" != "$reference_rows" ]]; then
    printf 'direct SELECT changed reference rows: %s\n' "$label" >&2
    failures=$((failures + 1))
  fi
  if ! grep -Fq "open-mode=$expected_mode" <<<"$actual"; then
    printf 'unexpected direct SELECT admission: %s\n' "$label" >&2
    failures=$((failures + 1))
  fi
}

check_pair two-limit 'SELECT ?person ?name' "$two_pattern" 'LIMIT 1' \
  'ibk3-sri2-tli1-oli2-object-subject-join(2)'
check_pair two-offset 'SELECT ?person ?name' "$two_pattern" 'OFFSET 1 LIMIT 1' \
  'ibk3-sri2-tli1-oli2-object-subject-join(2)'
check_pair two-sample 'SELECT (SAMPLE(?name) AS ?sample)' "$two_pattern" '' \
  'ibk3-sri2-tli1-oli2-object-subject-join(2)'
check_pair two-group-concat 'SELECT (GROUP_CONCAT(?name; SEPARATOR=",") AS ?names)' \
  "$two_pattern" '' 'ibk3-sri2-tli1-oli2-object-subject-join(2)'
check_pair three-sample 'SELECT (SAMPLE(?name) AS ?sample)' "$three_pattern" '' \
  'ibk3-sri2-tli1-subject-triple-join(3)'
check_pair three-group-concat 'SELECT (GROUP_CONCAT(?name; SEPARATOR=",") AS ?names)' \
  "$three_pattern" '' 'ibk3-sri2-tli1-subject-triple-join(3)'
check_pair two-distinct-asc 'SELECT DISTINCT ?person' "$two_pattern" \
  'ORDER BY ?person LIMIT 2' \
  'ibk3-sri2-tli1-oli2-object-subject-direct-select-distinct-subject(2)'
check_pair two-distinct-desc 'SELECT DISTINCT ?person' "$two_pattern" \
  'ORDER BY DESC(?person) LIMIT 2' \
  'ibk3-sri2-tli1-oli2-object-subject-direct-select-distinct-subject(2)'

two_plain=$("$bin/l4block-id-v3-query" "$run_dir" --query \
  "SELECT ?person ?name WHERE { $two_pattern }")
three_plain=$("$bin/l4block-id-v3-query" "$run_dir" --query \
  "SELECT ?person ?name ?team WHERE { $three_pattern }")
printf '%s\n%s\n' "$two_plain" "$three_plain"
grep -Fq 'open-mode=ibk3-sri2-tli1-oli2-object-subject-direct-select(2)' <<<"$two_plain"
grep -Fq 'open-mode=ibk3-sri2-tli1-subject-triple-direct-select(3)' <<<"$three_plain"
grep -q 'rows=4 ' <<<"$two_plain"
grep -q 'rows=4 ' <<<"$three_plain"

if [[ "$failures" != 0 ]]; then
  printf 'blockengine-ibk3-direct-select-smoke=fail failures=%s\n' "$failures" >&2
  exit 1
fi
echo 'blockengine-ibk3-direct-select-smoke=pass'
