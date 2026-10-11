#!/usr/bin/env bash
#
# tests/qlvr/run.sh — `l4qlvr` (the Lean QLever reader) against the QLever
# instance and its query oracle. https://github.com/danbri/factoidal/issues/778
#
#   (a) scans   every oracle query that is one triple pattern with a bound
#               predicate (`SELECT ?s ?o WHERE { ?s <p> ?o }`, with an
#               optional ORDER BY): `l4qlvr scan` rows against the oracle
#               .srj, as multisets of RDF terms, numbers compared by value
#               (tests/qlvr/compare_scan.py).
#   (b) dump    `l4qlvr dump` as a set of lines against the input N-Triples:
#               lines equal byte for byte; lines equal after QLever's
#               documented normalisations (tests/qlvr/canon_nt.py); lines
#               different. Passes when no line is different.
#   (c) words   `l4qlvr words` against `tools/qlvr/probe_index.py --words`
#               (every vocabulary word, sha256 of the whole listing).
#   (d) stats   `l4qlvr stats` runs and every permutation's block rows add up
#               to its triple count (the command fails otherwise).
#   (e) construct  when a QLever server answers on port 7019: the dump as a
#               set of lines equals QLever's own
#               `CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }` in N-Triples.
#               Not scored when no server answers.
#   (f) side    `l4qlvr side-index` rebuilds INDEXDIR.qlvr-side/, then
#               `l4qlvr side-check` compares the side index with the linear
#               scan on every distinct stored-form constant of the 21 queries
#               (`l4qlvr query --constants`), 1,000 sampled words and 100
#               absent words.
#   (g) queries tests/qlvr/queries.sh: every oracle query through
#               `l4qlvr query` against QLever's answer; prints
#               "N pass, M fail, R refused (out of 21)". Scored as one check.
#   (h) refusals queries outside the fragment of L4Factoidal.Qlvr.Query
#               (OPTIONAL, UNION, BIND, an ORDER BY expression, COUNT DISTINCT,
#               REGEX, CONSTRUCT, a date constant) must exit 3 with
#               "refused:" and print no answer.
#
# The stack canary case for the dump is in tests/stack/run.sh (qlvr-dump).
#
# Needs: formal/lean4/.lake/build/bin/l4qlvr (lake build l4qlvr, in
# formal/lean4), the instance and oracle in QLVR_WORK (default
# /home/user/qlvr-work; tools/qlvr/build-instance.sh), python3 with the
# zstandard package (for (c)). Prints "N pass, M fail (out of T)" per part
# and in total; exits 0 only when every scored check passes, 2 when an input
# is missing.
set -uo pipefail
export LC_ALL=C

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="$ROOT/formal/lean4/.lake/build/bin/l4qlvr"
WORK="${QLVR_WORK:-/home/user/qlvr-work}"
INST="$WORK/instance"
ORACLE="$WORK/oracle"
INPUT="$INST/olympics.nt"
PORT="${QLVR_PORT:-7019}"

for need in "$BIN" "$INST/olympics.index.spo" "$INPUT" "$ORACLE"; do
  if [ ! -e "$need" ]; then echo "missing: $need" >&2; exit 2; fi
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/qlvr-test.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT

PASS=0; FAIL=0
record() { # record <part> <name> <ok:0|1> <detail>
  if [ "$3" = 0 ]; then PASS=$((PASS + 1)); printf 'ok   %-10s %-40s %s\n' "$1" "$2" "$4"
  else FAIL=$((FAIL + 1)); printf 'FAIL %-10s %-40s %s\n' "$1" "$2" "$4"; fi
}
peak() { grep -o 'VmHWM): [0-9]* kB' "$1" | head -1 | sed 's/VmHWM): //'; }

# ------------------------------------------------------------------ (a) scans
echo "=== (a) bound-predicate scans against the oracle"
python3 -I - "$ROOT/tests/qlvr/queries" >"$TMP/scans.tsv" <<'PY'
import os, re, sys
d = sys.argv[1]
pat = re.compile(r"^\s*SELECT\s+\?(\w+)\s+\?(\w+)\s+WHERE\s*\{\s*\?(\w+)\s+(\S+)\s+\?(\w+)\s*\.?\s*\}\s*(ORDER BY\s+\?\w+\s*)?$", re.I)
for n in sorted(os.listdir(d)):
    if not n.endswith(".rq"):
        continue
    text = open(os.path.join(d, n)).read()
    prefixes = dict(re.findall(r"^PREFIX\s+(\w*):\s*<([^>]*)>", text, re.M))
    body = "\n".join(l for l in text.splitlines()
                     if l.strip() and not l.startswith("#") and not l.upper().startswith("PREFIX"))
    m = pat.match(body.replace("\n", " "))
    if not m or {m.group(1), m.group(2)} != {m.group(3), m.group(5)}:
        continue
    p = m.group(4)
    if p.startswith("<"):
        iri = p[1:-1]
    elif ":" in p and p.split(":", 1)[0] in prefixes:
        iri = prefixes[p.split(":", 1)[0]] + p.split(":", 1)[1]
    else:
        continue
    print("\t".join([n[:-3], iri, m.group(3), m.group(5)]))
PY
SP=0; SF=0
while IFS=$'\t' read -r name iri svar ovar; do
  srj="$ORACLE/$name.srj"
  if [ ! -f "$srj" ]; then record scan "$name" 1 "no oracle answer $srj"; SF=$((SF + 1)); continue; fi
  "$BIN" scan "$INST" "$iri" >"$TMP/$name.nt" 2>"$TMP/$name.err"; rc=$?
  if [ "$rc" -ne 0 ]; then
    record scan "$name" 1 "exit $rc: $(tail -1 "$TMP/$name.err")"; SF=$((SF + 1)); continue
  fi
  if res="$(python3 -I "$HERE/compare_scan.py" "$srj" "$TMP/$name.nt" "$svar" "$ovar")"; then
    record scan "$name" 0 "$res; $(sed -e 's/.*: VocabIndex/VocabIndex/' "$TMP/$name.err")"; SP=$((SP + 1))
  else
    record scan "$name" 1 "$res"; SF=$((SF + 1))
  fi
done <"$TMP/scans.tsv"
echo "qlvr scans: $SP pass, $SF fail (out of $((SP + SF)))"

# ------------------------------------------------------------------- (b) dump
echo
echo "=== (b) l4qlvr dump against the input N-Triples"
t0=$(date +%s%N)
"$BIN" dump "$INST" >"$TMP/dump.nt" 2>"$TMP/dump.err"; rc=$?
t1=$(date +%s%N)
cat "$TMP/dump.err"
if [ "$rc" -ne 0 ]; then
  record dump dump 1 "exit $rc"
else
  sort "$INPUT" >"$TMP/in.sorted"
  sort "$TMP/dump.nt" >"$TMP/dump.sorted"
  n_in=$(wc -l <"$TMP/in.sorted"); n_dump=$(wc -l <"$TMP/dump.sorted")
  n_in_u=$(uniq "$TMP/in.sorted" | wc -l)
  equal=$(comm -12 "$TMP/in.sorted" "$TMP/dump.sorted" | wc -l)
  comm -23 "$TMP/in.sorted" "$TMP/dump.sorted" >"$TMP/in.only"
  comm -13 "$TMP/in.sorted" "$TMP/dump.sorted" >"$TMP/dump.only"
  rm -f "$TMP/in.sorted" "$TMP/dump.sorted"
  python3 -I "$HERE/canon_nt.py" --side input <"$TMP/in.only" | sort >"$TMP/in.canon"
  python3 -I "$HERE/canon_nt.py" --side dump <"$TMP/dump.only" | sort >"$TMP/dump.canon"
  normalised=$(comm -12 "$TMP/in.canon" "$TMP/dump.canon" | wc -l)
  comm -23 "$TMP/in.canon" "$TMP/dump.canon" >"$TMP/in.diff"
  comm -13 "$TMP/in.canon" "$TMP/dump.canon" >"$TMP/dump.diff"
  d_in=$(wc -l <"$TMP/in.diff"); d_dump=$(wc -l <"$TMP/dump.diff")
  echo "input lines $n_in ($n_in_u distinct); dump lines $n_dump"
  echo "equal byte for byte: $equal; equal after normalisation: $normalised; different: $d_in input-only, $d_dump dump-only"
  echo "normalisation classes of the input-only lines (canon_nt.py --classes):"
  python3 -I "$HERE/canon_nt.py" --side input --classes <"$TMP/in.only" | sed 's/^/  /'
  if [ "$d_in" -ne 0 ] || [ "$d_dump" -ne 0 ]; then
    echo "first differences:"; head -5 "$TMP/in.diff" | sed 's/^/  input: /'; head -5 "$TMP/dump.diff" | sed 's/^/  dump:  /'
  fi
  ok=1
  [ "$d_in" -eq 0 ] && [ "$d_dump" -eq 0 ] && [ "$n_dump" -eq "$n_in_u" ] && ok=0
  record dump dump "$ok" "equal $equal, normalised $normalised, different $((d_in + d_dump)); $(( (t1 - t0) / 1000000 )) ms, peak RSS $(peak "$TMP/dump.err")"
fi

# ------------------------------------------------------------------ (c) words
echo
echo "=== (c) every vocabulary word against the Python probe"
"$BIN" words "$INST" >"$TMP/words.lean" 2>"$TMP/words.err"; rc=$?
if [ "$rc" -ne 0 ]; then
  record words words 1 "exit $rc: $(tail -1 "$TMP/words.err")"
elif ! python3 -I "$ROOT/tools/qlvr/probe_index.py" "$INST" olympics --words "$TMP/words.py" >/dev/null 2>"$TMP/words.pyerr"; then
  record words words 1 "probe failed (needs the zstandard package): $(tail -1 "$TMP/words.pyerr")"
else
  a=$(sha256sum <"$TMP/words.lean" | cut -c1-64); b=$(sha256sum <"$TMP/words.py" | cut -c1-64)
  n=$(wc -l <"$TMP/words.lean")
  if [ "$a" = "$b" ]; then record words words 0 "$n words, sha256 $a; $(tail -1 "$TMP/words.err")"
  else record words words 1 "sha256 lean $a, probe $b"; fi
fi

# ------------------------------------------------------------------ (d) stats
echo
echo "=== (d) stats"
if "$BIN" stats "$INST" >"$TMP/stats.out" 2>"$TMP/stats.err"; then
  cat "$TMP/stats.out"
  record stats stats 0 "$(cat "$TMP/stats.err")"
else
  record stats stats 1 "$(tail -1 "$TMP/stats.err")"
fi

# ------------------------------------------------------------------- (f) side
echo
echo "=== (f) side index against the linear scan"
"$BIN" side-index "$INST" 2>"$TMP/side.err"; rc=$?
cat "$TMP/side.err"
if [ "$rc" -ne 0 ]; then
  record side side-index 1 "exit $rc"
else
  : >"$TMP/constants"
  for rq in "$ROOT"/tests/qlvr/queries/q*.rq; do
    "$BIN" query "$INST" --file "$rq" --constants >>"$TMP/constants" 2>/dev/null
  done
  mapfile -t CONSTS < <(sort -u "$TMP/constants")
  "$BIN" side-check "$INST" "${CONSTS[@]}" >"$TMP/sidecheck.out" 2>"$TMP/sidecheck.err"; rc=$?
  cat "$TMP/sidecheck.out" "$TMP/sidecheck.err"
  record side side-check "$([ "$rc" = 0 ] && echo 0 || echo 1)" "$(grep '^side-check:' "$TMP/sidecheck.out")"
fi

# ---------------------------------------------------------------- (g) queries
echo
echo "=== (g) oracle queries through l4qlvr query"
"$HERE/queries.sh" | tee "$TMP/queries.out"; rc=${PIPESTATUS[0]}
record queries queries "$([ "$rc" = 0 ] && echo 0 || echo 1)" "$(tail -1 "$TMP/queries.out")"

# --------------------------------------------------------------- (h) refusals
echo
echo "=== (h) queries outside the fragment are refused"
P='PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#> PREFIX xsd: <http://www.w3.org/2001/XMLSchema#> '
while IFS='|' read -r rname rtext; do
  "$BIN" query "$INST" "$P$rtext" >"$TMP/ref.out" 2>"$TMP/ref.err"; rc=$?
  if [ "$rc" -eq 3 ] && grep -q 'refused:' "$TMP/ref.err" && [ ! -s "$TMP/ref.out" ]; then
    record refuse "$rname" 0 "$(grep -o 'refused: .*' "$TMP/ref.err")"
  else
    record refuse "$rname" 1 "exit $rc: $(tail -1 "$TMP/ref.err")"
  fi
done <<'EOF'
optional|SELECT ?s ?l WHERE { ?s ?p ?o OPTIONAL { ?s rdfs:label ?l } }
union|SELECT ?s WHERE { { ?s rdfs:label ?o } UNION { ?s rdfs:comment ?o } }
bind|SELECT ?s ?x WHERE { ?s rdfs:label ?o BIND(STR(?o) AS ?x) }
order-expression|SELECT ?s WHERE { ?s rdfs:label ?o } ORDER BY STRLEN(?o)
count-distinct|SELECT (COUNT(DISTINCT ?s) AS ?n) WHERE { ?s rdfs:label ?o }
regex|SELECT ?s WHERE { ?s rdfs:label ?o FILTER(REGEX(?o, "^Her")) }
construct|CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }
date-constant|SELECT ?s WHERE { ?s ?p "2020-01-01"^^xsd:date }
EOF

# -------------------------------------------------------------- (e) construct
echo
echo "=== (e) dump against QLever's CONSTRUCT { ?s ?p ?o } (server on port $PORT)"
if [ -f "$TMP/dump.nt" ] && curl -sf "localhost:$PORT" --data-urlencode 'query=ASK {}' >/dev/null 2>&1; then
  t0=$(date +%s%N)
  curl -sf "localhost:$PORT" -H 'Accept: application/n-triples' \
    --data-urlencode 'query=CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }' -o "$TMP/construct.nt"; rc=$?
  t1=$(date +%s%N)
  if [ "$rc" -ne 0 ]; then
    record construct construct 1 "curl exit $rc"
  else
    sort "$TMP/construct.nt" >"$TMP/c.sorted"; sort "$TMP/dump.nt" >"$TMP/d.sorted"
    eq=$(comm -12 "$TMP/c.sorted" "$TMP/d.sorted" | wc -l)
    co=$(comm -23 "$TMP/c.sorted" "$TMP/d.sorted" | wc -l)
    do_=$(comm -13 "$TMP/c.sorted" "$TMP/d.sorted" | wc -l)
    ok=1; [ "$co" -eq 0 ] && [ "$do_" -eq 0 ] && ok=0
    record construct construct "$ok" "equal $eq, construct-only $co, dump-only $do_; QLever CONSTRUCT over HTTP $(( (t1 - t0) / 1000000 )) ms"
  fi
else
  echo "not run (not scored): no dump output or no server on port $PORT"
fi

echo
echo "qlvr: $PASS pass, $FAIL fail (out of $((PASS + FAIL)))"
[ "$FAIL" -eq 0 ]
