#!/usr/bin/env bash
#
# tests/sbm11/update_where.sh -- SPARQL 1.1 Update with a WHERE clause, the graph
# management operations and fresh blank nodes on an SBM11 generation
# (https://github.com/danbri/factoidal/issues/849 and
# https://github.com/danbri/factoidal/issues/850). Record:
# docs/designissues/2026-10-12-sbm11-stage5.md section 10.
#
# The reference is the in-memory Lean engine: `l4factoidal update STATE --update REQ`
# gives the Graph Store after a request, and `l4factoidal query STATE` answers a query
# over it. The store is `l4sbm11 update`, which appends the whole request to the log
# as one batch. Two checks follow every request:
#
#   state    `l4sbm11 compact` folds the log into a new generation (it reads the
#            overlaid generation by the scans a query uses), `l4sbm11 dump` writes it,
#            and `l4sbm11-w3c compare` compares the dump with the reference state by
#            RDF dataset isomorphism (blank nodes up to a bijection; a named graph with
#            no triple is dropped on both sides: the store holds none);
#   queries  the queries of tests/sbm11/update/q on the overlay, on the path the name
#            says (ids-* on ids, ref-* on the reference fallback) and with --reference,
#            against `l4factoidal query` over the reference state (compare_answers.py:
#            a blank node equals any blank node).
#
# Groups:
#   steps        16 requests in order on the gate fixture (tests/sbm11/gate/gate.nq):
#                DELETE WHERE, DELETE/INSERT with a FILTER, WITH, USING, USING NAMED,
#                template blank nodes, INSERT DATA blank nodes, operations that read the
#                state the one before left, OPTIONAL and MINUS, a property path, COPY, ADD,
#                MOVE, CLEAR, DROP, CREATE, LOAD SILENT, template triples that are dropped,
#                GRAPH in WHERE and templates, VALUES and BIND, a WHERE clause with no
#                solution and an empty one.
#   destructive  23 requests, each on a fresh generation: the graph-wide forms of CLEAR
#                and DROP, COPY, MOVE and ADD with the default graph, the SILENT forms,
#                a request that clears a graph and inserts into it again, DELETE WHERE
#                over every graph, WITH and USING.
#   errors       12 requests the reference engine raises an error for (CLEAR, DROP, COPY,
#                MOVE and ADD of a graph that does not exist, CREATE of one that exists,
#                LOAD, an error in the second operation of a request, a SERVICE call that
#                fails, and a blank node in DELETE DATA, in a DELETE template and in
#                DELETE WHERE, which is a SPARQL syntax error): the store exits 1, the log
#                file does not exist afterwards (the request is atomic: nothing was written),
#                and the state is the original.
#   labels       the fresh blank node rule of tests/sbm11/update/labels.nq: the labels
#                of the base and of earlier batches are skipped (exact labels asserted),
#                the labels of one request differ, replay and compaction give the same
#                labels, a dump packed again and updated again gives new labels, and no
#                reader of the source layer produces a label with the prefix `sbm11u`.
#   sparql12     SPARQL 1.2 on tests/sbm11/gate12/gate12.nq: a blank node inside a nested
#                triple term in INSERT DATA and in an INSERT template, a triple-term
#                pattern with a variable in DELETE WHERE, the triple functions.
#   scaling      n and 4n: the compile time of an update with a WHERE clause and a template
#                blank node (10,000 and 40,000 solutions) and the replay time of a log (20,000
#                and 80,000 entries) each grow by less than 8 times for 4 times the input; and
#                the memory of the batch encoder (https://github.com/danbri/factoidal/issues/857,
#                repaired 2026-10-14: it was 64 bytes of memory for each byte of log).
#   shortfalls   expected failures that name an open issue: an empty named graph is not
#                stored (https://github.com/danbri/factoidal/issues/855), CLEAR NAMED
#                with a graph named by a blank node (https://github.com/danbri/factoidal/issues/856),
#                and the replay of a log at every open: 93 microseconds for each entry
#                (https://github.com/danbri/factoidal/issues/858).
#
# Prints "N pass, M fail, K expected-fail (out of T)". Exit 0 when no case failed and no
# expected failure passed; 2 when a binary is missing.
#
# Env: L4_BIN_DIR   directory of the binaries (default formal/lean4/.lake/build/bin)
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${L4_BIN_DIR:-$ROOT/formal/lean4/.lake/build/bin}"
FX="$HERE/update"
GATE="$HERE/gate/gate.nq"
GATE12="$HERE/gate12/gate12.nq"
for need in "$BIN/l4sbm11" "$BIN/l4sbm11-pack" "$BIN/l4sbm11-w3c" "$BIN/l4factoidal" "$GATE" "$GATE12" "$FX/labels.nq"; do
  if [ ! -e "$need" ]; then echo "missing: $need" >&2; exit 2; fi
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-update.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
PASS=0; FAIL=0; XFAIL=0
record() { # record <group> <name> <ok:0|1> <detail>
  if [ "$3" = 0 ]; then PASS=$((PASS + 1)); printf 'ok     %-12s %-34s %s\n' "$1" "$2" "$4"
  else FAIL=$((FAIL + 1)); printf 'FAIL   %-12s %-34s %s\n' "$1" "$2" "$4"; fi
}
xfail() { # xfail <group> <name> <issue-url> <expected-failure-holds:0|1> <detail>
  if [ "$4" = 0 ]; then XFAIL=$((XFAIL + 1)); printf 'XFAIL  %-12s %-34s (%s) %s\n' "$1" "$2" "$3" "$5"
  else FAIL=$((FAIL + 1)); printf 'XPASS  %-12s %-34s (%s) %s -- flip this case to a real assertion and close the issue\n' "$1" "$2" "$3" "$5"; fi
}

# new_store <dir> <source>: a collection root DIR whose generation `gen` is packed from SOURCE and activated
new_store() {
  rm -rf "$1"; mkdir -p "$(dirname "$1")"
  "$BIN/l4sbm11-pack" "$2" "$1/gen" --workers 1 >"$1.pack.log" 2>&1 \
    && "$BIN/l4sbm11" activate "$1" gen >"$1.act.log" 2>&1
}
# store_update <dir> <request file> [flags]: exit code in $URC, the log in <dir>.upd
store_update() {
  local d="$1" f="$2"; shift 2
  URC=0
  timeout 300 "$BIN/l4sbm11" update "$d" --file "$f" --base "file://$(realpath "$f")" "$@" >"$d.upd" 2>&1 || URC=$?
}
# replay_ms <dir>: the least of two replay times of `l4sbm11 query` on DIR (the "replay ms" of its stderr line),
# as an integer number of ms; nothing when a query fails
replay_ms() {
  local d="$1" best="" i v
  for i in 1 2; do
    timeout 300 "$BIN/l4sbm11" query "$d" 'ASK { ?s ?p ?o }' >/dev/null 2>"$d.replay.err" || return 0
    v="$(grep -o 'replay ms [0-9.]*' "$d.replay.err" | head -1 | grep -o '[0-9][0-9.]*$')"
    [ -n "$v" ] || return 0
    if [ -z "$best" ] || awk -v a="$v" -v b="$best" 'BEGIN { exit !(a < b) }'; then best="$v"; fi
  done
  printf '%.0f' "$best"
}
# ref_update <state file> <request file> <new state file> [format and flags]: exit code in $RRC
ref_update() {
  local st="$1" f="$2" out="$3"; shift 3
  RRC=0
  timeout 300 "$BIN/l4factoidal" update "$st" --update "$f" "$@" >"$out" 2>"$out.err" || RRC=$?
}
# check_state <dir> <reference state> <group> <name> <mode> [query flags]: the state check and the query checks
check_state() {
  local d="$1" st="$2" group="$3" name="$4" mode="$5" qflags="${6:-}" qfmt="${7:-nquads}" out rc
  rm -rf "$d/cmp"
  rc=0
  timeout 300 "$BIN/l4sbm11" compact "$d" "$d/cmp" >"$d.compact.log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ]; then record "$group" "$name-state" 1 "compact exit $rc: $(tail -1 "$d.compact.log")"; return; fi
  timeout 300 "$BIN/l4sbm11" dump "$d/cmp" >"$d.dump.nq" 2>/dev/null
  out="$("$BIN/l4sbm11-w3c" compare "$st" "$d.dump.nq" --expected nq --mode "$mode" 2>&1)" || true
  case "$out" in
    pass*) record "$group" "$name-state" 0 "$(wc -l <"$d.dump.nq") quads, isomorphic to the reference state" ;;
    *) record "$group" "$name-state" 1 "$(printf '%s' "$out" | head -1 | cut -c1-200)" ;;
  esac
  [ "$qflags" = none ] && return
  local bad="" n=0 rq nq want_path p qrc frc rrc v vf
  for rq in "$FX"/q/*.rq; do
    nq="$(basename "$rq" .rq)"; n=$((n + 1))
    qrc=0; timeout 120 "$BIN/l4sbm11" query "$d" --file "$rq" $qflags >"$d.q.json" 2>"$d.q.err" || qrc=$?
    frc=0; timeout 120 "$BIN/l4sbm11" query "$d" --file "$rq" --reference $qflags >"$d.f.json" 2>/dev/null || frc=$?
    rrc=0; timeout 120 "$BIN/l4factoidal" query "$st" --format "$qfmt" --query "$rq" $qflags >"$d.w.json" 2>/dev/null || rrc=$?
    v="$(python3 -I "$HERE/compare_answers.py" "$d.q.json" "$d.w.json" "$rrc")"
    vf="$(python3 -I "$HERE/compare_answers.py" "$d.f.json" "$d.w.json" "$rrc")"
    p="$(grep -o 'path=[a-z]*' "$d.q.err" | head -1)"
    want_path=path=ids; case $nq in ref-*) want_path=path=reference ;; esac
    if [ "$qrc" -ne 0 ] || [ "$frc" -ne 0 ]; then bad="$bad $nq(exit $qrc/$frc)"; continue; fi
    case "$v|$vf" in equal*"|"equal*) ;; *) bad="$bad $nq($v|$vf)"; continue ;; esac
    [ "$p" = "$want_path" ] || bad="$bad $nq($p)"
  done
  if [ -z "$bad" ]; then record "$group" "$name-queries" 0 "$n queries on the overlay (their path and --reference) equal the reference engine"
  else record "$group" "$name-queries" 1 "failed:$bad"; fi
}

echo "=== steps: 16 requests in order on the gate fixture"
S="$TMP/steps/col"
new_store "$S" "$GATE" || record steps setup 1 "pack or activate failed: $(tail -1 "$S.pack.log" "$S.act.log" 2>/dev/null | tr '\n' ' ')"
cp "$GATE" "$TMP/steps/state.nq"
for req in "$FX"/steps/*.ru; do
  n="$(basename "$req" .ru)"
  store_update "$S" "$req"
  ref_update "$TMP/steps/state.nq" "$req" "$TMP/steps/new.nq" --format nquads
  if [ "$URC" -eq 0 ] && [ "$RRC" -eq 0 ]; then
    record steps "$n" 0 "$(grep -o 'seq=[0-9]* epoch=[0-9]* ops=[0-9]*' "$S.upd"); $(grep -o 'where path=[a-z]*' "$S.upd" | sort | uniq -c | tr '\n' ' ' | sed 's/  */ /g')"
  else
    record steps "$n" 1 "store exit $URC, reference exit $RRC: $(grep -v ' op ' "$S.upd" | tail -1 | cut -c1-160) $(head -c 160 "$TMP/steps/new.nq.err")"
  fi
  [ "$RRC" -eq 0 ] && cp "$TMP/steps/new.nq" "$TMP/steps/state.nq"
  check_state "$S" "$TMP/steps/state.nq" steps "$n" rdf11
done

echo "=== destructive: 23 requests, each on a fresh generation"
for req in "$FX"/destructive/*.ru; do
  n="$(basename "$req" .ru)"
  D="$TMP/destructive/$n"
  new_store "$D" "$GATE"
  store_update "$D" "$req"
  ref_update "$GATE" "$req" "$TMP/destructive/$n.nq" --format nquads
  if [ "$URC" -eq 0 ] && [ "$RRC" -eq 0 ]; then
    record destructive "$n" 0 "$(grep -o 'seq=[0-9]* epoch=[0-9]* ops=[0-9]*' "$D.upd")"
    check_state "$D" "$TMP/destructive/$n.nq" destructive "$n" rdf11
  else
    record destructive "$n" 1 "store exit $URC, reference exit $RRC: $(grep -v ' op ' "$D.upd" | tail -1 | cut -c1-160) $(head -c 160 "$TMP/destructive/$n.nq.err")"
  fi
done

echo "=== errors: the reference engine raises an error, the store writes nothing"
for req in "$FX"/errors/*.ru; do
  n="$(basename "$req" .ru)"
  D="$TMP/errors/$n"
  new_store "$D" "$GATE"
  store_update "$D" "$req"
  ref_update "$GATE" "$req" "$TMP/errors/$n.nq" --format nquads
  if [ "$URC" -eq 1 ] && [ "$RRC" -ne 0 ] && [ ! -e "$D/gen/deltas.dlog" ] && grep -qE 'refused|parse error' "$D.upd"; then
    record errors "$n" 0 "$(grep -E 'refused|parse error' "$D.upd" | head -1 | cut -c1-120)"
  else
    record errors "$n" 1 "store exit $URC (want 1), reference exit $RRC (want non-zero), log file $([ -e "$D/gen/deltas.dlog" ] && echo exists || echo absent): $(tail -1 "$D.upd" | cut -c1-120)"
  fi
  check_state "$D" "$GATE" errors "$n" rdf11 none
done

echo "=== labels: fresh blank nodes"
L="$TMP/labels/col"
new_store "$L" "$FX/labels.nq"
bnodes() { # bnodes <dir>: the sorted distinct blank nodes that have a property ex:q, from a query
  "$BIN/l4sbm11" query "$1" 'SELECT DISTINCT ?s WHERE { ?s <http://ex.org/q> ?o FILTER(isBlank(?s)) }' 2>/dev/null | head -1 \
    | python3 -I -c 'import json,sys; d=json.load(sys.stdin); print(" ".join(sorted(b["s"]["value"] for b in d["results"]["bindings"])))'
}
# the base holds sbm11u0 and sbm11u2: two labels with the prefix, so the supply starts at 2, finds sbm11u2 held and takes 3
printf 'INSERT DATA { _:a <http://ex.org/q> "x" . _:b <http://ex.org/q> "y" . _:a <http://ex.org/q> "x2" }\n' >"$TMP/labels/u1.ru"
store_update "$L" "$TMP/labels/u1.ru"
got="$(bnodes "$L")"
if [ "$URC" -eq 0 ] && [ "$got" = "sbm11u3 sbm11u4" ]; then record labels skips-base-labels 0 "base holds sbm11u0 and sbm11u2; the request got $got (one label per request label)"
else record labels skips-base-labels 1 "exit $URC, labels: $got (want sbm11u3 sbm11u4)"; fi
# the log holds sbm11u3 and sbm11u4 and the base two: the supply starts at 4, finds sbm11u4 held (in the log) and takes 5
printf 'INSERT DATA { _:a <http://ex.org/q> "z" }\n' >"$TMP/labels/u2.ru"
store_update "$L" "$TMP/labels/u2.ru"
got="$(bnodes "$L")"
if [ "$URC" -eq 0 ] && [ "$got" = "sbm11u3 sbm11u4 sbm11u5" ]; then record labels skips-log-labels 0 "the second request got sbm11u5; all labels: $got"
else record labels skips-log-labels 1 "exit $URC, labels: $got (want sbm11u3 sbm11u4 sbm11u5)"; fi
# one request: INSERT DATA labels first (sbm11u6), then one label for each of the two solutions of the INSERT template
printf 'INSERT DATA { _:k <http://ex.org/q> "k" } ; INSERT { ?s <http://ex.org/q> _:t . _:t <http://ex.org/q> ?o } WHERE { ?s <http://ex.org/p> ?o FILTER(isIRI(?s)) }\n' >"$TMP/labels/u3.ru"
store_update "$L" "$TMP/labels/u3.ru"
got="$(bnodes "$L")"
if [ "$URC" -eq 0 ] && [ "$got" = "sbm11u3 sbm11u4 sbm11u5 sbm11u6 sbm11u7 sbm11u8" ]; then
  record labels one-label-per-solution 0 "INSERT DATA took sbm11u6, the template one label for each of its 2 solutions (sbm11u7, sbm11u8)"
else record labels one-label-per-solution 1 "exit $URC, labels: $got (want sbm11u3 to sbm11u8)"; fi
# replay and compaction give the same blank nodes
"$BIN/l4sbm11" query "$L" 'SELECT DISTINCT ?b WHERE { { ?b ?p ?o } UNION { ?s ?p ?b } FILTER(isBlank(?b)) }' 2>/dev/null | head -1 \
  | python3 -I -c 'import json,sys; d=json.load(sys.stdin); print("\n".join(sorted(b["b"]["value"] for b in d["results"]["bindings"])))' >"$TMP/labels/overlay.txt"
rm -rf "$L/cmp"
"$BIN/l4sbm11" compact "$L" "$L/cmp" >"$L.compact.log" 2>&1
"$BIN/l4sbm11" dump "$L/cmp" 2>/dev/null >"$TMP/labels/compacted.nq"
grep -o '_:[A-Za-z0-9_.-]*' "$TMP/labels/compacted.nq" | sed 's/^_://' | sort -u >"$TMP/labels/compacted.txt"
if [ -s "$TMP/labels/overlay.txt" ] && cmp -s "$TMP/labels/overlay.txt" "$TMP/labels/compacted.txt"; then
  record labels replay-equals-compaction 0 "$(wc -l <"$TMP/labels/overlay.txt") blank nodes, the same labels in the overlay and in the compacted generation"
else record labels replay-equals-compaction 1 "overlay: $(tr '\n' ' ' <"$TMP/labels/overlay.txt") compacted: $(tr '\n' ' ' <"$TMP/labels/compacted.txt")"; fi
# a dump packed again, then updated: the new labels are not any label the dump holds
"$BIN/l4sbm11" activate "$L" cmp >/dev/null 2>&1
before="$(wc -l <"$TMP/labels/compacted.txt")"
printf 'INSERT DATA { _:a <http://ex.org/q> "again" ; <http://ex.org/q> "again2" . _:b <http://ex.org/q> "again3" }\n' >"$TMP/labels/u4.ru"
store_update "$L" "$TMP/labels/u4.ru"
rm -rf "$L/cmp2"
"$BIN/l4sbm11" compact "$L" "$L/cmp2" >"$L.compact2.log" 2>&1
"$BIN/l4sbm11" dump "$L/cmp2" 2>/dev/null | grep -o '_:[A-Za-z0-9_.-]*' | sed 's/^_://' | sort -u >"$TMP/labels/compacted2.txt"
after="$(wc -l <"$TMP/labels/compacted2.txt")"
newl="$(comm -13 "$TMP/labels/compacted.txt" "$TMP/labels/compacted2.txt" | tr '\n' ' ' | sed 's/ $//')"
if [ "$URC" -eq 0 ] && [ "$after" -eq $((before + 2)) ] && [ "$newl" = "sbm11u10 sbm11u9" ]; then
  record labels after-compaction 0 "$before blank nodes in the compacted generation (sbm11u8 the last), 2 more after an update of it: $newl"
else record labels after-compaction 1 "exit $URC, $before before, $after after, new labels: $newl (want sbm11u10 sbm11u9)"; fi
# the source layer produces no label with the fresh prefix: every reader, on the documents of tests/sbm11/syntax with
# anonymous nodes, property lists and collections
bad=""; n=0
for f in "$HERE"/syntax/d3.ttl "$HERE"/syntax/d3.trig "$HERE"/syntax/d3.rdf "$HERE"/syntax/d3.jsonld "$HERE"/syntax/d3.nq "$HERE"/syntax/d3.nt \
         "$HERE"/syntax/bnode_collide.ttl "$HERE"/syntax/bnode_collide.trig "$HERE"/syntax/bnode_collide.rdf "$HERE"/syntax/bnode_collide.jsonld; do
  n=$((n + 1))
  "$BIN/l4sbm11" canon "$f" >"$TMP/labels/canon.nq" 2>/dev/null || { bad="$bad $(basename "$f")(exit)"; continue; }
  grep -q '_:' "$TMP/labels/canon.nq" || { bad="$bad $(basename "$f")(no blank node)"; continue; }
  if grep -q '_:sbm11u' "$TMP/labels/canon.nq"; then bad="$bad $(basename "$f")"; fi
done
if [ -z "$bad" ]; then record labels no-reader-label 0 "$n documents in six syntaxes with blank nodes: no label starts with sbm11u"
else record labels no-reader-label 1 "labels with the prefix in:$bad"; fi

echo "=== sparql12: SPARQL 1.2 on the RDF 1.2 gate fixture"
T="$TMP/s12/col"
new_store "$T" "$GATE12"
cp "$GATE12" "$TMP/s12/state.nq"
mkdir -p "$TMP/s12"
for req in "$FX"/sparql12/*.ru; do
  n="$(basename "$req" .ru)"
  store_update "$T" "$req" --sparql12
  ref_update "$TMP/s12/state.nq" "$req" "$TMP/s12/new.nq" --format nquads12 --sparql12
  if [ "$URC" -eq 0 ] && [ "$RRC" -eq 0 ]; then
    record sparql12 "$n" 0 "$(grep -o 'seq=[0-9]* epoch=[0-9]* ops=[0-9]*' "$T.upd"); $(grep -o 'where path=[a-z]*' "$T.upd" | sort | uniq -c | tr '\n' ' ' | sed 's/  */ /g')"
    cp "$TMP/s12/new.nq" "$TMP/s12/state.nq"
  else
    record sparql12 "$n" 1 "store exit $URC, reference exit $RRC: $(grep -v ' op ' "$T.upd" | tail -1 | cut -c1-160) $(head -c 160 "$TMP/s12/new.nq.err")"
  fi
  check_state "$T" "$TMP/s12/state.nq" sparql12 "$n" rdf12 none
done

echo "=== shortfalls: expected failures, each with an open issue"
# https://github.com/danbri/factoidal/issues/855: the store has no slot for an empty named graph
X="$TMP/short/empty"
new_store "$X" "$GATE"
printf 'PREFIX ex: <http://ex.org/>\nCREATE GRAPH ex:gx ; CLEAR GRAPH ex:gx\n' >"$TMP/short/create-clear.ru"
store_update "$X" "$TMP/short/create-clear.ru"
ref_update "$GATE" "$TMP/short/create-clear.ru" "$TMP/short/create-clear.nq" --format nquads
if [ "$RRC" -ne 0 ]; then record shortfalls empty-graph-reference 1 "the reference engine refused CREATE then CLEAR (exit $RRC)"
elif [ "$URC" -ne 0 ]; then xfail shortfalls xfail-empty-graph-slot https://github.com/danbri/factoidal/issues/855 0 "the reference accepts CREATE GRAPH then CLEAR GRAPH, the store refuses: $(grep refused "$X.upd" | head -1 | cut -c1-100)"
else xfail shortfalls xfail-empty-graph-slot https://github.com/danbri/factoidal/issues/855 1 "the store accepts CREATE GRAPH then CLEAR GRAPH"; fi
# https://github.com/danbri/factoidal/issues/856: a graph named by a blank node cannot be named in a log entry
Y="$TMP/short/bnode"
new_store "$Y" "$FX/bnode-graph.nq"
printf 'CLEAR NAMED\n' >"$TMP/short/clear-named.ru"
store_update "$Y" "$TMP/short/clear-named.ru"
ref_update "$FX/bnode-graph.nq" "$TMP/short/clear-named.ru" "$TMP/short/clear-named.nq" --format nquads
if [ "$RRC" -ne 0 ]; then record shortfalls bnode-graph-reference 1 "the reference engine refused CLEAR NAMED (exit $RRC)"
elif [ "$URC" -ne 0 ]; then xfail shortfalls xfail-bnode-named-graph https://github.com/danbri/factoidal/issues/856 0 "the reference clears the graph named by a blank node, the store refuses: $(grep refused "$Y.upd" | head -1 | cut -c1-100)"
else xfail shortfalls xfail-bnode-named-graph https://github.com/danbri/factoidal/issues/856 1 "the store accepts CLEAR NAMED with a graph named by a blank node"; fi

# https://github.com/danbri/factoidal/issues/857: the batch of a large request was encoded as a List UInt8 (about 64
# bytes of memory for each byte of log). The encoder works on a ByteArray since 2026-10-14
# (Storage/DeltaLogBytes.lean). Two assertions on an INSERT DATA of 40,000 quads: the encoder raises the peak RSS by
# at most 8 bytes for each byte of log (`peak RSS after compile` and `after encode` of the `sbm11-update:` line), and
# the whole process peaks at 16 bytes for each byte of log plus 96 MiB. The second bound was 64 MiB in the issue,
# before the repair was measured: the peak is reached while the request is parsed (139.8 MB for the 2.5 MB request; the
# encoder adds nothing to it), and a bound of 64 MiB left 3 percent of room.
Z="$TMP/short/batch"
python3 -I - "$TMP/short/big.ru" <<'PY'
import sys
with open(sys.argv[1], "w") as f:
    f.write("INSERT DATA {\n")
    for i in range(40000):
        f.write('<http://ex.org/b%d> <http://ex.org/p> "value %d" .\n' % (i, i))
    f.write("}\n")
PY
new_store "$Z" "$GATE"
store_update "$Z" "$TMP/short/big.ru"
bbytes="$(grep -o ' bytes=[0-9]*' "$Z.upd" | head -1 | cut -d= -f2)"
brss="$(grep -o 'peak RSS (VmHWM): [0-9]* kB' "$Z.upd" | grep -o '[0-9][0-9]*' | head -1)"
brc="$(grep -o 'peak RSS after compile [0-9]* kB' "$Z.upd" | grep -o '[0-9][0-9]*' | head -1)"
bre="$(grep -o 'after encode [0-9]* kB' "$Z.upd" | grep -o '[0-9][0-9]*' | head -1)"
if [ "$URC" -ne 0 ] || [ -z "$bbytes" ] || [ -z "$brss" ] || [ -z "$brc" ] || [ -z "$bre" ]; then
  record scaling batch-encoder-setup 1 "exit $URC, bytes '$bbytes', rss '$brss', after compile '$brc', after encode '$bre': $(tail -1 "$Z.upd" | cut -c1-120)"
else
  inc=$(((bre - brc) * 1024))
  if [ "$inc" -le $((8 * bbytes)) ] && [ $((brss * 1024)) -le $((16 * bbytes + 96 * 1024 * 1024)) ]; then
    record scaling batch-encoder-memory 0 "40,000 quads: batch $bbytes bytes; the encoder raised the peak RSS by $((inc / 1024)) kB (at most 8 bytes for each byte of log); peak RSS $((brss * 1024 / 1048576)) MB ($((brss * 1024 / bbytes)) bytes for each byte of log; at most 16 plus 96 MiB)"
  else
    record scaling batch-encoder-memory 1 "40,000 quads: batch $bbytes bytes; the encoder raised the peak RSS by $((inc / 1024)) kB; peak RSS $((brss * 1024 / 1048576)) MB ($((brss * 1024 / bbytes)) bytes for each byte of log)"
  fi
fi

# https://github.com/danbri/factoidal/issues/858: every open replays the log with one dictionary lookup for each term of each
# entry; the bound is 1,000 ms for the 40,000 entries of the store above (a slower or a busier machine only makes the
# expected failure hold longer, so the case cannot pass by noise)
RMS40="$(replay_ms "$Z")"
if [ -z "$RMS40" ]; then record shortfalls replay-time-setup 1 "no replay time: $(tail -1 "$Z.replay.err" | cut -c1-120)"
elif [ "$RMS40" -gt 1000 ]; then
  xfail shortfalls xfail-replay-time https://github.com/danbri/factoidal/issues/858 0 "40,000 entries: replay $RMS40 ms at open ($((RMS40 * 1000 / 40000)) microseconds for each entry; the bound is 1,000 ms)"
else xfail shortfalls xfail-replay-time https://github.com/danbri/factoidal/issues/858 1 "40,000 entries: replay $RMS40 ms"; fi

echo "=== scaling: the cost of an update and of a replay grows in proportion to the request (n and 4n)"
# The third checker of the skill danbri-function-precrime-checkers. The times are the tools' own lines. Compile and
# replay: a bound of 8 for 4 times the input (linear work gives 4, quadratic work gives 16; measured 3.9 to 5.1 for
# the compile time in 4 runs and 3.7 to 4.5 for the replay time in 3 runs). Before 2026-10-14 the replay of 10,000 and of 40,000
# entries took 1.2 s and 10.1 s (8.3), and the model a n + c n^2 fitted to the five sizes gives 11.5 for 20,000 and
# 80,000 entries: `Session.idOrNew` read the size of the vocabulary with `get` before the push, which left a second
# reference to the array, and every push copied it. (A pair of 5,000 and 40,000 entries gave 7.4 to 13.6 on the
# repaired code, because the fixed cost of an open is most of 5,000 entries: the pair was dropped.)
ratio_ok() { awk -v a="$1" -v b="$2" -v bound="$3" 'BEGIN { exit !(a > 0 && b <= bound * a) }'; }
# compile: INSERT { ?s ex:q _:b } WHERE { ?s ex:p ?o } over n subjects (n solutions, n fresh labels, n entries),
# the least of two runs on copies of one store
mkdir -p "$TMP/scale"
best_compile() { # best_compile <n>: the least "compile" time in ms (a decimal) of two runs
  local n="$1" run best="" v
  python3 -I - "$TMP/scale/src$n.nt" "$n" <<'PY'
import sys
with open(sys.argv[1], "w") as f:
    for i in range(int(sys.argv[2])):
        f.write('<http://ex.org/s%d> <http://ex.org/p> "v%d" .\n' % (i, i))
PY
  new_store "$TMP/scale/c$n" "$TMP/scale/src$n.nt" || { echo ""; return 0; }
  printf 'INSERT { ?s <http://ex.org/q> _:b } WHERE { ?s <http://ex.org/p> ?o }\n' >"$TMP/scale/req.ru"
  for run in 1 2; do
    rm -rf "$TMP/scale/c${n}r$run"; cp -r "$TMP/scale/c$n" "$TMP/scale/c${n}r$run"
    store_update "$TMP/scale/c${n}r$run" "$TMP/scale/req.ru"
    [ "$URC" -eq 0 ] || { echo ""; return 0; }
    v="$(grep -o 'compile [0-9.]* ms' "$TMP/scale/c${n}r$run.upd" | head -1 | grep -o '[0-9][0-9.]*')"
    [ -n "$v" ] || { echo ""; return 0; }
    if [ -z "$best" ] || awk -v a="$v" -v b="$best" 'BEGIN { exit !(a < b) }'; then best="$v"; fi
  done
  echo "$best"
}
C10="$(best_compile 10000)"; C40="$(best_compile 40000)"
if [ -z "$C10" ] || [ -z "$C40" ]; then record scaling compile-linear 1 "an update of 10,000 or 40,000 solutions failed or printed no compile time"
elif ratio_ok "$C10" "$C40" 8; then record scaling compile-linear 0 "10,000 solutions: $C10 ms, 40,000 solutions: $C40 ms (WHERE clause, templates, fresh labels; the bound for the quadruple is 8 times)"
else record scaling compile-linear 1 "10,000 solutions: $C10 ms, 40,000 solutions: $C40 ms: more than 8 times for 4 times the solutions"; fi
# replay: logs of 20,000 and 80,000 entries (INSERT DATA of that many quads on the gate fixture)
replay_of() { # replay_of <n>: the replay time in ms of a log of n entries, nothing on a failure
  local n="$1" d="$TMP/scale/ins$n"
  new_store "$d" "$GATE" || return 0
  python3 -I - "$TMP/scale/ins$n.ru" "$n" <<'PY'
import sys
with open(sys.argv[1], "w") as f:
    f.write("INSERT DATA {\n")
    for i in range(int(sys.argv[2])):
        f.write('<http://ex.org/b%d> <http://ex.org/p> "value %d" .\n' % (i, i))
    f.write("}\n")
PY
  store_update "$d" "$TMP/scale/ins$n.ru"
  [ "$URC" -eq 0 ] || return 0
  replay_ms "$d"
}
RMS20="$(replay_of 20000)"; RMS80="$(replay_of 80000)"
if [ -z "$RMS20" ] || [ -z "$RMS80" ]; then record scaling replay-linear 1 "the update or the replay of 20,000 or 80,000 entries failed"
elif ratio_ok "$RMS20" "$RMS80" 8; then record scaling replay-linear 0 "20,000 entries: $RMS20 ms, 80,000 entries: $RMS80 ms (the bound for the quadruple is 8 times)"
else record scaling replay-linear 1 "20,000 entries: $RMS20 ms, 80,000 entries: $RMS80 ms: more than 8 times for 4 times the entries"; fi

echo
echo "update where: $PASS pass, $FAIL fail, $XFAIL expected-fail (out of $((PASS + FAIL + XFAIL)))"
[ "$FAIL" -eq 0 ]
