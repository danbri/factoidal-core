#!/usr/bin/env bash
#
# tests/planner/sbm11_gate.sh — OKR batch 3 KR 4.1
# (https://github.com/danbri/factoidal/issues/875; epic
# https://github.com/danbri/factoidal/issues/800). Record:
# docs/designissues/2026-10-12-capability-aware-planner.md, section 12.
#
# The SBM11 gate fixture (tests/sbm11/gate/gate.nq) is packed and activated.
# For each tests/sbm11/gate/*.rq query:
#   - `l4planner-test sbm11-query GEN Q --check-pure` runs the planner's first
#     plan through IO (each access is a keyed id-path scan made at call time),
#     prints SPARQL Results JSON, and exits 1 if the IO rows differ from the
#     pure run over the default graph; exit 3: the planner does not accept the
#     query (`Requirement.ofQuery?` gives none, or no plan);
#   - an accepted query must read PRB1 bytes during the run
#     (prb1-bytes-in-run > 0), and its answer must equal `l4sbm11 query` on
#     the same generation (tests/sbm11/compare_answers.py, multisets).
# Prints "planner-sbm11-gate: N pass, M fail (out of T accepted); U not
# accepted". Exit 0 only when M = 0 and T > 0.
#
# The planner does not accept FILTER yet (no RowFilter from a SPARQL Expr):
# expected failure `rowfilter-from-expr` in Harness/PlannerTest.lean,
# https://github.com/danbri/factoidal/issues/801.
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="$ROOT/formal/lean4/.lake/build/bin"
GATE="$ROOT/tests/sbm11/gate"
for need in "$BIN/l4sbm11" "$BIN/l4sbm11-pack" "$BIN/l4planner-test"; do
  if [ ! -x "$need" ]; then echo "missing: $need" >&2; exit 2; fi
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/planner-gate.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
rc=0
"$BIN/l4sbm11-pack" "$GATE/gate.nq" "$TMP/st/gen" --workers 1 >"$TMP/pack.log" 2>&1 || rc=$?
[ "$rc" -eq 0 ] && { "$BIN/l4sbm11" activate "$TMP/st" gen >"$TMP/act.log" 2>&1 || rc=$?; }
if [ "$rc" -ne 0 ]; then
  echo "FAIL pack-activate: exit $rc"; cat "$TMP/pack.log" "$TMP/act.log" 2>/dev/null; exit 1
fi
PASS=0; FAIL=0; NOTACC=0
for rq in "$GATE"/*.rq; do
  n="$(basename "$rq" .rq)"
  prc=0
  timeout 120 "$BIN/l4planner-test" sbm11-query "$TMP/st/gen" "$rq" --check-pure \
    >"$TMP/$n.got" 2>"$TMP/$n.err" || prc=$?
  if [ "$prc" -eq 3 ]; then NOTACC=$((NOTACC + 1)); continue; fi
  if [ "$prc" -ne 0 ]; then
    FAIL=$((FAIL + 1)); echo "FAIL $n: planner exit $prc: $(tail -1 "$TMP/$n.err")"; continue
  fi
  bytes="$(grep -o 'prb1-bytes-in-run=[0-9]*' "$TMP/$n.err" | cut -d= -f2)"
  if [ -z "$bytes" ] || [ "$bytes" -eq 0 ]; then
    FAIL=$((FAIL + 1)); echo "FAIL $n: no PRB1 bytes read during the run"; continue
  fi
  qrc=0
  timeout 120 "$BIN/l4sbm11" query "$TMP/st" --file "$rq" --base "file://$(realpath "$rq")" \
    >"$TMP/$n.want" 2>"$TMP/$n.qerr" || qrc=$?
  if [ "$qrc" -ne 0 ]; then
    FAIL=$((FAIL + 1)); echo "FAIL $n: l4sbm11 query exit $qrc"; continue
  fi
  v="$(python3 -I "$ROOT/tests/sbm11/compare_answers.py" "$TMP/$n.got" "$TMP/$n.want" 0)"
  case "$v" in
    equal*) PASS=$((PASS + 1)); echo "ok   $n: $v; $(grep -o 'plan=.*' "$TMP/$n.err" | head -1)" ;;
    *) FAIL=$((FAIL + 1)); echo "FAIL $n: $v" ;;
  esac
done
T=$((PASS + FAIL))
echo "planner-sbm11-gate: $PASS pass, $FAIL fail (out of $T accepted); $NOTACC not accepted"
if [ "$FAIL" -eq 0 ] && [ "$T" -gt 0 ]; then exit 0; else exit 1; fi
