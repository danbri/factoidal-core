#!/usr/bin/env bash
#
# tests/sbm11/run.sh — SBM11 stage 4, SPARQL over a generation
# (https://github.com/danbri/factoidal/issues/790), and stage 5, the delta
# overlay and compaction (https://github.com/danbri/factoidal/issues/791; tracking
# https://github.com/danbri/factoidal/issues/787). Record:
# docs/designissues/2026-10-12-sbm11-stage4.md.
#
#   (a) oracle   q01 to q21 (tests/qlvr/queries) through `l4sbm11 query` on
#                the olympics generation against the QLever oracle
#                (QLVR_WORK/oracle/*.srj), as multisets by value, with the
#                differences of the comparison record section 3.3 handled as
#                that section says (tests/sbm11/compare_oracle.py). Prints
#                "N pass, M fail (out of 21)".
#   (b) render   every oracle query answered twice, by the key printer (the
#                default) and with --reference-render (every term through
#                jsonOfTerm); the outputs must be byte-identical.
#   (c) ids vs reference   oracle queries q03 to q18 answered on ids and with
#                --reference (the reference evaluator over the quads the
#                planner guard selects); equal as multisets
#                (tests/sbm11/compare_answers.py).
#   (d) gate     tests/sbm11/gate/gate.nq (default and named graphs, integer
#                types, a non-canonical integer, language tags, blank nodes)
#                packed and activated; each tests/sbm11/gate/*.rq answered by
#                `l4sbm11 query` and by the in-memory reference engine
#                (`l4factoidal query gate.nq`), equal as multisets. A query
#                named ids-* must run on ids (path=ids); one named ref-* must
#                take the reference fallback (path=reference): EXISTS, NOT
#                EXISTS, MINUS, sub-SELECT, the OPTIONAL shapes outside the id
#                fragment (nested, a variable two groups share that the base
#                does not bind, a FILTER in the group over a base variable, a
#                FILTER beside it over an optional variable, OPTIONAL first,
#                GRAPH in the group) and the other forms only the reference
#                semantics decide (CLAUDE.md anti-pattern 34). The
#                ids-optional-* queries run OPTIONAL on ids (issue 775): no
#                match, one, several, FILTER in the group true, false and an
#                error, two groups, GRAPH in the base, ORDER BY the optional
#                variable (with LIMIT, so the order is part of the answer),
#                COUNT and GROUP BY over it, DISTINCT, SELECT *.
#   (e) checks   `l4sbm11 prm-check` (the byte-array PRM1 decoder against the
#                list decoder of the round-trip theorem) and `l4sbm11
#                frame-check` (the word decoder against decodeColumnAt) on
#                every PRM1 file and every frame of the generation.
#   (f) verify   q01 to q21 answered with --verify merkle and --verify none
#                (https://github.com/danbri/factoidal/issues/796): the
#                outputs must be byte-identical. Parts (a) to (e) use the
#                CLI default (none when a CURRENT pointer names GEN).
#   (h) delta    stage 5 (https://github.com/danbri/factoidal/issues/791):
#                the gate fixture packed, then the batches of
#                tests/sbm11/delta/gate-ops.txt sent one by one with
#                `l4sbm11 update`; after each batch every gate query and every
#                tests/sbm11/delta/*.rq (EXISTS, NOT EXISTS, MINUS, OPTIONAL
#                with FILTER on the changed rows) answered on the overlay and
#                by `l4factoidal query` over the state tests/sbm11/delta_apply.py
#                computes (a separate implementation over the quads' text);
#                equal as multisets, on the path the name says. Then a fresh
#                pack of the final state answers the same; `l4sbm11 compact`
#                writes a generation whose every artifact is byte-identical to
#                the fresh pack's; the compacted generation answers the same;
#                an update after compaction is seen (epoch 2); an update with
#                WHERE and INSERT DATA with a blank node are refused (the
#                stage 5 limits: a change of either turns this RED).
#   (i) olympics stage 5 on the olympics generation (a copy): the batches of
#                tests/sbm11/delta/olympics-ops.txt, the inserted row seen,
#                the deleted row not seen; q01 to q21 and
#                tests/sbm11/delta/olympics/*.rq on the overlay equal to a
#                fresh pack of the updated source; the compacted generation
#                byte-identical to the fresh pack; compaction time at most 1.2
#                times the fresh pack time. Needs QLVR_WORK/instance/olympics.nt;
#                SBM11_DELTA_OLYMPICS=0 leaves (i) out (printed, not counted).
#   (j) exact    the exact permutation check of activation (lemma L3b,
#                Harness/Sbm11PermCheck.lean, PermSet.perms_same): the gate
#                fixture is admitted with groups of 1, 3 and 1,000,000 PSO rows
#                (SBM11_VERIFY_GROUP_ROWS); a copy whose POS files come from a
#                pack of the fixture with one quad changed (same dictionary, same
#                row count, another quad set; resealed) is refused by the exact
#                check with the digest comparison off (SBM11_VERIFY_DIGEST=0)
#                and by the digest with it on; no bucket directory is left.
#   (k) scaling  tests/sbm11/phase2_scaling.sh: packer phase 2 (the k-way
#                merge of the term runs) on synthetic sources of 1, 2 and 4
#                million lines (244 to 836 term runs; median of 3 runs each,
#                CPU time of the merge thread); 4n at most 6.25 times n, 2.5
#                per doubling (https://github.com/danbri/factoidal/issues/804;
#                about 2 minutes). SBM11_PHASE2_SCALING=0 leaves (k) out
#                (printed, not counted).
#   (g) tamper   a copy of the generation with one byte changed in a block
#                frame of spo.prb1 (manifest and sidecars kept): `scan` and
#                `query` must be refused under merkle (and by default, the
#                copy not being activated), and must answer with exit 0 and
#                other rows under none: the documented limit of none is
#                pinned, so a change of either behaviour fails the run.
#
# Usage: tests/sbm11/run.sh [GEN]   (default /home/user/qlvr-work/sbm11/s3/wfull,
# an activated olympics generation; tests/sbm11/stage3_check.sh makes one).
# Exit 0 only when every check passes; 2 when an input is missing.
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="$ROOT/formal/lean4/.lake/build/bin"
WORK="${QLVR_WORK:-/home/user/qlvr-work}"
GEN="${1:-$WORK/sbm11/s3/wfull}"
ORACLE="$WORK/oracle"
for need in "$BIN/l4sbm11" "$BIN/l4sbm11-pack" "$BIN/l4factoidal" "$GEN" "$ORACLE"; do
  if [ ! -e "$need" ]; then echo "missing: $need" >&2; exit 2; fi
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-run.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
PASS=0; FAIL=0
record() { # record <part> <name> <ok:0|1> <detail>
  if [ "$3" = 0 ]; then PASS=$((PASS + 1)); printf 'ok   %-8s %-34s %s\n' "$1" "$2" "$4"
  else FAIL=$((FAIL + 1)); printf 'FAIL %-8s %-34s %s\n' "$1" "$2" "$4"; fi
}

echo "=== (a) oracle queries"
OP=0; OF=0
for rq in "$ROOT"/tests/qlvr/queries/q*.rq; do
  n="$(basename "$rq" .rq)"
  rc=0
  timeout 600 "$BIN/l4sbm11" query "$GEN" --file "$rq" >"$TMP/$n.srj" 2>"$TMP/$n.err" || rc=$?
  if [ "$rc" -ne 0 ]; then
    record oracle "$n" 1 "exit $rc: $(tail -1 "$TMP/$n.err")"; OF=$((OF + 1)); continue
  fi
  v="$(python3 -I "$HERE/compare_oracle.py" "$ORACLE/$n.srj" "$TMP/$n.srj" "$rq" "$n" 2>&1)"; c=$?
  p="$(grep -o 'path=[a-z]*' "$TMP/$n.err")"
  record oracle "$n" "$c" "$p; $(printf '%s' "$v" | head -1)"
  if [ "$c" = 0 ]; then OP=$((OP + 1)); else OF=$((OF + 1)); fi
done
echo "oracle: $OP pass, $OF fail (out of $((OP + OF)))"

echo "=== (b) key printer against jsonOfTerm"
for rq in "$ROOT"/tests/qlvr/queries/q*.rq; do
  n="$(basename "$rq" .rq)"
  timeout 600 "$BIN/l4sbm11" query "$GEN" --file "$rq" --reference-render >"$TMP/$n.ref" 2>/dev/null
  if cmp -s "$TMP/$n.srj" "$TMP/$n.ref"; then record render "$n" 0 "byte-identical ($(wc -c <"$TMP/$n.srj") bytes)"
  else record render "$n" 1 "outputs differ"; fi
done

echo "=== (c) the id path against the reference fallback"
for rq in "$ROOT"/tests/qlvr/queries/q*.rq; do
  n="$(basename "$rq" .rq)"
  case $n in q0[3-9]*|q1[0-8]*) ;; *) continue ;; esac
  rc=0
  timeout 600 "$BIN/l4sbm11" query "$GEN" --file "$rq" --reference >"$TMP/$n.fb" 2>"$TMP/$n.fberr" || rc=$?
  if [ "$rc" -ne 0 ]; then record ids-ref "$n" 1 "fallback exit $rc"; continue; fi
  v="$(python3 -I "$HERE/compare_answers.py" "$TMP/$n.srj" "$TMP/$n.fb" 0)"
  case "$v" in equal*) record ids-ref "$n" 0 "$v; $(grep -o 'quads=[0-9]*' "$TMP/$n.fberr")" ;; *) record ids-ref "$n" 1 "$v" ;; esac
done

echo "=== (d) gate fixture: id path and reference fallback against l4factoidal"
G="$TMP/gate"
rc=0
"$BIN/l4sbm11-pack" "$HERE/gate/gate.nq" "$G/gen" --workers 1 >"$TMP/gpack.log" 2>&1 || rc=$?
[ "$rc" -eq 0 ] && { "$BIN/l4sbm11" activate "$G" gen >"$TMP/gact.log" 2>&1 || rc=$?; }
if [ "$rc" -ne 0 ]; then
  record gate pack-activate 1 "exit $rc: $(tail -1 "$TMP/gpack.log" "$TMP/gact.log" 2>/dev/null | tr '\n' ' ')"
else
  for rq in "$HERE"/gate/*.rq; do
    n="$(basename "$rq" .rq)"
    qb="file://$(realpath "$rq")"
    rc=0
    timeout 120 "$BIN/l4sbm11" query "$G" --file "$rq" --base "$qb" >"$TMP/g-$n.got" 2>"$TMP/g-$n.err" || rc=$?
    if [ "$rc" -ne 0 ]; then record gate "$n" 1 "exit $rc: $(tail -1 "$TMP/g-$n.err")"; continue; fi
    rrc=0
    timeout 120 "$BIN/l4factoidal" query "$HERE/gate/gate.nq" --format nquads --query "$rq" \
      >"$TMP/g-$n.want" 2>/dev/null || rrc=$?
    v="$(python3 -I "$HERE/compare_answers.py" "$TMP/g-$n.got" "$TMP/g-$n.want" "$rrc")"
    p="$(grep -o 'path=[a-z]*' "$TMP/g-$n.err")"
    want_path=path=ids; case $n in ref-*) want_path=path=reference ;; esac
    if [ "$p" != "$want_path" ]; then record gate "$n" 1 "$p, expected $want_path"
    else case "$v" in equal*) record gate "$n" 0 "$p; $v" ;; *) record gate "$n" 1 "$p; $v" ;; esac
    fi
  done
fi

echo "=== (e) decoder checks on every PRM1 file and frame"
if out="$("$BIN/l4sbm11" prm-check "$GEN" 2>&1)"; then record checks prm-check 0 "$(printf '%s' "$out" | tr '\n' ' ' | head -c 150)"
else record checks prm-check 1 "$out"; fi
if out="$("$BIN/l4sbm11" frame-check "$GEN" 2>&1)"; then record checks frame-check 0 "$out"
else record checks frame-check 1 "$out"; fi

echo "=== (f) the same answers under --verify merkle and --verify none"
for rq in "$ROOT"/tests/qlvr/queries/q*.rq; do
  n="$(basename "$rq" .rq)"
  rm=0; rn=0
  timeout 600 "$BIN/l4sbm11" query "$GEN" --file "$rq" --verify merkle >"$TMP/$n.vm" 2>"$TMP/$n.vmerr" || rm=$?
  timeout 600 "$BIN/l4sbm11" query "$GEN" --file "$rq" --verify none >"$TMP/$n.vn" 2>"$TMP/$n.vnerr" || rn=$?
  if [ "$rm" -ne 0 ] || [ "$rn" -ne 0 ]; then record verify "$n" 1 "exit merkle $rm, none $rn"
  elif ! grep -q 'verify=merkle' "$TMP/$n.vmerr" || ! grep -q 'verify=none' "$TMP/$n.vnerr"; then
    record verify "$n" 1 "stderr does not name the verify option"
  elif cmp -s "$TMP/$n.vm" "$TMP/$n.vn"; then
    record verify "$n" 0 "byte-identical; fetched merkle $(grep -o 'range bytes fetched [0-9]*' "$TMP/$n.vmerr" | grep -o '[0-9]*$'), none $(grep -o 'range bytes fetched [0-9]*' "$TMP/$n.vnerr" | grep -o '[0-9]*$')"
  else record verify "$n" 1 "outputs differ"; fi
done

echo "=== (g) a changed byte in a block frame: refused under merkle, NOT detected under none"
# The documented limit of --verify none (https://github.com/danbri/factoidal/issues/796):
# it relies on activation, so a byte changed after activation is read as data.
# Both halves are asserted, so a change of either behaviour turns this RED.
SRC="$GEN"; [ -f "$GEN/CURRENT" ] && SRC="$GEN/$(cat "$GEN/CURRENT")"
T="$TMP/tamper"
rc=0; cp -r "$SRC" "$T" || rc=$?
if [ "$rc" -ne 0 ]; then record tamper copy 1 "cp exit $rc"
else
  # SPO block 0, column 2 (objects, a delta frame): the object of row 1 (the
  # second quad of the first subject) becomes another id k away, the deltas
  # of rows 1 and 2 re-encoded with the same byte length. Rows stay strictly
  # increasing and the first and last rows, which the reader compares with
  # PRM1, do not change, so the frame decodes without error.
  if ! python3 -I -c 'import sys
d = sys.argv[1]
m = open(d + "/spo.prm1", "rb").read()
le = lambda b: int.from_bytes(b, "little")
e = 22
rows, off = le(m[e + 64:e + 68]), le(m[e + 68:e + 76])
l0, l1, l2 = le(m[e + 76:e + 80]), le(m[e + 80:e + 84]), le(m[e + 84:e + 88])
b = bytearray(open(d + "/spo.prb1", "rb").read())
f = off + l0 + l1
if b[f] != 2 or rows < 3: sys.exit("SPO block 0 column 2 is not a delta frame of 3 or more rows")
def var(n):
    out = [n % 128]; n //= 128
    while n: out.append(128 | (n % 128)); n //= 128
    return bytes(reversed(out))
zz = lambda p, v: 2 * (v - p) if p <= v else 2 * (p - v) - 1
vals, i, prev = [], f + 1, 0
for _ in range(rows):
    z = 0
    while True:
        z = z * 128 + (b[i] & 127); i += 1
        if b[i - 1] < 128: break
    prev = prev + z // 2 if z % 2 == 0 else prev - (z + 1) // 2
    vals.append(prev)
old = b"".join(var(zz(p, v)) for p, v in zip([0] + vals, vals))
if old != bytes(b[f + 1:f + l2]): sys.exit("the frame does not re-encode")
for k in (1, -1, 2, -2, 3, -3, 4, -4):
    new = list(vals); new[1] += k
    enc = b"".join(var(zz(p, v)) for p, v in zip([0] + new, new))
    if len(enc) == len(old):
        b[f + 1:f + l2] = enc
        open(d + "/spo.prb1", "wb").write(b); sys.exit(0)
sys.exit("no change of the same length")' "$T" 2>"$TMP/t-flip.err"; then
    record tamper flip 1 "$(cat "$TMP/t-flip.err")"
  fi
  sm=0; "$BIN/l4sbm11" scan "$T" spo --ids --limit 5 --verify merkle >"$TMP/t-m.out" 2>"$TMP/t-m.err" || sm=$?
  if [ "$sm" -ne 0 ] && grep -q 'refused' "$TMP/t-m.err"; then record tamper scan-merkle 0 "refused (exit $sm)"
  else record tamper scan-merkle 1 "exit $sm: $(tail -1 "$TMP/t-m.err")"; fi
  sd=0; "$BIN/l4sbm11" scan "$T" spo --ids --limit 5 >"$TMP/t-d.out" 2>"$TMP/t-d.err" || sd=$?
  if [ "$sd" -ne 0 ] && grep -q 'verify=merkle\|refused' "$TMP/t-d.err"; then record tamper default-not-activated 0 "a directory no CURRENT names: merkle, refused"
  else record tamper default-not-activated 1 "exit $sd: $(tail -1 "$TMP/t-d.err")"; fi
  "$BIN/l4sbm11" scan "$SRC" spo --ids --limit 5 --verify none >"$TMP/t-orig.out" 2>/dev/null
  sn=0; "$BIN/l4sbm11" scan "$T" spo --ids --limit 5 --verify none >"$TMP/t-n.out" 2>"$TMP/t-n.err" || sn=$?
  if [ "$sn" -eq 0 ] && [ -s "$TMP/t-n.out" ] && ! cmp -s "$TMP/t-n.out" "$TMP/t-orig.out"; then
    record tamper scan-none 0 "not detected: exit 0, other ids than the original (documented limit)"
  else record tamper scan-none 1 "exit $sn; expected exit 0 and changed rows"; fi
  # the first subject of SPO, bound: the plan reads SPO block 0
  S="$("$BIN/l4sbm11" scan "$SRC" spo --limit 1 --verify none 2>/dev/null | sed 's/^\(<[^>]*>\).*/\1/')"
  Q="SELECT ?p ?o WHERE { $S ?p ?o }"
  qm=0; "$BIN/l4sbm11" query "$T" "$Q" --verify merkle >"$TMP/t-qm.out" 2>"$TMP/t-qm.err" || qm=$?
  if [ "$qm" -ne 0 ] && grep -q 'refused' "$TMP/t-qm.err"; then record tamper query-merkle 0 "refused (exit $qm)"
  else record tamper query-merkle 1 "exit $qm: $(tail -1 "$TMP/t-qm.err")"; fi
  "$BIN/l4sbm11" query "$SRC" "$Q" --verify none >"$TMP/t-qo.out" 2>/dev/null
  qn=0; "$BIN/l4sbm11" query "$T" "$Q" --verify none >"$TMP/t-qn.out" 2>"$TMP/t-qn.err" || qn=$?
  if [ "$qn" -eq 0 ] && ! cmp -s "$TMP/t-qn.out" "$TMP/t-qo.out"; then
    record tamper query-none 0 "not detected: exit 0, other answer than the original (documented limit)"
  else record tamper query-none 1 "exit $qn: $(tail -1 "$TMP/t-qn.err"); expected exit 0 and a changed answer"; fi
fi
if [ -f "$GEN/CURRENT" ]; then
  "$BIN/l4sbm11" query "$GEN" 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }' --explain >/dev/null 2>"$TMP/def.err"
  if grep -q 'plan: verify=none (default' "$TMP/def.err"; then record tamper default-activated 0 "GEN has CURRENT: verify=none by default"
  else record tamper default-activated 1 "$(grep 'verify' "$TMP/def.err" | head -1)"; fi
fi

# --- stage 5 ----------------------------------------------------------------
# run_q <gen> <rq> <out> <err>: one query on a generation, exit code in $QRC
run_q() {
  QRC=0
  timeout 600 "$BIN/l4sbm11" query "$1" --file "$2" --base "file://$(realpath "$2")" >"$3" 2>"$4" || QRC=$?
}
# want_path <name>: the path a query named ref-* must take (path=reference);
# every other query, path=ids
want_path() { case $1 in ref-*) echo path=reference ;; *) echo path=ids ;; esac; }
ARTS="dict.gdv1 dict.gdx1 pso.prb1 pso.prm1 pos.prb1 pos.prm1 spo.prb1 spo.prm1 osp.prb1 osp.prm1"
# same_artifacts <dirA> <dirB>: every artifact and its .merkle sidecar byte-identical
same_artifacts() {
  for a in $ARTS; do
    cmp -s "$1/$a" "$2/$a" || { echo "$a differs"; return 1; }
    cmp -s "$1/$a.merkle" "$2/$a.merkle" || { echo "$a.merkle differs"; return 1; }
  done
  echo "10 artifacts and their .merkle sidecars byte-identical"
}

echo "=== (h) delta overlay on the gate fixture"
H="$TMP/delta"
mkdir -p "$H"
"$BIN/l4sbm11" canon "$HERE/gate/gate.nq" >"$H/base.nq"
NB="$(python3 -I "$HERE/delta_apply.py" "$H/base.nq" "$HERE/delta/gate-ops.txt" "$H/ops")"
rc=0
"$BIN/l4sbm11-pack" "$H/base.nq" "$H/col/gen" --workers 1 >"$H/pack.log" 2>&1 || rc=$?
[ "$rc" -eq 0 ] && { "$BIN/l4sbm11" activate "$H/col" gen >"$H/act.log" 2>&1 || rc=$?; }
GQ="$(ls "$HERE"/gate/*.rq "$HERE"/delta/*.rq)"
# check_all <gen> <reference.nq> <label> [<directory to keep the answers in>]
check_all() {
  local bad="" n=0 nq rrc v
  for rq in $GQ; do
    nq="$(basename "$rq" .rq)"
    n=$((n + 1))
    run_q "$1" "$rq" "$H/got.srj" "$H/got.err"
    if [ "$QRC" -ne 0 ]; then bad="$bad $nq(exit $QRC)"; continue; fi
    [ -n "${4:-}" ] && cp "$H/got.srj" "$4/$nq.srj"
    rrc=0
    timeout 120 "$BIN/l4factoidal" query "$2" --format nquads --query "$rq" >"$H/want.srj" 2>/dev/null || rrc=$?
    v="$(python3 -I "$HERE/compare_answers.py" "$H/got.srj" "$H/want.srj" "$rrc")"
    case "$v" in equal*) ;; *) bad="$bad $nq($v)"; continue ;; esac
    if [ "$(grep -o 'path=[a-z]*' "$H/got.err")" != "$(want_path "$nq")" ]; then bad="$bad $nq(path)"; fi
  done
  if [ -z "$bad" ]; then record delta "$3" 0 "$n queries equal to the reference engine, each on its path"
  else record delta "$3" 1 "failed:$bad"; fi
}
if [ "$rc" -ne 0 ]; then
  record delta pack-activate 1 "exit $rc"
else
  for k in $(seq 1 "$NB"); do
    urc=0
    "$BIN/l4sbm11" update "$H/col" "$(cat "$H/ops/batch-$k.ru")" >"$H/upd-$k.log" 2>&1 || urc=$?
    if [ "$urc" -ne 0 ]; then record delta "batch-$k-update" 1 "exit $urc: $(tail -1 "$H/upd-$k.log")"; continue; fi
    check_all "$H/col" "$H/ops/after-$k.nq" "batch-$k"
  done
  # the overlay's answers after the last batch, kept for the comparisons below
  mkdir -p "$H/ans-overlay" "$H/ans-fresh"
  check_all "$H/col" "$H/ops/final.nq" "final-overlay" "$H/ans-overlay"
  rc=0
  "$BIN/l4sbm11-pack" "$H/ops/final.nq" "$H/fresh" --workers 1 >"$H/fresh.log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ]; then record delta fresh-pack 1 "exit $rc"; fi
  bad=""
  for rq in $GQ; do
    nq="$(basename "$rq" .rq)"
    run_q "$H/fresh" "$rq" "$H/ans-fresh/$nq.srj" "$H/f.err"
    v="$(python3 -I "$HERE/compare_answers.py" "$H/ans-overlay/$nq.srj" "$H/ans-fresh/$nq.srj" "$QRC")"
    case "$v" in equal*) ;; *) bad="$bad $nq($v)" ;; esac
  done
  if [ -z "$bad" ]; then record delta overlay-vs-fresh-pack 0 "$(echo $GQ | wc -w) queries: overlay answers equal a fresh pack of the updated data"
  else record delta overlay-vs-fresh-pack 1 "differ:$bad"; fi
  crc=0
  "$BIN/l4sbm11" compact "$H/col" "$H/col/gen2" >"$H/compact.log" 2>&1 || crc=$?
  if [ "$crc" -ne 0 ]; then record delta compact 1 "exit $crc: $(tail -1 "$H/compact.log")"
  else
    v="$(same_artifacts "$H/col/gen2" "$H/fresh")"; c=$?
    record delta compact-equals-fresh-pack "$c" "$v"
    "$BIN/l4sbm11" activate "$H/col" gen2 >"$H/act2.log" 2>&1 || record delta activate-compacted 1 "$(tail -1 "$H/act2.log")"
    check_all "$H/col" "$H/ops/final.nq" "compacted"
    run_q "$H/col" "$HERE/delta/ids-upd-count.rq" "$H/c.srj" "$H/c.err"
    if grep -q 'delta batches 0' "$H/c.err"; then record delta compacted-no-replay 0 "the compacted generation replays no batch"
    else record delta compacted-no-replay 1 "$(grep -o 'delta batches [0-9]*' "$H/c.err")"; fi
    urc=0
    "$BIN/l4sbm11" update "$H/col" 'INSERT DATA { <http://ex.org/after> <http://ex.org/name> "after compaction" }' >"$H/upd-after.log" 2>&1 || urc=$?
    "$BIN/l4sbm11" query "$H/col" 'SELECT ?n WHERE { <http://ex.org/after> <http://ex.org/name> ?n }' >"$H/after.srj" 2>/dev/null
    if [ "$urc" -eq 0 ] && grep -q 'epoch=2' "$H/upd-after.log" && grep -q 'after compaction' "$H/after.srj"; then
      record delta update-after-compaction 0 "epoch 2 batch committed and seen"
    else record delta update-after-compaction 1 "exit $urc: $(tail -1 "$H/upd-after.log")"; fi
  fi
  # the stage 5 limits, pinned: both must stay refused until they are implemented
  r1=0; "$BIN/l4sbm11" update "$H/col" 'DELETE WHERE { ?s <http://ex.org/name> ?n }' >"$H/r1.log" 2>&1 || r1=$?
  if [ "$r1" -eq 1 ] && grep -q 'refused' "$H/r1.log"; then record delta refuse-where 0 "DELETE WHERE refused (stage 5 limit)"
  else record delta refuse-where 1 "exit $r1: $(tail -1 "$H/r1.log")"; fi
  r2=0; "$BIN/l4sbm11" update "$H/col" 'INSERT DATA { _:b <http://ex.org/name> "blank" }' >"$H/r2.log" 2>&1 || r2=$?
  if [ "$r2" -eq 1 ] && grep -q 'refused' "$H/r2.log"; then record delta refuse-insert-bnode 0 "INSERT DATA with a blank node refused (stage 5 limit)"
  else record delta refuse-insert-bnode 1 "exit $r2: $(tail -1 "$H/r2.log")"; fi
fi

echo "=== (i) delta overlay and compaction on olympics"
OLY_SRC="$WORK/instance/olympics.nt"
if [ "${SBM11_DELTA_OLYMPICS:-1}" = 0 ]; then
  echo "(i) left out: SBM11_DELTA_OLYMPICS=0 (not counted)"
elif [ ! -f "$OLY_SRC" ]; then
  record olympics source 1 "missing: $OLY_SRC"
else
  O="$TMP/oly"
  SRCG="$GEN"; [ -f "$GEN/CURRENT" ] && SRCG="$GEN/$(cat "$GEN/CURRENT")"
  mkdir -p "$O/col" "$O/ans-overlay" "$O/ans-fresh"
  cp -r "$SRCG" "$O/col/gen" && rm -f "$O/col/gen/deltas.dlog" "$O/col/gen/compacted.epoch"
  "$BIN/l4sbm11" activate "$O/col" gen >"$O/act.log" 2>&1 || record olympics activate 1 "$(tail -1 "$O/act.log")"
  NO="$(python3 -I "$HERE/delta_apply.py" "$OLY_SRC" "$HERE/delta/olympics-ops.txt" "$O/ops" --final-only)"
  for k in $(seq 1 "$NO"); do
    urc=0
    "$BIN/l4sbm11" update "$O/col" "$(cat "$O/ops/batch-$k.ru")" >"$O/upd-$k.log" 2>&1 || urc=$?
    record olympics "batch-$k-update" "$urc" "$(tail -1 "$O/upd-$k.log" | cut -c1-140)"
  done
  OQ="$(ls "$ROOT"/tests/qlvr/queries/q*.rq "$HERE"/delta/olympics/*.rq)"
  for rq in $OQ; do
    nq="$(basename "$rq" .rq)"
    run_q "$O/col" "$rq" "$O/ans-overlay/$nq.srj" "$O/ans-overlay/$nq.err"
  done
  rows() { python3 -I -c 'import json,sys; print(len(json.load(open(sys.argv[1]))["results"]["bindings"]))' "$1" 2>/dev/null; }
  n1="$(rows "$O/ans-overlay/ids-seen-insert.srj")"
  if [ "$n1" = 1 ]; then record olympics insert-seen 0 "1 row"; else record olympics insert-seen 1 "$n1 rows"; fi
  n0="$(rows "$O/ans-overlay/ids-not-seen-delete.srj")"
  if [ "$n0" = 0 ]; then record olympics delete-not-seen 0 "0 rows"; else record olympics delete-not-seen 1 "$n0 rows"; fi
  echo "    overlay q19: $(grep -o 'execution [0-9.]* ms; total [0-9.]* ms; peak RSS (VmHWM): [0-9]* kB' "$O/ans-overlay/q19-scan-bound-predicate-iri.err")"
  prc=0
  t0=$(date +%s%N)
  "$BIN/l4sbm11-pack" "$O/ops/final.nq" "$O/fresh" >"$O/fresh.log" 2>&1 || prc=$?
  pwall=$(( ($(date +%s%N) - t0) / 1000000 ))
  rm -f "$O/ops/final.nq"
  crc=0
  t0=$(date +%s%N)
  "$BIN/l4sbm11" compact "$O/col" "$O/col/gen2" >"$O/compact.log" 2>&1 || crc=$?
  cwall=$(( ($(date +%s%N) - t0) / 1000000 ))
  if [ "$prc" -ne 0 ] || [ "$crc" -ne 0 ]; then
    record olympics pack-and-compact 1 "pack exit $prc, compact exit $crc: $(tail -1 "$O/compact.log")"
  else
    pms="$(grep -o 'total-ms=[0-9.]*' "$O/fresh.log" | cut -d= -f2)"
    cms="$(grep -o 'total-ms=[0-9.]*' "$O/compact.log" | cut -d= -f2)"
    ratio="$(python3 -I -c 'import sys; print(round(float(sys.argv[2]) / float(sys.argv[1]), 3))' "$pms" "$cms")"
    if python3 -I -c 'import sys; sys.exit(0 if float(sys.argv[1]) <= 1.2 else 1)' "$ratio"; then
      record olympics compact-time 0 "compact $cms ms, fresh pack $pms ms, ratio $ratio (limit 1.2); load $(cut -d' ' -f1-3 /proc/loadavg)"
    else
      record olympics compact-time 1 "compact $cms ms, fresh pack $pms ms, ratio $ratio: above 1.2"
    fi
    echo "    pack:    process wall $pwall ms; $(grep -o 'peak-rss=[0-9]* kB' "$O/fresh.log"); $(grep -o 'total-on-disk=[0-9]*' "$O/fresh.log")"
    echo "    compact: process wall $cwall ms; $(grep -o 'peak-rss=[0-9]* kB' "$O/compact.log"); $(grep -o 'total-on-disk=[0-9]*' "$O/compact.log")"
    grep 'ms=' "$O/compact.log" | sed 's/^/    /'
    v="$(same_artifacts "$O/col/gen2" "$O/fresh")"; c=$?
    record olympics compact-equals-fresh-pack "$c" "$v"
    bad=""
    for rq in $OQ; do
      nq="$(basename "$rq" .rq)"
      run_q "$O/fresh" "$rq" "$O/ans-fresh/$nq.srj" "$O/ans-fresh/$nq.err"
      v="$(python3 -I "$HERE/compare_answers.py" "$O/ans-overlay/$nq.srj" "$O/ans-fresh/$nq.srj" "$QRC")"
      case "$v" in equal*) ;; *) bad="$bad $nq($v)" ;; esac
      p="$(grep -o 'path=[a-z]*' "$O/ans-overlay/$nq.err")"
      case $nq in ref-*|ids-*) [ "$p" = "$(want_path "$nq")" ] || bad="$bad $nq($p)" ;; esac
    done
    if [ -z "$bad" ]; then record olympics overlay-vs-fresh-pack 0 "$(echo $OQ | wc -w) queries equal (q01 to q21 and the delta queries)"
    else record olympics overlay-vs-fresh-pack 1 "differ:$bad"; fi
  fi
fi

echo "=== (j) the exact permutation check of activation (lemma L3b)"
J="$TMP/exact"
mkdir -p "$J"
# B: the gate fixture with one quad changed to another quad over the same
# terms (same dictionary, same row count, another quad set)
sed 's|^<http://ex.org/a> <http://ex.org/knows> <http://ex.org/b> \.$|<http://ex.org/a> <http://ex.org/knows> <http://ex.org/d> .|' \
  "$HERE/gate/gate.nq" >"$J/b.nq"
if cmp -s "$HERE/gate/gate.nq" "$J/b.nq"; then
  record exact fixture 1 "the sed did not change gate.nq"
else
  rc=0
  "$BIN/l4sbm11-pack" "$HERE/gate/gate.nq" "$J/a" --workers 1 --block-rows 2 >"$J/pa.log" 2>&1 || rc=$?
  "$BIN/l4sbm11-pack" "$J/b.nq" "$J/b" --workers 1 --block-rows 2 >"$J/pb.log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ]; then record exact pack 1 "exit $rc"
  elif ! cmp -s "$J/a/dict.gdv1" "$J/b/dict.gdv1"; then record exact same-dictionary 1 "GDV1 differs"
  else
    # blocks of two rows; groups of 1 row (one block each), 3 rows, all rows
    for gr in 1 3 1000000; do
      vrc=0
      SBM11_VERIFY_GROUP_ROWS=$gr "$BIN/l4sbm11" verify "$J/a" >"$J/va-$gr.log" 2>&1 || vrc=$?
      if [ "$vrc" -eq 0 ] && grep -q "exact permutation check: buckets=[0-9]* group-rows=$gr digest=on failures=0" "$J/va-$gr.log"; then
        record exact "admitted-group-rows-$gr" 0 "$(grep -o 'buckets=[0-9]*' "$J/va-$gr.log")"
      else record exact "admitted-group-rows-$gr" 1 "exit $vrc: $(grep 'FAIL\|exact' "$J/va-$gr.log" | head -2 | tr '\n' ' ')"; fi
    done
    # A with the POS files of B: same row count, same ids, another quad set
    cp -r "$J/a" "$J/t"
    cp "$J/b/pos.prb1" "$J/b/pos.prm1" "$J/t/"
    "$BIN/l4sbm11" reseal "$J/t" >/dev/null 2>&1
    for gr in 1 1000000; do
      vrc=0
      SBM11_VERIFY_DIGEST=0 SBM11_VERIFY_GROUP_ROWS=$gr "$BIN/l4sbm11" verify "$J/t" >"$J/vt-$gr.log" 2>&1 || vrc=$?
      if [ "$vrc" -ne 0 ] && grep -q "FAIL: pos .*\(other quads than pso\|rows in bucket\)" "$J/vt-$gr.log" \
          && grep -q "digest=off failures=1" "$J/vt-$gr.log"; then
        record exact "refused-digest-off-$gr" 0 "$(grep -o 'FAIL: pos.*' "$J/vt-$gr.log" | head -1)"
      else record exact "refused-digest-off-$gr" 1 "exit $vrc: $(grep 'FAIL\|exact' "$J/vt-$gr.log" | head -2 | tr '\n' ' ')"; fi
    done
    vrc=0
    "$BIN/l4sbm11" verify "$J/t" >"$J/vt-d.log" 2>&1 || vrc=$?
    if [ "$vrc" -ne 0 ] && grep -q "holds other quads than pso (digest)" "$J/vt-d.log"; then
      record exact refused-digest-on 0 "the digest refuses it too"
    else record exact refused-digest-on 1 "exit $vrc"; fi
    # no bucket directory is left next to the generation
    left="$(ls -d "$J"/*.verify-* 2>/dev/null | wc -l)"
    if [ "$left" = 0 ]; then record exact temp-removed 0 "no bucket directory left"
    else record exact temp-removed 1 "$left left"; fi
  fi
fi

echo "=== (k) packer merge scaling (issue 804)"
if [ "${SBM11_PHASE2_SCALING:-1}" = 0 ]; then
  echo "(k) left out: SBM11_PHASE2_SCALING=0 (not counted)"
else
  rc=0
  SBM11_WORK="$TMP/p2scale" L4_SBM11_PACK="$BIN/l4sbm11-pack" "$HERE/phase2_scaling.sh" >"$TMP/p2scale.log" 2>&1 || rc=$?
  grep -E '^(ok|FAIL) ' "$TMP/p2scale.log" | sed 's/^/     /'
  if [ "$rc" -eq 0 ]; then record scaling phase2-n-2n-4n 0 "$(grep -c '^ok' "$TMP/p2scale.log") assertions hold"
  else record scaling phase2-n-2n-4n 1 "exit $rc: $(grep -E '^FAIL' "$TMP/p2scale.log" | head -1)"; fi
fi

echo
echo "sbm11 stages 4 and 5: $PASS pass, $FAIL fail (out of $((PASS + FAIL)))"
[ "$FAIL" -eq 0 ]
