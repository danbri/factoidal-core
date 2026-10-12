#!/usr/bin/env bash
#
# tests/sbm11/run.sh — SBM11 stage 4, SPARQL over a generation
# (https://github.com/danbri/factoidal/issues/790; tracking
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
#                EXISTS, MINUS, OPTIONAL with FILTER, sub-SELECT and the other
#                forms only the reference semantics decide (CLAUDE.md
#                anti-pattern 34).
#   (e) checks   `l4sbm11 prm-check` (the byte-array PRM1 decoder against the
#                list decoder of the round-trip theorem) and `l4sbm11
#                frame-check` (the word decoder against decodeColumnAt) on
#                every PRM1 file and every frame of the generation.
#   (f) verify   q01 to q21 answered with --verify merkle and --verify none
#                (https://github.com/danbri/factoidal/issues/796): the
#                outputs must be byte-identical. Parts (a) to (e) use the
#                CLI default (none when a CURRENT pointer names GEN).
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

echo
echo "sbm11 stage 4: $PASS pass, $FAIL fail (out of $((PASS + FAIL)))"
[ "$FAIL" -eq 0 ]
