#!/usr/bin/env bash
#
# tests/sbm11/medium_ops.sh — the SBM11 wasm-dispatch ops (sbm11Open,
# sbm11Query, sbm11Close; Wasm/Ops/Sbm11.lean) against `l4sbm11 query`, on
# the same generation (https://github.com/danbri/factoidal/issues/1009 KR1).
#
# For each fixture (tests/sbm11/gate/gate.nq with tests/sbm11/gate/*.rq, and
# tests/sbm11/gate/samegraphs/data.nq with its queries): `l4sbm11-pack` and
# `l4sbm11 activate` make a collection root; `l4sbm11 query ROOT` answers
# each query (--verify default); `l4wasm-cli callseq` runs sbm11Open ROOT,
# one sbm11Query per query (the query file's IRI as base) and sbm11Close in
# one process, through the dispatch entry the wasm module serves, with the
# native realisation of the medium (ffi/l4_medium.c: POSIX pread of
# ROOT/name). tests/sbm11/compare_ops.py compares the answers.
#
# NOT a W3C result, and NOT the KR1 exit (census on olympics and the DBpedia
# slice, which need the bench data); it checks that the ops and the native
# command give the same answers on the gate fixtures.
# Exit 0 only when every query matches; 2 when a binary is missing.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="$ROOT/formal/lean4/.lake/build/bin"
for b in l4sbm11 l4sbm11-pack l4wasm-cli; do
  [ -x "$BIN/$b" ] || { echo "missing: $BIN/$b" >&2; exit 2; }
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-ops.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
run_fixture() {
  local tag="$1" fix="$2" qdir="$3" G="$TMP/$1" rc=0
  mkdir -p "$G"
  "$BIN/l4sbm11-pack" "$fix" "$G/gen" --workers 1 >"$G.pack.log" 2>&1 || rc=$?
  [ "$rc" -eq 0 ] && { "$BIN/l4sbm11" activate "$G" gen >"$G.act.log" 2>&1 || rc=$?; }
  if [ "$rc" -ne 0 ]; then echo "FAIL $tag: pack or activate exit $rc"; return; fi
  : >"$G.names"
  python3 -I - "$G" "$qdir" "$G.seq.json" "$G.names" <<'PY'
import glob, json, os, sys
g, qdir, seq, names = sys.argv[1:5]
calls = [["sbm11Open", [g]]]
with open(names, "w") as out:
    for rq in sorted(glob.glob(os.path.join(qdir, "*.rq"))):
        name = os.path.basename(rq)[:-3]
        base = "file://" + os.path.realpath(rq)
        calls.append(["sbm11Query", ["sbm11-1", open(rq, encoding="utf-8").read(), json.dumps({"base": base})]])
        out.write(name + "\n")
calls.append(["sbm11Close", ["sbm11-1"]])
json.dump(calls, open(seq, "w"))
PY
  while read -r n; do
    timeout 120 "$BIN/l4sbm11" query "$G" --file "$qdir/$n.rq" --base "file://$(realpath "$qdir/$n.rq")" \
      >"$G/$n.got" 2>"$G/$n.err" || echo "native exit $? on $n" >>"$G.native.log"
  done <"$G.names"
  timeout 600 "$BIN/l4wasm-cli" callseq "$G.seq.json" >"$G.envs" 2>"$G.ops.err" || { echo "FAIL $tag: callseq exit $?"; return; }
  echo "== $tag"
  python3 -I "$HERE/compare_ops.py" "$G.envs" "$G.names" "$G"
}
run_fixture gate "$HERE/gate/gate.nq" "$HERE/gate" | tee "$TMP/gate.out"
run_fixture samegraphs "$HERE/gate/samegraphs/data.nq" "$HERE/gate/samegraphs" | tee "$TMP/samegraphs.out"
# the totals of both fixtures; a fixture that did not reach the comparison
# counts as one failure
read -r P F N < <(cat "$TMP/gate.out" "$TMP/samegraphs.out" | python3 -I -c '
import re, sys
p = f = n = 0
text = sys.stdin.read()
for m in re.finditer(r"(\d+) pass, (\d+) fail \(out of (\d+)\)", text):
    p += int(m.group(1)); f += int(m.group(2)); n += int(m.group(3))
f += text.count("FAIL gate:") + text.count("FAIL samegraphs:")
print(p, f, p + f)')
echo "sbm11 medium ops: $P pass, $F fail, 0 expected-fail (out of $N)"
[ "$F" -eq 0 ]
