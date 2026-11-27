# BLS signature verification (public keys in G1, signatures in G2) and hashing to G2: build with
# the build-time guards, axiom audit, compiled-code checks, RFC 9380 vectors and differential run
# against the Nat definitions, the consensus-specification vectors, timing, the command line, and
# a scratch package that takes the kit by source (srcDir) without the EVM.
set -uo pipefail
status=0
log=$(mktemp)
for module in Precompiles.HashToCurveG2 Precompiles.BLSSignature BLSSig.Rfc9380Vectors BLSSig.Reference; do
  start=$SECONDS
  lake -f lakefile-fieldperf.toml build "EVMCleanroom.$module" 2>&1 | tee -a "$log"
  [ "${PIPESTATUS[0]}" = 0 ] || status=1
  echo "TIMING blssig build $module: $(( SECONDS - start )) s"
done
lake -f lakefile-fieldperf.toml build evm-blssig || status=1
[ "$status" = 0 ] || { echo "FAILURES blssig: build"; exit 1; }
# Axioms: every theorem of the two library modules ends in `#print axioms`; lake replays the
# messages for modules it did not rebuild. Only propext, Classical.choice and Quot.sound may appear.
python3 - "$log" <<'PY' || status=1
import re, sys
text = open(sys.argv[1], encoding="utf-8", errors="replace").read()
found = {}
for m in re.finditer(r"'(EVMCleanroom\.Precompiles\.(?:HashToCurve|BLSSignature)\.[A-Za-z0-9_'.]+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])", text):
    found[m.group(1)] = set(a.strip() for a in (m.group(3) or "").replace("\n", " ").split(",") if a.strip())
allowed = {"propext", "Classical.choice", "Quot.sound"}
bad = {name: sorted(ax - allowed) for name, ax in found.items() if ax - allowed}
print("RESULT blssig axioms: %d theorems audited, outside propext, Classical.choice, Quot.sound: %s" % (len(found), bad or "none"))
sys.exit(0 if len(found) >= 30 and not bad else 1)
PY
rm -f "$log"
# Compiled code: closure calls and surviving native recursion in the two library modules.
rm -rf /tmp/blssig-ir && mkdir -p /tmp/blssig-ir/EVMCleanroom/Precompiles
for f in HashToCurveG2 BLSSignature; do
  c=.lake/build/ir/EVMCleanroom/Precompiles/$f.c
  cp "$c" /tmp/blssig-ir/EVMCleanroom/Precompiles/
  echo "RESULT blssig $f.c: closure calls $(grep -c 'lean_apply_' "$c" || true), lines $(wc -l < "$c")"
  awk '/^(LEAN_EXPORT|static) .*\(.*\) *\{$/ { fn=$0 } /lean_apply_/ { print "RESULT blssig closure call in: " substr(fn, 1, 160) }' "$c" | sort | uniq -c | head -20
done
top=$(git rev-parse --show-toplevel)
python3 "$top/tools/lean-tail-recursion-audit.py" --ir-dir /tmp/blssig-ir --lean-dir . --json /tmp/blssig-tail.json > /tmp/blssig-tail.txt 2>&1 || true
python3 - <<'PY' || status=1
import json, sys
try:
    audit = json.load(open("/tmp/blssig-tail.json"))
except Exception as error:
    print("RESULT blssig tail-recursion audit did not produce a report: %s" % error); sys.exit(1)
rows = audit.get("rows", []); cycles = audit.get("cycles", [])
print("RESULT blssig tail-recursion audit: %s C files, %d recursive functions, %d cycles" % (audit.get("cfiles"), len(rows), len(cycles)))
for row in rows[:10]: print("  ", str(row)[:300])
sys.exit(0 if audit.get("cfiles") == 2 and not rows and not cycles else 1)
PY
# RFC 9380 vectors, differential run against the Nat reference, timing.
.lake/build/bin/evm-blssig --check "${BLSSIG_SCALE:-3}" || { echo "FAILURES blssig: check run"; status=1; }
# The consensus-specification and bls12-381-tests vectors, with altered-expectation controls.
python3 scripts/blssig/run-vectors.py --binary .lake/build/bin/evm-blssig > /tmp/blssig-vectors.json \
  && python3 -c 'import json; x=json.load(open("/tmp/blssig-vectors.json")); assert x["status"]=="pass" and x["failed"]==0 and x["cases"]==97 and x["alteredExpectationControls"]==x["alteredExpectationControlsReported"]==8, x; print("RESULT blssig published vectors:", x)' \
  || { echo "FAILURES blssig: published vectors"; cat /tmp/blssig-vectors.json; status=1; }
# The command line for cross-checks from other packages: one call, and a file of calls.
pk=b53d21a4cfd562c469cc81514d4ce5a6b577d8403d32a394dc265dd190b47fa9f829fdd7963afdf972e5e77854051f6f
msg=abababababababababababababababababababababababababababababababab
sig=ae82747ddeefe4fd64cf9cedb9b04ae3e8a43420cd255e3c7cd06a8d88b7c7f8638543719981c5d16fa3527c468c25f0026704a6951bde891360c7e8d12ddee0559004ccdbe6046b55bae1b257ee97f7cdb955773d7cf29adf3ccbb9975e4eb9
inf=c0$(printf '0%.0s' $(seq 1 190))
printf '%s %s %s\n0x%s 0x%s00 0x%s\n%s - %s\nc0%s %s %s\n%s %s %s\nzz %s %s\n' \
  "$pk" "$msg" "$sig" "$pk" "$msg" "$sig" "$pk" "$inf" "$(printf '0%.0s' $(seq 1 94))" "$msg" "$sig" "$pk" "$msg" "${sig%??}" "$msg" "$sig" > /tmp/blssig-lines.txt
got=$(.lake/build/bin/evm-blssig --verify "0x$pk" "$msg" "$sig"; .lake/build/bin/evm-blssig --verify-file /tmp/blssig-lines.txt)
want=$(printf 'true\ntrue\nfalse\nfalse\ninvalid\ninvalid\nbadhex')
if [ "$got" = "$want" ]; then echo "RESULT blssig command line: --verify and --verify-file give true, false, invalid as expected"
else echo "FAILURES blssig: command line gave: $(echo "$got" | tr '\n' ' ')"; status=1; fi
# Another package takes the kit by source.
if [ "${BLSSIG_SKIP_PROBE:-0}" = 1 ]; then echo "RESULT blssig srcDir probe: skipped in this run"
else bash scripts/blssig/srcdir-probe.sh || { echo "FAILURES blssig: srcDir probe"; status=1; }; fi
[ "$status" = 0 ] && echo "RESULT blssig: all checks passed" || echo "FAILURES blssig"
exit $status
