# The group-operation precompiles on limbs (alt_bn128 add and mul, BLS12-381 add, multi-scalar
# multiplication, map to curve, subgroup checks, KZG helpers): build, differential run against the
# Nat definitions, published vectors through the router, and time per call, old beside new.
set -uo pipefail
status=0
rm -f /tmp/blsops-build.log
# Every module on its own, so one run reports the errors of all of them.
for module in LimbBytes Fp2Limb CurveFast LimbInverse LimbSquare BN254Fast BLS12381Fast BLS12381Msm BLS12381Map KZGFast; do
  start=$(date +%s)
  lake -f lakefile-fieldperf.toml build "EVMCleanroom.Precompiles.$module" 2>&1 | tee -a /tmp/blsops-build.log
  [ "${PIPESTATUS[0]}" = 0 ] || status=1
  echo "RESULT build $module: $(( $(date +%s) - start )) s, status so far $status"
done
[ "$status" = 0 ] || { echo "RESULT blsops: module build FAILURES"; exit 1; }
# The axioms printed by the modules (lake replays the lines of modules it did not rebuild).
python3 - <<'PY' || status=1
import re
text = open("/tmp/blsops-build.log").read().replace("\n ", " ")
found = {}
for name, _, axioms in re.findall(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text):
    found[name] = {a.strip() for a in axioms.split(",") if a.strip()}
allowed = {"propext", "Classical.choice", "Quot.sound"}
bad = {name: sorted(used - allowed) for name, used in found.items() if used - allowed}
print("RESULT blsops axioms: %d theorems printed, outside propext/Classical.choice/Quot.sound: %s" % (len(found), bad or "none"))
raise SystemExit(1 if bad or len(found) < 30 else 0)
PY
[ "$status" = 0 ] || { echo "RESULT blsops: axiom audit FAILURES"; exit 1; }
set -e
lake -f lakefile-fieldperf.toml build evm-blsops
for f in CurveFast BN254Fast BLS12381Fast BLS12381Msm BLS12381Map KZGFast; do
  c=.lake/build/ir/EVMCleanroom/Precompiles/$f.c
  echo "$f.c: closure calls $(grep -c 'lean_apply_' "$c" || true), constructor allocations $(grep -c 'lean_alloc_ctor' "$c" || true)"
  # Which functions still call through a closure (the generic copies are expected; a specialised one is not).
  awk '/^(LEAN_EXPORT|static) .*\(.*\) *\{$/ {name=$0} /lean_apply_/ {count[name]++} END {for (n in count) print "  closure calls " count[n] ": " substr(n, 1, 150)}' "$c" | sort | head -40
done
.lake/build/bin/evm-blsops
lake -f lakefile-fieldperf.toml build evm-precompile
python3 scripts/precompiles/run-vectors.py --binary .lake/build/bin/evm-precompile --cache /tmp/precompile-vectors \
  | tee .lake/precompile-vectors.json \
  | python3 -c 'import json,sys; x=json.load(sys.stdin); assert x["status"]=="pass" and x["failed"]==0 and x["files"]>=30 and x["publishedCases"]>=3915 and x["differentialCases"]>=3000 and x["alteredOutputControls"]==x["alteredOutputControlsRejected"]>=20 and x["gasShortfallControls"]>=3300, x; print("RESULT vectors through the router:", {k: x[k] for k in ("status","failed","files","publishedCases","differentialCases","gasShortfallControls","alteredOutputControlsRejected")})'
python3 scripts/precompiles/bench.py --binary .lake/build/bin/evm-precompile --cache /tmp/precompile-vectors --repeats 3 --max-cases-per-file 12 > /tmp/bench-new.json
# The router of the base commit, built in a copy of the tree with this build directory, for old beside new.
base=7fbcd099bc5384a4553d81396ec7d4a276bdbbe6
top=$(git rev-parse --show-toplevel)
here=$PWD
rm -rf /tmp/fp-base /tmp/bench-old.json && mkdir -p /tmp/fp-base
git -C "$top" fetch -q --depth 1 origin "$base" \
  && git -C "$top" archive "$base" formal/lean4/evm-cleanroom | tar -x -C /tmp/fp-base \
  && cp -r .lake /tmp/fp-base/formal/lean4/evm-cleanroom/.lake \
  && cd /tmp/fp-base/formal/lean4/evm-cleanroom \
  && lake -f lakefile-fieldperf.toml build evm-precompile >/tmp/fp-base-build.log 2>&1 \
  && python3 scripts/precompiles/bench.py --binary .lake/build/bin/evm-precompile --cache /tmp/precompile-vectors --repeats 3 --max-cases-per-file 12 > /tmp/bench-old.json \
  || echo "RESULT base router not built: bench.py rows below are for the new router only"
cd "$here"
# Process start: the limb modules add constants that are built when a program starts (Montgomery forms of the
# curve and isogeny constants); the fixed-base tables of the KZG helpers must not be among them.
python3 - <<'PY'
import os, subprocess, time
def start_ms(binary):
    if not os.path.exists(binary):
        return None
    times = []
    for _ in range(40):
        begin = time.perf_counter()
        subprocess.run([binary, "--run", "shanghaiPlus", "2", "72", "616263"], capture_output=True)
        times.append(time.perf_counter() - begin)
    return round(sorted(times)[len(times) // 2] * 1000, 3)
new = start_ms(".lake/build/bin/evm-precompile")
old = start_ms("/tmp/fp-base/formal/lean4/evm-cleanroom/.lake/build/bin/evm-precompile")
print("TIMING process start (one SHA-256 call, median of 40, ms): old %s, new %s" % (old, new))
if old is not None and new is not None and new > old + 3.0:
    print("RESULT blsops: process start grew by more than 3 ms, FAILURES")
    raise SystemExit(1)
PY
python3 - <<'PY'
import json, os
new = {r["address"]: r for r in json.load(open("/tmp/bench-new.json"))["rows"]}
old = {r["address"]: r for r in json.load(open("/tmp/bench-old.json"))["rows"]} if os.path.exists("/tmp/bench-old.json") else {}
for address in (6, 7, 10, 11, 12, 13, 14, 15, 16, 17):
    n = new.get(address)
    if n is None:
        continue
    o = old.get(address)
    before = "old p50 %s p95 %s max %s us; " % (o["p50_us"], o["p95_us"], o["max_us"]) if o else ""
    print("TIMING bench.py %s (%d cases): %snew p50 %s p95 %s max %s us, %s ns/gas at p50" % (
        n["name"], n["cases"], before, n["p50_us"], n["p95_us"], n["max_us"], n["ns_per_gas_p50"]))
PY
