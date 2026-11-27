# The pairing checks on the limb tower (0x08, 0x0f, KZG): build with the build-time guards,
# closure-call check of the compiled C, run-time differential check against the Nat path,
# the published vectors through the router, and timings of the old and the new path.
set -uo pipefail
status=0
step() {
  echo "--- $*"
  local start=$SECONDS
  "$@" || { echo "RESULT pairing: step FAILED: $*"; status=1; }
  echo "TIMING pairing: $(( SECONDS - start )) s for: $*"
}
L="lake -f lakefile-fieldperf.toml build"
step $L EVMCleanroom.Precompiles.BN254Pairing
step $L EVMCleanroom.Precompiles.BLS12381Pairing
step $L EVMCleanroom.Precompiles.KZGPairing
step $L EVMCleanroom.Precompiles.FastPairingProofs
step $L evm-pairingperf
step $L evm-precompile
# Closure calls in the compiled C. The generic modules keep them in their unspecialised
# bodies; the curve modules hold the specialised code that runs. For each closure call,
# the function it is in.
for f in FastTower FastPairing BN254Pairing BLS12381Pairing KZGPairing; do
  c=.lake/build/ir/EVMCleanroom/Precompiles/$f.c
  [ -f "$c" ] || continue
  echo "RESULT pairing: $f.c closure calls $(grep -c 'lean_apply_' "$c" || true), lines $(wc -l < "$c")"
  case $f in BN254Pairing|BLS12381Pairing|KZGPairing)
    awk '/^(LEAN_EXPORT|static) [a-z_0-9A-Z]+\*? ?[a-zA-Z_0-9]+\(/ { fn=$0 } /lean_apply_/ { print "RESULT pairing: closure call in: " fn }' "$c" | sort | uniq -c | cut -c1-220 ;;
  esac
done
if [ -x .lake/build/bin/evm-pairingperf ]; then
  step .lake/build/bin/evm-pairingperf "${PAIRING_SCALE:-100}"
fi
if [ -x .lake/build/bin/evm-precompile ]; then
  vectors() {
    python3 scripts/precompiles/run-vectors.py --binary .lake/build/bin/evm-precompile --cache /tmp/precompile-vectors \
      > /tmp/pairing-vectors.json || return 1
    python3 -c 'import json,sys; x=json.load(open("/tmp/pairing-vectors.json")); assert x["status"]=="pass" and x["failed"]==0 and x["files"]>=30 and x["publishedCases"]>=3915 and x["differentialCases"]>=3000 and x["alteredOutputControls"]==x["alteredOutputControlsRejected"]>=20 and x["gasShortfallControls"]>=3300, x; print("RESULT pairing: vectors", {k: x[k] for k in ("status","failed","files","publishedCases","differentialCases","gasShortfallControls","alteredOutputControlsRejected")})'
  }
  step vectors
  report() {
    python3 scripts/precompiles/bench.py --binary "$1" --cache /tmp/precompile-vectors --repeats 5 --max-cases-per-file 40 \
      | python3 -c 'import json,sys; label=sys.argv[1]
for r in json.load(sys.stdin)["rows"]:
    if r["address"] in (8, 10, 15): print("TIMING bench %s %s: p50 %s us, p95 %s us, max %s us, %s cases, %s ns/gas" % (label, r["name"], r["p50_us"], r["p95_us"], r["max_us"], r["cases"], r["ns_per_gas_p50"]))' "$2"
  }
  [ -x .lake/build/bin/evm-pairingperf ] && step report .lake/build/bin/evm-pairingperf OLD
  step report .lake/build/bin/evm-precompile NEW
fi
exit $status
