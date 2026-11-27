# Fast ECRECOVER: generic windowed scalar multiplication, the secp256k1 fast path, its differential check and timing.
set -euo pipefail
L="lake -f lakefile-fieldperf.toml"
$L build EVMCleanroom.Precompiles.ScalarMul EVMCleanroom.Precompiles.Secp256k1FieldFast
( ulimit -v 12000000; timeout 600 $L build EVMCleanroom.Precompiles.Secp256k1Glv ) || { echo "FAILURES Glv build"; exit 1; }
echo "RESULT Glv built"
P=EVMCleanroom/Precompiles/Secp256k1Point.lean
for cut in "def madd" "def padd" "def betaL" "end EVMCleanroom"; do
  n=$(grep -n "^$cut" $P | head -1 | cut -d: -f1)
  head -n $((n-1)) $P > /tmp/Probe.lean
  s=$(date +%s)
  ( ulimit -v 12000000; timeout 240 $L env lean -D profiler=true -D profiler.threshold=300 /tmp/Probe.lean > /tmp/probe.out 2>&1 ) && r=ok || r="exit $?"
  echo "RESULT probe up to '$cut': $r, $(( $(date +%s)-s )) s"
  grep -v "^$" /tmp/probe.out | grep -v "^	" | cut -c1-400 | head -25
done
exit 1
