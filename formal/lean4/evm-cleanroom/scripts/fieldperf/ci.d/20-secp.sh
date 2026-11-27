# Fast ECRECOVER: generic windowed scalar multiplication, the secp256k1 fast path, its differential check and timing.
set -euo pipefail
L="lake -f lakefile-fieldperf.toml"
$L build EVMCleanroom.Precompiles.ScalarMul EVMCleanroom.Precompiles.Secp256k1FieldFast EVMCleanroom.Precompiles.Secp256k1Glv
( ulimit -v 12000000; timeout 900 $L build EVMCleanroom.Precompiles.Secp256k1Point ) || { echo "FAILURES Point build"; exit 1; }
echo "RESULT Point built"
for f in scripts/fieldperf/probe/P*.lean; do
  s=$(date +%s)
  ( ulimit -v 4000000; timeout 100 $L env lean -D profiler=true -D profiler.threshold=200 $f > /tmp/probe.out 2>&1 ) && r=ok || r="exit $?"
  echo "RESULT probe $f: $r, $(( $(date +%s)-s )) s"
  grep -v "^$" /tmp/probe.out | grep -v "^	" | cut -c1-300 | head -8 || true
done
exit 1
[ "$r" = ok ] || exit 1
( ulimit -v 12000000; timeout 900 $L build EVMCleanroom.Precompiles.Secp256k1Fast EVMCleanroom.Precompiles.Ecrecover ) || { echo "FAILURES Fast build"; exit 1; }
echo "RESULT secp modules built (theorems and build-time guards)"
( ulimit -v 12000000; timeout 1200 $L build evm-secpperf ) || { echo "FAILURES exe build"; exit 1; }
for f in Secp256k1FieldFast Secp256k1Point Secp256k1Fast; do
  c=.lake/build/ir/EVMCleanroom/Precompiles/$f.c
  echo "$f.c: closure calls $(grep -c 'lean_apply_' "$c" || true), constructor allocations $(grep -c 'lean_alloc_ctor' "$c" || true), lines $(wc -l < "$c")"
done
.lake/build/bin/evm-secpperf 2000
