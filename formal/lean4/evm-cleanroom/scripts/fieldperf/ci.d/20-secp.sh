# Fast ECRECOVER: generic windowed scalar multiplication, the secp256k1 fast path, its differential check and timing.
set -euo pipefail
lake -f lakefile-fieldperf.toml build EVMCleanroom.Precompiles.ScalarMul EVMCleanroom.Precompiles.Secp256k1FieldFast \
  EVMCleanroom.Precompiles.Secp256k1Fast EVMCleanroom.Precompiles.Ecrecover
echo "RESULT secp modules built (theorems and build-time guards)"
lake -f lakefile-fieldperf.toml build evm-secpperf
for f in Secp256k1FieldFast Secp256k1Fast; do
  c=.lake/build/ir/EVMCleanroom/Precompiles/$f.c
  echo "$f.c: closure calls $(grep -c 'lean_apply_' "$c" || true), constructor allocations $(grep -c 'lean_alloc_ctor' "$c" || true), lines $(wc -l < "$c")"
done
.lake/build/bin/evm-secpperf 2000
