# The limb fields: build, differential guard against the Nat definitions, time per operation.
set -euo pipefail
lake -f lakefile-fieldperf.toml build evm-fieldperf
for f in Limb Montgomery Secp256k1Field Curve; do
  c=.lake/build/ir/EVMCleanroom/Precompiles/$f.c
  echo "$f.c: closure calls $(grep -c 'lean_apply_' "$c" || true), constructor allocations $(grep -c 'lean_alloc_ctor' "$c" || true)"
done
.lake/build/bin/evm-fieldperf 2000000
