# Proofs that the limb primitives, the four-limb routines and the secp256k1 base field
# compute the Nat definitions. Each module is built on its own so that every failure is reported.
set -uo pipefail
fail=0
for m in OmegaProbe LimbProofs LimbU256Proofs; do
  start=$(date +%s)
  lake -f lakefile-fieldperf.toml build EVMCleanroom.Precompiles.$m || fail=1
  echo "TIMING proofs-a $m $(( $(date +%s) - start )) s"
done
if [ "$fail" != 0 ]; then echo "FAILURES proofs-a"; exit 1; fi
echo "RESULT proofs-a: all proof modules built"
