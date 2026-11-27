# Proofs that Montgomery arithmetic on four and six limbs computes the Nat definitions.
# Each module is built on its own so that every failure is reported.
set -uo pipefail
fail=0
for m in MontgomeryMath; do
  start=$(date +%s)
  lake -f lakefile-fieldperf.toml build EVMCleanroom.Precompiles.$m || fail=1
  echo "TIMING proofs-b $m $(( $(date +%s) - start )) s"
done
if [ "$fail" != 0 ]; then echo "FAILURES proofs-b"; exit 1; fi
echo "RESULT proofs-b: all proof modules built"
