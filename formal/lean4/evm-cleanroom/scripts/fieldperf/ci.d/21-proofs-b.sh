# Proofs that Montgomery arithmetic on four and six limbs computes the Nat definitions.
# Each module is built on its own so that every failure is reported; then the axioms printed
# by the modules are checked (only propext, Classical.choice, Quot.sound).
set -uo pipefail
fail=0
log=$(mktemp)
for m in MontgomeryMath Limb384Proofs MontgomeryRedcProofs MontgomeryProofs MontgomeryFieldProofs; do
  start=$(date +%s)
  lake -f lakefile-fieldperf.toml build EVMCleanroom.Precompiles.$m 2>&1 | tee -a "$log"
  [ "${PIPESTATUS[0]}" = 0 ] || fail=1
  echo "TIMING proofs-b $m $(( $(date +%s) - start )) s"
done
# Every theorem of these modules ends in a '#print axioms' line; lake replays those lines for
# modules it did not rebuild.
grep -E "'EVMCleanroom\.Precompiles\.(MontMath|U384|U256\.(redc_row|redc_rows|redc_spec|toNat_mod|widen_toNat|toNat_zero)|Mont256|Mont384|Secp256k1\.scalarField_|BN254\.baseField_|BLS12381\.baseField_)[A-Za-z0-9_'.]*' (depends on axioms|does not depend)" "$log" | sed 's/^.*: .EVMCleanroom/EVMCleanroom/' | sort -u > "$log.ax"
count=$(wc -l < "$log.ax")
bad=$(sed -e 's/.*depends on axioms: \[//' -e 's/\]$//' -e 's/.*does not depend on any axioms//' "$log.ax"   | tr ',' '\n' | sed 's/ //g' | grep -v -E '^(propext|Classical\.choice|Quot\.sound|)$' | sort -u | tr '\n' ' ')
echo "proofs-b: $count theorems audited; axioms outside the allowed three: [${bad}]"
if [ "$count" -lt 115 ] || [ -n "$bad" ]; then fail=1; fi
rm -f "$log" "$log.ax"
if [ "$fail" != 0 ]; then echo "FAILURES proofs-b"; exit 1; fi
echo "RESULT proofs-b: all proof modules built, $count theorems, axioms within propext, Classical.choice, Quot.sound"
