# Proofs that the limb primitives, the four-limb routines and the secp256k1 base field compute
# the Nat definitions. Each module is built on its own so that every failure is reported; then
# the axioms printed by the modules are checked (only propext, Classical.choice, Quot.sound).
set -uo pipefail
fail=0
log=$(mktemp)
for m in LimbProofs LimbU256Proofs Secp256k1FieldProofs; do
  start=$(date +%s)
  lake -f lakefile-fieldperf.toml build EVMCleanroom.Precompiles.$m 2>&1 | tee -a "$log"
  [ "${PIPESTATUS[0]}" = 0 ] || fail=1
  echo "TIMING proofs-a $m $(( $(date +%s) - start )) s"
done
# Every theorem of the three modules ends in `#print axioms`; lake replays those lines for
# modules it did not rebuild.
grep -E "'EVMCleanroom\.Precompiles\.(Limb|U256|Secp256k1\.Fe)\.[A-Za-z0-9_']+' (depends on axioms|does not depend)" "$log" | sort -u > "$log.ax"
count=$(wc -l < "$log.ax")
bad=$(sed -e 's/.*depends on axioms: \[//' -e 's/\]$//' -e 's/.*does not depend on any axioms//' "$log.ax" \
  | tr ',' '\n' | sed 's/ //g' | grep -v -E '^(propext|Classical\.choice|Quot\.sound|)$' | sort -u | tr '\n' ' ')
echo "proofs-a: $count theorems audited; axioms outside the allowed three: [${bad}]"
if [ "$count" -lt 37 ] || [ -n "$bad" ]; then fail=1; fi
rm -f "$log" "$log.ax"
if [ "$fail" != 0 ]; then echo "FAILURES proofs-a"; exit 1; fi
echo "RESULT proofs-a: all proof modules built, $count theorems, axioms within propext, Classical.choice, Quot.sound"
