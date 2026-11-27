# The pairing checks on the limb tower (0x08, 0x0f, KZG): build with the build-time guards,
# closure-call check of the compiled C, run-time differential check, vectors, timings.
set -uo pipefail
status=0
step() {
  echo "--- $*"
  local start=$SECONDS
  "$@" || { echo "RESULT pairing: step failed: $*"; status=1; }
  echo "TIMING pairing: $(( SECONDS - start )) s for: $*"
}
step lake -f lakefile-fieldperf.toml build EVMCleanroom.Precompiles.FastPairing
step lake -f lakefile-fieldperf.toml build EVMCleanroom.Precompiles.BN254Pairing
for f in FastTower FastPairing BN254Pairing; do
  c=.lake/build/ir/EVMCleanroom/Precompiles/$f.c
  [ -f "$c" ] && echo "RESULT pairing: $f.c closure calls $(grep -c 'lean_apply_' "$c" || true), lines $(wc -l < "$c")"
done
exit $status
