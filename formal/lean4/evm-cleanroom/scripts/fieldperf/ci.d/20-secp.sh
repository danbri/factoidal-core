# Fast ECRECOVER: generic windowed scalar multiplication, the secp256k1 fast path, its differential check and timing.
set -euo pipefail
L="lake -f lakefile-fieldperf.toml"
$L build EVMCleanroom.Precompiles.ScalarMul EVMCleanroom.Precompiles.Secp256k1FieldFast EVMCleanroom.Precompiles.Secp256k1Glv
( ulimit -v 12000000; timeout 900 $L build EVMCleanroom.Precompiles.Secp256k1Point ) || { echo "FAILURES Point build"; exit 1; }
echo "RESULT Point built"
F=EVMCleanroom/Precompiles/Secp256k1Fast.lean
total=$(wc -l < $F)
for n in $(grep -n "^structure Plan\|^/-- Affine coordinates as natural numbers, given\|^open Fast\|^#guard\|^#print axioms Fast.go_len" $F | cut -d: -f1) $((total+1)); do
  head -n $((n-1)) $F > /tmp/Probe.lean
  s=$(date +%s)
  ( ulimit -v 6000000; timeout 150 $L env lean /tmp/Probe.lean > /tmp/probe.out 2>&1 ) && r=ok || r="exit $?"
  echo "RESULT probe Fast up to line $n ($(sed -n ${n}p $F | cut -c1-60)): $r, $(( $(date +%s)-s )) s"
  grep "error" /tmp/probe.out | grep -v "unexpected end of input\|unterminated comment" | cut -c1-400 | head -8 || true
  case "$r" in "exit 1"|ok) ;; *) echo "FAILURES probe stopped"; exit 1;; esac
done
[ "$r" = ok ] || exit 1
( ulimit -v 12000000; timeout 900 $L build EVMCleanroom.Precompiles.Secp256k1Fast EVMCleanroom.Precompiles.Ecrecover ) || { echo "FAILURES Fast build"; exit 1; }
echo "RESULT secp modules built (theorems and build-time guards)"
( ulimit -v 12000000; timeout 1200 $L build evm-secpperf ) || { echo "FAILURES exe build"; exit 1; }
for f in Secp256k1FieldFast Secp256k1Point Secp256k1Fast; do
  c=.lake/build/ir/EVMCleanroom/Precompiles/$f.c
  echo "$f.c: closure calls $(grep -c 'lean_apply_' "$c" || true), constructor allocations $(grep -c 'lean_alloc_ctor' "$c" || true), lines $(wc -l < "$c")"
done
.lake/build/bin/evm-secpperf 2000
