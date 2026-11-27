# Fast ECRECOVER: generic windowed scalar multiplication, the secp256k1 fast path, its differential check and timing.
set -euo pipefail
lake -f lakefile-fieldperf.toml build EVMCleanroom.Precompiles.ScalarMul
echo "RESULT ScalarMul built (recoding theorems and guards against Curve.mul, Curve.mul2)"
