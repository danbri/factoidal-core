#!/bin/bash
# Development loop on Linux CI for the field-arithmetic work: build the named targets, then run the timing tool.
set -euo pipefail
cd "$(dirname "$0")/../.."
lake -f lakefile-fieldperf.toml build evm-fieldperf-exp
for f in .lake/build/ir/EVMCleanroom/FieldPerf/Exp.c .lake/build/ir/EVMCleanroom/Precompiles/Curve.c .lake/build/ir/EVMCleanroom/Precompiles/Secp256k1Field.c; do
  echo "$f: closure calls $(grep -c 'lean_apply_' "$f" || true), constructor allocations $(grep -c 'lean_alloc_ctor' "$f" || true)"
done
grep -n 'loopDoubleDict\|loopDoubleClass' .lake/build/ir/EVMCleanroom/FieldPerf/Exp.c | head -20 || true
.lake/build/bin/evm-fieldperf-exp 2000000
.lake/build/bin/evm-fieldperf-exp 2000000 | grep ns/op
