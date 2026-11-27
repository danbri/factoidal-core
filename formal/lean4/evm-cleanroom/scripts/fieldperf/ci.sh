#!/bin/bash
# Development loop on Linux CI for the field-arithmetic work: build the named targets, then run the timing tool.
set -euo pipefail
cd "$(dirname "$0")/../.."
lake -f lakefile-fieldperf.toml build evm-fieldperf-exp
grep -c lean_alloc_ctor .lake/build/ir/EVMCleanroom/FieldPerf/Exp.c || true
.lake/build/bin/evm-fieldperf-exp 2000000
.lake/build/bin/evm-fieldperf-exp 2000000
