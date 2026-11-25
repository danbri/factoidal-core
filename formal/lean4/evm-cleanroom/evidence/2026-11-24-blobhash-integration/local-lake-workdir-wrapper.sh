#!/bin/bash
# Legacy test harnesses invoke `lake exe` from the package directory.
# Preserve their command while enforcing this repository's required workdir.
set -e
cd /workspace/scratch/9833f7e76cdb/factoidal-core/formal/lean4
exec /workspace/scratch/9833f7e76cdb/toolchain/lean-4.33.1-linux/bin/lake -d evm-cleanroom "$@"
