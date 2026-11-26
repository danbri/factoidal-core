#!/bin/bash
set -euo pipefail
ulimit -v 8388608
export PATH=/workspace/scratch/9833f7e76cdb/lake-test-bin:/workspace/scratch/9833f7e76cdb/toolchain/lean-4.33.1-linux/bin:$PATH
export LEAN_NUM_THREADS=1 LEAN_STACK_SIZE_KB=65536 MIMALLOC_ARENA_RESERVE=67108864
export EVM_GETH_EXE=/workspace/scratch/9833f7e76cdb/oracles/geth-alltools-linux-amd64-1.17.10-1df30b18/evm
blobhash_evidence=/workspace/scratch/9833f7e76cdb/blobhash-retained
node scripts/differential/call-repairs.mjs > "$blobhash_evidence/call-repairs.json"
node scripts/eels/run-lean-prague-all-types.mjs --fixture .lake/eels/eip7623.json --out "$blobhash_evidence/prague-six.json" > "$blobhash_evidence/prague-summary.json"
python3 scripts/check-prague-six-ledger.py "$blobhash_evidence/prague-six.json" > "$blobhash_evidence/prague-six-ledger.json"
node scripts/eels/prague-all-selftest.mjs .lake/eels/eip7623.json .lake/eels/negative-controls > "$blobhash_evidence/prague-negative.json"
node scripts/eels/run-lean-contract-state-tests.mjs --fixture .lake/eels/push0-contracts.json --out "$blobhash_evidence/cancun-six.json" > "$blobhash_evidence/cancun-summary.json"
node scripts/eels/contract-selftest.mjs .lake/eels/push0-contracts.json > "$blobhash_evidence/cancun-negative.json"
node scripts/eels/replay-first-mainnet.mjs --fixture evidence/frontier-mainnet-46147.json --out "$blobhash_evidence/frontier-commitments.json" > "$blobhash_evidence/frontier-summary.json"
node scripts/eels/verify-frontier-account-witness.mjs --historical evidence/frontier-mainnet-46147.json --witness .lake/eels/frontier-46146-archive-witness.json --out "$blobhash_evidence/frontier-state-roots.json" > "$blobhash_evidence/frontier-roots-summary.json"
python3 scripts/eels/independent-frontier-trie.py .lake/eels/frontier-46146-archive-witness.json > "$blobhash_evidence/frontier-independent-python.json"
python3 scripts/eels/frontier-independent-negative.py .lake/eels/frontier-46146-archive-witness.json > "$blobhash_evidence/frontier-python-negative.json"
