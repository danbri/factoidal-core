#!/usr/bin/env bash
#
# tests/qlvr/kernel.sh — the q07 kernel (scan two permutation ranges, merge
# join on one Id column) in Lean and in C on the same input
# (https://github.com/danbri/factoidal/issues/778; record:
# docs/designissues/2026-10-11-qlvr-performance.md).
#
#   1. `l4qlvr kernel-dump` writes the input (decoded columns of the POS blocks
#      for wso:medal Gold and the PSO blocks for wso:athlete) to a temp file;
#   2. `l4qlvr kernel FILE ITERS` runs each Lean implementation
#      (Harness/QlvrKernel.lean);
#   3. tools/qlvr/bench/kernel.c, compiled with cc -O2, runs the C reference
#      (the same algorithm, and the range variant).
# Every implementation prints its output rows and checksum; the script fails
# when they disagree. ITERS (default 30) runs each; the median is printed.
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${L4QLVR:-$ROOT/formal/lean4/.lake/build/bin/l4qlvr}"
WORK="${QLVR_WORK:-/home/user/qlvr-work}"
ITERS="${ITERS:-30}"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/qlvr-kernel.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
CC="${CC:-cc}"

"$BIN" kernel-dump "$WORK/instance" "$TMP/q07.kernel" || exit 2
"$CC" -O2 -o "$TMP/kernel-c" "$ROOT/tools/qlvr/bench/kernel.c" || exit 2
echo "C compiler: $("$CC" --version | head -1)"
"$BIN" kernel "$TMP/q07.kernel" "$ITERS" | tee "$TMP/out.txt"; lrc=${PIPESTATUS[0]}
"$TMP/kernel-c" "$TMP/q07.kernel" "$ITERS" | tee -a "$TMP/out.txt"
sums="$(grep -o 'checksum [0-9]*' "$TMP/out.txt" | sort -u | wc -l)"
if [ "$lrc" -ne 0 ] || [ "$sums" -ne 1 ]; then echo "kernel: implementations disagree"; exit 1; fi
echo "kernel: all implementations agree"
