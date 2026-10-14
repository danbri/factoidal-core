#!/usr/bin/env bash
#
# tests/merkle-range/run.sh -- the verified range readers of
# formal/lean4/Harness/PosixRangeIO.lean against an independent digest
# (https://github.com/danbri/factoidal/issues/859).
#
# `l4merkle-range-read` (Harness/MerkleRangeRead.lean) writes a file of fixed
# 65,536-byte chunks with its Merkle sidecar and root, and reads a range with one of
# three readers: `leaves` (`readVerifiedRange?`, no cache), `tree`
# (`readVerifiedRangeTree?`, the proof table of the file given by the caller) and
# `cached` (`readVerifiedRangeCached?`, a new chunk cache). For files of 1 to 17
# chunks, whole and short last chunks, differential.py checks that:
#   - every reader returns the bytes of the range: the SHA-256 of what it returns
#     is the SHA-256 that Python computes from the file (`--check` also reads the
#     range without any check and compares);
#   - a range outside the file, or of length 0, is refused by every reader;
#   - one changed byte in any chunk is refused by every reader when the range
#     touches that chunk, and a chunk the range does not touch is not read.
# The scaling of the uncached reader is the row `merkle-range-read-time` of
# tests/stack/lean_scaling.py. Prints "N pass, M fail (out of T)"; exit 0 only when
# no check fails, 2 when the tool is not built.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${L4_MERKLE_RANGE_BIN:-$ROOT/formal/lean4/.lake/build/bin/l4merkle-range-read}"
if [ ! -x "$BIN" ]; then
  echo "missing: $BIN (cd formal/lean4 && lake build l4merkle-range-read)" >&2
  exit 2
fi
TMP="$(mktemp -d "${TMPDIR:-/tmp}/merkle-range.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
exec python3 -I "$HERE/differential.py" "$BIN" "$TMP"
