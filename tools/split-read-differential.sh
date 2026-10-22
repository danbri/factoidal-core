#!/usr/bin/env bash
# tools/split-read-differential.sh [DIR...]
#
# The Turtle and TriG split read of the source layer (several readers, one for
# each byte range between dot boundaries; formal/lean4/L4Factoidal/Syntax/
# TurtleSplitScan.lean, `Source.Reader.resume`) against the single reader
# (https://github.com/danbri/factoidal/issues/842; the theorem that would make
# this run unnecessary is https://github.com/danbri/factoidal/issues/944, row
# SR-1 of tests/known-defects/run.sh). Every .ttl and .trig file under DIR
# (default: third_party/testing/w3c and tests/sbm11/syntax) goes to
# `l4split-diff` (formal/lean4/Harness/SplitReadDiff.lean), which tries every
# split alone (at most 120 per file) and the plans for 2, 3, 4 and 8 workers.
#
# Prints the summary line of each batch and the totals. Exit 0 when every case
# agrees, 1 when one differs, 2 on a setup error (no binary, no file).
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="${L4_SPLIT_DIFF:-$ROOT/formal/lean4/.lake/build/bin/l4split-diff}"
[ -x "$BIN" ] || { echo "not built: $BIN (cd formal/lean4 && lake build l4split-diff)" >&2; exit 2; }
if [ "$#" -eq 0 ]; then
  set -- "$ROOT/third_party/testing/w3c" "$ROOT/tests/sbm11/syntax"
fi
LIST="$(mktemp)"; OUT="$(mktemp)"
trap 'rm -f "$LIST" "$OUT"' EXIT
for d in "$@"; do
  find -L "$d" \( -name '*.ttl' -o -name '*.trig' \) -type f -print
done | sort > "$LIST"
n=$(wc -l < "$LIST")
[ "$n" -gt 0 ] || { echo "no Turtle or TriG file under: $*" >&2; exit 2; }
RC=0
xargs -d '\n' -a "$LIST" "$BIN" > "$OUT" || RC=$?
grep -v '^l4split-diff:' "$OUT"
grep '^l4split-diff:' "$OUT"
grep '^l4split-diff:' "$OUT" | python3 -c '
import re, sys
t = [0] * 8
for line in sys.stdin:
    n = [int(x) for x in re.findall(r"\d+", line)]
    n = [n[i] for i in (1, 2, 3, 4, 5, 6, 8, 9)]
    t = [a + b for a, b in zip(t, n)]
print(f"total: {t[0]} files ({t[1]} not split: <<, ~ or the annotation syntax); {t[2]} agree ({t[3]} accepted "
      f"by both, {t[4]} refused by both), {t[5]} differ (out of {t[2] + t[5]} cases, {t[6]} with at least one "
      f"split); {t[7]} count mismatches (read as one range by the packer)")'
# xargs exits 123 when one invocation exits 1..125.
case "$RC" in
  0) exit 0 ;;
  1|123) exit 1 ;;
  *) exit 2 ;;
esac
