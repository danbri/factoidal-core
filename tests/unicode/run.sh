#!/usr/bin/env bash
#
# tests/unicode/run.sh — the Unicode algorithms in Lean
# (formal/lean4/L4Factoidal/Unicode, Unicode 18.0.0) over the Unicode
# conformance files (third_party/testing/unicode-18.0.0, provenance in
# third_party/testing/unicode-18.0.0-PROVENANCE.md;
# https://github.com/danbri/factoidal/issues/1167, milestone 4).
#
#   1. every generator in tools/unicode/ with --check: the data modules match
#      the vendored Unicode 18.0.0 files.
#   2. l4unicode over each conformance file, under a 1 MB stack:
#      "CMD: N pass, M fail (out of T)".
#
# Exits 0 only when every step passes.
set -euo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
LEAN="$ROOT/formal/lean4"
T="$ROOT/third_party/testing/unicode-18.0.0"
for g in "$ROOT"/tools/unicode/gen-*.py; do
  [ -e "$g" ] || continue
  python3 "$g" --check
done
(cd "$LEAN" && timeout 1800 lake build l4unicode >/dev/null)
BIN="$LEAN/.lake/build/bin/l4unicode"
RC=0
run() { (ulimit -s 1024; timeout 900 "$BIN" "$1" "$T/$2") || RC=1; }
run norm NormalizationTest.txt
run grapheme GraphemeBreakTest.txt
run word WordBreakTest.txt
run sentence SentenceBreakTest.txt
run bidi BidiTest.txt
run bidichar BidiCharacterTest.txt
run linebreak LineBreakTest.txt
exit $RC
