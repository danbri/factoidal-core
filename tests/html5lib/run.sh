#!/usr/bin/env bash
#
# tests/html5lib/run.sh — the HTML tokenizer and tree builder in Lean
# (formal/lean4/L4Factoidal/HTML, WHATWG HTML snapshot whatwg/html 93967771,
# 2026-10-26; https://github.com/danbri/factoidal/issues/1167, milestone 5).
#
#   1. tree construction: web-platform-tests html/syntax/parsing/resources/*.dat
#      (third_party/testing/wpt-html-parsing, wpt ce5ca396);
#   2. tokenizer: html5lib-tests tokenizer/*.test
#      (third_party/testing/html5lib-tests, c777c408);
#   3. agreement: 5000 generated documents that are well-formed XML and that
#      the HTML parser reads with no parse error give the same tree from the
#      HTML parser and the XML parser.
#
# Expected failures and defective test data: tests/html5lib/expected-failures.txt
# (each line names its open issue; a listed case that passes fails the run).
# Exits 0 only when every step passes.
set -euo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
LEAN="$ROOT/formal/lean4"
(cd "$LEAN" && timeout 1800 lake build l4html5lib >/dev/null)
BIN="$LEAN/.lake/build/bin/l4html5lib"
EXP="$HERE/expected-failures.txt"
RC=0
(ulimit -s 1024; timeout 900 "$BIN" --expect "$EXP" tree "$ROOT"/third_party/testing/wpt-html-parsing/html/syntax/parsing/resources/*.dat) || RC=1
(ulimit -s 1024; timeout 900 "$BIN" --expect "$EXP" tokenizer "$ROOT"/third_party/testing/html5lib-tests/tokenizer/*.test) || RC=1
(ulimit -s 1024; timeout 900 "$BIN" agree 5000) || RC=1
exit $RC
