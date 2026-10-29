#!/usr/bin/env bash
#
# tests/whatwg-url/run.sh — the WHATWG URL Standard in Lean
# (formal/lean4/L4Factoidal/WHATWG/URL) over the vendored web-platform-tests
# url/ data files (third_party/testing/wpt-url, provenance in
# third_party/testing/wpt-url-PROVENANCE.md;
# https://github.com/danbri/factoidal/issues/1167, milestone 3).
#
#   1. tools/whatwg/gen-idna-data.py --check: IdnaData.lean matches the
#      vendored Unicode 18.0.0 files.
#   2. l4whatwg-url selftest, under a 1 MB stack.
#   3. tests/whatwg-url/run.mjs: "N pass, M fail, X expected-fail,
#      S stale (out of T)".
#
# Exits 0 only when every step passes.
set -euo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
LEAN="$ROOT/formal/lean4"
python3 "$ROOT/tools/whatwg/gen-idna-data.py" --check
(cd "$LEAN" && timeout 1800 lake build l4whatwg-url >/dev/null)
BIN="$LEAN/.lake/build/bin/l4whatwg-url"
(ulimit -s 1024; timeout 300 "$BIN" selftest)
timeout 900 node "$HERE/run.mjs" "$BIN" "$@"
