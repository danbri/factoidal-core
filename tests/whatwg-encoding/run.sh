#!/usr/bin/env bash
#
# tests/whatwg-encoding/run.sh — the WHATWG Encoding Standard in Lean
# (formal/lean4/L4Factoidal/WHATWG/Encoding) over the vendored
# web-platform-tests encoding/ directory (third_party/testing/wpt-encoding,
# provenance in third_party/testing/wpt-encoding-PROVENANCE.md;
# https://github.com/danbri/factoidal/issues/1167, milestone 2).
#
#   1. tools/whatwg/gen-encoding-data.py --check: Data.lean matches the
#      vendored encodings.json and indexes.json.
#   2. l4whatwg-encoding selftest.
#   3. tests/whatwg-encoding/run.mjs: "N pass, M fail, X expected-fail,
#      S stale (out of T); K excluded (defective test data)".
#
# Exits 0 only when every step passes.
set -euo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
LEAN="$ROOT/formal/lean4"
python3 "$ROOT/tools/whatwg/gen-encoding-data.py" --check
(cd "$LEAN" && timeout 1800 lake build l4whatwg-encoding >/dev/null)
BIN="$LEAN/.lake/build/bin/l4whatwg-encoding"
(ulimit -s 1024; timeout 120 "$BIN" selftest)
# --js-float16array: encodeInto.any.js constructs Float16Array (Node 22 has it
# behind this flag).
timeout 1200 node --js-float16array "$HERE/run.mjs" "$BIN" "$@"
