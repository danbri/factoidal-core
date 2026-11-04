#!/usr/bin/env bash
#
# tests/dom/run.sh — the DOM node tree as an arena in Lean
# (formal/lean4/L4Factoidal/DOM, DOM Standard whatwg/dom 3c53f93a;
# https://github.com/danbri/factoidal/issues/1167, milestone 6).
#
#   1. web-platform-tests tree construction tests (wpt ce5ca396), with the
#      tree read from the DOM arena that DOM.ofTreeBuilder makes of the parse;
#   2. differential test against jsdom 30.1.3 (tests/dom/package.json):
#      2000 scripts of 60 DOM operations, two seeds; every operation result and
#      every final tree must be the same;
#   3. scaling (tests/dom/scaling.mjs): time at n and 4n children of one node,
#      ratio at most 6; `remove` of half the children is an expected failure
#      (quadratic, https://github.com/danbri/factoidal/issues/1216);
#   4. expected failure (https://github.com/danbri/factoidal/issues/1216):
#      moveBefore is not checked against another implementation, because
#      jsdom 30.1.3 has none. When jsdom has it, this step fails as STALE.
#
# Exits 0 only when every step passes.
set -euo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
LEAN="$ROOT/formal/lean4"
(cd "$LEAN" && timeout 1800 lake build l4dom l4html5lib >/dev/null)
(cd "$HERE" && timeout 600 npm ci --no-audit --no-fund >/dev/null)
RC=0
(ulimit -s 1024; timeout 900 "$LEAN/.lake/build/bin/l4html5lib" --expect "$ROOT/tests/html5lib/expected-failures.txt" \
  dom-tree "$ROOT"/third_party/testing/wpt-html-parsing/html/syntax/parsing/resources/*.dat) | tail -1 || RC=1
for SEED in 1 2; do
  (ulimit -s 1024; timeout 900 node "$HERE/diff.mjs" "$LEAN/.lake/build/bin/l4dom" 2000 60 "$SEED") || RC=1
done
node "$HERE/scaling.mjs" "$LEAN/.lake/build/bin/l4dom" || RC=1
if (cd "$HERE" && node -e 'const {JSDOM}=require("jsdom");process.exit(typeof new JSDOM("").window.document.body.moveBefore==="function"?0:1)'); then
  echo "STALE expected failure: jsdom has moveBefore now; add it to diff.mjs and close the item in https://github.com/danbri/factoidal/issues/1216"
  RC=1
else
  echo "1 expected failure: moveBefore not compared with another implementation (https://github.com/danbri/factoidal/issues/1216)"
fi
exit $RC
