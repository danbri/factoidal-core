#!/usr/bin/env bash
# tests/web-demos/hub_post18_value_check.sh
#
# Headless-Chromium VALUE checks of hub post 18, "The durable log, live"
# (https://github.com/danbri/factoidal/issues/728). hub_browser_all.sh sees
# only a REJECTED cell or a page error, and post 18's cells catch their own
# errors and answer {available: false}, so that sweep passes when the log
# does not work. tests/hub/post18_test.mjs runs the cells under Node, with
# the in-memory host store. This script runs them in a real page, over the
# browser entry and real IndexedDB, and reads the values:
#
#   1. no pageerror;
#   2. cell 1 lists Alice, Bob and Carol;
#   3. cells 2 to 4 answer available: true;
#   4. cell 4: Eve survives and Frank is lost to the cut last record;
#   5. after page.reload() the lifecycle log holds one more batch (cell 2
#      appended again; the earlier record survived the reload) and cell 3
#      reads at least two batches.
#
# Builds the site offline with the vendored Eleventy and serves it under
# /factoidal/, as hub_browser_all.sh does.
#
# Usage:
#   tests/web-demos/hub_post18_value_check.sh
#   HUB_POST18_CHECK_PORT=8942 tests/web-demos/hub_post18_value_check.sh
#
# Exit code: 0 iff every check passes. Wall-clock capped (anti-pattern #17).

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

WORKDIR="$(mktemp -d)"
HTTP_PID=""
cleanup() {
  [ -n "$HTTP_PID" ] && kill "$HTTP_PID" >/dev/null 2>&1 || true
  rm -rf "$WORKDIR"
}
trap cleanup EXIT

PLAYWRIGHT_PKG_DIR="${PLAYWRIGHT_PKG:-/opt/node22/lib/node_modules/playwright}"
if [ -d "$PLAYWRIGHT_PKG_DIR" ]; then
  PLAYWRIGHT_IMPORT_SPEC="$PLAYWRIGHT_PKG_DIR/index.mjs"
else
  if ! node -e "require.resolve('playwright')" >/dev/null 2>&1; then
    echo "Missing playwright (looked in \$PLAYWRIGHT_PKG_DIR=$PLAYWRIGHT_PKG_DIR and node's module path)." >&2
    exit 2
  fi
  PLAYWRIGHT_IMPORT_SPEC="playwright"
fi

for f in third_party/eleventy/npm-cache third_party/observable/dist/runtime.esm.js npm/factoidal/browser.js npm/factoidal/l4-assets/l4factoidal.wasm; do
  [ -e "$f" ] || { echo "Missing $f -- run the vendoring steps first." >&2; exit 2; }
done

echo "== Installing vendored Eleventy offline (third_party/eleventy/install.sh) =="
third_party/eleventy/install.sh docs

echo "== Building docs/ site (npx @11ty/eleventy --output=_site) =="
BUILD_LOG="$WORKDIR/build.log"
BUILD_RC=0
( cd docs && rm -rf _site && npx @11ty/eleventy --output=_site ) >"$BUILD_LOG" 2>&1 || BUILD_RC=$?
tail -n 20 "$BUILD_LOG"

SITE_DIR="$REPO_ROOT/docs/_site"
if [ "$BUILD_RC" -ne 0 ]; then
  if grep -q "2026-07-05-csvw-program-plan.md" "$BUILD_LOG"; then
    # The known CSVW Nunjucks-comment defect hub_browser_all.sh works around.
    echo "NOTE: full docs/ build failed on the known CSVW Nunjucks-comment defect; falling back to an isolated copy." >&2
    ISO="$WORKDIR/docs-iso"
    mkdir -p "$ISO"
    rsync -a --exclude=node_modules --exclude=_site docs/ "$ISO/"
    ln -s "$REPO_ROOT/third_party" "$WORKDIR/third_party"
    sed -i -E 's/\{#([A-Za-z_]+)\}/[FRAGMENT \1]/g' \
      "$ISO/designissues/2026-07-05-csvw-program-plan.md"
    ( cd "$ISO" && rm -rf _site && "$REPO_ROOT/docs/node_modules/.bin/eleventy" --input=. --output=_site ) >>"$BUILD_LOG" 2>&1
    SITE_DIR="$ISO/_site"
  else
    echo "FAIL: docs/ build failed for a reason other than the known CSVW defect -- see log above." >&2
    exit 1
  fi
fi

PAGE="$SITE_DIR/web/hub/18-the-durable-log-live/index.html"
[ -f "$PAGE" ] || { echo "FAIL: $PAGE was not produced." >&2; exit 1; }

echo "== Serving $SITE_DIR under /factoidal/ and driving headless Chromium =="
SERVE_ROOT="$WORKDIR/serve-root"
mkdir -p "$SERVE_ROOT"
ln -s "$SITE_DIR" "$SERVE_ROOT/factoidal"

PORT="${HUB_POST18_CHECK_PORT:-8942}"
( cd "$SERVE_ROOT" && exec python3 -m http.server "$PORT" --bind 127.0.0.1 ) >"$WORKDIR/http-server.log" 2>&1 &
HTTP_PID=$!

for _ in $(seq 1 50); do
  curl -sS -o /dev/null "http://127.0.0.1:$PORT/factoidal/web/hub/18-the-durable-log-live/" 2>/dev/null && break
  sleep 0.2
done

DRIVER_PATH="$WORKDIR/driver.mjs"
cat >"$DRIVER_PATH" <<'DRIVER_EOF'
const { chromium } = await import(process.env.PLAYWRIGHT_IMPORT_SPEC);
const PORT = process.env.HUB_POST18_PORT_RESOLVED;
const URL_18 = `http://127.0.0.1:${PORT}/factoidal/web/hub/18-the-durable-log-live/`;
const LOG = 'factoidal-hub-post18-lifecycle';

let failures = 0;
function check(label, ok) {
  console.log((ok ? 'PASS' : 'FAIL') + ' -- ' + label);
  if (!ok) failures++;
}

// The cells settle when the four lifecycle cells show a value; the
// Inspector renders an object as "key" "value" text runs.
async function cellTexts(page) {
  await page.waitForFunction(() => {
    const cells = [...document.querySelectorAll('.observable-cell')];
    return cells.length >= 5 && cells.slice(0, 4).every((c) => /available(true|false)/.test(c.textContent));
  }, { timeout: 45000 });
  return page.$$eval('.observable-cell', (els) => els.map((e) => e.textContent));
}

async function inspect(page) {
  return page.evaluate(async (name) => {
    const F = await import('/factoidal/npm/factoidal/browser.js');
    return F.deltaLogInspect({ dbName: name });
  }, LOG);
}

const browser = await chromium.launch({ args: ['--disable-gpu', '--no-sandbox'] });
const page = await browser.newPage();
const pageErrors = [];
page.on('pageerror', (err) => pageErrors.push(err.message));

await page.goto(URL_18, { waitUntil: 'networkidle', timeout: 30000 });
let texts = await cellTexts(page);
check('cell 1: namesAfterInsert is Alice, Bob, Carol', texts[0].includes('["Alice","Bob","Carol"]'));
for (const i of [1, 2, 3]) {
  check(`cell ${i + 1}: available true`, texts[i].includes('availabletrue'));
}
check('cell 4: Eve survives the cut last record', texts[3].includes('eveSurvivesCorruptiontrue'));
check('cell 4: Frank is lost to the cut last record', texts[3].includes('frankWasLostToCorruptiontrue'));
const before = await inspect(page);
check(`lifecycle log after the first load: ${before.batches} batch(es), not torn`,
  before.batches >= 1 && before.torn === false);

await page.reload({ waitUntil: 'networkidle', timeout: 30000 });
texts = await cellTexts(page);
const after = await inspect(page);
check(`after page.reload(): ${after.batches} batches (one more than ${before.batches})`,
  after.batches === before.batches + 1 && after.torn === false);
const m = /batchesInLog(\d+)/.exec(texts[2]);
check(`after page.reload(): cell 3 reads ${m ? m[1] : '?'} batches (at least 2)`, !!m && Number(m[1]) >= 2);
check('zero pageerror events', pageErrors.length === 0);
if (pageErrors.length) console.log('  pageerrors: ' + pageErrors.join(' | '));

await browser.close();
console.log('===');
console.log(`hub_post18_value_check: ${failures === 0 ? 'ALL PASS' : failures + ' FAILURE(S)'}`);
process.exit(failures === 0 ? 0 : 1);
DRIVER_EOF

DRIVER_RC=0
PLAYWRIGHT_IMPORT_SPEC="$PLAYWRIGHT_IMPORT_SPEC" \
HUB_POST18_PORT_RESOLVED="$PORT" \
  timeout 180 node "$DRIVER_PATH" || DRIVER_RC=$?

exit "$DRIVER_RC"
