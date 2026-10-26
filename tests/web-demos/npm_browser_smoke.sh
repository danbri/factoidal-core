#!/usr/bin/env bash
# tests/web-demos/npm_browser_smoke.sh
#
# The browser entry of @factoidal/core (npm/factoidal/browser.js) in
# headless Chromium (Playwright), from a static page a local node http
# server serves. browser.js loads the Lean engine itself: it imports
# l4-assets/l4factoidal.js and compiles l4-assets/l4factoidal.wasm with
# fetch() + WebAssembly.instantiateStreaming (issue 713 stage 3).
#
# The page runs one parse, one SELECT, one canonicalize, one XPath
# evaluation and one query against the sample store through a fetch()
# reader, and the script asserts each answer, that
# WebAssembly.instantiateStreaming was called once, that the wasm was
# served as application/wasm, and that no pageerror or console error fired.
#
# The store is the test fixture npm/factoidal/test/fixtures/sample-store
# (the package stopped carrying a sample store in 0.10.0).
#
# Until 2026-10-24 a second page tested the core entry core-browser.js. The
# package has carried one wasm and no core entry since commit 6ed227fe
# (owner, 2026-10-20: "For now, we have a single fat core"), so that page
# exited 2 on a missing file and the gate was not run.
#
# Usage:
#   tests/web-demos/npm_browser_smoke.sh
#   NPM_BROWSER_SMOKE_PORT=8936 tests/web-demos/npm_browser_smoke.sh
#
# Requirements: node >= 22.12; Playwright with Chromium (the container has
# it under /opt/pw-browsers; do not run `playwright install`); the Lean wasm
# in npm/factoidal/l4-assets/ (formal/lean4/Wasm/build-wasm.sh, or
# tools/fetch-builds.sh).
#
# Exit status: 0 PASS, 1 FAIL, 2 environment (no Playwright, no Chromium,
# no wasm).
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
PKG_DIR="$REPO_ROOT/npm/factoidal"

for f in "$PKG_DIR/browser.js" "$PKG_DIR/l4-assets/l4factoidal.js" \
         "$PKG_DIR/l4-assets/l4factoidal.mjs" "$PKG_DIR/l4-assets/l4factoidal.wasm" \
         "$PKG_DIR/test/fixtures/sample-store/CURRENT"; do
  [ -f "$f" ] || { echo "Missing $f" >&2; exit 2; }
done

PLAYWRIGHT_PKG_DIR="${PLAYWRIGHT_PKG:-/opt/node22/lib/node_modules/playwright}"
if [ -d "$PLAYWRIGHT_PKG_DIR" ]; then
  PLAYWRIGHT_IMPORT_SPEC="$PLAYWRIGHT_PKG_DIR/index.mjs"
elif node -e "require.resolve('playwright')" >/dev/null 2>&1; then
  PLAYWRIGHT_IMPORT_SPEC="playwright"
else
  echo "Missing playwright (looked in \$PLAYWRIGHT_PKG_DIR=$PLAYWRIGHT_PKG_DIR and node's module path)." >&2
  exit 2
fi

WORKDIR="$(mktemp -d)"
trap 'rm -rf "$WORKDIR"' EXIT
PORT="${NPM_BROWSER_SMOKE_PORT:-8936}"

cat >"$WORKDIR/index.html" <<'HTML_EOF'
<!doctype html>
<html>
<head><meta charset="utf-8"><title>loading</title></head>
<body>
<script type="module">
import { parse, query, canonicalize, xpathEval, openStore, engine, version }
  from '/pkg/browser.js';
try {
  const ds = await parse('@prefix ex: <http://example.org/> . ex:a ex:p "x" , "y" . ex:b ex:q [ ex:r 1 ] .');
  const rows = await query(ds, 'SELECT ?o WHERE { ?s <http://example.org/p> ?o } ORDER BY ?o');
  const c14n = await canonicalize(ds);
  const xp = await xpathEval('<r><a>1</a><a>2</a><a>3</a></r>', 'count(//a)');
  const store = await openStore((p) => fetch('/pkg/test/fixtures/sample-store/' + p).then((r) => {
    if (!r.ok) throw new Error(p + ': ' + r.status);
    return r.arrayBuffer();
  }));
  const n = await store.query('SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }');
  await store.close();
  window.__result = {
    size: ds.size,
    rows: rows.map((r) => r.get('o').value),
    c14nLines: c14n.trim().split('\n').length,
    c14nBlank: /_:c14n0/.test(c14n),
    xpath: xp,
    storeCount: Number(n[0].get('n').value),
    engine, version,
  };
  document.title = 'done';
} catch (e) {
  window.__result = { error: String((e && e.stack) || e) };
  document.title = 'error';
}
</script>
</body>
</html>
HTML_EOF

cat >"$WORKDIR/driver.mjs" <<'DRIVER_EOF'
import { readFileSync } from 'node:fs';
import { createServer } from 'node:http';
import path from 'node:path';

const PKG_DIR = process.env.PKG_DIR;
const PAGE_DIR = process.env.PAGE_DIR;
const PORT = Number(process.env.PORT_RESOLVED);
const MIME = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8',
  '.mjs': 'text/javascript; charset=utf-8', '.wasm': 'application/wasm', '.json': 'application/json' };

const served = [];
const server = createServer((req, res) => {
  const urlPath = decodeURIComponent((req.url === '/' ? '/index.html' : req.url).split('?')[0]);
  let filePath;
  if (urlPath.startsWith('/pkg/')) filePath = path.join(PKG_DIR, urlPath.slice('/pkg/'.length));
  else filePath = path.join(PAGE_DIR, urlPath);
  if (!filePath.startsWith(PKG_DIR) && !filePath.startsWith(PAGE_DIR)) { res.writeHead(403).end(); return; }
  let body;
  try { body = readFileSync(filePath); } catch (_e) { res.writeHead(404).end('not found'); return; }
  const type = MIME[path.extname(filePath)] || 'application/octet-stream';
  served.push({ urlPath, type });
  res.writeHead(200, { 'Content-Type': type });
  res.end(body);
});
await new Promise((resolve, reject) => { server.on('error', reject); server.listen(PORT, '127.0.0.1', resolve); });

let chromium;
try {
  ({ chromium } = await import(process.env.PLAYWRIGHT_IMPORT_SPEC));
} catch (e) {
  console.error('npm_browser_smoke: could not import Playwright:', e.message);
  server.close(); process.exit(2);
}
let browser;
try {
  browser = await chromium.launch({ args: ['--disable-gpu', '--no-sandbox'] });
} catch (e) {
  console.error('npm_browser_smoke: Chromium failed to launch:', e.message);
  server.close(); process.exit(2);
}
// One page in its own browser context: load it, wait for it to settle, and
// answer its result, the instantiateStreaming count, the requests served and
// the errors it raised.
async function runPage(html) {
  served.length = 0;
  const context = await browser.newContext();
  const page = await context.newPage();
  const pageErrors = [];
  const consoleErrors = [];
  page.on('pageerror', (err) => pageErrors.push(err.message));
  page.on('console', (msg) => { if (msg.type() === 'error') consoleErrors.push(msg.text()); });
  // Count the calls the entry makes, without changing what they do.
  await page.addInitScript(() => {
    window.__instantiateStreamingCalls = 0;
    const original = WebAssembly.instantiateStreaming;
    WebAssembly.instantiateStreaming = function (...args) {
      window.__instantiateStreamingCalls += 1;
      return original.apply(this, args);
    };
  });
  const failures = [];
  const t0 = Date.now();
  try {
    await page.goto(`http://127.0.0.1:${PORT}/${html}`, { waitUntil: 'load', timeout: 20000 });
    await page.waitForFunction(() => document.title !== 'loading', { timeout: 60000 });
  } catch (e) {
    failures.push(`${html}: page did not settle: ${e.message}`);
  }
  const ms = Date.now() - t0;
  const result = await page.evaluate(() => window.__result).catch(() => null);
  const calls = await page.evaluate(() => window.__instantiateStreamingCalls).catch(() => null);
  await context.close().catch(() => {});
  return { failures, ms, result, calls, served: [...served], pageErrors, consoleErrors };
}

const failures = [];
const notes = [];
const common = (html, run, wasmName) => {
  const check = (ok, what) => { if (!ok) failures.push(`${html}: ${what}`); };
  failures.push(...run.failures);
  check(run.calls === 1, `WebAssembly.instantiateStreaming calls: ${run.calls}, expected 1`);
  const wasmServed = run.served.filter((s) => s.urlPath.endsWith('.wasm'));
  check(wasmServed.length === 1 && wasmServed[0].type === 'application/wasm' &&
        wasmServed[0].urlPath.endsWith('/' + wasmName),
    `wasm requests: ${JSON.stringify(wasmServed)}, expected one ${wasmName}`);
  check(run.pageErrors.length === 0, `pageerror: ${run.pageErrors[0]}`);
  check(run.consoleErrors.length === 0, `console.error: ${run.consoleErrors[0]}`);
  return check;
};

// The full entry, browser.js.
{
  const run = await runPage('index.html');
  const check = common('index.html', run, 'l4factoidal.wasm');
  const result = run.result;
  if (!result || result.error) {
    failures.push(`index.html: page error: ${result && result.error}`);
  } else {
    check(result.size === 4, `parse: size ${result.size}, expected 4`);
    check(JSON.stringify(result.rows) === '["x","y"]', `SELECT: ${JSON.stringify(result.rows)}`);
    check(result.c14nLines === 4 && result.c14nBlank, `canonicalize: ${result.c14nLines} lines, blank ${result.c14nBlank}`);
    check(result.xpath && String(result.xpath.value) === '3', `xpathEval: ${JSON.stringify(result.xpath)}`);
    check(result.storeCount === 4434, `store COUNT: ${result.storeCount}, expected 4434`);
    check(result.engine === 'lean4-wasm', `engine: ${result.engine}`);
  }
  notes.push(`full entry: ${run.ms} ms to settle`);
}

await browser.close().catch(() => {});
server.close();

if (failures.length > 0) {
  console.log(`FAIL npm_browser_smoke: ${failures.join('; ')}`);
  process.exit(1);
}
console.log(`PASS npm_browser_smoke: parse, SELECT, canonicalize, xpathEval, openStore ` +
  `over fetch; instantiateStreaming called once and the wasm served as application/wasm; ` +
  `${notes.join(', ')}`);
process.exit(0);
DRIVER_EOF

RC=0
PLAYWRIGHT_IMPORT_SPEC="$PLAYWRIGHT_IMPORT_SPEC" PKG_DIR="$PKG_DIR" PAGE_DIR="$WORKDIR" \
PORT_RESOLVED="$PORT" timeout 180 node "$WORKDIR/driver.mjs" || RC=$?
exit "$RC"
