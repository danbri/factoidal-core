// Run after Eleventy builds docs/_site. Uses an installed Playwright/Chromium.
// PLAYWRIGHT_MODULE=/path/to/playwright/index.mjs node tests/web-demos/gdsl_app_browser.mjs --report /tmp/gdsl-browser.json
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {createServer} from 'node:http';
import {createReadStream} from 'node:fs';
import {mkdir, readFile, stat, writeFile} from 'node:fs/promises';
import {dirname, extname, resolve, sep} from 'node:path';
import {fileURLToPath} from 'node:url';
import {sourceProvenance} from '../../tools/pvgraph-evidence-provenance.mjs';
import {execFileSync} from 'node:child_process';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const site = resolve(root, 'docs/_site');
const reportPath = process.argv.includes('--report')
  ? resolve(process.argv[process.argv.indexOf('--report') + 1]) : null;
const screenshotDirectory = process.argv.includes('--screenshots')
  ? resolve(process.argv[process.argv.indexOf('--screenshots') + 1]) : null;
const {chromium} = await import(process.env.PLAYWRIGHT_MODULE || 'playwright');
const downloads = new Map(), checks = [], pageErrors = [], requests = [];
const expected = {mixed: [7, 13, 16, 26, 42, 41, 57, 62],
  cumulative: [7, 20, 36, 62, 104, 145, 202, 264]};
const fixtureA = [2, 3, 5, 7, 11, 13, 17, 19], fixtureB = [1, 4, 1, 5, 9, 2, 6, 5];
const record = (name, detail = {}) => {
  checks.push({name, passed: true, ...detail});
  console.log(`PASS ${name}`);
};
const mime = {'.html': 'text/html', '.mjs': 'text/javascript', '.js': 'text/javascript',
  '.css': 'text/css', '.wasm': 'application/wasm', '.json': 'application/json', '.svg': 'image/svg+xml'};
const server = createServer(async (request, response) => {
  try {
    const pathname = decodeURIComponent(new URL(request.url, 'http://localhost').pathname);
    if (downloads.has(pathname)) {
      response.writeHead(200, {'content-type': 'text/html', 'cache-control': 'no-store'});
      response.end(downloads.get(pathname));
      return;
    }
    const mapping = pathname.startsWith('/factoidal/') ? [site, pathname.slice(11)]
      : pathname.startsWith('/vendor/factoidal/') ? [resolve(root, 'npm/factoidal'), pathname.slice(18)] : null;
    if (!mapping) { response.writeHead(404); response.end('Not found'); return; }
    let file = resolve(mapping[0], mapping[1]);
    if (file !== mapping[0] && !file.startsWith(mapping[0] + sep)) throw new Error('Invalid path');
    if ((await stat(file)).isDirectory()) file = resolve(file, 'index.html');
    const metadata = await stat(file);
    response.writeHead(200, {'content-type': mime[extname(file)] || 'application/octet-stream',
      'content-length': metadata.size, 'cache-control': 'no-store'});
    createReadStream(file).pipe(response);
  } catch { response.writeHead(404); response.end('Not found'); }
});

let browser, fatal, acceptancePage, browserVersion, runtime, source;
const started = new Date().toISOString();
await stat(resolve(site, 'web/hub/gdsl-app/index.html'));
await new Promise(resolveReady => server.listen(0, '127.0.0.1', resolveReady));
const origin = `http://127.0.0.1:${server.address().port}`;
const timer = setTimeout(() => {
  fatal = {message: 'Browser acceptance exceeded 180 seconds.'};
  console.error(fatal.message);
  // Closing our browser rejects an in-flight Playwright action and reaches finally.
  void browser?.close();
  server.close();
}, 180000);
try {
  const head = process.env.SOURCE_COMMIT || execFileSync('git', ['rev-parse', 'HEAD'], {cwd: root, encoding: 'utf8'}).trim();
  const sourceAssets = resolve(root, 'npm/factoidal/l4-assets');
  runtime = JSON.parse(await readFile(resolve(sourceAssets, 'version.json'), 'utf8'));
  source = sourceProvenance(head, resolve(sourceAssets, 'l4factoidal.wasm'));
  assert.equal(runtime.stamped, true, 'runtime metadata must be generated from a real build');
  assert.match(runtime.gitSha, /^[0-9a-f]{40}$/);
  if (process.env.REQUIRE_EXACT_GDSL_RUNTIME === '1')
    assert.equal(runtime.gitSha, head, 'browser test must use the freshly built full runtime');
  const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
  for (const name of ['l4factoidal.js', 'l4factoidal.mjs', 'l4factoidal.wasm', 'version.json']) {
    const installed = await readFile(resolve(sourceAssets, name));
    const rendered = await readFile(resolve(site, 'npm/factoidal/l4-assets', name));
    assert.equal(sha256(rendered), sha256(installed), `rendered ${name} must match the installed runtime`);
    if (name.endsWith('.wasm')) {
      assert.equal(sha256(installed), runtime.wasmSha256);
      assert.equal(installed.length, runtime.wasmBytes);
    }
  }
  record('runtime-provenance-and-rendered-bytes', {sourceCommit: head,
    runtimeCommit: runtime.gitSha, wasmSha256: runtime.wasmSha256, wasmBytes: runtime.wasmBytes});
  if (screenshotDirectory) await mkdir(screenshotDirectory, {recursive: true});
  browser = await chromium.launch({headless: true,
    ...(process.env.CHROMIUM_EXECUTABLE ? {executablePath: process.env.CHROMIUM_EXECUTABLE} : {}),
    args: ['--no-sandbox', '--disable-gpu']});
  browserVersion = browser.version();
  const context = await browser.newContext({viewport: {width: 1365, height: 960}, acceptDownloads: true});
  context.on('page', page => {
    page.on('pageerror', error => pageErrors.push({url: page.url(), error: error.message}));
    page.on('request', request => requests.push({page: page.url(), url: request.url()}));
  });
  const page = await context.newPage();
  acceptancePage = page;
  const $ = id => page.locator(`#${id}`);
  await page.goto(`${origin}/factoidal/web/hub/gdsl-app/`, {waitUntil: 'networkidle'});
  await $('integration-code').waitFor({state: 'visible'});
  assert.match(await $('integration-code').textContent(), /const bindings/);
  assert.equal(await $('run-example').isEnabled(), true);
  assert.equal(requests.some(r => /\.(wasm)(?:\?|$)|\/npm\/factoidal\//.test(r.url)), false);
  assert.match(await $('runtime-status').textContent(), /No runtime loaded/);
  record('lazy-runtime-before-run', {requests: requests.length});

  async function noOverflow(label) {
    const measured = await page.evaluate(() => ({width: innerWidth,
      content: document.documentElement.scrollWidth, body: document.body.scrollWidth}));
    assert.ok(measured.content <= measured.width + 1, JSON.stringify(measured));
    assert.ok(measured.body <= measured.width + 1, JSON.stringify(measured));
    record(label, measured);
  }
  await noOverflow('desktop-layout');
  await page.setViewportSize({width: 390, height: 844});
  await noOverflow('mobile-layout-before-run');
  await page.setViewportSize({width: 1365, height: 960});

  async function run(mode) {
    await $('execution-mode').selectOption(mode);
    await $('run-example').click();
    await page.waitForFunction(() => document.getElementById('run-status').getAttribute('aria-busy') === 'false');
    return {kind: await $('run-status').getAttribute('data-kind'),
      message: await $('run-status').textContent(), backend: await $('backend').textContent()};
  }
  async function checkRows(values) {
    const rows = await $('result-rows').locator('tr').evaluateAll(rows =>
      rows.map(row => Array.from(row.cells, cell => Number(cell.textContent))));
    assert.deepEqual(rows, values.mixed.map((value, i) => [i, fixtureA[i], fixtureB[i], value, values.cumulative[i]]));
  }
  let result = await run('cpu');
  assert.equal(result.kind, 'success');
  assert.equal(result.backend, 'CPU');
  await checkRows(expected);
  record('cpu-default-fixture');
  if (screenshotDirectory) {
    await page.screenshot({path: resolve(screenshotDirectory, 'desktop-default-result.png'), fullPage: true});
    await page.setViewportSize({width: 390, height: 844});
    await page.screenshot({path: resolve(screenshotDirectory, 'mobile-default-result.png'), fullPage: true});
    await page.setViewportSize({width: 1365, height: 960});
  }

  await $('gain').fill('4');
  assert.equal(await $('save-report').isDisabled(), true);
  assert.equal(await $('backend').textContent(), '—');
  assert.match(await $('result-rows').textContent(), /Inputs changed/);
  record('editing-clears-stale-result');
  await $('gain').fill('3');
  result = await run('auto');
  assert.equal(result.kind, 'success');
  await checkRows(expected);
  record('automatic-default-fixture', {backend: result.backend, reason: await $('placement').textContent()});

  await $('input-b').fill('[1]');
  result = await run('cpu');
  assert.equal(result.kind, 'error');
  assert.match(result.message, /length|shape/i);
  assert.equal(await $('save-report').isDisabled(), true);
  assert.equal(await $('backend').textContent(), '—');
  record('unequal-buffers-refused', {message: result.message});

  await $('input-b').fill('[1,');
  assert.equal(await $('download-app').isDisabled(), true);
  result = await run('cpu');
  assert.equal(result.kind, 'error');
  assert.match(result.message, /JSON/);
  assert.equal(await $('save-report').isDisabled(), true);
  record('malformed-input-refused', {message: result.message});

  await $('input-b').fill(JSON.stringify(fixtureB));
  result = await run('cpu');
  assert.equal(result.kind, 'success');
  await checkRows(expected);
  record('recovery-after-invalid-input');

  await $('sample-size').selectOption('2048');
  await $('load-sample').click();
  result = await run('auto');
  assert.equal(result.kind, 'success');
  assert.match(await $('preview-note').textContent(), /2,048 words per output/);
  assert.equal(await $('result-rows').locator('tr').count(), 128);
  record('larger-automatic-sample', {backend: result.backend});

  result = await run('gpu');
  if (result.kind === 'error') {
    assert.match(result.message, /GPU|adapter|device/i);
    assert.equal(await $('backend').textContent(), '—');
    assert.equal(await $('save-report').isDisabled(), true);
    record('required-gpu-refusal', {message: result.message});
  } else {
    assert.equal(result.backend, 'WebGPU');
    assert.match(await $('agreement').textContent(), /All GPU output words matched/);
    record('required-gpu-completed', {dispatches: Number(await $('dispatches').textContent())});
  }
  result = await run('cpu');
  assert.equal(result.kind, 'success');
  record('recovery-after-required-gpu');

  const reportDownload = page.waitForEvent('download');
  await $('save-report').click();
  const reportFile = await reportDownload;
  const report = JSON.parse(await readFile(await reportFile.path(), 'utf8'));
  assert.equal(report.format, 'factoidal-gdsl-app/1');
  assert.equal(report.execution.outputs.mixed.length, 2048);
  assert.equal(report.execution.outputs.cumulative.length, 2048);
  let total = 0n;
  const independent = report.request.bindings.a.map((a, i) => {
    const mixed = Number(BigInt.asUintN(32, BigInt(a) * 3n + BigInt(report.request.bindings.b[i])));
    total = BigInt.asUintN(32, total + BigInt(mixed));
    return [mixed, Number(total)];
  });
  assert.deepEqual(report.execution.outputs.mixed, independent.map(pair => pair[0]));
  assert.deepEqual(report.execution.outputs.cumulative, independent.map(pair => pair[1]));
  record('complete-json-report-download', {wordsPerOutput: 2048, filename: reportFile.suggestedFilename()});

  await page.setViewportSize({width: 390, height: 844});
  await page.locator('#use-in-app').scrollIntoViewIfNeeded();
  await noOverflow('mobile-layout-with-results-and-code');
  await page.setViewportSize({width: 1365, height: 960});

  for (const mode of ['cpu', 'auto', 'gpu']) {
    await $('execution-mode').selectOption(mode);
    const downloadEvent = page.waitForEvent('download');
    await $('download-app').click();
    const file = await downloadEvent;
    const html = await readFile(await file.path(), 'utf8');
    assert.equal(file.suggestedFilename(), 'gdsl-example.html');
    assert.match(html, /\.\/vendor\/factoidal\/gdsl\.mjs/);
    assert.doesNotMatch(html, /cdn\.jsdelivr|\/web\/hub\//);
    downloads.set(`/standalone-${mode}.html`, html);
    const independentPage = await context.newPage();
    const requestStart = requests.length;
    await independentPage.goto(`${origin}/standalone-${mode}.html`, {waitUntil: 'networkidle'});
    await independentPage.waitForFunction(() => !document.getElementById('result').textContent.startsWith('Loading'));
    const displayed = await independentPage.locator('#result').textContent();
    if (screenshotDirectory && mode === 'cpu')
      await independentPage.screenshot({path: resolve(screenshotDirectory, 'independent-app-result.png')});
    if (mode === 'gpu' && displayed.startsWith('Run failed:')) {
      assert.match(displayed, /GPU|adapter|device/i);
      record('standalone-required-gpu-refusal', {message: displayed});
    } else {
      const observed = JSON.parse(displayed);
      assert.deepEqual(observed.outputs, report.execution.outputs);
      if (mode === 'gpu') assert.equal(observed.status, 'gpu-observed');
      record(`standalone-${mode}-execution`, {status: observed.status, wordsPerOutput: 2048});
    }
    const seen = requests.slice(requestStart).filter(request => request.page.includes(`/standalone-${mode}.html`));
    const wasmRequests = seen.map(request => new URL(request.url)).filter(url =>
      url.origin === origin && url.pathname === '/vendor/factoidal/l4-assets/l4factoidal.wasm');
    assert.ok(wasmRequests.length > 0, `No local runtime request for ${mode}: ${JSON.stringify(seen)}`);
    // The loader intentionally adds ?v=<wasm hash> to avoid stale browser caches.
    // Check both the actual local asset and its content-hash query, not a URL suffix.
    for (const url of wasmRequests)
      assert.equal(url.searchParams.get('v'), runtime.wasmSha256.slice(0, 12), 'standalone runtime content hash');
    assert.equal(seen.some(request => request.url.includes('/web/hub/')), false);
    assert.equal(seen.some(request => !request.url.startsWith(origin + '/')), false);
    record(`standalone-${mode}-runtime-request`, {urls: wasmRequests.map(url => url.href)});
    await independentPage.close();
  }
  record('standalone-local-package-only');
  assert.deepEqual(pageErrors, []);
  assert.equal(requests.some(request => !request.url.startsWith(origin + '/')), false);
  record('no-unhandled-errors-or-external-requests', {requests: requests.length});
  await context.close();
} catch (error) {
  fatal = {message: error.message, stack: error.stack};
  console.error(error);
  if (screenshotDirectory && acceptancePage && !acceptancePage.isClosed()) {
    try { await acceptancePage.screenshot({path: resolve(screenshotDirectory, 'failure.png'), fullPage: true}); }
    catch (captureError) { fatal.screenshotError = captureError.message; }
  }
} finally {
  clearTimeout(timer);
  await browser?.close();
  await new Promise(resolveClosed => server.close(resolveClosed));
  const report = {started, completed: new Date().toISOString(), origin,
    browser: 'Chromium headless with --disable-gpu', browserVersion,
    source, runtime, screenshots: screenshotDirectory, checks, passed: checks.length,
    failed: fatal ? 1 : 0, error: fatal ?? null, pageErrors, requests};
  if (reportPath) await writeFile(reportPath, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({passed: report.passed, failed: report.failed, reportPath}));
}
if (fatal) process.exitCode = 1;
