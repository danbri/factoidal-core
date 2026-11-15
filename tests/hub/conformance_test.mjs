// The Hub Conformance page (docs/web/hub/conformance/) rendered in Node with sample data:
// one data set with no full Test262 run and a partial rival, one with full Test262 runs.
// The page's HTML comes from the same functions the browser uses (conformance.mjs); the
// treemap uses the vendored d3 the page loads. The schema check is tests/hub/conformance_schema.mjs.
import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import * as d3 from '../../third_party/observable/dist/d3.esm.js';
import {pageHTML, treemapHTML, tableHTML, detailHTML, lineChart, STALE_HOURS} from '../../docs/web/hub/conformance/conformance.mjs';
import {checkDir, validate} from './conformance_schema.mjs';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const FIX = path.join(HERE, 'conformance-fixtures');
const load = name => ['data.json', 'history.json'].map(f => JSON.parse(fs.readFileSync(path.join(FIX, name, f), 'utf8')));
const NOW = Date.parse('2026-11-15T20:00:00Z');
const colours = ['#e6effb', '#b7d3f6', '#6da7ec', '#2a78d6', '#184f95', '#0d366b'];

/** Tags opened and closed in order (a cheap check that the HTML strings nest). */
function balanced(html) {
  const VOID = new Set(['br', 'img', 'input', 'meta', 'link', 'hr']);
  const stack = [];
  for (const [, close, name, self] of html.matchAll(/<(\/?)([a-zA-Z][a-zA-Z0-9]*)\b[^>]*?(\/?)>/g)) {
    const n = name.toLowerCase();
    if (self || (VOID.has(n) && !close)) continue;
    if (!close) stack.push(n);
    else if (stack.pop() !== n) return false;
  }
  return stack.length === 0;
}

test('the sample data files match the schema', () => {
  for (const name of ['no-full-test262', 'full-test262']) {
    for (const [file, errs] of Object.entries(checkDir(path.join(FIX, name)))) assert.deepEqual(errs, [], `${name}/${file}`);
  }
});

test('the schema check finds a bad share and a missing field', () => {
  const schema = JSON.parse(fs.readFileSync(path.join(HERE, '..', '..', 'docs', 'web', 'hub', 'conformance', 'data.schema.json'), 'utf8'));
  const [, H] = load('no-full-test262');
  const bad = structuredClone(H);
  bad.wpt[0].share = 91.8;
  delete bad.test262wpt;
  const errs = validate(bad, schema['history.json'], schema.definitions);
  assert.ok(errs.some(e => /wpt\[0\]\.share: 91\.8 > 1/.test(e)), errs.join('\n'));
  assert.ok(errs.some(e => /no test262wpt/.test(e)), errs.join('\n'));
});

test('no full Test262 run: Test262 comes first, says so, and Test262 through WPT is the headline', () => {
  const [D, H] = load('no-full-test262');
  const html = pageHTML(D, H, {now: NOW, width: 360});
  assert.ok(balanced(html), 'tags nest');
  const t262 = html.indexOf('id="test262"'), wpt = html.indexOf('id="wpt"');
  assert.ok(t262 > 0 && wpt > t262, 'Test262 section before WPT');
  assert.match(html, /No full Test262 run recorded yet/);
  assert.match(html, /<div class="card hero"><h3>Test262 through WPT<\/h3>/);
  assert.match(html, /80\.6%/);
  assert.match(html, /Servo: no run at this WPT commit/);
  assert.match(html, /Ladybird: partial run: 51,020 of 94,695 tests reported/);
  assert.match(html, /Apple&#39;s bar 80%/);
  assert.match(html, /Goal 90%/);
  assert.match(html, /Data as of <b>2026-11-15 18:41 UTC<\/b>/);
  assert.doesNotMatch(html, /class="stale"/, 'not stale at 20:00');
  assert.equal((html.match(/<svg class="chart"/g) || []).length, 2, 'Test262 through WPT and WPT history charts');
});

test('full Test262 runs: share, share without excluded features, failing directories, history', () => {
  const [D, H] = load('full-test262');
  const html = pageHTML(D, H, {now: NOW, width: 1100});
  assert.ok(balanced(html), 'tags nest');
  const full = html.indexOf('<h3>Full Test262</h3>'), thru = html.indexOf('<h3>Test262 through WPT</h3>'), wpt = html.indexOf('id="wpt"');
  assert.ok(full > 0 && thru > full && wpt > thru, 'full Test262, then through WPT, then WPT');
  assert.match(html, /<b>86\.4%<\/b><span>41,234 of 47,734 tests passed/);
  assert.match(html, /<b>91\.2%<\/b><span>without the excluded features \(Temporal, ShadowRealm\)/);
  // Directories by failing tests: Temporal (3,880) before RegExp (400); annexB has 10.
  const dirs = html.slice(html.indexOf('most failing tests'));
  assert.ok(dirs.indexOf('built-ins/Temporal') < dirs.indexOf('built-ins/RegExp'));
  assert.match(dirs, /<b>3,880<\/b>/);
  assert.equal((html.match(/<svg class="chart"/g) || []).length, 3);
  assert.match(html, /Full Test262 over time/);
  // The headline number is the largest on the page: the hero card is the full suite.
  assert.match(html, /<div class="card hero"><h3>Full Test262<\/h3>/);
});

test('a run older than 12 hours gets a staleness note', () => {
  const [D, H] = load('full-test262');
  const later = Date.parse(D.test262.full.latest.finished) + (STALE_HOURS + 3) * 36e5;
  const html = pageHTML(D, H, {now: later, width: 760});
  assert.match(html, /<p class="stale">The newest run here is 15 hours old/);
  assert.match(html, /The newest full WPT run is 1\d hours old/);
});

test('the treemap fits the width at phone and desktop sizes', () => {
  const [D] = load('no-full-test262');
  for (const width of [358, 1068]) {
    const html = treemapHTML(D, {d3, width, height: 420, colours});
    const cells = [...html.matchAll(/left:(\d+)px;top:(\d+)px;width:(\d+)px;height:(\d+)px/g)].map(m => m.slice(1).map(Number));
    assert.ok(cells.length >= 20, `${cells.length} cells`);
    for (const [l, t, w, h] of cells) assert.ok(l + w <= width && t + h <= 420, `cell inside at ${width}`);
  }
  const zoom = treemapHTML(D, {d3, width: 358, height: 420, colours, zoom: 'css', eng: 1});
  assert.match(zoom, /css\/[^:]+: Chrome passes/);
  assert.match(detailHTML(D, 'css/css-grid', 0, null) + detailHTML(D, D.strata[0][0], 0, null), /Chrome's subtests/);
});

test('the directory table sorts and every engine has a column', () => {
  const [D] = load('no-full-test262');
  const t = tableHTML(D, {sortCol: 'k', sortDir: 1, showAll: true});
  assert.ok(balanced('<table>' + t.html + '</table>'));
  const names = [...t.html.matchAll(/<tr><td>([^<]+)<\/td>/g)].map(m => m[1]);
  assert.deepEqual(names, [...names].sort((a, b) => a.localeCompare(b)));
  for (const n of ['Foafnaut', 'Chrome', 'Firefox', 'Safari', 'Edge', 'WPE WebKit']) assert.match(t.html, new RegExp(`>${n}`));
  assert.doesNotMatch(t.html, />Ladybird/, 'a partial rival has no column');
});

test('a chart with one run and a chart with none', () => {
  const one = lineChart({width: 360, series: [{label: 'x', cls: 's1', pts: [{t: NOW, v: 0.8, tip: 't'}]}], targets: [["Apple's bar", 80]], title: 't'});
  assert.match(one, /<svg class="chart"/);
  assert.doesNotMatch(one, /NaN/);
  assert.match(lineChart({width: 360, series: [{label: 'x', cls: 's1', pts: []}], title: 't'}), /No runs to chart yet/);
});
