// BROWSER-SURFACE PARITY, all posts: every `fn.<name>(` a published hub
// page calls must exist on the browser `fn`, and every `Factoidal.<name>`
// it reads must be an export of the module hub.njk binds as `Factoidal`.
//
// On the page (docs/_includes/hub.njk), `Factoidal` is @factoidal/core's
// browser entry, npm/factoidal/browser.js (the Lean engine, issue 726),
// and `fn` is `Object.assign({}, Factoidal.default, hubHelpers)`: the
// package's typed API plus the hub-only helpers defined in hub.njk. So a
// name is on the browser surface when browser.js exports it or hubHelpers
// defines it.
//
// Why: the reactive node harness binds `fn` to the NODE package
// (npm/factoidal/index.mjs), so a page can be fully green under
// `node --test` while its cells reject in a real browser. Three live
// breakages of this class shipped before this pin existed:
// fn.rhoDfFragmentCheck and fn.owlClosure (post 32, owner-reported
// 2026-08-07/08) and fn.sigmoidFormulaMathml + fn.sigmoidPoints (post
// 28, found by the 2026-08-08 hub_browser_all.sh sweep).
//
// The export list is read by importing browser.js itself (the import
// loads no wasm), so this pins the real module surface, not a text
// match. Value-level browser checks live in tests/web-demos/
// (hub_browser_all.sh for rejected cells on every post).

import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync } from 'node:fs';
import { xfail } from './_helpers.mjs';

// Names a published post calls that the Lean package does not serve yet,
// each with its open issue. Every one is also an expected-failure case
// below, so the entry must go when the package gains the name. (The six
// deltaLog* names of post 18 were here until the Lean package served them,
// https://github.com/danbri/factoidal/issues/728.)
const KNOWN_GAPS = {};

const HUB_DIR = new URL('../../docs/web/hub/', import.meta.url);
const hub = readFileSync(new URL('../../docs/_includes/hub.njk', import.meta.url), 'utf8');
const browser = await import(new URL('../../npm/factoidal/browser.js', import.meta.url).href);
const nodeEntry = await import(new URL('../../npm/factoidal/index.mjs', import.meta.url).href);

const postFiles = readdirSync(HUB_DIR).filter((f) => /^\d{2}-.*\.md$/.test(f)).sort();

// The hubHelpers object literal of hub.njk, and the method names it defines.
const helpersSource = (() => {
  const start = hub.indexOf('const hubHelpers = {');
  const end = hub.indexOf('\nconst fn = Object.assign({}, Factoidal.default, hubHelpers);');
  assert.ok(start >= 0 && end > start, 'hub.njk defines hubHelpers and fn = Object.assign({}, Factoidal.default, hubHelpers)');
  return hub.slice(start, end);
})();
const helperNames = new Set([...helpersSource.matchAll(/^ {2}async\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(/gm)].map((m) => m[1]));

test('fn-surface parity: hub.njk binds Factoidal to the package browser entry and builds fn from it', () => {
  assert.match(hub, /import \* as Factoidal from "\{\{ '\/npm\/factoidal\/browser\.js' \| url \}\}";/);
  assert.equal(typeof browser.default, 'object');
  assert.ok(helperNames.has('l4Call') && helperNames.has('loadL4'), 'hubHelpers defines the Lean dispatch helpers');
});

test('fn-surface parity: browser.js exports every name the Node entry exports, except the Node-only store path', () => {
  const nodeOnly = new Set(['sampleStorePath', 'sampleStoreFacts', 'loadEngine']);
  const missing = Object.keys(nodeEntry).filter((n) => !nodeOnly.has(n) && !(n in browser));
  assert.deepEqual(missing, [], 'names index.mjs exports and browser.js does not');
});

test('fn-surface parity: every fn.* and Factoidal.* name called by any published hub post is on the browser surface', () => {
  assert.ok(postFiles.length >= 30, `expected 30+ hub posts, found ${postFiles.length}`);
  const missingFn = [];
  const missingFactoidal = [];
  for (const f of postFiles) {
    const page = readFileSync(new URL(f, HUB_DIR), 'utf8');
    const cells = [...page.matchAll(/```observable-js[^\n]*\n([\s\S]*?)```/g)].map((m) => m[1]).join('\n');
    for (const name of new Set([...cells.matchAll(/\bfn\.([A-Za-z_][A-Za-z0-9_]*)\b/g)].map((m) => m[1]))) {
      if (!(name in browser.default) && !helperNames.has(name)) missingFn.push(`${f}: fn.${name}`);
    }
    for (const name of new Set([...cells.matchAll(/\bFactoidal\.([A-Za-z_][A-Za-z0-9_]*)\b/g)].map((m) => m[1]))) {
      if (!(name in browser) && !(`Factoidal.${name}` in KNOWN_GAPS)) missingFactoidal.push(`${f}: Factoidal.${name}`);
    }
  }
  assert.deepEqual(missingFn, [],
    'fn.* names that neither npm/factoidal/browser.js nor hub.njk hubHelpers defines (cells REJECT live)');
  assert.deepEqual(missingFactoidal, [],
    'Factoidal.* names npm/factoidal/browser.js does not export');
});

// Post 18's durable update log, an expected failure naming
// https://github.com/danbri/factoidal/issues/728 until the Lean package
// served it.
for (const name of ['deltaLogOpen', 'deltaLogAppend', 'deltaLogReadAllHex', 'deltaLogMerge',
  'deltaLogDestroy', '_deltaLogCorruptLastForTest']) {
  test(`fn-surface parity: npm/factoidal/browser.js exports ${name}`, () => {
    assert.equal(typeof browser[name], 'function', `Factoidal.${name} is not exported`);
  });
}

for (const [qualified, issue] of Object.entries(KNOWN_GAPS)) {
  xfail(`fn-surface parity: npm/factoidal/browser.js exports ${qualified.split('.')[1]}`, issue, () => {
    assert.ok(qualified.split('.')[1] in browser, `${qualified} is not exported`);
  });
}
