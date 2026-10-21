// Pins every code sample in docs/web/historical-fstar-notebooks/12-the-api-tour.md.

import { createRequire } from 'node:module';
import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '12-the-api-tour.md';

const cells = extractObservableCells(POST_FILE);

test('post12: post has at least 2 live cells', () => {
  assert.ok(cells.length >= 2, `expected >= 2 live cells, found ${cells.length}`);
});

test('post12 cell 1 (parse + query, the one door): SELECT returns Alice then Bob', async () => {
  const result = await runObservableCell(cells[0], { fn: factoidal });
  assert.deepEqual(result, ['Alice', 'Bob']);
});

test('post12 cell 2 (capability probe): every RIF/SHACL/ShEx/OWL/RML/CSVW/JSON-LD capability is true against the real bundle', async () => {
  const result = await runObservableCell(cells[1], { fn: factoidal });
  assert.equal(result.available, true);
  for (const key of ['rif', 'shacl', 'shex', 'owlClosure', 'rml', 'csvw', 'jsonld']) {
    assert.equal(result.caps[key], true, `expected caps.${key} to be true against the committed bundle`);
  }
});

test('post12 cell 2 degrades gracefully when the npm-entry bundle is unavailable', async () => {
  const brokenFn = {
    async capabilities() {
      return { entry: false };
    },
  };
  const result = await runObservableCell(cells[1], { fn: brokenFn });
  assert.equal(result.available, false);
  assert.equal(result.caps.entry, false);
});

// ---------------------------------------------------------------------
// Direct API checks, independent of the cell-extraction machinery above.
// ---------------------------------------------------------------------

test('post12: capabilities() function list matches the table this post documents', async () => {
  const caps = await factoidal.capabilities();
  for (const key of [
    'entry', 'construct', 'update', 'canonicalize', 'graphs', 'canonicalHash',
    'shacl', 'shex', 'owlClosure', 'rml', 'csvw', 'jsonld', 'rif',
  ]) {
    assert.ok(key in caps, `capabilities() should report a '${key}' field`);
  }
  assert.equal(caps.entry, true);
  assert.equal(caps.rif, true);
  assert.equal(caps.csvw, true);
});

test('post12: the package has one entry; factoidal/wasm left in 0.9.0 (issue 713)', async () => {
  const fs = await import('node:fs');
  const pkg = JSON.parse(fs.readFileSync(new URL('../../npm/factoidal/package.json', import.meta.url), 'utf8'));
  assert.equal(pkg.exports['./wasm'], undefined, 'no ./wasm export');
  assert.equal(fs.existsSync(new URL('../../npm/factoidal/wasm.js', import.meta.url)), false);
});
