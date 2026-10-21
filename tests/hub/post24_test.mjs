// Pins every live cell in docs/web/historical-fstar-notebooks/24-hdt-header-dictionary-triples.md.
//
// The post's three cells fetch the in-repo RML-Core HDT fixture and
// hand its bytes to `fn.queryHdt(bytes, sparql)`, which encapsulates
// the `--data-hdt` argv+files primitive entirely -- the cell never
// builds a virtual path or fake-filesystem entry itself. In the
// browser `fn.queryHdt` (docs/_includes/hub.njk's adapter) is built on
// `Factoidal.runFactoidalCli` (browser.js), which drives the
// js_of_ocaml CLI bundle; a hub cell has no js bundle here, so this
// test provides a Node-side `fn.queryHdt` that materializes the bytes
// to a temp file and shells out to the SAME CLI via the committed
// native binary (bin/<platform>/factoidal) -- mirroring the adapter's
// own logic (byte-pack, run --data-hdt, reshape SRJ bindings into
// Map<string,Term> rows) one layer down. `fetch` is stubbed to serve
// the local fixture bytes (the cell's page-relative URL is ignored).
// `Plot` is an echo stub capturing marks/data so the histogram cell's
// derived data can be asserted (same browser-vs-test duality
// documented for pretty()/Plot in hub/README.md and post23_test.mjs).

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell, runReactivePost, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = path.join(__dirname, '..', '..');
const POST_FILE = '24-hdt-header-dictionary-triples.md';

const HDT_FIXTURE = path.join(
  REPO_ROOT, 'third_party', 'testing', 'hdt', 'rml-core-ontology.hdt');

// Locate the committed native binary for this platform (same layout
// bin/<platform>/ the CLAUDE.md rule-#9 committed binaries use).
// The page's fn.queryHdt is the package's queryHdt(bytes, sparql): the
// Lean HDT reader inside the wasm module, the file passed as the
// dispatch ABI's byte region (issue 726). The test binds the same
// function from the Node entry.
const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const fn = factoidal;

const Plot = {
  plot: (spec) => ({ isPlot: true, ...spec }),
  barX: (data, options) => ({ mark: 'barX', data, options }),
  text: (data, options) => ({ mark: 'text', data, options }),
  ruleX: (data, options) => ({ mark: 'ruleX', data, options }),
};

// Serve the local HDT fixture for the cells' page-relative fetch().
const realFetch = globalThis.fetch;
globalThis.fetch = async () => {
  const buf = fs.readFileSync(HDT_FIXTURE);
  const ab = buf.buffer.slice(buf.byteOffset, buf.byteOffset + buf.byteLength);
  return { ok: true, async arrayBuffer() { return ab; } };
};
test.after(() => { globalThis.fetch = realFetch; });

const cells = extractObservableCells(POST_FILE);
const B = { fn, pretty, Plot };

test('post24: post has 4 live cells (buf fetch hoisted into its own named cell)', () => {
  assert.equal(cells.length, 4, `expected 4 live cells, found ${cells.length}`);
});

test('post24: dependency inference wires buf into every query cell', () => {
  const post = runReactivePost(cells, B);
  assert.equal(post.names[0], 'buf');
  for (const i of [1, 2, 3]) {
    assert.ok(post.infos[i].refs.includes('buf'), `cell ${i + 1} references buf`);
  }
});

test('post24 cell 1 (count triples): 343', async () => {
  const post = runReactivePost(cells, B);
  const result = await post.value(post.names[1]);
  assert.equal(result, 343);
});

test('post24 cell 2 (owl:Class labels): pretty table including RML classes', async () => {
  const post = runReactivePost(cells, B);
  const result = await post.value(post.names[2]);
  assert.equal(result.kind, 'table');
  assert.deepEqual(result.columns, ['class', 'label']);
  assert.ok(result.rows.length >= 20, `expected >= 20 class rows, got ${result.rows.length}`);
  const labels = result.rows.map((r) => r[1]);
  for (const expected of ['Triples Map', 'Subject Map', 'Object Map']) {
    assert.ok(labels.includes(expected), `missing class label ${expected}`);
  }
});

test('post24 cell 3 (predicate histogram): rdf:type bar at 84', async () => {
  const post = runReactivePost(cells, B);
  const result = await post.value(post.names[3]);
  assert.equal(result.isPlot, true);
  const bar = result.marks.find((m) => m.mark === 'barX');
  assert.ok(bar, 'expected a barX mark');
  assert.ok(bar.data.length >= 1 && bar.data.length <= 8, 'top-8 predicate bars');
  const typeBar = bar.data.find((d) => d.predicate === 'type');
  assert.ok(typeBar, 'expected an rdf:type bar');
  assert.equal(typeBar.count, 84);
  // Bars are sorted descending, so rdf:type is the tallest (first).
  assert.equal(bar.data[0].predicate, 'type');
});

// Coverage gap this closes: the three cell tests above shell out to the
// committed NATIVE binary (runFactoidalCli -> execFileSync). The browser
// hub runs the js_of_ocaml BUNDLE instead, and the bundle diverges from
// native exactly where an F* value extracts through stdint's Uint32,
// whose C externals (uint32_xor, ...) have no js_of_ocaml realisation.
// HDT.Container's CRC16 (and HDT.Dictionary's CRC8/CRC32C) used
// FStar.UInt32, so opening any HDT file aborted in-browser with
// Failure("uint32_xor not implemented") -> empty stdout -> the cell's
// JSON.parse threw "Unexpected EOF", while every native test stayed
// green. This case drives the ACTUAL bundle the way browser.js does
// (engine-js.js runCli over the '/static/' fake device) so a
// native-only regression can never hide here again.
test('post24: HDT count is 343 through the package API directly (no cell machinery)', async () => {
  const rows = await factoidal.queryHdt(fs.readFileSync(HDT_FIXTURE),
    'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }');
  assert.equal(rows[0].get('n').value, '343');
});
