// @factoidal/core/api — createApi(engine): the typed API over a Lean engine
// handle the caller loaded (api.mjs). The route for a bundler build or a
// page with its own asset layout: it fetches nothing and evaluates nothing
// itself. See api.mjs's header comment and README.md's "Bundlers and
// Content Security Policy" section.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');
const path = require('node:path');
const { pathToFileURL } = require('node:url');

const { createApi } = require('../api.js');
const indexEngine = require('../index.js');
const pkgVersion = require('../package.json').version;

const TTL = `
  @prefix ex:   <http://example.org/> .
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows ex:bob .
  ex:bob   a foaf:Person ; foaf:name "Bob" .
`;
const SELECT = `
  PREFIX foaf: <http://xmlns.com/foaf/0.1/>
  SELECT ?name WHERE { ?p foaf:name ?name }
`;
const ASK = `
  PREFIX foaf: <http://xmlns.com/foaf/0.1/>
  PREFIX ex:   <http://example.org/>
  ASK { ex:alice foaf:knows ex:bob }
`;

function normRows(rows) {
  return rows
    .map((r) => [...r.entries()]
      .map(([k, v]) => `${k}=${v.termType}:${v.value}`)
      .sort()
      .join('|'))
    .sort();
}

// The engine handle, loaded the way a bundler page would: import the loader
// from l4-assets/ and call loadL4().
async function loadHandle() {
  const loader = path.join(__dirname, '..', 'l4-assets', 'l4factoidal.js');
  const mod = await import(pathToFileURL(loader).href);
  return mod.loadL4();
}

test('createApi(handle): parse/SELECT/ASK match index.js', async () => {
  const factoidal = createApi(await loadHandle());
  const [entryDs, indexDs] = [await factoidal.parse(TTL), await indexEngine.parse(TTL)];
  assert.equal(entryDs.size, indexDs.size);
  assert.equal(
    await factoidal.canonicalize(entryDs), await indexEngine.canonicalize(indexDs));
  const [entryRows, indexRows] = [
    await factoidal.query(TTL, SELECT),
    await indexEngine.query(TTL, SELECT),
  ];
  assert.deepEqual(normRows(entryRows), normRows(indexRows));
  assert.ok(entryRows.length > 0, 'SELECT actually returned rows');
  assert.equal(await factoidal.query(TTL, ASK), true);
});

test('createApi accepts a Promise of the handle', async () => {
  const factoidal = createApi(loadHandle());
  assert.equal(await factoidal.query(TTL, ASK), true);
});

test('createApi accepts a zero-argument thunk returning a Promise of the handle', async () => {
  let calls = 0;
  const factoidal = createApi(() => { calls += 1; return loadHandle(); });
  assert.equal(calls, 0, 'the thunk runs on the first operation, not at createApi()');
  assert.equal(await factoidal.query(TTL, ASK), true);
  assert.equal(await factoidal.query(TTL, ASK), true);
  assert.equal(calls, 1, 'the thunk runs once');
});

test('createApi: an object without call() throws a TypeError', () => {
  assert.throws(() => createApi({}), (err) => err instanceof TypeError && /call\(op, args\)/.test(err.message));
  assert.throws(() => createApi(null), TypeError);
});

test('createApi: openStore takes a reader function only (no file system)', async () => {
  const factoidal = createApi(await loadHandle());
  await assert.rejects(() => factoidal.openStore('/some/path'), TypeError);
});

test('version matches package.json on every entry point', () => {
  assert.equal(indexEngine.version, pkgVersion);
  assert.equal(require('../api.js').version, pkgVersion);
});

test('engine field is lean4-wasm on every entry point', async () => {
  assert.equal(indexEngine.engine, 'lean4-wasm');
  assert.equal(createApi(await loadHandle()).engine, 'lean4-wasm');
});

test('the 0.9.x aliases ./l4 and ./l4-core are gone in 0.10.0', () => {
  const pkg = require('../package.json');
  assert.equal(pkg.exports['./l4'], undefined);
  assert.equal(pkg.exports['./l4-core'], undefined);
  for (const f of ['l4.js', 'l4.d.ts', 'l4-core.js', 'l4-core.d.ts']) {
    assert.ok(!pkg.files.includes(f), f);
  }
});
