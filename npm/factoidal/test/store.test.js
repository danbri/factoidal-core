// The persisted store on the main entry (issue 713 stage 3): openStore,
// queryStore, listStores and the Store handle, over the sample store this
// package carries (sample-store/, 4,434 triples in 13 predicate blocks).
// Every format decision is the engine's (ops storeManifestInspect,
// storeQueryPlan, storeOpen, storeHandleQuery); these cases check the
// typed shapes and the host plumbing: CURRENT, the generation option, a
// reader function, and the refusals.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const os = require('node:os');

const factoidal = require('../index.js');
const { openStore, queryStore, listStores, Store, Dataset } = factoidal;
const { sampleStorePath, sampleStoreFacts } = require('./fixtures/sample-store.mjs');

const SKOS = 'http://www.w3.org/2004/02/skos/core#';
const COUNT = 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }';

test('openStore(path): an activated generation, verified and retained', async () => {
  const store = await openStore(sampleStorePath());
  try {
    assert.ok(store instanceof Store);
    assert.equal(store.generation, 'gen-1');
    assert.equal(store.activated, true);
    assert.equal(store.layout, sampleStoreFacts.layout);
    assert.equal(store.wireVersion, sampleStoreFacts.wireVersion);
    assert.equal(store.rows, sampleStoreFacts.triples);
    assert.equal(typeof store.handle, 'string');
    assert.ok(store.bytes > 0);
    const n = await store.query(COUNT);
    assert.equal(Number(n[0].get('n').value), sampleStoreFacts.triples);
  } finally {
    await store.close();
  }
});

test('Store.query: SELECT, ASK and CONSTRUCT answer the typed shapes', async () => {
  const store = await openStore(sampleStorePath());
  try {
    const rows = await store.query(
      `SELECT ?p (COUNT(*) AS ?n) WHERE { ?s ?p ?o } GROUP BY ?p ORDER BY DESC(?n) LIMIT 1`);
    assert.equal(rows.length, 1);
    assert.equal(rows[0].get('p').value, `${SKOS}prefLabel`);
    assert.equal(await store.query('ASK { ?s ?p ?o }'), true);
    assert.equal(await store.query('ASK { <http://e/none> ?p ?o }'), false);
    const ds = await store.query(
      `CONSTRUCT { ?s <http://e/label> ?o } WHERE { ?s <${SKOS}prefLabel> ?o } LIMIT 3`);
    assert.ok(ds instanceof Dataset);
    assert.equal(ds.size, 3);
  } finally {
    await store.close();
  }
});

test('Store.inspect: the engine decodes the manifest', async () => {
  const store = await openStore(sampleStorePath());
  try {
    const m = await store.inspect();
    assert.equal(m.wireVersion, sampleStoreFacts.wireVersion);
    assert.equal(m.entries.length, sampleStoreFacts.blocks);
    assert.equal(m.totalRows, sampleStoreFacts.triples);
  } finally {
    await store.close();
  }
});

test('Store.close is idempotent and a closed store refuses queries', async () => {
  const store = await openStore(sampleStorePath());
  await store.close();
  await store.close();
  assert.equal(store.closed, true);
  await assert.rejects(() => store.query(COUNT), /is closed/);
});

test('listStores reports the open handles and the residency caps', async () => {
  const store = await openStore(sampleStorePath());
  try {
    const list = await listStores();
    assert.ok(list.handles.some((h) => h.handle === store.handle && h.rows === sampleStoreFacts.triples));
    assert.equal(typeof list.handleCap, 'number');
    assert.equal(typeof list.bytesCap, 'number');
  } finally {
    await store.close();
  }
  assert.ok(!(await listStores()).handles.some((h) => h.rows === undefined));
});

test('openStore({sparql}) reads only the plan\'s blocks; a query outside them is refused', async () => {
  const q = `SELECT (COUNT(*) AS ?n) WHERE { ?s <${SKOS}prefLabel> ?o }`;
  const store = await openStore(sampleStorePath(), { sparql: q });
  try {
    assert.ok(store.rows < sampleStoreFacts.triples, `${store.rows} rows retained`);
    const n = await store.query(q);
    assert.ok(Number(n[0].get('n').value) > 0);
    // Every predicate: the plan needs blocks this handle did not read.
    await assert.rejects(() => store.query(COUNT));
  } finally {
    await store.close();
  }
});

test('queryStore: one query, open and close', async () => {
  const n = await queryStore(sampleStorePath(), COUNT);
  assert.equal(Number(n[0].get('n').value), sampleStoreFacts.triples);
});

test('openStore(reader): a function from root-relative paths to bytes', async () => {
  const root = sampleStorePath();
  const asked = [];
  const store = await openStore((p) => {
    asked.push(p);
    const b = fs.readFileSync(path.join(root, p));
    return new Uint8Array(b.buffer, b.byteOffset, b.byteLength).slice().buffer; // an ArrayBuffer
  });
  try {
    assert.equal(asked[0], 'CURRENT');
    assert.ok(asked.includes('gen-1/manifest.sbm2'));
    const n = await store.query(COUNT);
    assert.equal(Number(n[0].get('n').value), sampleStoreFacts.triples);
  } finally {
    await store.close();
  }
});

test('openStore({generation}) opens a generation directly, not through CURRENT', async () => {
  const store = await openStore(sampleStorePath(), { generation: 'gen-1' });
  try {
    assert.equal(store.activated, false);
    assert.equal(store.generation, 'gen-1');
  } finally {
    await store.close();
  }
});

test('openStore refusals: no CURRENT, a bad generation name, a wrong source type', async () => {
  const empty = fs.mkdtempSync(path.join(os.tmpdir(), 'factoidal-store-'));
  try {
    await assert.rejects(() => openStore(empty), /CURRENT/);
    await assert.rejects(() => openStore(sampleStorePath(), { generation: '../gen-1' }), /path separator/);
    await assert.rejects(() => openStore(sampleStorePath(), { generation: 'no-such-gen' }), /none of manifest/);
    await assert.rejects(() => openStore(42), TypeError);
  } finally {
    fs.rmSync(empty, { recursive: true, force: true });
  }
});

test('a tampered block is refused, naming the artifact', async () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'factoidal-store-'));
  try {
    fs.cpSync(sampleStorePath(), dir, { recursive: true });
    const block = path.join(dir, 'gen-1', 'predicate-0.ibk3');
    const bytes = fs.readFileSync(block);
    bytes[bytes.length - 1] ^= 0xff;
    fs.writeFileSync(block, bytes);
    await assert.rejects(() => openStore(dir), /predicate-0\.ibk3/);
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
});
