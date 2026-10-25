// openSbm11Store(): an SBM11 store opened through the wasm ops sbm11Open,
// sbm11Query, sbm11Close over the Node file-system medium
// (https://github.com/danbri/factoidal/issues/1009 KR1). Each query's answer
// must equal `query()` over the same quads read from N-Quads text: SELECT as
// multisets of solutions, ASK by the boolean, CONSTRUCT by the quad count and
// as multisets of N-Quads lines with blank-node labels masked.
//
// The store: docs/sbm11-sample/data.nq packed by the native
// `l4sbm11-pack` and activated by `l4sbm11 activate` when a repository
// checkout has them built (formal/lean4/.lake/build/bin, or $SBM11_BIN_DIR),
// else the checked-in generation docs/sbm11-sample/store (packed from
// the same file by the same commands).
//
// Skipped when the loaded wasm has no sbm11Open op (an engine built before
// issue 1009), like test/explain-1002.test.mjs.

import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import * as f from '../index.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const fixture = join(here, '..', 'docs', 'sbm11-sample');
const dataNq = join(fixture, 'data.nq');

let skip = 'wasm engine not built';
try {
  const caps = await f.capabilities();
  skip = caps.sbm11 ? false : 'wasm has no sbm11Open op';
} catch (_err) { /* engine did not load: skip */ }

// The store root: a fresh native pack, or the checked-in one.
function storeRoot() {
  const bin = process.env.SBM11_BIN_DIR || join(here, '..', '..', '..', 'formal', 'lean4', '.lake', 'build', 'bin');
  const pack = join(bin, 'l4sbm11-pack');
  const cli = join(bin, 'l4sbm11');
  if (existsSync(pack) && existsSync(cli)) {
    const root = mkdtempSync(join(tmpdir(), 'sbm11-npm-'));
    const p = spawnSync(pack, [dataNq, join(root, 'gen'), '--workers', '1'], { encoding: 'utf8' });
    const a = p.status === 0 ? spawnSync(cli, ['activate', root, 'gen'], { encoding: 'utf8' }) : p;
    if (a.status === 0) return { root, packed: 'native l4sbm11-pack', cleanup: () => rmSync(root, { recursive: true, force: true }) };
    rmSync(root, { recursive: true, force: true });
  }
  return { root: join(fixture, 'store'), packed: 'checked-in fixture', cleanup: () => {} };
}

function termKey(t) {
  if (!t) return null;
  return [t.termType, t.value, t.language || '', t.datatype ? t.datatype.value : ''].join('|');
}
function rowKeys(rows) {
  return rows.map((m) => JSON.stringify([...m.entries()]
    .map(([k, v]) => [k, v.termType === 'BlankNode' ? 'BlankNode' : termKey(v)])
    .sort((x, y) => (x[0] < y[0] ? -1 : 1)))).sort();
}
async function linesOf(ds) {
  const text = await f.serialize(ds, 'nquads');
  return text.split('\n').filter((l) => l.trim()).map((l) => l.replace(/_:[A-Za-z0-9_.-]+/g, '_:')).sort();
}

const QUERIES = [
  'SELECT ?s ?o WHERE { ?s <http://ex.org/p> ?o }',
  'SELECT * WHERE { ?s ?p ?o }',
  'SELECT ?g ?s ?o WHERE { GRAPH ?g { ?s ?p ?o } }',
  'SELECT ?s ?n WHERE { GRAPH <http://ex.org/g1> { ?s <http://ex.org/q> ?n } }',
  'SELECT ?s ?x WHERE { ?s <http://ex.org/p> ?o . ?o <http://ex.org/q> ?x }',
  'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }',
  'SELECT ?s WHERE { ?s <http://ex.org/q> ?n FILTER (?n > 6) }',
  'SELECT ?l WHERE { ?c <http://www.w3.org/2000/01/rdf-schema#label> ?l FILTER (LANG(?l) = "fr") }',
  'SELECT ?s (EXISTS { ?s <http://ex.org/q> ?x } AS ?e) WHERE { ?s <http://ex.org/p> ?o }',
  'ASK { <http://ex.org/a> <http://ex.org/q> 5 }',
  'ASK { <http://ex.org/a> <http://ex.org/q> 6 }',
];
const CONSTRUCTS = [
  'CONSTRUCT { ?o <http://ex.org/r> ?s } WHERE { ?s <http://ex.org/p> ?o }',
];

test('openSbm11Store answers as query() over the same quads', { skip }, async () => {
  const { root, packed, cleanup } = storeRoot();
  const ref = await f.parse(readFileSync(dataNq, 'utf8'), { format: 'nquads' });
  const store = await f.openSbm11Store(root);
  try {
    assert.equal(store.generation, 'gen', packed);
    assert.equal(store.quads, 9);
    const paths = new Set();
    for (const q of QUERIES) {
      const got = await store.query(q);
      const want = await f.query(ref, q);
      paths.add(store.explain().path);
      if (typeof want === 'boolean') assert.equal(got, want, q);
      else assert.deepEqual(rowKeys(got), rowKeys(want), q);
    }
    for (const q of CONSTRUCTS) {
      const got = await store.query(q);
      const want = await f.query(ref, q);
      assert.deepEqual(await linesOf(got), await linesOf(want), q);
    }
    // both paths ran: the id path and the reference fallback (EXISTS in SELECT)
    assert.deepEqual([...paths].sort(), ['ids', 'reference']);
  } finally {
    await store.close();
    cleanup();
  }
  assert.equal(store.closed, true);
  await store.close(); // idempotent
});

test('openSbm11Store refuses a root with no store, and a closed handle', { skip }, async () => {
  await assert.rejects(() => f.openSbm11Store(join(fixture, 'no-such-store')), /no such object/);
  await assert.rejects(() => f.openSbm11Store(''), TypeError);
  const store = await f.openSbm11Store(join(fixture, 'store'));
  await store.close();
  await assert.rejects(() => store.query('ASK {}'), (err) => err.code === 'handle.disposed');
});

test('openSbm11Store takes a caller host', { skip }, async () => {
  const files = new Map();
  const base = join(fixture, 'store');
  const host = {
    read(_root, name, off, len) {
      if (!files.has(name)) {
        try { files.set(name, readFileSync(join(base, name))); } catch (_e) { return null; }
      }
      const b = files.get(name);
      return off + len <= b.length ? new Uint8Array(b.subarray(off, off + len)) : null;
    },
    size(_root, name) {
      try { return readFileSync(join(base, name)).length; } catch (_e) { return -1; }
    },
  };
  const store = await f.openSbm11Store('memory:sbm11-sample', { host });
  try {
    assert.equal(await store.query('ASK { <http://ex.org/b> <http://ex.org/q> 7 }'), true);
  } finally {
    await store.close();
  }
});
