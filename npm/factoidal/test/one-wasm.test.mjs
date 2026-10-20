// One wasm carries every capability (owner, 2026-10-20). The package ships
// l4factoidal.wasm only; before 0.10.0 the `./core` subpath loaded the
// smaller l4factoidal-core.wasm. This test reads the core dispatch table's op
// names from the Lean source (Wasm/CoreDispatch.lean, coreOpNames and
// coreIOOpNames) and checks the full engine serves each, then runs every JS
// function the core entry served against the full engine.

import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, existsSync } from 'node:fs';
import * as f from '../index.mjs';

const LEAN = new URL('../../../formal/lean4/Wasm/CoreDispatch.lean', import.meta.url);

function coreOpNames() {
  const src = readFileSync(LEAN, 'utf8');
  const names = [];
  for (const def of ['coreOpNames', 'coreIOOpNames']) {
    const i = src.indexOf(`def ${def} : List String :=`);
    assert.ok(i >= 0, `CoreDispatch.lean defines ${def}`);
    const body = src.slice(i, src.indexOf(']', i));
    for (const m of body.matchAll(/"([A-Za-z0-9]+)"/g)) names.push(m[1]);
  }
  return names;
}

test('the package ships no core wasm', () => {
  const pkg = JSON.parse(readFileSync(new URL('../package.json', import.meta.url), 'utf8'));
  assert.equal(pkg.exports['./core'], undefined);
  assert.equal(pkg.exports['./core-browser'], undefined);
  assert.ok(pkg.files.includes('!l4-assets/l4factoidal-core.*'));
});

test('the full engine serves every op of the core dispatch table', { skip: !existsSync(LEAN) }, async () => {
  const engine = await f.loadEngine();
  const served = new Set(engine.call('ops', []).ops);
  const core = coreOpNames();
  assert.ok(core.length >= 30, `read ${core.length} core op names`);
  const missing = core.filter((op) => !served.has(op));
  assert.deepEqual(missing, []);
});

test('every function the core entry served answers from the one wasm', async () => {
  const ttl = '@prefix ex: <http://e/> . ex:a a ex:C . ex:C <http://www.w3.org/2000/01/rdf-schema#subClassOf> ex:D .';
  const ds = await f.parse(ttl, { format: 'turtle' });
  assert.equal((await f.query(ds, 'SELECT * WHERE { ?s ?p ?o }')).length, 2);
  assert.equal(await f.query(ttl, 'ASK { <http://e/a> a <http://e/D> }', { format: 'turtle', entail: 'RDFS' }), true);
  const u = await f.update(ds, 'INSERT DATA { <http://e/x> <http://e/y> 1 }');
  assert.equal(u.size, 3);
  assert.match(await f.serialize(ds, { format: 'turtle' }), /ex:a a ex:C/);
  assert.match(await f.canonicalize(ds), /<http:\/\/e\/a>/);
  assert.equal((await f.owlClosure(ds, 'RDFS')).size >= 3, true);
  assert.equal((await f.coreRdfsClosure(ds)).size >= 3, true);
  assert.equal((await f.rdfsPlusClosure(ds)).size >= 3, true);
  assert.equal((await f.coreRdfsCheck(ds)).fragment, true);
  const v = await f.shaclValidate(ds, '<http://e/S> a <http://www.w3.org/ns/shacl#NodeShape> .', { format: 'turtle' });
  assert.equal(v.conforms, true);
  const raw = await f.queryRaw(ttl, 'SELECT ?s WHERE { ?s ?p ?o }', { dataFormat: 'turtle', output: 'csv' });
  assert.match(raw, /^s/);
  const len = await f.parse('<http://e/a> <http://e/p> "x" .\nBAD .\n', { format: 'ntriples', lenient: true });
  assert.equal(len.diagnostics.length, 1);
  const h = await f.openDataset(ttl, { format: 'turtle' });
  assert.equal(await h.query('ASK { ?s ?p ?o }', { sparql12: true }), true);
  const log = await f.deltaLogOpen('one-wasm-test');
  await f.deltaLogAppend(log, 'INSERT DATA { <http://e/a> <http://e/p> "v" }');
  assert.match(await f.deltaLogMerge(log, ''), /"v"/);
  await f.deltaLogDestroy(log);
  for (const d of [ds, u, h, v.report, len]) d.dispose();
});
