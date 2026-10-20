// The engine-resident Dataset (https://github.com/danbri/factoidal/issues/882
// item 1): one class, data kept in the wasm, producers answer it, consumers
// take it or text, explicit options, unknown option keys throw.

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';

const TTL = '@prefix ex: <http://example.org/> .\n' +
  'ex:alice ex:name "Alice" ; ex:knows ex:bob .\nex:bob ex:name "Bob" .\n';

test('parse answers a Dataset held in the engine', async () => {
  const ds = await f.parse(TTL, { format: 'turtle' });
  assert.ok(ds instanceof f.Dataset);
  assert.equal(typeof ds.handle, 'string');
  assert.equal(ds.size, 3);
  assert.equal(ds.format, 'turtle');
  assert.equal(ds.formatInferred, false);
  assert.deepEqual(ds.prefixes, { ex: 'http://example.org/' });
  assert.equal([...ds].length, 3);
  ds.dispose();
});

test('format inference only when the format is omitted, and it is reported', async () => {
  const ds = await f.parse(TTL);
  assert.equal(ds.formatInferred, true);
  assert.equal(ds.format, 'turtle12');
  ds.dispose();
  // An explicit format is never overridden: N-Triples refuses Turtle syntax.
  await assert.rejects(f.parse(TTL, { format: 'ntriples' }));
  // An inference that fails says so.
  await assert.rejects(f.parse('<http://e/a> <http://e/p> "x" <http://e/g> .'),
    (err) => /format inferred as 'turtle12'/.test(err.message) && err.formatInferred === true);
  const nq = await f.parse('<http://e/a> <http://e/p> "x" <http://e/g> .\n', { format: 'nquads' });
  assert.equal(nq.size, 1);
  nq.dispose();
});

test('Dataset methods: query, update in place, closure, validate, clone', async () => {
  const ds = await f.parse(TTL, { format: 'turtle' });
  const rows = await ds.query('SELECT ?n WHERE { ?s <http://example.org/name> ?n } ORDER BY ?n');
  assert.deepEqual(rows.map((r) => r.get('n').value), ['Alice', 'Bob']);
  assert.equal(await ds.query('ASK { ?s ?p ?o }'), true);
  const c = await ds.query('CONSTRUCT { ?s a <http://e/P> } WHERE { ?s <http://example.org/name> ?n }');
  assert.ok(c instanceof f.Dataset);
  assert.equal(c.size, 2);
  const copy = ds.clone();
  assert.equal(await ds.update('INSERT DATA { <http://e/x> <http://e/y> <http://e/z> }'), ds);
  assert.equal(ds.size, 4);
  assert.equal(copy.size, 3);
  const onto = await f.parse('<http://e/a> a <http://e/C> . <http://e/C> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://e/D> .', { format: 'ntriples' });
  const closed = await onto.closure('rdfs');
  assert.ok(closed instanceof f.Dataset);
  assert.equal(await closed.query('ASK { <http://e/a> a <http://e/D> }'), true);
  const shapes = '@prefix sh: <http://www.w3.org/ns/shacl#> . @prefix ex: <http://example.org/> .\n' +
    'ex:S a sh:NodeShape ; sh:targetSubjectsOf ex:knows ; sh:property [ sh:path ex:name ; sh:minCount 1 ] .';
  const v = await ds.validateShacl(shapes, { format: 'turtle' });
  assert.equal(v.conforms, true);
  assert.ok(v.report instanceof f.Dataset);
  assert.equal(await ds.validateShex('PREFIX ex: <http://example.org/>\nstart = @<S>\n<S> { ex:name . }',
    { focus: 'http://example.org/bob' }), true);
  for (const d of [ds, copy, c, onto, closed, v.report]) d.dispose();
});

test('a disposed Dataset throws a clear error; using disposes', async () => {
  const ds = await f.parse(TTL, { format: 'turtle' });
  ds.dispose();
  ds.dispose(); // idempotent
  assert.equal(ds.disposed, true);
  assert.throws(() => ds.size, /disposed/);
  await assert.rejects(ds.query('ASK {}'), /Dataset.query: the Dataset was disposed/);
  await assert.rejects(f.query(ds, 'ASK {}'), /disposed/);
  const d2 = await f.parse(TTL, { format: 'turtle' });
  {
    d2[Symbol.dispose]();
  }
  assert.equal(d2.disposed, true);
});

test('unknown option keys throw', async () => {
  await assert.rejects(f.parse(TTL, { fromat: 'turtle' }), /unknown option 'fromat'/);
  const ds = await f.parse(TTL, { format: 'turtle' });
  await assert.rejects(f.query(ds, 'ASK {}', { entailment: 'RDFS' }), /unknown option 'entailment'/);
  await assert.rejects(ds.serialize({ formt: 'turtle' }), /unknown option 'formt'/);
  await assert.rejects(f.csvwToRdf('a\n1\n', '', { modes: 'minimal' }), /unknown option 'modes'/);
  assert.throws(() => ds.toString({ format: 'turtle', bogus: 1 }), /unknown option 'bogus'/);
  ds.dispose();
});

test('producers answer a Dataset and consumers accept it with no text step', async () => {
  const csv = 'id,name\n1,a\n2,b\n';
  const meta = JSON.stringify({ '@context': 'http://www.w3.org/ns/csvw', url: 't.csv',
    tableSchema: { columns: [{ name: 'id' }, { name: 'name' }], aboutUrl: 'http://ex/r/{id}' } });
  const ds = await f.csvwToRdf(csv, meta, { url: 'http://ex/t.csv', mode: 'minimal' });
  assert.ok(ds instanceof f.Dataset);
  assert.equal(ds.size, 4);
  const rows = await f.query(ds, 'SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }');
  assert.equal(rows[0].get('c').value, '4');
  const jl = await f.jsonldToRdf('{"@id":"http://e/a","http://e/p":"v"}');
  assert.ok(jl instanceof f.Dataset);
  assert.equal(jl.size, 1);
  for (const d of [ds, jl]) d.dispose();
});

test('the functional update() answers a new Dataset and leaves its argument unchanged', async () => {
  const ds = await f.parse(TTL, { format: 'turtle' });
  const out = await f.update(ds, 'DELETE WHERE { ?s ?p ?o }');
  assert.equal(out.size, 0);
  assert.equal(ds.size, 3);
  out.dispose(); ds.dispose();
});

test('query results formats', async () => {
  const ds = await f.parse(TTL, { format: 'turtle' });
  const q = 'SELECT ?n WHERE { ?s <http://example.org/name> ?n } ORDER BY ?n';
  const csv = await ds.query(q, { output: 'csv' });
  assert.match(csv, /^n\r?\nAlice\r?\nBob/);
  const xml = await ds.query(q, { output: 'xml' });
  assert.match(xml, /<sparql/);
  const tsv = await ds.query(q, { output: 'tsv' });
  assert.match(tsv, /^\?n/);
  const json = await ds.query(q, { output: 'json' });
  assert.deepEqual(json.head.vars, ['n']);
  ds.dispose();
});

test('DatasetHandle is a deprecated alias of Dataset', () => {
  assert.equal(f.DatasetHandle, f.Dataset);
});
