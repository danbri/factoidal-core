// A graph is a set of triples (RDF 1.1 Concepts section 3), a dataset a
// default graph plus named graphs that are each a set (section 4).
// https://github.com/danbri/factoidal/issues/966: npm parse kept a triple
// that the source stated twice. The Lean parse gives a set of quads since
// commit 10f799c7 (Dataset.toSet; Wasm/GraphSetTests.lean). These cases check
// every npm surface that builds or returns a Dataset. No RDF logic is here:
// the assertions only read sizes, rows and text that the engine answers.

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';

const T = '<http://e/s> <http://e/p> <http://e/o>';
const NT = `${T} .\n${T} .\n`;
const ALL = 'SELECT ?o WHERE { ?s ?p ?o }';
const lines = (s) => s.split('\n').filter((l) => l.trim() !== '');

async function oneTriple(ds) {
  assert.equal(ds.size, 1);
  assert.equal(lines(ds.toNQuads()).length, 1);
  assert.equal((await f.query(ds, ALL)).length, 1);
}

const SOURCES = {
  ntriples: NT,
  turtle: `@prefix e: <http://e/> . e:s e:p e:o . e:s e:p e:o .\n`,
  'turtle:list': `@prefix e: <http://e/> . e:s e:p e:o, e:o .\n`,
  nquads: `${T} <http://e/g> .\n${T} <http://e/g> .\n`,
  trig: `@prefix e: <http://e/> . e:g { e:s e:p e:o . e:s e:p e:o } e:g { e:s e:p e:o }\n`,
  rdfxml: '<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" xmlns:e="http://e/">' +
    '<rdf:Description rdf:about="http://e/s"><e:p rdf:resource="http://e/o"/><e:p rdf:resource="http://e/o"/></rdf:Description>' +
    '<rdf:Description rdf:about="http://e/s"><e:p rdf:resource="http://e/o"/></rdf:Description></rdf:RDF>',
  jsonld: '{"@id":"http://e/s","http://e/p":[{"@id":"http://e/o"},{"@id":"http://e/o"}]}',
};

for (const [format, text] of Object.entries(SOURCES)) {
  test(`parse ${format}: a repeated triple is one triple`, async () => {
    const ds = await f.parse(text, { format: format.split(':')[0] });
    assert.equal(ds.size, 1);
    assert.equal(lines(ds.toNQuads()).length, 1);
    const rows = await f.query(ds, 'SELECT ?o WHERE { { ?s ?p ?o } UNION { GRAPH ?g { ?s ?p ?o } } }');
    assert.equal(rows.length, 1);
    ds.dispose();
  });
}

test('parse with the format inferred, N-Triples text', async () => {
  const ds = await f.parse(NT);
  await oneTriple(ds);
  ds.dispose();
});

test('query and serialize and canonicalize take the text directly', async () => {
  assert.equal((await f.query(NT, ALL, 'ntriples')).length, 1);
  assert.equal(lines(await f.serialize(NT, 'nquads')).length, 1);
  assert.equal(lines(await f.canonicalize(NT)).length, 1);
});

test('jsonldToRdf: a repeated value is one triple', async () => {
  const ds = await f.jsonldToRdf(SOURCES.jsonld);
  await oneTriple(ds);
  ds.dispose();
});

test('fromQuads: the same quad given twice is one quad', async () => {
  const q = { subject: { termType: 'NamedNode', value: 'http://e/s' },
    predicate: { termType: 'NamedNode', value: 'http://e/p' },
    object: { termType: 'NamedNode', value: 'http://e/o' },
    graph: { termType: 'DefaultGraph', value: '' } };
  const ds = await f.fromQuads([q, { ...q }]);
  assert.equal(ds.size, 1);
  ds.dispose();
});

test('Dataset.add of a quad the dataset has keeps one quad', async () => {
  const ds = await f.parse(NT);
  ds.add([...ds][0]);
  assert.equal(ds.size, 1);
  ds.dispose();
});

test('update: INSERT DATA of a triple the graph has changes nothing', async () => {
  const ds = await f.update(NT, `INSERT DATA { ${T} }`, 'ntriples');
  await oneTriple(ds);
  ds.dispose();
});

test('CONSTRUCT over two graphs that share a triple answers one triple (union)', async () => {
  const nq = `${T} <http://e/g1> .\n${T} <http://e/g2> .\n`;
  const ds = await f.parse(nq, { format: 'nquads' });
  assert.equal(ds.size, 2); // two graphs, two quads
  const out = await f.query(ds, 'CONSTRUCT { ?s ?p ?o } WHERE { GRAPH ?g { ?s ?p ?o } }');
  const res = out instanceof f.Dataset ? out : await f.parse(String(out), { format: 'ntriples' });
  assert.equal(res.size, 1);
  ds.dispose();
});

test('DESCRIBE answers each triple once', async () => {
  const ds = await f.parse(NT);
  const out = await f.query(ds, 'DESCRIBE <http://e/s>');
  const res = out instanceof f.Dataset ? out : await f.parse(String(out), { format: 'ntriples' });
  assert.equal(res.size, 1);
  ds.dispose();
});

for (const regime of ['rdfs', 'rho-df', 'rdfs-plus', 'owl-rl']) {
  test(`closure ${regime}: a repeated triple stays one triple`, async () => {
    const ds = await f.parse(`${T} .\n${T} .\n`);
    const c = await f.closure(ds, regime);
    const rows = (await f.query(c, 'SELECT * WHERE { <http://e/s> <http://e/p> <http://e/o> }'));
    assert.equal(rows.length, 1);
    const all = lines(c.toNQuads());
    assert.equal(new Set(all).size, all.length);
    ds.dispose();
    c.dispose();
  });
}

test('the union of two graphs that share a triple is one triple (isomorphism with the single graph)', async () => {
  const a = await f.parse(`${T} .\n<http://e/s> <http://e/p> <http://e/a> .\n`);
  const b = await f.parse(`${T} .\n<http://e/s> <http://e/p> <http://e/b> .\n`);
  const u = await f.parse(a.toNQuads() + b.toNQuads());
  assert.equal(u.size, 3);
  assert.equal(lines(u.toNQuads()).length, 3);
  a.dispose(); b.dispose(); u.dispose();
});
