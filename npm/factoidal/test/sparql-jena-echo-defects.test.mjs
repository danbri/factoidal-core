// SPARQL and Dataset defects found by the Jena-style echo (danbri/echochamber,
// working name leana), fixed in the Lean engine. Each case is a plain assertion.
//
// https://github.com/danbri/factoidal/issues/1090 (extension functions with `output`)
// https://github.com/danbri/factoidal/issues/1094 (add/delete in a graph named by a blank node)
// https://github.com/danbri/factoidal/issues/1095 (IRI() in an Update uses the BASE)
// https://github.com/danbri/factoidal/issues/1096 (INSERT template with a literal graph name)

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';

const df = f.dataFactory;
const ex = (x) => df.namedNode('http://example/' + x);

test('#1090: Dataset.query with output calls a registered extension function (SPARQL 1.1 §17.6)', async () => {
  const iri = 'http://e/up-1090';
  await f.registerExtensionFunction(iri, () => ({ type: 'literal', value: 'ABC' }));
  try {
    const d = await f.openDataset('', 'nquads');
    const q = `SELECT (<${iri}>("abc") AS ?u) {}`;
    assert.equal([...(await d.query(q))][0].get('u').value, 'ABC');
    const j = await d.query(q, { output: 'json' });
    assert.deepEqual(j.results.bindings, [{ u: { type: 'literal', value: 'ABC' } }]);
    assert.equal(await d.query(q, { output: 'csv' }), 'u\r\nABC\r\n');
    assert.equal(await d.query(q, { output: 'tsv' }), '?u\n"ABC"\n');
    assert.match(await d.query(q, { output: 'xml' }), /<literal>ABC<\/literal>/);
    assert.match(await d.query(q, { output: 'table' }), /"ABC"/);
  } finally {
    await f.unregisterExtensionFunction(iri);
  }
});

test('#1090: an async extension function is resolved with output too', async () => {
  const iri = 'http://e/up-1090-async';
  await f.registerExtensionFunction(iri, async () => ({ type: 'literal', value: 'XYZ' }));
  try {
    const d = await f.openDataset('', 'nquads');
    const q = `SELECT (<${iri}>("x") AS ?u) {}`;
    assert.equal(await d.query(q, { output: 'csv' }), 'u\r\nXYZ\r\n');
  } finally {
    await f.unregisterExtensionFunction(iri);
  }
});

test('#1094: Dataset.add and Dataset.delete take a quad in a graph named by a blank node (RDF 1.1 Concepts §4)', async () => {
  const ds = await f.openDataset('', 'nquads');
  ds.add(df.quad(ex('s'), ex('p'), ex('o'), df.blankNode('g')));
  assert.equal(ds.size, 1);
  const [q] = [...ds];
  assert.equal(q.graph.termType, 'BlankNode');
  ds.add(df.quad(ex('s'), ex('p'), ex('o2'), q.graph));
  assert.equal(ds.size, 2);
  ds.add(q); // set semantics: no second copy
  assert.equal(ds.size, 2);
  ds.delete(q);
  assert.equal(ds.size, 1);
  assert.equal([...ds][0].object.value, 'http://example/o2');

  const ds2 = await f.openDataset('<http://example/s> <http://example/p> <http://example/o> _:g .\n', 'nquads');
  assert.equal(ds2.size, 1);
  ds2.delete([...ds2][0]);
  assert.equal(ds2.size, 0);
  // A quad in another graph named by a blank node is not deleted.
  const ds3 = await f.openDataset('<http://example/s> <http://example/p> <http://example/o> _:g .\n', 'nquads');
  ds3.delete(df.quad(ex('s'), ex('p'), ex('o'), df.blankNode('other')));
  assert.equal(ds3.size, 1);
});

test('#1095: IRI() in a SPARQL Update resolves against the BASE of the request (Query §17.4.2.8)', async () => {
  const a = await f.parse('', 'nquads');
  await a.update("BASE <http://www.example.org/> INSERT { ?s ?s ?s } WHERE { BIND(IRI('s') AS ?s) }");
  assert.equal(a.size, 1);
  const [q] = [...a];
  assert.equal(q.subject.value, 'http://www.example.org/s');
  assert.equal(q.predicate.value, 'http://www.example.org/s');
  assert.equal(q.object.value, 'http://www.example.org/s');
  const b = await f.parse('', 'nquads');
  await b.update("BASE <http://www.example.org/> INSERT { ?s ?s ?s } WHERE { BIND(URI('t') AS ?s) }");
  assert.equal([...b][0].subject.value, 'http://www.example.org/t');
});

test('#1096: an INSERT template quad whose graph name is a literal is not inserted (Update §3.1.3)', async () => {
  const b = await f.parse('', 'nquads');
  await b.update("INSERT { GRAPH ?g { <http://e/s> <http://e/p> <http://e/o> } } WHERE { BIND('g' AS ?g) }");
  assert.equal(b.toString({ format: 'nquads' }), '');
  // An unbound graph variable: the quad is not inserted either.
  await b.update('INSERT { GRAPH ?g { <http://e/s> <http://e/p> <http://e/o> } } WHERE {}');
  assert.equal(b.size, 0);
  // An IRI graph name is inserted into that graph.
  await b.update("INSERT { GRAPH ?g { <http://e/s> <http://e/p> <http://e/o> } } WHERE { BIND(<http://e/g> AS ?g) }");
  assert.equal(b.toString({ format: 'nquads' }), '<http://e/s> <http://e/p> <http://e/o> <http://e/g> .\n');
  // DELETE: a literal graph name removes nothing from the default graph.
  const c = await f.parse('<http://e/s> <http://e/p> <http://e/o> .\n', 'nquads');
  await c.update("DELETE { GRAPH ?g { <http://e/s> <http://e/p> <http://e/o> } } WHERE { BIND('g' AS ?g) }");
  assert.equal(c.size, 1);
});
