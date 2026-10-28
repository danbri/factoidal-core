// query() and Dataset.query with both `sparql12` and `entail`: the engine
// closes the dataset under the regime and runs the SPARQL 1.2 evaluator
// (wasm op datasetQuery12Entail, https://github.com/danbri/factoidal/issues/1109).

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';

const DATA = `VERSION "1.2"
PREFIX ex: <http://example.org/>
PREFIX owl: <http://www.w3.org/2002/07/owl#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
ex:dave ex:said <<( ex:bob ex:likes ex:tea )>> .
ex:bob owl:sameAs ex:robert .
ex:r1 rdf:reifies <<( ex:bob ex:likes ex:tea )>> ; ex:source ex:diary .
ex:diary a ex:Notebook .
ex:Notebook rdfs:subClassOf ex:Document .
`.replace('rdf:reifies', '<http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies>');
const P = 'PREFIX ex: <http://example.org/>\n';

test('OWL-RL: owl:sameAs inside a triple term, in one SPARQL 1.2 query', async () => {
  const ds = await f.parse(DATA, { format: 'turtle12' });
  const q = P + 'ASK { ex:dave ex:said <<( ex:robert ex:likes ex:tea )>> }';
  assert.equal(await ds.query(q, { sparql12: true, entail: 'OWL-RL' }), true);
  assert.equal(await ds.query(q, { sparql12: true }), false);
});

test('RDFS: a reifier pattern joined with an entailed type', async () => {
  const ds = await f.parse(DATA, { format: 'turtle12' });
  const q = P + 'SELECT ?r WHERE { ?r <http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> <<( ex:bob ex:likes ?o )>> ; ex:source ?s . ?s a ex:Document }';
  const rows = await ds.query(q, { version: '1.2', entail: 'RDFS' });
  assert.deepEqual(rows.map((r) => r.get('r').value), ['http://example.org/r1']);
  assert.deepEqual(await ds.query(q, { version: '1.2' }), []);
});

test('the store is not changed by the closure', async () => {
  const ds = await f.parse(DATA, { format: 'turtle12' });
  const before = ds.size;
  await ds.query(P + 'ASK { ?s ?p ?o }', { sparql12: true, entail: 'OWL-RL' });
  assert.equal(ds.size, before);
});

test('output with SPARQL 1.2 is still refused', async () => {
  const ds = await f.parse(DATA, { format: 'turtle12' });
  await assert.rejects(ds.query(P + 'ASK { ?s ?p ?o }', { sparql12: true, entail: 'RDFS', output: 'csv' }),
    (e) => e.code === 'option.conflict');
});
