// https://github.com/danbri/factoidal/issues/876: the query ops (they evaluate
// on `indexedDatasetBackend`) see every named graph of RDF 1.1 Concepts
// section 4: a graph named by a blank node (part 2, fixed by
// https://github.com/danbri/factoidal-core/pull/75, graph names are `Subject`)
// and a named graph with no triple (part 1, fixed by
// https://github.com/danbri/factoidal-core/pull/94). These are the issue's own
// measurements, as plain assertions.

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';

const NQ = '_:b <http://e/p> <http://e/o> _:g .\n' +
  '<http://e/s> <http://e/p> <http://e/o> <http://e/g1> .\n';

// tests/sbm11/syntax/d5.trig: six named graphs, three IRIs (ex:g0 and ex:g2
// have no triple) and three blank nodes (_:e and [] have no triple).
const D5 = `@prefix ex: <http://example.org/> .
ex:s ex:p ex:o .
ex:g0 { }
ex:g1 { ex:a ex:p ex:b . }
GRAPH ex:g2 { }
_:b1 { ex:c ex:p "x" . }
_:e { }
[] { }
ex:g1 { ex:a2 ex:p ex:b2 }
`;

const row = (r) => ({ g: r.get('g').termType, s: r.get('s')?.termType });

test('GRAPH ?g binds ?g to a blank-node graph name (issue 876 part 2)', async () => {
  const ds = await f.parse(NQ, { format: 'nquads' });
  const rows = await ds.query('SELECT ?g ?s WHERE { GRAPH ?g { ?s ?p ?o } }');
  assert.deepEqual(rows.map(row).sort((a, b) => a.g.localeCompare(b.g)), [
    { g: 'BlankNode', s: 'BlankNode' },
    { g: 'NamedNode', s: 'NamedNode' },
  ]);
  const iri = rows.find((r) => r.get('g').termType === 'NamedNode');
  assert.equal(iri.get('g').value, 'http://e/g1');
  assert.equal(await ds.query('ASK { GRAPH ?g { ?s <http://e/p> <http://e/o> } FILTER(isBlank(?g)) }'), true);
});

test('GRAPH ?g { } gives every named graph of d5.trig, with and without triples (issue 876)', async () => {
  const ds = await f.parse(D5, { format: 'trig' });
  const rows = await ds.query('SELECT ?g WHERE { GRAPH ?g { } }');
  const kinds = rows.map((r) => r.get('g').termType);
  assert.equal(rows.length, 6);
  assert.equal(kinds.filter((k) => k === 'BlankNode').length, 3);
  assert.equal(kinds.filter((k) => k === 'NamedNode').length, 3);
});
