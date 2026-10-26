// The wrong answers of the 2026-10-21 JS glue audit, one test each
// (https://github.com/danbri/factoidal/issues/894). Each failed on main
// before the RDF decisions moved into Lean ops, and passes after.

import test from 'node:test';
import assert from 'node:assert/strict';
import * as api from '../index.mjs';
import { dataFactory as df, DatasetCore, termToNQuads, nquadsToQuads } from '../rdfjs.mjs';
import { createRequire } from 'node:module';

const require = createRequire(import.meta.url);
const fn = require('../fn.js');

const XSD = 'http://www.w3.org/2001/XMLSchema#';

test('N-Quads writer: \\b and \\f are escaped as the engine escapes them (finding 1)', async () => {
  await api.parse('', { format: 'nquads' }); // loads the engine
  const lit = df.literal('a\bb\fc');
  const ds = await api.parse('<http://e/s> <http://e/p> "a\\bb\\fc" .\n', { format: 'nquads' });
  const engineLine = ds.toNQuads();
  const token = termToNQuads(lit);
  assert.ok(!token.includes('\b') && !token.includes('\f'), `raw control character in ${JSON.stringify(token)}`);
  assert.equal(`<http://e/s> <http://e/p> ${token} .\n`, engineLine);
  ds.dispose();
});

test('N-Quads reader: a line the grammar rejects is rejected (finding 2)', async () => {
  await api.parse('', { format: 'nquads' });
  // An IRIREF may not contain a space (RDF 1.2 N-Quads grammar, production IRIREF).
  assert.throws(() => DatasetCore.fromNQuads('<http://e/a b> <http://e/p> <http://e/o> .\n'));
  assert.throws(() => nquadsToQuads('<http://e/a> <http://e/p> "x"^^<http://e/d d> .\n'));
  // a grammatical line still reads
  assert.equal(nquadsToQuads('<http://e/a> <http://e/p> "x\\u0041" .\n')[0].object.value, 'xA');
});

test('isomorphism: blank nodes inside triple terms (finding 4)', async () => {
  const a = await fn.parse('<http://e/s> <http://e/p> <<( _:x <http://e/q> <http://e/o> )>> .\n',
    { format: 'nquads12' });
  const b = await fn.parse('<http://e/s> <http://e/p> <<( _:y <http://e/q> <http://e/o> )>> .\n',
    { format: 'nquads12' });
  assert.equal(await fn.equals(a, b), true);
  const c = await fn.parse('<http://e/s> <http://e/p> <<( <http://e/z> <http://e/q> <http://e/o> )>> .\n',
    { format: 'nquads12' });
  assert.equal(await fn.equals(a, c), false);
});

test('extension function answer 1e21 is an xsd:double in canonical form (finding 5)', async () => {
  const iri = 'urn:x-test:big894';
  api.registerExtensionFunction(iri, () => 1e21);
  try {
    const rows = await api.query('<http://e/s> <http://e/p> <http://e/o> .',
      `SELECT ?x WHERE { BIND(<${iri}>() AS ?x) }`);
    const x = rows[0].get('x');
    assert.equal(x.datatype.value, XSD + 'double');
    assert.equal(x.value, '1.0E21');
  } finally {
    api.unregisterExtensionFunction(iri);
  }
});

test('extension function answers: integer, fraction, -0, boolean (finding 5)', async () => {
  const cases = [[7, '7', 'integer'], [0.1, '1.0E-1', 'double'], [-0, '-0.0E0', 'double'],
    [true, 'true', 'boolean'], [2 ** 60, '1.152921504606847E18', 'double']];
  for (const [value, lex, dt] of cases) {
    const iri = 'urn:x-test:v894';
    api.registerExtensionFunction(iri, () => value);
    try {
      const rows = await api.query('<http://e/s> <http://e/p> <http://e/o> .',
        `SELECT ?x WHERE { BIND(<${iri}>() AS ?x) }`);
      const x = rows[0].get('x');
      assert.equal(x.value, lex, `value ${value}`);
      assert.equal(x.datatype.value, XSD + dt, `value ${value}`);
    } finally {
      api.unregisterExtensionFunction(iri);
    }
  }
});

test('graph names: an IRI and a blank node with the same string are two graphs (finding 6)', async () => {
  const s = df.namedNode('http://e/s');
  const p = df.namedNode('http://e/p');
  const ds = fn.fromDataset(new DatasetCore([
    df.quad(s, p, df.literal('1'), df.namedNode('urn:g')),
    df.quad(s, p, df.literal('2'), df.blankNode('urn:g')),
  ]));
  const gs = fn.graphs(ds);
  assert.equal(gs.length, 2);
});

test('graph names through the engine: datasetGraphNames distinguishes IRI and blank node', async () => {
  const ds = await api.parse('<http://e/s> <http://e/p> "1" <http://e/g> .\n<http://e/s> <http://e/p> "2" _:g .\n',
    { format: 'nquads' });
  const gs = api.graphs(ds);
  assert.equal(gs.length, 2);
  for (const [, g] of gs) g.dispose();
  ds.dispose();
});
