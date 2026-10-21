// An extension function may answer with an exact RDF term: the application
// chooses the datatype IRI and the lexical form, and the engine keeps them
// (RDF 1.1 Concepts 3.3). The engine checks only what RDF requires.
// One term-string reader: every API that takes a term as a string reads it
// as one N-Triples term, so `_:x` is a blank node and `<...>` an IRI.
// https://github.com/danbri/factoidal/issues/894

import test from 'node:test';
import assert from 'node:assert/strict';
import {
  parse, query, graphs, shexValidate, dataFactory as df,
  registerExtensionFunction, clearExtensionFunctions,
} from '../index.mjs';

const EX = 'http://example.org/fn#';
const XSD = 'http://www.w3.org/2001/XMLSchema#';
const RDF = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#';
const DATA = '<http://e/a> <http://e/p> "1" .\n';

test.afterEach(async () => { await clearExtensionFunctions(); });

async function answer (fn) {
  await registerExtensionFunction(`${EX}f`, fn);
  const rows = await query(DATA, `SELECT ?x WHERE { ?s ?p ?o BIND(<${EX}f>(?o) AS ?x) }`,
    { format: 'ntriples' });
  assert.equal(rows.length, 1);
  return rows[0].get('x');
}

test('"007"^^xsd:integer is kept as given', async () => {
  const t = await answer(() => df.literal('007', df.namedNode(`${XSD}integer`)));
  assert.equal(t.termType, 'Literal');
  assert.equal(t.value, '007');
  assert.equal(t.datatype.value, `${XSD}integer`);
});

test('plain object {value, datatype}: custom datatype IRI kept', async () => {
  const t = await answer(() => ({ value: 'x/y', datatype: 'http://example.org/dt#path' }));
  assert.equal(t.value, 'x/y');
  assert.equal(t.datatype.value, 'http://example.org/dt#path');
});

test('"1e21"^^xsd:double is kept as given (no canonical form)', async () => {
  const t = await answer(() => ({ value: '1e21', datatype: df.namedNode(`${XSD}double`) }));
  assert.equal(t.value, '1e21');
  assert.equal(t.datatype.value, `${XSD}double`);
});

test('ill-typed "abc"^^xsd:integer is still a literal, kept as given', async () => {
  const t = await answer(() => ({ value: 'abc', datatype: `${XSD}integer` }));
  assert.equal(t.value, 'abc');
  assert.equal(t.datatype.value, `${XSD}integer`);
});

test('language tag and base direction', async () => {
  const t = await answer(() => ({ value: 'שלום', language: 'he', direction: 'rtl' }));
  assert.equal(t.value, 'שלום');
  assert.equal(t.language, 'he');
  assert.equal(t.direction, 'rtl');
  assert.equal(t.datatype.value, `${RDF}dirLangString`);
  const u = await answer(() => df.literal('colour', 'en-GB'));
  assert.equal(u.language.toLowerCase(), 'en-gb');
  assert.equal(u.datatype.value, `${RDF}langString`);
});

test('NamedNode and BlankNode answers', async () => {
  const n = await answer(() => df.namedNode('http://example.org/x'));
  assert.equal(n.termType, 'NamedNode');
  assert.equal(n.value, 'http://example.org/x');
  const b = await answer(() => df.blankNode('b7'));
  assert.equal(b.termType, 'BlankNode');
});

test('triple-term answer (RDF 1.2)', async () => {
  const t = await answer(() => df.quad(df.namedNode('http://e/s'), df.namedNode('http://e/p'),
    df.literal('o')));
  assert.equal(t.termType, 'Quad');
  assert.equal(t.subject.value, 'http://e/s');
  assert.equal(t.object.value, 'o');
});

test('relative datatype IRI is the 17.6 expression error', async () => {
  const t = await answer(() => ({ value: '1', datatype: 'integer' }));
  assert.equal(t, undefined);
});

test('invalid language tag is the 17.6 expression error', async () => {
  assert.equal(await answer(() => ({ value: 'a', language: 'en_US' })), undefined);
  assert.equal(await answer(() => ({ value: 'a', language: 'en', direction: 'up' })), undefined);
});

test('plain JavaScript numbers still go through jsLiteral', async () => {
  const big = await answer(() => 1e21);
  assert.equal(big.datatype.value, `${XSD}double`);
  assert.equal(big.value, '1.0E21');
  const small = await answer(() => 7);
  assert.equal(small.datatype.value, `${XSD}integer`);
  assert.equal(small.value, '7');
});

test('a JavaScript string "_:x" answer is a string literal, never a blank node', async () => {
  const t = await answer(() => '_:x');
  assert.equal(t.termType, 'Literal');
  assert.equal(t.value, '_:x');
});

// ---------------------------------------------------------------- term strings

const GDATA = '<http://e/s> <http://e/p> "1" <urn:g> .\n<http://e/s> <http://e/p> "2" _:g .\n';

test('graphs(): an IRI and a blank node with the same text are two terms', async () => {
  const ds = await parse(GDATA, { format: 'nquads' });
  const gs = graphs(ds);
  const kinds = gs.map(([name]) => name.termType).sort();
  assert.deepEqual(kinds, ['BlankNode', 'NamedNode']);
  for (const [, g] of gs) g.dispose();
  ds.dispose();
});

test('match(): a string is one N-Triples term, `_:g` a blank node, `<urn:g>` an IRI', async () => {
  const ds = await parse(GDATA, { format: 'nquads' });
  // parse() scopes blank-node labels to the Dataset; graphs() reports the label
  const bnode = graphs(ds).find(([n]) => n.termType === 'BlankNode')[0];
  const viaIri = ds.match(null, null, null, '<urn:g>');
  assert.equal(viaIri.size, 1);
  assert.equal([...viaIri][0].object.value, '1');
  const viaBnode = ds.match(null, null, null, `_:${bnode.value}`);
  assert.equal(viaBnode.size, 1);
  assert.equal([...viaBnode][0].object.value, '2');
  const lit = ds.match(null, null, '"2"', null);
  assert.equal(lit.size, 1);
  assert.throws(() => ds.match(null, null, null, 'urn:g'), /quad pattern/);
  for (const d of [viaIri, viaBnode, lit]) d.dispose();
  ds.dispose();
});

test('shexValidate: focus `_:b` is a blank node, `<...>` an IRI, a bare IRI is refused', async () => {
  const data = '_:b <http://e/name> "B" .\n<http://e/a> <http://e/name> "A" .\n';
  const schema = 'PREFIX e: <http://e/>\ne:S { e:name LITERAL }\n';
  const ds = await parse(data, { format: 'nquads' });
  const b = [...ds].find((q) => q.subject.termType === 'BlankNode').subject;
  assert.equal(await ds.validateShex(schema, { focus: `_:${b.value}`, shape: '<http://e/S>' }), true);
  assert.equal(await ds.validateShex(schema, { focus: '_:nosuch', shape: '<http://e/S>' }), false);
  ds.dispose();
  assert.equal(await shexValidate(data, schema, '<http://e/a>', '<http://e/S>', { format: 'nquads' }), true);
  await assert.rejects(shexValidate(data, schema, 'http://e/a', '<http://e/S>', { format: 'nquads' }));
});
