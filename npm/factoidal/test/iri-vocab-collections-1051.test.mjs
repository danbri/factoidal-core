// https://github.com/danbri/factoidal/issues/1051 items 4, 5 and 6: IRI split,
// the vocabulary table, RDF lists and containers. The engine decides each
// (formal/lean4/L4Factoidal/RDF/IriSplit.lean, VocabularyTable.lean,
// Collections.lean; the ops of Wasm/Ops/Terms.lean and Wasm/Ops/Collections.lean).
import './helpers.js';

import test from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';

const require = createRequire(import.meta.url);
const { ready, parse, splitIri, isNCName, vocabularies, memberIri, memberOrdinal,
  dataFactory: f, FactoidalError } = require('..');

const RDF = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#';

test('splitIri: the longest NCName suffix is the local name', async () => {
  await ready();
  assert.deepEqual(splitIri('http://e/ns#name'), { namespace: 'http://e/ns#', localName: 'name' });
  assert.deepEqual(splitIri(f.namedNode(RDF + 'type')), { namespace: RDF, localName: 'type' });
  assert.deepEqual(splitIri('http://e/123abc'), { namespace: 'http://e/123', localName: 'abc' });
  assert.deepEqual(splitIri('http://e/a.b-c_d'), { namespace: 'http://e/', localName: 'a.b-c_d' });
  assert.deepEqual(splitIri('http://e/a/'), { namespace: 'http://e/a/', localName: '' });
  assert.deepEqual(splitIri('urn:isbn:0451'), { namespace: 'urn:isbn:0451', localName: '' });
  for (const iri of ['http://e/ns#name', 'http://e/x%20y', 'urn:x:1', 'http://e/café']) {
    const { namespace, localName } = splitIri(iri);
    assert.equal(namespace + localName, iri);
    assert.ok(localName === '' || isNCName(localName), iri);
  }
});

test('isNCName: the prefix-label and local-name check', async () => {
  await ready();
  assert.equal(isNCName('ex'), true);
  assert.equal(isNCName('a.b-c'), true);
  assert.equal(isNCName('_x'), true);
  assert.equal(isNCName('1a'), false);
  assert.equal(isNCName('a:b'), false);
  assert.equal(isNCName('a b'), false);
  assert.equal(isNCName(''), false);
});

test('vocabularies: rdf, rdfs, xsd, owl with terms; the other namespaces', async () => {
  await ready();
  const v = vocabularies();
  const by = Object.fromEntries(v.map((r) => [r.prefix, r]));
  assert.deepEqual(v.map((r) => r.prefix), ['rdf', 'rdfs', 'xsd', 'owl', 'foaf', 'dcterms', 'dc', 'schema']);
  assert.equal(by.rdf.namespace, RDF);
  assert.equal(by.rdfs.namespace, 'http://www.w3.org/2000/01/rdf-schema#');
  assert.equal(by.xsd.namespace, 'http://www.w3.org/2001/XMLSchema#');
  assert.equal(by.owl.namespace, 'http://www.w3.org/2002/07/owl#');
  for (const t of ['type', 'first', 'rest', 'nil', 'langString', 'dirLangString', 'reifies']) {
    assert.ok(by.rdf.terms.includes(t), t);
  }
  for (const t of ['int', 'integer', 'dateTime', 'dateTimeStamp']) assert.ok(by.xsd.terms.includes(t), t);
  for (const t of ['Class', 'sameAs', 'Thing']) assert.ok(by.owl.terms.includes(t), t);
  assert.ok(by.rdfs.terms.includes('subClassOf'));
  assert.deepEqual(by.foaf.terms, []);
  assert.equal(by.rdf.terms.length, 24);
  assert.equal(by.rdfs.terms.length, 16);
  assert.equal(by.xsd.terms.length, 50);
  assert.equal(by.owl.terms.length, 79);
});

test('memberIri and memberOrdinal: rdf:_n', async () => {
  await ready();
  assert.equal(memberIri(3).value, RDF + '_3');
  assert.equal(memberIri(3).termType, 'NamedNode');
  assert.equal(memberOrdinal(RDF + '_12'), 12);
  assert.equal(memberOrdinal(f.namedNode(RDF + '_1')), 1);
  assert.equal(memberOrdinal(RDF + '_0'), null);
  assert.equal(memberOrdinal(RDF + '_01'), null);
  assert.equal(memberOrdinal(RDF + 'type'), null);
  assert.throws(() => memberIri(0), (e) => e instanceof FactoidalError && e.code === 'call.arguments');
});

const LISTS = `@prefix : <http://e/> .
:s :p ( :a "b" 3 ) .
:s :empty () .
:bad1 :p _:n1 . _:n1 <${RDF}first> :x .
:bad2 :p _:c1 . _:c1 <${RDF}first> :x ; <${RDF}rest> _:c2 . _:c2 <${RDF}first> :y ; <${RDF}rest> _:c1 .
:bad3 :p _:m1 . _:m1 <${RDF}first> :x , :y ; <${RDF}rest> <${RDF}nil> .
`;

test('Dataset.listItems: the items in order; rdf:nil is empty', async () => {
  const ds = await parse(LISTS, { format: 'turtle' });
  const head = ds.match(f.namedNode('http://e/s'), f.namedNode('http://e/p')).toArray()[0].object;
  const items = ds.listItems(head);
  assert.deepEqual(items.map((t) => [t.termType, t.value]),
    [['NamedNode', 'http://e/a'], ['Literal', 'b'], ['Literal', '3']]);
  assert.equal(items[2].datatype.value, 'http://www.w3.org/2001/XMLSchema#integer');
  assert.deepEqual(ds.listItems(f.namedNode(RDF + 'nil')), []);
  assert.deepEqual(ds.listItems(head, f.defaultGraph()).length, 3);
  // The list is in the default graph only.
  assert.throws(() => ds.listItems(head, f.namedNode('http://e/g')),
    (e) => e instanceof FactoidalError && e.code === 'op.failed' && /no-first/.test(e.message));
  ds.dispose();
});

test('Dataset.listItems: a list that is not well formed is refused with the reason', async () => {
  const ds = await parse(LISTS, { format: 'turtle' });
  const headOf = (s) => ds.match(f.namedNode('http://e/' + s), f.namedNode('http://e/p')).toArray()[0].object;
  const refused = (s, reason) => assert.throws(() => ds.listItems(headOf(s)),
    (e) => e instanceof FactoidalError && e.code === 'op.failed' && e.message.includes(`(${reason})`), s);
  refused('bad1', 'no-rest');
  refused('bad2', 'cycle');
  refused('bad3', 'branch');
  assert.throws(() => ds.listItems(f.namedNode('http://e/nothing')), /no-first/);
  ds.dispose();
});

test('Dataset.addList: builds a list on fresh blank nodes; listItems gives it back', async () => {
  const ds = await parse(LISTS, { format: 'turtle' });
  const before = ds.size;
  const items = [f.namedNode('http://e/x'), f.literal('y', 'en'), f.blankNode('z')];
  const head = ds.addList(items);
  assert.equal(head.termType, 'BlankNode');
  assert.equal(ds.size, before + 6);
  assert.deepEqual(ds.listItems(head).map((t) => t.value).slice(0, 2), ['http://e/x', 'y']);
  // A second list does not share a node with the first.
  const head2 = ds.addList([f.literal('1')]);
  assert.notEqual(head2.value, head.value);
  assert.equal(ds.listItems(head).length, 3);
  assert.equal(ds.addList([]).value, RDF + 'nil');
  assert.equal(ds.size, before + 8);
  // A named graph.
  const g = f.namedNode('http://e/g');
  const h3 = ds.addList([f.literal('in g')], g);
  assert.equal(ds.listItems(h3, g)[0].value, 'in g');
  ds.dispose();
});

const CONTAINERS = `@prefix : <http://e/> . @prefix rdf: <${RDF}> .
:c a rdf:Seq ; rdf:_2 "two" ; rdf:_1 "one" ; rdf:_10 "ten" ; :other "x" .
:b a rdf:Bag ; rdf:_1 :m .
:plain rdf:_3 "three" .
`;

test('Dataset.containerItems: members sorted by n, and the kind', async () => {
  const ds = await parse(CONTAINERS, { format: 'turtle' });
  const c = ds.containerItems(f.namedNode('http://e/c'));
  assert.equal(c.kind.value, RDF + 'Seq');
  assert.deepEqual(c.items.map((m) => [m.ordinal, m.term.value]), [[1, 'one'], [2, 'two'], [10, 'ten']]);
  assert.equal(ds.containerItems(f.namedNode('http://e/b')).kind.value, RDF + 'Bag');
  const p = ds.containerItems(f.namedNode('http://e/plain'));
  assert.equal(p.kind, null);
  assert.deepEqual(p.items.map((m) => m.ordinal), [3]);
  assert.deepEqual(ds.containerItems(f.namedNode('http://e/none')).items, []);
  // Build one with memberIri.
  for (const [i, v] of ['p', 'q'].entries()) {
    ds.add(f.quad(f.namedNode('http://e/new'), memberIri(i + 1), f.literal(v)));
  }
  assert.deepEqual(ds.containerItems(f.namedNode('http://e/new')).items.map((m) => m.term.value), ['p', 'q']);
  ds.dispose();
});
