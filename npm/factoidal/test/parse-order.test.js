// What parse() promises about blank nodes and statement order
// (README.md "Blank nodes, labels and statement order";
// https://github.com/danbri/factoidal/issues/683), stated as the
// properties RDF fixes rather than as label text or line order:
//
//   1. Each `[ ... ]` in a Turtle document denotes its own blank node
//      (RDF 1.1 Turtle §2.6), joined to the statements inside it.
//   2. The returned Dataset is the SET of the document's statements: equal,
//      up to blank-node relabelling (RDF 1.1 Concepts §3.6, isomorphism),
//      to the same graph written with explicit labels. RDFC-1.0
//      canonicalization decides the isomorphism.
//   3. Blank nodes of two parse() calls never join (one call is one
//      document).
//
// The label TEXT (`p<k>_d<n>_anon_<i>` on the Lean engine) and the ORDER of
// the N-Quads lines are not part of the contract; nothing here pins them.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');

const { parse, canonicalize, dataFactory: df } = require('..');

// Document order is charlie, alice, bravo: deliberately not alphabetical.
const TTL = `
  @prefix ex: <http://example.org/> .
  ex:charlie ex:p [ ex:q "c" ] .
  ex:alice   ex:p [ ex:q "a" ] .
  ex:bravo   ex:p [ ex:q "b" ] .
`;

// The same graph with explicit blank-node labels.
const LABELLED_NT = [
  '<http://example.org/charlie> <http://example.org/p> _:x .',
  '_:x <http://example.org/q> "c" .',
  '<http://example.org/alice> <http://example.org/p> _:y .',
  '_:y <http://example.org/q> "a" .',
  '<http://example.org/bravo> <http://example.org/p> _:z .',
  '_:z <http://example.org/q> "b" .',
].join('\n');

function bnodeObjectOf(ds, localName) {
  const quads = [...ds.match(df.namedNode('http://example.org/' + localName),
    df.namedNode('http://example.org/p'))];
  assert.equal(quads.length, 1, `exactly one ex:p triple for ex:${localName}`);
  assert.equal(quads[0].object.termType, 'BlankNode');
  return quads[0].object;
}

test('each [] is its own blank node, joined to the statements inside it', async () => {
  const ds = await parse(TTL);
  const q = df.namedNode('http://example.org/q');
  const seen = new Set();
  for (const [name, value] of [['charlie', 'c'], ['alice', 'a'], ['bravo', 'b']]) {
    const b = bnodeObjectOf(ds, name);
    seen.add(b.value);
    const inner = [...ds.match(b, q)];
    assert.equal(inner.length, 1, `ex:${name}'s blank node has one ex:q statement`);
    assert.equal(inner[0].object.value, value, `ex:${name}'s blank node carries ex:q "${value}"`);
  }
  assert.equal(seen.size, 3, 'three distinct blank nodes');
});

test('the Dataset is the document graph: isomorphic to the labelled form (RDFC-1.0)', async () => {
  const ds = await parse(TTL);
  assert.equal(ds.size, 6, 'three ex:p triples + three ex:q triples');
  assert.equal(ds.toNQuads().trim().split('\n').length, 6);
  assert.equal(await canonicalize(ds), await canonicalize(LABELLED_NT, { format: 'ntriples' }));
});

test('blank nodes of two parse() calls never join', async () => {
  const [a, b] = [await parse(TTL), await parse(TTL)];
  assert.ok(!bnodeObjectOf(a, 'alice').equals(bnodeObjectOf(b, 'alice')),
    'the same [] in two documents is two blank nodes');
});
