// Two parser repairs, pinned through the package's own wasm module (the user
// path; the Lean build-time guards and the shell suites do not run it):
//
//   * RDF/XML: the scope of a property element closes with it
//     (https://github.com/danbri/factoidal/issues/841). The xml:lang and
//     xml:base of one property element must not reach the next one.
//   * JSON-LD: a blank node label that the document writes cannot equal a label
//     that the conversion generates
//     (https://github.com/danbri/factoidal/issues/840). A document that wrote
//     `_:_jld_anon0` and also held a node object with no @id read as one node.

'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');

const { parse } = require('..');

const RDF_NS = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#';
const rdfxml = (body, attrs = '') =>
  '<?xml version="1.0"?>\n' +
  `<rdf:RDF xmlns:rdf="${RDF_NS}" xmlns:ex="http://example.org/"${attrs}>` + body + '</rdf:RDF>';

const objectOf = (ds, predicate) => {
  const qs = [...ds].filter((q) => q.predicate.value === predicate);
  assert.equal(qs.length, 1, `one quad with predicate ${predicate}`);
  return qs[0].object;
};

test('RDF/XML: the xml:lang of a property element does not reach the next one', async () => {
  const ds = await parse(rdfxml(
    '<rdf:Description rdf:about="http://example.org/s">' +
    '<ex:p xml:lang="fr">a</ex:p><ex:q>b</ex:q></rdf:Description>'), { format: 'rdfxml' });
  assert.equal(ds.size, 2);
  const p = objectOf(ds, 'http://example.org/p');
  const q = objectOf(ds, 'http://example.org/q');
  assert.equal(p.language, 'fr');
  assert.equal(q.value, 'b');
  assert.equal(q.language, '', 'the second literal is a plain literal');
  assert.equal(q.datatype.value, 'http://www.w3.org/2001/XMLSchema#string');
});

test('RDF/XML: the language after a property element is the one of the node element', async () => {
  const ds = await parse(rdfxml(
    '<rdf:Description rdf:about="http://example.org/s" xml:lang="en">' +
    '<ex:p xml:lang="fr">a</ex:p><ex:q xml:lang="">b</ex:q><ex:r>c</ex:r></rdf:Description>'),
  { format: 'rdfxml' });
  assert.equal(objectOf(ds, 'http://example.org/p').language, 'fr');
  assert.equal(objectOf(ds, 'http://example.org/q').language, '');
  assert.equal(objectOf(ds, 'http://example.org/r').language, 'en');
});

test('RDF/XML: nested node elements and xml:base close with their property element', async () => {
  const ds = await parse(rdfxml(
    '<rdf:Description rdf:about="http://example.org/s">' +
    '<ex:p xml:lang="fr" xml:base="http://other.example/n/">' +
    '<rdf:Description rdf:about="m"><ex:r xml:lang="it">c</ex:r><ex:t>d</ex:t></rdf:Description>' +
    '</ex:p><ex:u rdf:resource="z"/><ex:w>e</ex:w></rdf:Description>',
    ' xml:base="http://example.org/dir/doc.rdf"'), { format: 'rdfxml' });
  assert.equal(objectOf(ds, 'http://example.org/p').value, 'http://other.example/n/m');
  assert.equal(objectOf(ds, 'http://example.org/r').language, 'it');
  assert.equal(objectOf(ds, 'http://example.org/t').language, 'fr');
  assert.equal(objectOf(ds, 'http://example.org/u').value, 'http://example.org/dir/z');
  assert.equal(objectOf(ds, 'http://example.org/w').language, '');
});

const COLLIDE = {
  '@context': { ex: 'http://example.org/' },
  '@graph': [
    { '@id': '_:_jld_anon0', 'ex:p': 'explicit _jld_anon0' },
    { 'ex:p': 'generated first' },
    { '@id': '_:_jld_anon1', 'ex:p': 'explicit _jld_anon1' },
    { 'ex:q': 'generated second' },
    { '@id': '_:genid1', 'ex:p': 'explicit genid1' },
  ],
};

test('JSON-LD: a written blank node label does not merge with a generated node', async () => {
  const ds = await parse(JSON.stringify(COLLIDE), { format: 'jsonld' });
  assert.equal(ds.size, 5);
  const subjects = new Set([...ds].map((q) => q.subject.value));
  assert.equal(subjects.size, 5, 'five nodes, five blank node labels');
  const byObject = new Map([...ds].map((q) => [q.object.value, q.subject.value]));
  // the node that wrote the label keeps its label, whatever the form of the label
  assert.match(byObject.get('explicit _jld_anon0'), /_jld_anon0$/);
  assert.notEqual(byObject.get('generated first'), byObject.get('explicit _jld_anon0'));
  assert.notEqual(byObject.get('generated second'), byObject.get('explicit _jld_anon1'));
});

test('JSON-LD: a list cell does not merge with a node that wrote the label of the first cell', async () => {
  const ds = await parse(JSON.stringify([
    { '@id': '_:_jld_anon0', 'http://example.org/p': [{ '@list': ['a', 'b'] }] },
  ]), { format: 'jsonld' });
  // the node, two cells: three blank nodes; one p quad, two rdf:first, two rdf:rest
  assert.equal(ds.size, 5);
  const blank = new Set();
  for (const q of ds) {
    if (q.subject.termType === 'BlankNode') blank.add(q.subject.value);
    if (q.object.termType === 'BlankNode') blank.add(q.object.value);
  }
  assert.equal(blank.size, 3);
});
