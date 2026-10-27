// DatasetCore (rdfjs.mjs) keeps set semantics in O(1) per quad: add(), has()
// and delete() use a Set of quad keys. Until 2026-10-10 add() scanned the
// quad array, so a parse() of 12,000 quads spent 3.1 s building its DatasetCore
// (issue 713 stage 5, https://github.com/danbri/factoidal/issues/713). The
// scaling case fails when building 4n quads costs more than 9 times n quads
// (skills/danbri-function-precrime-checkers: the n/4n assertion).

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');

let rdfjsPromise = null;
const rdfjs = () => (rdfjsPromise ||= import('../rdfjs.mjs'));

function quadsOf(f, n) {
  const out = [];
  for (let i = 0; i < n; i += 1) {
    out.push(f.quad(f.namedNode(`http://e/s${i}`), f.namedNode('http://e/p'),
      f.literal(String(i), f.namedNode('http://www.w3.org/2001/XMLSchema#integer'))));
  }
  return out;
}

test('DatasetCore: set semantics by term equality', async () => {
  const { DatasetCore, dataFactory: f } = await rdfjs();
  const a = f.quad(f.namedNode('http://e/a'), f.namedNode('http://e/p'), f.literal('x'));
  const a2 = f.quad(f.namedNode('http://e/a'), f.namedNode('http://e/p'), f.literal('x'));
  const lang = f.quad(f.namedNode('http://e/a'), f.namedNode('http://e/p'), f.literal('x', 'en'));
  const langUpper = f.quad(f.namedNode('http://e/a'), f.namedNode('http://e/p'), f.literal('x', 'EN'));
  const iri = f.quad(f.namedNode('http://e/a'), f.namedNode('http://e/p'), f.namedNode('x'));
  const named = f.quad(f.namedNode('http://e/a'), f.namedNode('http://e/p'), f.literal('x'),
    f.namedNode('http://e/g'));
  const ds = new DatasetCore([a, a2, lang, langUpper, iri, named]);
  // a and a2 are equal; "x"@en and "x"@EN are one term (the factory gives the
  // tag in lowercase, RDF/JS Data Model, Literal.language; RDF 1.2 Concepts
  // section 3.4; https://github.com/danbri/factoidal/issues/1054); the literal
  // with a language tag, the IRI and the quad in a named graph are not equal to
  // a, nor to each other.
  assert.ok(lang.equals(langUpper));
  assert.equal(ds.size, 4);
  assert.ok(ds.has(a2));
  assert.ok(ds.has(langUpper));
  assert.ok(!ds.has(f.quad(f.namedNode('http://e/b'), f.namedNode('http://e/p'), f.literal('x'))));
  ds.delete(a2);
  assert.equal(ds.size, 3);
  assert.ok(!ds.has(a));
  ds.add(a);
  assert.equal(ds.size, 4);
  // match() answers a DatasetCore with the same set semantics.
  const m = ds.match(f.namedNode('http://e/a'));
  assert.equal(m.size, 4);
  assert.ok(m.has(named));
  m.add(named);
  assert.equal(m.size, 4);
});

test('DatasetCore: building 4n quads costs at most 9 times n quads', async () => {
  const { DatasetCore, dataFactory: f } = await rdfjs();
  const n = 5000;
  const small = quadsOf(f, n);
  const large = quadsOf(f, 4 * n);
  const time = (qs) => {
    let best = Infinity;
    for (let r = 0; r < 3; r += 1) {
      const t = performance.now();
      const ds = new DatasetCore(qs);
      best = Math.min(best, performance.now() - t);
      assert.equal(ds.size, qs.length);
    }
    return best;
  };
  const tn = time(small);
  const t4n = time(large);
  assert.ok(t4n <= 9 * Math.max(tn, 20),
    `DatasetCore of ${4 * n} quads: ${t4n.toFixed(1)} ms; of ${n}: ${tn.toFixed(1)} ms`);
});
