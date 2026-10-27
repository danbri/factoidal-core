// https://github.com/danbri/factoidal/issues/1053: the syntax of a document by
// its file name or media type, from one engine table (the W3C registrations,
// formal/lean4/L4Factoidal/RDF/MediaType.lean); formats() lists the same
// media types and extensions. Lean pins: the `#guard`s of MediaType.lean
// (syntaxOfNames) and Wasm/Ops/Terms.lean (syntaxForOp).
import './helpers.js';

import test from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';

const require = createRequire(import.meta.url);
const { ready, syntaxFor, formats, parse } = require('..');

test('syntaxFor: a file name or an IRI path by its registered extension', async () => {
  await ready();
  assert.equal(syntaxFor('data.ttl'), 'turtle');
  assert.equal(syntaxFor('/tmp/x/DATA.NQ'), 'nquads');
  assert.equal(syntaxFor('a.nt'), 'ntriples');
  assert.equal(syntaxFor('a.trig'), 'trig');
  assert.equal(syntaxFor('a.rdf'), 'rdfxml');
  assert.equal(syntaxFor('a.jsonld'), 'jsonld');
  assert.equal(syntaxFor('http://e/data.ttl?version=2#top'), 'turtle');
  assert.equal(syntaxFor({ fileName: 'a.trig' }), 'trig');
});

test('syntaxFor: an unknown or missing extension is null', async () => {
  await ready();
  assert.equal(syntaxFor('data.unknown'), null);
  assert.equal(syntaxFor('data'), null);
  assert.equal(syntaxFor(''), null);
  // .owl and .xml are not registered for RDF/XML.
  assert.equal(syntaxFor('a.owl'), null);
});

test('syntaxFor: the media type wins; its parameters and case do not matter', async () => {
  await ready();
  assert.equal(syntaxFor({ mediaType: 'text/turtle' }), 'turtle');
  assert.equal(syntaxFor({ mediaType: 'Application/N-Quads; charset=utf-8' }), 'nquads');
  assert.equal(syntaxFor({ mediaType: 'application/ld+json; profile="http://www.w3.org/ns/json-ld#expanded"' }), 'jsonld');
  assert.equal(syntaxFor({ fileName: 'a.nt', mediaType: 'text/turtle' }), 'turtle');
  // An unknown media type does not fall back to the name.
  assert.equal(syntaxFor({ fileName: 'a.ttl', mediaType: 'text/plain' }), null);
});

test('formats(): each RDF syntax has its media type and extension; syntaxFor agrees', async () => {
  const rows = await formats();
  const want = {
    turtle: ['text/turtle', '.ttl'], ntriples: ['application/n-triples', '.nt'],
    nquads: ['application/n-quads', '.nq'], trig: ['application/trig', '.trig'],
    rdfxml: ['application/rdf+xml', '.rdf'], jsonld: ['application/ld+json', '.jsonld'],
  };
  for (const row of rows) {
    assert.ok(Array.isArray(row.mediaTypes) && Array.isArray(row.extensions), row.name);
    if (want[row.name]) {
      assert.deepEqual([row.mediaTypes, row.extensions], [[want[row.name][0]], [want[row.name][1]]], row.name);
      assert.equal(syntaxFor({ mediaType: row.mediaTypes[0] }), row.name);
      assert.equal(syntaxFor('x' + row.extensions[0]), row.name);
    } else {
      assert.deepEqual([row.mediaTypes, row.extensions], [[], []], row.name);
    }
  }
  assert.deepEqual(Object.keys(want).filter((n) => !rows.some((r) => r.name === n)), []);
});

test('syntaxFor: the answer is a format parse() reads', async () => {
  const fmt = syntaxFor('doc.nt');
  const ds = await parse('<http://e/s> <http://e/p> <http://e/o> .\n', { format: fmt });
  assert.equal(ds.size, 1);
  ds.dispose();
});
