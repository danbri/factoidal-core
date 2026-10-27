// parse() takes the option `rdfstar` for JSON-LD, as the 0.18.0 changelog
// says (0.18.0 refused it with option.unknown; jsonldToRdf took it). The
// JSON-LD-star reader is the one jsonldToRdf uses.

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';

const STAR = '{"@id":"http://e/s","http://e/p":{"@triple":' +
  '{"@id":"http://e/a","http://e/q":{"@id":"http://e/b"}}}}';

const nq = (ds) => ds.toString('nquads');

test('parse {format: jsonld, rdfstar: true} reads @triple as a triple term', async () => {
  const ds = await f.parse(STAR, { format: 'jsonld', rdfstar: true });
  assert.equal(ds.format, 'jsonld');
  assert.equal(ds.formatInferred, false);
  assert.match(nq(ds), /<<\(/);
  const ref = await f.jsonldToRdf(STAR, { rdfstar: true });
  assert.equal(nq(ds), nq(ref));
});

test('parse {rdfstar: true} with no format infers jsonld', async () => {
  const ds = await f.parse(STAR, { rdfstar: true });
  assert.equal(ds.format, 'jsonld');
  assert.equal(ds.formatInferred, true);
  assert.match(nq(ds), /<<\(/);
});

test('parse without rdfstar ignores @triple (JSON-LD 1.1)', async () => {
  const ds = await f.parse(STAR, { format: 'jsonld' });
  assert.doesNotMatch(nq(ds), /<<\(/);
});

test('parse rdfstar with a format other than jsonld is option.conflict', async () => {
  await assert.rejects(f.parse('<http://e/s> <http://e/p> <http://e/o> .',
    { format: 'turtle', rdfstar: true }), { code: 'option.conflict' });
  await assert.rejects(f.parse('<http://e/s> <http://e/p> <http://e/o> .',
    { rdfstar: true }), { code: 'option.conflict' });
});

test('parse rdfstar with lenient is option.conflict', async () => {
  await assert.rejects(f.parse(STAR, { format: 'jsonld', rdfstar: true, lenient: true }),
    { code: 'option.conflict' });
});
