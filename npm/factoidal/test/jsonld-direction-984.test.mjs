// https://github.com/danbri/factoidal/issues/984: the JSON-LD writer writes
// the base direction of an RDF 1.2 rdf:dirLangString as @direction in every
// rdfDirection mode. Reading it back follows the reader's rdfDirection.

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';

const NT = '<http://e/s> <http://e/p> "y"@ar--rtl .';

async function roundTrip(opts, readOpts) {
  const ds = await f.parse(NT, { format: 'ntriples12' });
  const text = ds.toString({ format: 'jsonld', ...opts });
  const value = JSON.parse(text)[0]['http://e/p'][0];
  const back = (await f.jsonldToRdf(text, readOpts)).toString('nquads').trim();
  return { value, back };
}

test('984: no option writes @direction; the JSON-LD 1.1 reader drops it', async () => {
  const { value, back } = await roundTrip({}, {});
  assert.deepEqual(value, { '@value': 'y', '@language': 'ar', '@direction': 'rtl' });
  assert.equal(back, '<http://e/s> <http://e/p> "y"@ar .');
});

test('984: rdfDirection rdf-1.2 keeps the direction', async () => {
  const { value, back } = await roundTrip({ rdfDirection: 'rdf-1.2' }, { rdfDirection: 'rdf-1.2' });
  assert.equal(value['@direction'], 'rtl');
  assert.equal(back, '<http://e/s> <http://e/p> "y"@ar--rtl .');
});

test('984: rdfstar keeps the direction', async () => {
  const { back } = await roundTrip({ rdfstar: true }, { rdfstar: true });
  assert.equal(back, '<http://e/s> <http://e/p> "y"@ar--rtl .');
});

test('984: rdfDirection i18n-datatype reads @direction as an i18n datatype', async () => {
  const { value, back } = await roundTrip({ rdfDirection: 'i18n-datatype' },
    { rdfDirection: 'i18n-datatype' });
  assert.equal(value['@direction'], 'rtl');
  assert.equal(back, '<http://e/s> <http://e/p> "y"^^<https://www.w3.org/ns/i18n#ar_rtl> .');
});
