// Pins every live cell of docs/web/hub/jsonld-star.md. The cells run
// through the same reactive runtime the page uses, with `Factoidal` bound
// to the npm package's Node entry. Needs a wasm with the option `rdfstar`
// (0.18.0 or later); the `parse` case needs `rdfstar` on `parse` (0.20.0 or
// later, https://github.com/danbri/factoidal-core/pull/152).

import test from 'node:test';
import assert from 'node:assert/strict';

import { extractObservableCells, runReactivePost, pretty, HUB_PAGE_DIR } from './_helpers.mjs';
import * as Factoidal from '../../npm/factoidal/index.mjs';

const cells = extractObservableCells('jsonld-star.md', HUB_PAGE_DIR);
const post = runReactivePost(cells, { Factoidal, fn: Factoidal.default, pretty });

const ex = (s) => `http://example.org/${s}`;

test('jsonld-star: Turtle 1.2 written as JSON-LD-star', async () => {
  const nodes = await post.value('starJson');
  const byId = new Map(nodes.map((n) => [n['@id'], n]));
  assert.deepEqual(byId.get(ex('alice'))[ex('said')][0]['@triple'],
    { '@id': ex('bob'), [ex('likes')]: [{ '@id': ex('tea') }] });
  const liked = byId.get(ex('bob'))[ex('likes')][0];
  assert.equal(liked['@id'], ex('tea'));
  assert.equal(liked['@annotation'][0]['@id'], ex('claim1'));
  assert.deepEqual(byId.get(ex('note'))[ex('text')][0],
    { '@value': 'hello', '@language': 'en', '@direction': 'ltr' });
  assert.equal(await post.value('refusedWithout'), 'serialize.failed');
});

test('jsonld-star: JSON-LD-star read as RDF 1.2 and queried', async () => {
  const fromStar = await post.value('fromStar');
  const nq = await fromStar.serialize({ format: 'nquads' });
  const tt = (o) => `<<( <${ex('bob')}> <${ex('likes')}> <${ex(o)}> )>>`;
  const reifies = '<http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies>';
  assert.ok(nq.includes(`<${ex('alice')}> <${ex('said')}> ${tt('tea')} .`), nq);
  assert.ok(nq.includes(`<${ex('bob')}> <${ex('likes')}> <${ex('tea')}> .`), nq);
  assert.ok(nq.includes(`<${ex('claim1')}> ${reifies} ${tt('tea')} .`), nq);
  assert.ok(nq.includes(`<${ex('claim2')}> ${reifies} ${tt('coffee')} .`), nq);
  assert.ok(!nq.includes(`<${ex('bob')}> <${ex('likes')}> <${ex('coffee')}> .`), 'the @reifies triple is not asserted');
  assert.equal(fromStar.size, 6);
  assert.deepEqual(await post.value('sources'),
    [`${ex('coffee')} from ${ex('rumour')}`, `${ex('tea')} from ${ex('diary')}`]);
});

test('jsonld-star: round trip and base direction', async () => {
  assert.deepEqual(await post.value('roundTrip'), { quads: 5, same: true });
  const d = await post.value('direction');
  assert.match(d.rdfstar, /"مرحبا"@ar--rtl \.$/);
  assert.match(d.jsonld11, /"مرحبا"@ar \.$/);
});

test('jsonld-star: without rdfstar the keywords are ignored (JSON-LD 1.1)', async () => {
  const starDoc = await post.value('starDoc');
  const plain = await Factoidal.jsonldToRdf(starDoc);
  const nq = await plain.serialize({ format: 'nquads' });
  assert.ok(!nq.includes('<<('), nq);
  assert.ok(!nq.includes('22-rdf-syntax-ns#reifies'), nq);
});

test('jsonld-star: parse takes the option rdfstar for JSON-LD (issue 1091)', async () => {
  const starDoc = await post.value('starDoc');
  const ds = await Factoidal.parse(starDoc, { format: 'jsonld', rdfstar: true });
  assert.equal(ds.size, 6);
});
