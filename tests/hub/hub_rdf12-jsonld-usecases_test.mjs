// Pins every live cell of docs/web/hub/rdf12-jsonld-usecases.md. The cells
// run through the same reactive runtime the page uses, with `Factoidal`
// bound to the npm package's Node entry. Needs a wasm with the option
// `rdfstar` (0.18.0 or later).

import test from 'node:test';
import assert from 'node:assert/strict';

import { extractObservableCells, runReactivePost, pretty, HUB_PAGE_DIR, xfail } from './_helpers.mjs';
import * as Factoidal from '../../npm/factoidal/index.mjs';

const cells = extractObservableCells('rdf12-jsonld-usecases.md', HUB_PAGE_DIR);
const post = runReactivePost(cells, { Factoidal, fn: Factoidal.default, pretty });

const ex = (s) => `http://example.org/${s}`;
const REIFIES = '<http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies>';

test('rdf12 use cases: the document as RDF 1.2', async () => {
  const ds = await post.value('ds');
  assert.equal(ds.size, 22);
  const nq = await post.value('nquads');
  assert.ok(nq.includes(`<${ex('claim1')}> ${REIFIES} <<( <${ex('bob')}> <${ex('age')}> "23"^^<http://www.w3.org/2001/XMLSchema#integer> )>> .`), nq);
  assert.ok(nq.includes(`<${ex('liz')}> <${ex('spouse')}> <${ex('richard')}> .`), nq);
  assert.ok(!nq.includes(`<${ex('bob')}> <${ex('likes')}> <${ex('coffee')}> .`), 'the @reifies triple is not asserted');
});

test('rdf12 use cases: provenance, occurrences, edge properties', async () => {
  assert.deepEqual(await post.value('provenance'), [{ age: '23', src: ex('census'), when: '2026-10-27' }]);
  assert.deepEqual(await post.value('marriages'), [
    { m: ex('m1'), start: '1964', end: '1974' },
    { m: ex('m2'), start: '1975', end: '1976' },
  ]);
  assert.deepEqual(await post.value('counts'), [{ asserted: '1', reifiers: '2' }]);
  assert.deepEqual(await post.value('edge'), [{ since: '2019', weight: '8.0E-1' }]);
});

test('rdf12 use cases: unasserted statements and one reifier for two triples', async () => {
  assert.deepEqual(await post.value('claims'), {
    claimedBy: [{ who: ex('carol') }],
    said: [{ who: ex('dave'), what: ex('tea') }],
    coffeeAsserted: false,
    teaAsserted: false,
  });
  assert.deepEqual(await post.value('observation'), [
    { p: ex('humidity'), o: '40', at: '2026-10-27T10:00:00Z' },
    { p: ex('temp'), o: '21', at: '2026-10-27T10:00:00Z' },
  ]);
});

test('rdf12 use cases: written back as JSON-LD-star; owl:sameAs inside a triple term', async () => {
  const liz = await post.value('written');
  const value = liz[ex('spouse')][0];
  assert.equal(value['@id'], ex('richard'));
  assert.deepEqual(value['@annotation'].map((a) => a['@id']).sort(), [ex('m1'), ex('m2')]);
  assert.deepEqual(await post.value('sameAs'), [{ who: ex('dave') }]);
});

xfail('rdf12 use cases: entail with sparql12 in one query', 'https://github.com/danbri/factoidal/issues/1109', async () => {
  const data = await Factoidal.parse(`VERSION "1.2"
PREFIX ex: <http://example.org/>
PREFIX owl: <http://www.w3.org/2002/07/owl#>
ex:dave ex:said <<( ex:bob ex:likes ex:tea )>> .
ex:bob owl:sameAs ex:robert .`, { format: 'turtle12' });
  const yes = await data.query('PREFIX ex: <http://example.org/> ASK { ex:dave ex:said <<( ex:robert ex:likes ex:tea )>> }',
    { sparql12: true, entail: 'OWL-RL' });
  assert.equal(yes, true);
});
