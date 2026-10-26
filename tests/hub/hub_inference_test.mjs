// Pins every live cell of docs/web/hub/inference.md (see
// hub_rdf_syntaxes_test.mjs for the harness shape).

import test from 'node:test';
import assert from 'node:assert/strict';

import { extractObservableCells, runReactivePost, pretty, xfail, HUB_PAGE_DIR } from './_helpers.mjs';
import * as Factoidal from '../../npm/factoidal/index.mjs';

const cells = extractObservableCells('inference.md', HUB_PAGE_DIR);
const post = runReactivePost(cells, { Factoidal, fn: Factoidal.default, pretty });
const pairs = (rows, a, b) => rows.map((r) => `${r.get(a).value.split('/').pop()} ${r.get(b).value.split('/').pop()}`);

test('inference: RDFS closure over the pipeline output', async () => {
  const rows = await post.value('rdfsTypes');
  const got = pairs(rows, 'thing', 'type');
  for (const want of ['eli Line', 'pad Station', 'pad Place', 'kgx Place']) assert.ok(got.includes(want), `${want} in ${got}`);
  assert.equal(await post.value('entailedAsk'), true);
});

test('inference: OWL 2 RL inverseOf, derived triples in their own graph', async () => {
  assert.deepEqual(pairs(await post.value('servedBy'), 'station', 'line'), ['kgx vic', 'pad eli']);
  const rows = await post.value('padFacts');
  const graphs = new Set(rows.map((r) => r.get('g').value.split('/').pop()));
  assert.ok(graphs.has('csvw') && graphs.has('owl-rl'), [...graphs].join(' '));
  const derived = rows.filter((r) => r.get('g').value.endsWith('owl-rl')).map((r) => r.get('p').value.split('/').pop());
  assert.ok(derived.includes('servedBy'));
  assert.ok(!rows.some((r) => r.get('g').value.endsWith('owl-rl') && r.get('p').value.endsWith('rdf-schema#label')),
    'an asserted label is not repeated in the derived graph');
});

test('inference: unsupported consistency examples remain unknown; separate entailment succeeds', async () => {
  // One ontology is satisfiable and the other inconsistent. The checked
  // reader refuses both; these are API-contract checks, not OWL coverage.
  for (const name of ['consistent', 'inconsistent']) {
    const verdict = await post.value(name);
    assert.equal(verdict.consistent, null);
    assert.match(verdict.reason, /unsupported-syntax/);
  }
  assert.equal((await post.value('entails')).entailed, true);
});

test('inference: the closures accept an RDF 1.2 triple term', async () => {
  const ds = await Factoidal.parse('VERSION "1.2"\n@prefix ex: <http://example.org/> .\n@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .\nex:said rdfs:domain ex:Speaker .\nex:a ex:said <<( ex:b ex:p ex:c )>> .', { format: 'turtle12' });
  for (const regime of ['rdfs', 'owl-rl']) {
    const c = await ds.closure(regime);
    assert.equal(await c.query('ASK { <http://example.org/a> a <http://example.org/Speaker> }'), true, regime);
  }
});

xfail('inference: owlIsConsistent on a dataset with an RDF 1.2 triple term', 'https://github.com/danbri/factoidal/issues/873', async () => {
  const ds = await Factoidal.parse('VERSION "1.2"\n@prefix ex: <http://example.org/> .\nex:a ex:said <<( ex:b ex:p ex:c )>> .', { format: 'turtle12' });
  const r = await Factoidal.owlIsConsistent(ds);
  assert.equal(r.consistent, true);
});
