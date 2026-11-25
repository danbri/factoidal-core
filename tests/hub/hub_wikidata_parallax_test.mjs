import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { test } from 'node:test';

const data = JSON.parse(readFileSync(new URL(
  '../../docs/web/hub/wikidata-parallax/wikidata-parallax.11tydata.json', import.meta.url), 'utf8'));
const { queries, tiers, entities } = data;

test('tiers partition the classified queries', () => {
  const ids = tiers.flatMap(t => t.ids);
  assert.equal(new Set(ids).size, queries.length);
  for (const t of tiers) for (const id of t.ids) assert.equal(queries.find(q => q.id === id).tier, t.tier, id);
});

test('a set-browsing query draws as one tree: no edges left outside it, no blockers', () => {
  for (const q of queries.filter(q => q.tier !== 'N')) {
    assert.ok(q.flow.sets.length >= 1, q.id);
    assert.deepEqual(q.flow.loose, [], q.id);
    assert.deepEqual(q.flow.beyond, [], q.id);
    for (const s of q.flow.sets.slice(1)) assert.ok(s.via?.from || s.stage, `${q.id}: set ${s.var} is neither a pivot nor a stage`);
  }
});

test('a query beyond set browsing says why', () => {
  for (const q of queries.filter(q => q.tier === 'N')) assert.ok(q.flow.beyond.length, q.id);
});

test('every entity a page shows has a card with a label', () => {
  for (const q of queries) for (const id of q.flow.entities) assert.ok(entities[id]?.label, `${q.id}: ${id}`);
  for (const e of Object.values(entities)) if (e.image) assert.doesNotMatch(e.image, /^https?:/);
});

test('exclusion chips are worded as removing a facet value', () => {
  for (const q of queries) for (const s of q.flow.sets) for (const c of s.chips) {
    assert.match(c.verb, /^(exclude|require|any)$/, q.id);
    assert.doesNotMatch(c.label, / is not /, q.id);
  }
});
