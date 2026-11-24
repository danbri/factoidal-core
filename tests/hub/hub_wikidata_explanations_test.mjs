import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { test } from 'node:test';

const data = JSON.parse(readFileSync(new URL(
  '../../docs/web/hub/wikidata-explanations/wikidata-explanations.11tydata.json', import.meta.url), 'utf8'));
const { queries, counts, byRule } = data;

test('every query appears once, and counts add up', () => {
  const ids = queries.map(q => q.id);
  assert.equal(new Set(ids).size, ids.length);
  assert.equal(counts.total, queries.length);
  const stubs = Object.values(counts.stubs).reduce((a, b) => a + b, 0);
  assert.equal(counts.explained + stubs, counts.total);
});

test('an explained query has an explanation, its Factoidal rewrite and its original', () => {
  for (const q of queries.filter(q => !q.stub)) {
    assert.ok(q.explanation?.length, q.id);
    assert.ok(q.rewritten?.length, q.id);
    assert.ok(q.original?.length, q.id);
    assert.ok(!q.explanation.includes('UNEXPLAINED'), `${q.id} has unexplained parts`);
  }
});

test('answer-changing badges come from the caveats, and the rule index matches them', () => {
  for (const q of queries.filter(q => !q.stub)) {
    const rules = new Set(q.caveats.filter(c => c.severity === 'changes_answer').map(c => c.rule));
    assert.deepEqual(new Set(q.answerChanging), rules, q.id);
  }
  for (const { rule, ids } of byRule) {
    assert.deepEqual(ids, queries.filter(q => (q.answerChanging || []).includes(rule)).map(q => q.id), rule);
  }
});

test('the data carries its licence and provenance', () => {
  assert.equal(data.corpus.license, 'CC-BY-SA-4.0');
  assert.match(data.corpus.attribution, /Martin Poulter/);
  assert.ok(data.labels.retrieved);
});
