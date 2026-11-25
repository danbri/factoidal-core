// Parallax classification, with the negation-as-facet cases checked on real corpus queries.
import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { classifyParallax } from './parallax.mjs';
import { Names } from './names.mjs';

const names = new Names(new URL('../data/wikidata-labels.json', import.meta.url).pathname);
const asts = {};
for (const line of fs.readFileSync(new URL('../data/interim/ast-lean-interim.jsonl', import.meta.url), 'utf8').split('\n')) {
  if (!line) continue; const r = JSON.parse(line);
  if (r.field === 'lean_replacement_query' && r.result.ok) asts[r.id] = r.result.ast;
}
const run = (id) => classifyParallax(asts[id], (i) => names.iri(i));

test('core Parallax query has no blockers and no negations', () => {
  const r = run('mlp-059');
  assert.equal(r.tier, 'A'); assert.deepEqual(r.negations, []);
});

test('"lacks a property" becomes an exclusion chip phrased positively', () => {
  const r = run('mlp-022');
  assert.notEqual(r.tier, 'N');
  assert.ok(r.negations.some(n => n.label === 'exclude: has any value for dissolved, abolished or demolished (P576)'), JSON.stringify(r.negations));
});

test('negated qualifier on a statement node needs statement traversal (C)', () => {
  const r = run('mlp-268');
  assert.equal(r.tier, 'C');
  assert.ok(r.negations.some(n => n.label === 'exclude: this statement has an end time (P582) qualifier'));
});

test('sitelink negation is named by site', () => {
  assert.ok(run('mlp-066').negations.some(n => n.label === 'exclude: has a sitelink to en.wikipedia.org'));
});

test('subclass closure inside a negation is type selection (D)', () => {
  const r = run('mlp-073');
  assert.ok(r.negations.some(n => n.label === 'exclude: is actor (Q33999) or a subclass of it, at any depth'));
});

test('"not (A and B)" is blocked: it reads as two exclusions', () => {
  const r = run('mlp-013');
  assert.equal(r.tier, 'N');
  assert.ok(r.blockers.some(b => b.startsWith('negated combination')));
});

test('negation sharing a second column is blocked (correlated)', () => {
  const r = run('mlp-038');
  assert.ok(r.blockers.includes('negation tied to two columns (correlated, not one facet)'));
});

test('label negation tied to a language column is blocked', () => {
  assert.ok(run('mlp-348').blockers.some(b => b.startsWith('negation')));
});

test('"only X" (MINUS with != X) becomes "P includes something other than X"', () => {
  const r = run('mlp-327');
  assert.notEqual(r.tier, 'N', JSON.stringify(r.blockers));
  assert.ok(r.negations.some(n => n.label === 'exclude: made from material (P186) includes something other than gold (Q897)'), JSON.stringify(r.negations));
});

test('text match on a sitelink URL is a chip, tier B or above', () => {
  const r = run('mlp-386');
  assert.ok(r.negations.some(n => n.label === 'exclude: has a sitelink whose URL contains "wikipedia"'), JSON.stringify(r.negations));
});

test('a language taken from another column is reported as correlated', () => {
  for (const id of ['mlp-348', 'mlp-364', 'mlp-523'])
    assert.ok(run(id).blockers.includes('negation tied to two columns (correlated, not one facet)'), id);
});
