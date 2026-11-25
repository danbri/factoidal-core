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
    assert.ok(q.sets >= 1, q.id);
    assert.deepEqual(q.flow.loose, [], q.id);
    assert.deepEqual(q.flow.beyond, [], q.id);
    const ops = q.blocks.items.filter(it => it.op).map(it => it.op.op);
    assert.ok(ops.every(o => o === 'stage'), `${q.id}: ${ops}`);
    assert.ok(q.blocks.items.filter(it => it.chain).length <= 1, `${q.id}: one chain at most`);
  }
});

test('a query beyond set browsing says why', () => {
  for (const q of queries.filter(q => q.tier === 'N')) {
    assert.ok(q.flow.why.length, q.id);
    for (const w of q.flow.why) assert.notEqual(w.text, w.code, `${q.id}: no plain wording for "${w.code}"`);
  }
});

test('every entity a page shows has a card with a label', () => {
  for (const q of queries) for (const id of q.flow.entities) assert.ok(entities[id]?.label, `${q.id}: ${id}`);
  for (const e of Object.values(entities)) if (e.image) assert.doesNotMatch(e.image, /^https?:/);
});

test('exclusion chips are worded as removing a facet value', () => {
  const pieces = (prog) => prog.items.flatMap(it => it.chain ? it.chain.rows.flat() : it.op.slots.flatMap(pieces));
  let n = 0;
  for (const q of queries) for (const p of pieces(q.blocks)) for (const c of p.chips || []) {
    n++;
    assert.match(c.verb, /^(exclude|require|any)$/, q.id);
    assert.doesNotMatch(c.label, / is not /, q.id);
  }
  assert.ok(n > 100, `only ${n} chips drawn`);
});

test('a query beyond set browsing is drawn as blocks: chains, plus an operation or an any-property piece', () => {
  const OPS = new Set(['join', 'either', 'except', 'optional', 'stage', 'loop']);
  const walk = (prog, out) => {
    for (const it of prog.items) {
      if (it.chain) {
        for (const row of it.chain.rows) {
          assert.ok(row.length && row.every((p, i) => (p.kind === 'pivot') === (i % 2 === 1)), 'pieces alternate set, pivot, set');
          for (const p of row) if (p.wild) out.wild++;
        }
      } else {
        assert.ok(OPS.has(it.op.op), it.op.op);
        assert.ok(it.op.slots.length || it.op.extras.length, `${it.op.op} block is empty`);
        out.ops++;
        it.op.slots.forEach(s => walk(s, out));
      }
    }
    return out;
  };
  for (const q of queries) {
 if (q.tier !== 'N') continue;
    const r = walk(q.blocks, { ops: 0, wild: 0 });
    assert.ok(r.ops + r.wild > 0, `${q.id}: nothing marks what goes beyond browsing`);
  }
});
