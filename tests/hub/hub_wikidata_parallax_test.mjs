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
    const parts = q.grammar.program.parts;
    const ops = parts.filter(p => p.t === 'combine').map(p => p.op);
    assert.ok(ops.every(o => o === 'stage'), `${q.id}: ${ops}`);
    assert.ok(parts.filter(p => p.t === 'chain').length <= 1, `${q.id}: one chain at most`);
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
  const steps = (prog) => prog.parts.flatMap(p => p.t === 'chain' ? p.rows.flat() : p.args.flatMap(steps));
  let n = 0;
  for (const q of queries) for (const p of steps(q.grammar.program)) for (const k of p.keep || []) {
    n++;
    assert.match(k.mode, /^(exclude|require|anyOf)$/, q.id);
    assert.ok(q.grammar.lex[k.key], `${q.id}: no words for a chip`);
    assert.doesNotMatch(q.grammar.lex[k.key], / is not /, q.id);
  }
  assert.ok(n > 100, `only ${n} chips drawn`);
});

test('a query beyond set browsing is drawn as blocks: chains, plus an operation or an any-property step', () => {
  const OPS = new Set(['join', 'either', 'except', 'optional', 'stage', 'link']);
  const walk = (prog, out) => {
    for (const part of prog.parts) {
      if (part.t === 'chain') {
        for (const row of part.rows) {
          assert.ok(row.length && row.every((p, i) => (p.t === 'pivot') === (i % 2 === 1)), 'steps alternate set, pivot, set');
          for (const p of row) if (p.any) out.wild++;
        }
      } else {
        assert.ok(OPS.has(part.op), part.op);
        assert.ok(part.args.length, `${part.op} block is empty`);
        out.ops++;
        part.args.forEach(a => walk(a, out));
      }
    }
    return out;
  };
  for (const q of queries) {
    if (q.tier !== 'N') continue;
    const r = walk(q.grammar.program, { ops: 0, wild: 0 });
    assert.ok(r.ops + r.wild > 0, `${q.id}: nothing marks what goes beyond browsing`);
  }
});

test('the grammar is data only: every word a block shows comes from the lexicon', () => {
  for (const q of queries) {
    const { program, lex } = q.grammar;
    const json = JSON.stringify(program);
    // No English in the program: op names, SPARQL terms, variables, step numbers only.
    assert.doesNotMatch(json, /"(label|title|name|text|whyText)":/, q.id);
    const walk = (prog) => prog.parts.forEach(p => p.t === 'chain'
      ? p.rows.flat().forEach(s => {
        if (s.v) assert.ok(lex[`?${s.v}`], `${q.id}: no name for ?${s.v}`);
        if (s.t === 'pivot') assert.ok(lex[s.p], `${q.id}: no words for ${s.p}`);
        for (const x of [...(s.narrow || []), ...(s.show || [])]) assert.ok(lex[x.p], `${q.id}: no words for ${x.p}`);
      })
      : p.args.forEach(walk));
    walk(program);
  }
});

test('stepping: every step adds SPARQL placed in the whole query, and the steps are drawn', async () => {
  const { draftQuery, fragmentsUpTo } = await import('../../docs/web/hub/wikidata-parallax/draft.mjs');
  let steps = 0;
  for (const q of queries) {
    const g = q.grammar;
    assert.ok(g.full && /SELECT/i.test(g.full), `${q.id}: no whole query`);
    g.steps.forEach((s, k) => {
      steps++;
      for (const f of s.sparql) assert.ok(f.at >= 0, `${q.id} step ${k}: fragment not found in the query: ${f.s}`);
      const d = draftQuery(g, k);
      const open = (d.match(/\{/g) || []).length, close = (d.match(/\}/g) || []).length;
      assert.equal(open, close, `${q.id} step ${k}: unbalanced draft`);
      assert.ok(fragmentsUpTo(g.steps, k).length >= fragmentsUpTo(g.steps, Math.max(0, k - 1)).length, `${q.id}: drafts only grow`);
    });
    const n = (JSON.stringify(g.program).match(/"step":/g) || []).length + (g.program.whereStep != null ? 1 : 0);
    assert.equal(n, g.steps.length, `${q.id}: every step is drawn once`);
  }
  assert.ok(steps > 1500, `only ${steps} steps`);
});

test('the whole query (the last step) declares every prefix it uses, as QLever requires', () => {
  for (const q of queries) {
    const full = q.grammar.full;
    const declared = new Set([...full.matchAll(/^\s*PREFIX\s+(\w*):/gim)].map(m => m[1]));
    const body = full.replace(/^\s*PREFIX[^\n]*\n/gim, '').replace(/"(?:[^"\\]|\\.)*"|<[^>\s]*>|#[^\n]*/g, ' ');
    for (const m of body.matchAll(/(?:^|[^\w:.?$-])([A-Za-z][\w-]*):[A-Za-z_\d]/g)) assert.ok(declared.has(m[1]), `${q.id}: ${m[1]}: is not declared`);
  }
});
