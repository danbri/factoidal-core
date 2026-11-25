import assert from 'node:assert/strict';
import { test } from 'node:test';
import { astOf, nameOf } from './run.mjs';
import { grammarOf } from './grammar.mjs';
import { pathText, exprSparql, queryText } from './sparql.mjs';

test('paths are written back with the brackets they need', () => {
  const P = (n) => ({ path: 'iri', iri: `http://www.wikidata.org/prop/direct/P${n}` });
  assert.equal(pathText({ path: 'sequence', a: P(31), b: { path: 'zeroOrMore', p: P(279) } }), 'wdt:P31/wdt:P279*');
  assert.equal(pathText({ path: 'zeroOrMore', p: { path: 'alternative', a: P(1), b: P(2) } }), '(wdt:P1|wdt:P2)*');
  assert.equal(pathText({ path: 'inverse', p: { path: 'sequence', a: P(1), b: P(2) } }), '^(wdt:P1/wdt:P2)');
});

test('expressions are SPARQL, not prose; an absent optional argument is left out', () => {
  const v = (name) => ({ e: 'var', name });
  const s = (lex) => ({ e: 'lit', lit: { lex, datatype: 'http://www.w3.org/2001/XMLSchema#string' } });
  assert.equal(exprSparql({ e: 'compare', op: '=', args: [{ e: 'lang', args: [v('l')] }, s('en')] }), 'LANG(?l) = "en"');
  assert.equal(exprSparql({ e: 'replace', args: [v('x'), s('a'), s('b'), null] }), 'REPLACE(?x, "a", "b")');
  assert.equal(exprSparql({ e: 'aggregate', fn: 'count', distinct: true, arg: v('x') }), 'COUNT(DISTINCT ?x)');
});

test('a browsing query becomes one chain: set, pivot, set; each step with its SPARQL', () => {
  const g = grammarOf(astOf('mlp-048'), nameOf);
  const [chain] = g.program.parts;
  assert.equal(chain.t, 'chain');
  assert.deepEqual(chain.rows[0].map(s => s.t), ['set', 'pivot', 'set']);
  assert.deepEqual(g.steps.map(s => [s.kind, s.v]), [['set', 'alum'], ['pivot', 'nationality'], ['set', 'nationality']]);
  assert.ok(g.steps[0].sparql.some(f => f.s === '?alum wdt:P69 wd:Q459506 .'));
  assert.equal(g.lex['wdt:P27'], 'country of citizenship (P27)');
  // The drafts follow the query's own order, which every fragment can be found in.
  const full = queryText(astOf('mlp-048')).replace(/\s+/g, ' ');
  for (const s of g.steps) for (const f of s.sparql) assert.ok(f.at >= 0 && full.includes(f.s.replace(/\s+/g, ' ')), f.s);
});

test('operations beyond browsing are combine nodes holding programs', () => {
  const g = grammarOf(astOf('mlp-038'), nameOf);
  const ops = g.program.parts.filter(p => p.t === 'combine').map(p => p.op);
  assert.deepEqual(ops, ['either', 'except']);
  const except = g.program.parts.find(p => p.op === 'except');
  assert.deepEqual(except.on, ['author', 'date']);
  assert.match(except.sparql, /^MINUS \{/);
});

test('after a pivot the rows are pairs: steps say what they carry, the answer says its shape', () => {
  const g = grammarOf(astOf('mlp-048'), nameOf);
  assert.deepEqual(g.steps.map(s => s.carries), [['alum'], ['alum', 'nationality'], ['alum', 'nationality']]);
  assert.deepEqual(g.answer.vars, ['nationality', 'alum']);
  assert.equal(g.answer.shape, 'rows');
  const nationality = g.program.parts[0].rows[0][2];
  assert.equal(nationality.shape, 'rows');
  assert.deepEqual(nationality.with, ['alum']);
  // One set, DISTINCT: a set. Grouped and counted: counted, with the aggregate.
  assert.equal(grammarOf(astOf('mlp-059'), nameOf).answer.shape, 'set');
  const counted = grammarOf(astOf('mlp-342'), nameOf).answer;
  assert.equal(counted.shape, 'counted');
  assert.deepEqual(counted.counted, ['q']);
  assert.match(counted.aggregates[0].sparql, /^COUNT\(/);
});
