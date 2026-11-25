// Regression check: the T1–T13 targets in SPEC §8, as the rule IDs (and key
// phrases) each explanation must contain. Uses the interim Lean AST dump.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { explainId } from './run.mjs';
import { renderL1 } from './render.mjs';

const TARGETS = {
  'mlp-003': { rules: ['R-SUBCLASS', 'R-TRUTHY', 'R-COUNT-ROWS'], text: ['R-MULT-PATH'] },
  'mlp-349': { rules: ['R-SOMEVALUE', 'R-MINUS', 'R-TRUTHY', 'R-COUNT-ROWS'], text: ['inventory number (P217) value it has'] },
  'mlp-268': { rules: ['R-FULLSTMT', 'R-QUALIFIER', 'R-MINUS', 'R-COUNT-STMTS'] },
  'mlp-030': { rules: ['R-UNION', 'R-COUNT-ROWS'], text: ['UNION', 'R-MULT-PATH'] },
  'mlp-352': { rules: ['R-VALUES-PRED', 'R-LITERAL-EXACT', 'R-LABEL-EXACT'], absent: ['R-ANYPROP', 'R-DISTINCT-ROW'], text: ['Rows are deduplicated (DISTINCT).'] },
  'mlp-382': { rules: ['R-TRUTHY', 'R-OPTIONAL', 'R-SITELINK'], text: ['F-SITELINK-UNIQUE', 'published in Plomer DBP'] },
  'mlp-348': { rules: ['R-SUBCLASS', 'R-NOTEXISTS', 'R-LABEL-EXACT', 'R-MULT-DUP'], text: ['?item, ?lang', 'mul'] },
  'mlp-248': { rules: ['R-SCOPE-LEAK', 'R-MINUS'], absent: ['R-SAMPLE', 'R-GROUP-BY-LABEL'] },
  'mlp-345': { rules: ['R-SUBQUERY', 'R-JOIN-DROP', 'R-COUNT-ROWS'], absent: ['R-MULT-PER-ENTITY'] },
  'mlp-117': { rules: ['R-HAVING', 'R-SITELINK'], absent: ['R-COUNT-ROWS'] },
  'mlp-197': { rules: ['R-ANYPROP', 'R-MINUS', 'R-OPTIONAL', 'R-YEAR', 'R-MULT-PER-ENTITY', 'R-ORDER-UNBOUND'], text: ['DISTINCT removes only rows that are identical in every column'] },
  'mlp-329': { stub: 'skipped_unsupported' },
  'mlp-039': { rules: ['R-DIRECT-ONLY', 'R-SOMEVALUE', 'R-FULLSTMT', 'R-QUALIFIER', 'R-SAMPLE', 'R-GROUP-KEY-MULT', 'R-GROUP-BY-LABEL', 'R-VIEW'], text: ['Not closed down'] },
};

const ruleIdsIn = (r) => {
  const ids = new Set(r.caveats.map(c => c.rule));
  for (const sec of ['required', 'optional', 'excluded', 'filters']) for (const x of r[sec]) {
    ids.add(x.rule);
    for (const part of x.parts || []) ids.add(part.rule);
  }
  for (const s of r.subqueries) for (const x of s.required) ids.add(x.rule);
  if (r.display) ids.add(r.display.rule);
  return ids;
};

for (const [id, t] of Object.entries(TARGETS)) {
  test(`${id} meets its SPEC §8 target`, () => {
    const r = explainId(id);
    if (t.stub) { assert.equal(r.stub, true); assert.equal(r.reason, t.stub); return; }
    assert.equal(r.unexplained.length, 0, `unexplained: ${JSON.stringify(r.unexplained)}`);
    const ids = ruleIdsIn(r);
    for (const rule of t.rules || []) assert.ok(ids.has(rule), `missing ${rule}`);
    for (const rule of t.absent || []) assert.ok(!ids.has(rule), `unexpected ${rule}`);
    const text = renderL1(r);
    for (const s of t.text || []) assert.ok(text.includes(s), `missing text: ${s}`);
  });
}
