// Defects found by the SPARQL differential campaign
// (https://github.com/danbri/factoidal-core/issues/1184), recorded as expected failures:
// a case passes while the defect is there, and the run fails when it is fixed,
// until the case is turned into a plain assertion and the issue is closed.

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';

const EXISTS_LITERAL = 'https://github.com/danbri/factoidal-core/issues/1210';
const AGG_UNBOUND = 'https://github.com/danbri/factoidal-core/issues/1211';

function xfail(name, issueUrl, fn) {
  test(`xfail: ${name} (${issueUrl})`, async (t) => {
    let failed = false;
    try { await fn(); } catch (err) { failed = true; t.diagnostic(String(err && err.message)); }
    assert.ok(failed, `unexpected pass: ${name} now works; flip this xfail to an assertion and close ${issueUrl}`);
  });
}

const Q_EXISTS = 'SELECT * WHERE { ?a <http://e/p> ?c . FILTER EXISTS { ?c ?d ?a } }';

test('control: EXISTS with a literal subject and no triple to object ?a is false', async () => {
  const rows = await f.query('<http://e/a> <http://e/p> "x" .\n', Q_EXISTS, { format: 'ntriples' });
  assert.equal(rows.length, 0);
});

for (const lit of ['"x"@en', '"x"', '"1"^^<http://www.w3.org/2001/XMLSchema#integer>']) {
  xfail(`EXISTS { ?c ?d ?a } is false when ?c is the literal ${lit}`, EXISTS_LITERAL, async () => {
    const data = `<http://e/a> <http://e/p> ${lit} .\n<http://e/b> <http://e/q> <http://e/a> .\n`;
    const rows = await f.query(data, Q_EXISTS, { format: 'ntriples' });
    assert.equal(rows.length, 0);
  });
}

test('control: COUNT of a never-bound variable is 0', async () => {
  const rows = await f.query('<http://e/a> <http://e/p> "x" .\n',
    'SELECT (COUNT(?c) AS ?n) WHERE { <http://e/a> ?p ?o }', { format: 'ntriples' });
  assert.equal(rows[0].get('n').value, '0');
});

for (const agg of ['AVG', 'SUM']) {
  xfail(`${agg} of a never-bound variable leaves the AS variable unbound`, AGG_UNBOUND, async () => {
    const rows = await f.query('<http://e/a> <http://e/p> "x" .\n',
      `SELECT (${agg}(?c) AS ?x) WHERE { <http://e/a> ?p ?o }`, { format: 'ntriples' });
    assert.equal(rows.length, 1);
    assert.equal(rows[0].get('x'), undefined);
  });
}
