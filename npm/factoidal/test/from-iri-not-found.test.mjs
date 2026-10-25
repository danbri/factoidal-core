// https://github.com/danbri/factoidal/issues/1032: a FROM / FROM NAMED IRI that
// names no graph of the dataset adds no graph (the rows do not change), and the
// query envelope carries a `warnings` member of class `dataset-iri-not-found`.
// The Lean op gives the warning (formal/lean4/Wasm/Ops/Query.lean, #guards);
// the published wasm was built before it, so the warning case is an expected
// failure until the wasm is rebuilt. The harness turns RED on an unexpected
// pass: then flip it to an assertion and close the issue.

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';

const ISSUE = 'https://github.com/danbri/factoidal/issues/1032';
const NQ = '<http://e/s> <http://e/p> "x" <http://e/g1> .\n';
const eng = await f.loadEngine();

function xfail(name, issueUrl, fn) {
  test(`xfail: ${name} (${issueUrl})`, async (t) => {
    let failed = false;
    try { await fn(); } catch (err) { failed = true; t.diagnostic(String(err && err.message)); }
    assert.ok(failed, `unexpected pass: ${name} now works; flip this xfail to an assertion and close ${issueUrl}`);
  });
}

test('FROM with an IRI not in the dataset: the rows are those of the graphs found', async () => {
  const none = eng.call('queryDataset', [NQ, 'SELECT ?o FROM <http://e/nope> WHERE { ?s ?p ?o }']);
  assert.equal(none.ok, true);
  assert.deepEqual(none.srj.results.bindings, []);
  const one = eng.call('queryDataset', [NQ,
    'SELECT ?o FROM <http://e/g1> FROM <http://e/nope> WHERE { ?s ?p ?o }']);
  assert.deepEqual(one.srj.results.bindings.map((b) => b.o.value), ['x']);
  const found = eng.call('queryDataset', [NQ, 'SELECT ?o FROM <http://e/g1> WHERE { ?s ?p ?o }']);
  assert.equal(found.warnings, undefined);
});

xfail('FROM / FROM NAMED with an IRI not in the dataset gives a dataset-iri-not-found warning',
  ISSUE, async () => {
    const r = eng.call('queryDataset', [NQ,
      'SELECT ?o FROM <http://e/g1> FROM NAMED <http://e/nope> WHERE { ?s ?p ?o }']);
    assert.ok(Array.isArray(r.warnings), 'the envelope has a warnings member');
    assert.deepEqual(r.warnings.map((w) => [w.class, w.clause, w.iri]),
      [['dataset-iri-not-found', 'FROM NAMED', 'http://e/nope']]);
  });

xfail('query() gives the dataset-iri-not-found warning as rows.warnings', ISSUE, async () => {
  const ds = await f.parse(NQ, { format: 'nquads' });
  const rows = await f.query(ds, 'SELECT ?o FROM <http://e/g1> FROM NAMED <http://e/nope> WHERE { ?s ?p ?o }');
  assert.deepEqual(rows.map((b) => b.get('o').value), ['x']);
  assert.ok(Array.isArray(rows.warnings), 'rows.warnings is an array');
  assert.deepEqual(rows.warnings.map((w) => [w.class, w.clause, w.iri]),
    [['dataset-iri-not-found', 'FROM NAMED', 'http://e/nope']]);
});
