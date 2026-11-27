// N-Triples and N-Quads allow at most one statement per line:
// RDF 1.1 N-Triples [1] ntriplesDoc ::= triple? (EOL triple)* EOL?
// RDF 1.1 N-Quads   [1] nquadsDoc   ::= statement? (EOL statement)* EOL?
// The readers accept two statements on one line today
// (https://github.com/danbri/factoidal-core/issues/1209, found by the mutated-document
// campaign of https://github.com/danbri/factoidal-core/issues/1184). The cases below are
// expected failures: when the readers refuse such a line, they pass, and the run fails
// until they are turned into plain assertions and the issue is closed.

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';

const ISSUE = 'https://github.com/danbri/factoidal-core/issues/1209';

function xfail(name, issueUrl, fn) {
  test(`xfail: ${name} (${issueUrl})`, async (t) => {
    let failed = false;
    try { await fn(); } catch (err) { failed = true; t.diagnostic(String(err && err.message)); }
    assert.ok(failed, `unexpected pass: ${name} now works; flip this xfail to an assertion and close ${issueUrl}`);
  });
}

const TWO_NT = '<http://e/a> <http://e/p> "x" . <http://e/b> <http://e/p> "y" .\n';
const TWO_NQ = '<http://e/a> <http://e/p> "x" <http://e/g> . _:b <http://e/p> "y" .\n';

test('control: one statement per line is read', async () => {
  const nt = await f.parse('<http://e/a> <http://e/p> "x" .\n<http://e/b> <http://e/p> "y" .\n', { format: 'ntriples' });
  assert.equal(nt.size ?? (await nt.serialize({ format: 'nquads' })).trim().split('\n').length, 2);
  await f.parse('<http://e/a> <http://e/p> "x" <http://e/g> .\n', { format: 'nquads' });
});

xfail('N-Triples: two triples on one line are refused', ISSUE, async () => {
  await assert.rejects(f.parse(TWO_NT, { format: 'ntriples' }));
});

xfail('N-Quads: two statements on one line are refused', ISSUE, async () => {
  await assert.rejects(f.parse(TWO_NQ, { format: 'nquads' }));
});
