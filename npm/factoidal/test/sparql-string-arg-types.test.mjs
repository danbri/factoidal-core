// https://github.com/danbri/factoidal/issues/1036: SPARQL 1.1 string
// functions accept arguments that the specification makes type errors, and
// SUBSTR rounds differently from fn:substring. Found by porting Apache Jena's
// one-line ARQ expression tests (docs/designissues/2026-10-25-jena-style-facade-feasibility.md).
//
// Each case is an expected failure on the current engine. The harness turns
// RED when a case starts to pass: then flip it to an assertion and close the
// issue. In a type-error case the BIND variable must be unbound
// (SPARQL 1.1 §18.6, Extend: an error leaves the variable unbound).

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';

const ISSUE = 'https://github.com/danbri/factoidal/issues/1036';
const ds = await f.parse('', { format: 'nquads' });

async function valueOf(expr) {
  const rows = await ds.query(`SELECT ?v WHERE { BIND(${expr} AS ?v) }`);
  assert.equal(rows.length, 1);
  return rows[0].get('v');
}

function xfail(name, fn) {
  test(`xfail: ${name} (${ISSUE})`, async (t) => {
    let failed = false;
    try { await fn(); } catch (err) { failed = true; t.diagnostic(String(err && err.message)); }
    assert.ok(failed, `unexpected pass: ${name} now works; flip this xfail to an assertion and close ${ISSUE}`);
  });
}

// Type errors: the variable must be unbound.
for (const [expr, rule] of [
  ['md5(1234)', '§17.4.6.1: MD5 takes a simple literal or xsd:string'],
  ['contains("abc", "a"@en)', '§17.4.3.1.4: arguments not argument-compatible'],
  ['substr(1, 1, 3)', '§17.4.3.3: SUBSTR takes a string literal'],
  ['strlen(1)', '§17.4.3.2: STRLEN takes a string literal'],
  ['ucase(1)', '§17.4.3.4: UCASE takes a string literal'],
]) {
  xfail(`${expr} is a type error (${rule})`, async () => {
    assert.equal(await valueOf(expr), undefined);
  });
}

// SUBSTR follows fn:substring: characters at positions p (from 1) with
// round(start) <= p < round(start) + round(length).
xfail('substr("12345", 0, 3) is "12" (§17.4.3.3, fn:substring)', async () => {
  assert.equal((await valueOf('substr("12345", 0, 3)')).value, '12');
});

// Controls that already hold, so a broken harness cannot pass the xfails.
test('controls: well-typed calls give their values', async () => {
  assert.equal((await valueOf('substr("12345", 2, 3)')).value, '234');
  assert.equal((await valueOf('contains("abc"@en, "a"@en)')).value, 'true');
  assert.equal((await valueOf('strlen("abc")')).value, '3');
});
