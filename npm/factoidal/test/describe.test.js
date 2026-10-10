// SPARQL 1.1 §16.4 DESCRIBE through the npm surface, on both engines.
//
// Lean engine (factoidal/l4-core): the answer is the Concise Bounded
// Description (W3C Member Submission, CBD §2) of each named resource, read
// from the active default graph. Design record:
// docs/designissues/2026-10-10-sparql-describe.md.
//
// F* engine (the main entry): DESCRIBE returns the empty graph. That is an
// expected failure tracked at https://github.com/danbri/factoidal/issues/702;
// the case below fails the suite when it starts to pass.

'use strict';

const { PENDING } = require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');

const factoidal = require('..');
const l4 = require('../l4.js');
const l4core = require('../l4-core.js');

const FSTAR_DESCRIBE_ISSUE = 'https://github.com/danbri/factoidal/issues/702';

const X = 'http://x/';
// CBD(<a>) is the first three triples: <a>'s own statements, plus the
// statements of the blank node <a> reaches. <c> is an IRI, so its
// statement is not part of the description.
const NT = [
  `<${X}a> <${X}p> _:b1 .`,
  `_:b1 <${X}q> "v" .`,
  `<${X}a> <${X}r> <${X}c> .`,
  `<${X}c> <${X}p> "outside the description" .`,
].join('\n');
const DESCRIBE_A = `DESCRIBE <${X}a>`;

function sortedLines(nq) {
  return nq.split('\n').map((l) => l.trim()).filter((l) => l !== '').sort();
}

test('l4-core DESCRIBE <iri> returns the Concise Bounded Description', async (t) => {
  if (!l4.available()) {
    t.skip('Lean wasm assets not resolvable (l4.js available() is false)');
    return;
  }
  const out = await l4core.query(NT, DESCRIBE_A, { format: 'ntriples' });
  assert.equal(out.constructor.name, 'Dataset');
  const lines = sortedLines(await l4core.serialize(out, { format: 'nquads' }));
  assert.equal(lines.length, 3, lines.join('\n'));
  assert.ok(lines.includes(`<${X}a> <${X}r> <${X}c> .`));
  assert.ok(lines.some((l) => l.endsWith(`<${X}q> "v" .`)), 'the blank node is followed');
  assert.ok(!lines.some((l) => l.includes('outside the description')), 'an IRI object is not followed');
});

test('l4-core DESCRIBE of a resource with no statements returns the empty graph', async (t) => {
  if (!l4.available()) {
    t.skip('Lean wasm assets not resolvable (l4.js available() is false)');
    return;
  }
  const out = await l4core.query(NT, `DESCRIBE <${X}none>`, { format: 'ntriples' });
  assert.equal(out.constructor.name, 'Dataset');
  assert.equal(out.size, 0);
});

// Same shape as the xfail helper in xmpp.test.mjs (skills/test-suites
// § Expected failures), plus a skip when the F* npm-entry bundle is absent,
// so a missing bundle is not counted as the expected failure.
test(`xfail: F* engine DESCRIBE <iri> returns the Concise Bounded Description (${FSTAR_DESCRIBE_ISSUE})`, async (t) => {
  const caps = await factoidal.capabilities();
  if (!caps.construct) {
    t.skip(PENDING);
    return;
  }
  let failed = false;
  try {
    const out = await factoidal.query(NT, DESCRIBE_A);
    assert.equal(out.size, 3);
  } catch (error) {
    failed = true;
    t.diagnostic(`expected failure: ${String(error.message).slice(0, 160)}`);
  }
  assert.ok(failed,
    `unexpected pass: F* DESCRIBE now works — flip this xfail to an assertion and close ${FSTAR_DESCRIBE_ISSUE}`);
});
