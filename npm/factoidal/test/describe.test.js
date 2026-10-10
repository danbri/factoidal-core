// SPARQL 1.1 §16.4 DESCRIBE through the npm surface: the answer is the
// Concise Bounded Description (W3C Member Submission, CBD §2) of each named
// resource, read from the active default graph. Design record:
// docs/designissues/2026-10-10-sparql-describe.md. (The F* engine's DESCRIBE,
// issue 702, is compared in tests/engine-compare/.)

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');

const factoidal = require('..');

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

test('DESCRIBE <iri> returns the Concise Bounded Description', async () => {
  const out = await factoidal.query(NT, DESCRIBE_A, { format: 'ntriples' });
  assert.ok(out instanceof factoidal.Dataset);
  const lines = sortedLines(await factoidal.serialize(out, { format: 'nquads' }));
  assert.equal(lines.length, 3, lines.join('\n'));
  assert.ok(lines.includes(`<${X}a> <${X}r> <${X}c> .`));
  assert.ok(lines.some((l) => l.endsWith(`<${X}q> "v" .`)), 'the blank node is followed');
  assert.ok(!lines.some((l) => l.includes('outside the description')), 'an IRI object is not followed');
});

test('DESCRIBE of a resource with no statements returns the empty graph', async () => {
  const out = await factoidal.query(NT, `DESCRIBE <${X}none>`, { format: 'ntriples' });
  assert.ok(out instanceof factoidal.Dataset);
  assert.equal(out.size, 0);
});
