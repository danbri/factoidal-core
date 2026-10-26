// npm explain(): the Lean #guard cases of
// formal/lean4/L4Factoidal/Dataflow/ExplainGraphTests.lean through the wasm
// op explainGraph (https://github.com/danbri/factoidal/issues/1002).
// Skipped when the loaded wasm has no explainGraph op.

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';

let skip = 'wasm engine not built';
try {
  const caps = await f.capabilities();
  skip = caps.explain ? false : 'wasm has no explainGraph op';
} catch (_err) { /* engine did not load: skip */ }

const SOURCES = `
  @prefix ex: <http://example.org/> .
  @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
  ex:alice ex:worksFor ex:acme .
  ex:worksFor rdfs:domain ex:Employee .
  ex:Employee rdfs:subClassOf ex:Person .
  ex:bob ex:name ex:BobName .
`;
const PRE = '@prefix ex: <http://example.org/> .\n';
const EX = 'http://example.org/';

test('entailed: rdfs2 and rdfs9, _:x maps to ex:alice', { skip }, async () => {
  const r = await f.explain(SOURCES, PRE +
    '_:x a ex:Person . _:x a ex:Employee . _:x ex:worksFor ex:acme .', { profile: 'rdfs' });
  assert.equal(r.entailed, true);
  assert.equal(r.rejection, null);
  assert.deepEqual(r.assumptions, []);
  assert.ok(r.bundle);
  assert.equal(r.bundle.support.length, 3);
  assert.ok(r.bundle.mapping.some((m) => m.term === `<${EX}alice>`));
  const rules = r.bundle.steps.map((s) => s.rule);
  assert.ok(rules.some((x) => /rdfs2/.test(x)));
  assert.ok(rules.some((x) => /rdfs9/.test(x)));
  assert.equal(typeof r.entailedMeans, 'string');
});

test('not entailed, noMatch: names triple 1', { skip }, async () => {
  const r = await f.explain(SOURCES, PRE +
    '_:x a ex:Person . _:x ex:worksFor ex:globex .');
  assert.equal(r.entailed, false);
  assert.equal(r.bundle, null);
  assert.equal(r.rejection.kind, 'noMatch');
  assert.equal(r.rejection.index, 1);
  assert.match(r.rejection.triple, /globex/);
  assert.ok(r.assumptions.length > 0);
});

test('not entailed, noJointMapping', { skip }, async () => {
  const r = await f.explain(SOURCES, PRE +
    '_:x ex:worksFor ex:acme . _:x ex:name ex:BobName .');
  assert.equal(r.entailed, false);
  assert.equal(r.bundle, null);
  assert.deepEqual(r.rejection, { kind: 'noJointMapping' });
  assert.ok(r.assumptions.length > 0);
});

test('a description with a named graph is refused', { skip }, async () => {
  await assert.rejects(
    f.explain(SOURCES, '<http://e/a> <http://e/p> <http://e/b> <http://e/g> .', { format: 'nquads' }),
    (err) => err instanceof f.FactoidalError);
});

test('an unknown profile is a TypeError', { skip }, async () => {
  await assert.rejects(f.explain('', '', { profile: 'owl' }), TypeError);
});
