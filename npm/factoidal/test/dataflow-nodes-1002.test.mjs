// The node-composition API (https://github.com/danbri/factoidal/issues/1002,
// step 2): stages() is the engine's op stageList (the Lean registry,
// formal/lean4/Wasm/Ops/StageList.lean); node/pipe/run wire them, one
// evidence record per node, and a run reports the union of the nodes' named
// assumptions. Skipped when the loaded wasm has no stageList op.

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';

let skip = 'wasm engine not built';
try {
  const caps = await f.capabilities();
  skip = caps.stages && caps.explain ? false : 'wasm has no stageList op';
} catch (_err) { /* engine did not load: skip */ }

const SOURCES = `
  @prefix ex: <http://example.org/> .
  @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
  ex:alice ex:worksFor ex:acme .
  ex:worksFor rdfs:domain ex:Employee .
  ex:Employee rdfs:subClassOf ex:Person .
`;
const DESCRIPTION = `@prefix ex: <http://example.org/> .
  _:x a ex:Person . _:x ex:worksFor ex:acme .`;
const STATUSES = ['proved', 'tested', 'assumed', 'missing'];

const byName = async () => new Map((await f.stages()).map((s) => [s.name, s]));
const union = (lists) => [...new Set(lists.flat())].sort();

test('stages(): one element per registry entry, unique names, runnable iff not missing', { skip }, async () => {
  const list = await f.stages();
  assert.ok(list.length > 100, `only ${list.length} stages`);
  assert.equal(new Set(list.map((s) => s.name)).size, list.length);
  for (const s of list) {
    assert.ok(STATUSES.includes(s.status), s.status);
    assert.equal(s.runnable, s.status !== 'missing', s.name);
    assert.equal(s.declaration === null, s.kind === null, s.name);
    assert.ok(Array.isArray(s.assumptions) && Array.isArray(s.theorems) && Array.isArray(s.tests));
    if (s.status === 'proved') assert.ok(s.contract, `${s.name}: proved with no contract`);
    if (s.status === 'assumed') assert.ok(s.assumptions.length > 0, `${s.name}: assumed with no assumption`);
    if (s.status === 'missing' || s.status === 'tested') assert.equal(s.contract, null, s.name);
  }
  assert.ok(list.some((s) => s.status === 'missing'));
  const m = await byName();
  assert.equal(m.get('rdfsReasoner').kind, 'SoundReasoner');
  assert.equal(m.get('turtleDocumentReader').kind, 'RdfReader');
  assert.equal(m.get('rdfsExplainGraphStage').declaration, 'L4Factoidal.Dataflow.rdfsExplainGraphStage');
});

test('every stage the package runs is registered and not missing', { skip }, async () => {
  const bound = (await f.stages()).filter((s) => s.bound);
  const names = bound.map((s) => s.name);
  for (const n of ['turtleDocumentReader', 'rdfsReasoner', 'owlRlReasoner', 'shaclValidator',
    'shippedEvaluator', 'nquadsDocumentWriter', 'turtleDocumentWriter', 'rdfcStage',
    'rdfsExplainGraphStage']) {
    assert.ok(names.includes(n), `${n} is not bound`);
  }
  for (const s of bound) assert.notEqual(s.status, 'missing', s.name);
});

test('parse Turtle -> RDFS closure -> explain: one record per node, statuses and the assumption union', { skip }, async () => {
  const m = await byName();
  const p = f.pipe(
    await f.node('turtleDocumentReader'),
    await f.node('rdfsReasoner'),
    await f.node('rdfsExplainGraphStage', { description: DESCRIPTION }),
  );
  const r = await f.run(p, SOURCES);
  const names = ['turtleDocumentReader', 'rdfsReasoner', 'rdfsExplainGraphStage'];
  assert.deepEqual(r.evidence.map((e) => e.stage), names);
  for (const e of r.evidence) {
    const s = m.get(e.stage);
    assert.equal(e.status, s.status);
    assert.equal(e.contract, s.contract);
    assert.deepEqual([...e.assumptions], [...s.assumptions]);
  }
  const explained = r.evidence[2].artefact;
  assert.equal(explained.entailed, true);
  assert.ok(explained.bundle);
  assert.ok(r.graph instanceof f.Dataset);
  const expected = union(names.map((n) => [...m.get(n).assumptions]));
  assert.deepEqual([...r.assumptions].sort(), expected);
  assert.deepEqual([...p.assumptions].sort(), expected);
});

test('an assumed writer adds its named assumption to the union', { skip }, async () => {
  const m = await byName();
  const w = m.get('turtleDocumentWriter');
  assert.equal(w.status, 'assumed');
  assert.ok(w.assumptions.length > 0);
  const r = await f.run(f.pipe(await f.node('turtleDocumentReader'), await f.node('turtleDocumentWriter')),
    '<http://example.org/a> <http://example.org/p> <http://example.org/b> .');
  assert.deepEqual(r.evidence.map((e) => e.stage), ['turtleDocumentReader', 'turtleDocumentWriter']);
  assert.equal(typeof r.evidence[1].artefact.text, 'string');
  const expected = union(['turtleDocumentReader', 'turtleDocumentWriter'].map((n) => [...m.get(n).assumptions]));
  assert.deepEqual([...r.assumptions].sort(), expected);
  for (const a of w.assumptions) assert.ok(r.assumptions.includes(a));
});

test('a SHACL node keeps the graph and records the report', { skip }, async () => {
  const shapes = `@prefix sh: <http://www.w3.org/ns/shacl#> . @prefix ex: <http://example.org/> .
    ex:S a sh:NodeShape ; sh:targetClass ex:Person ; sh:property [ sh:path ex:worksFor ; sh:minCount 1 ] .`;
  const r = await f.run(f.pipe(await f.node('turtleDocumentReader'), await f.node('rdfsReasoner'),
    await f.node('shaclValidator', { shapes })), SOURCES);
  assert.equal(r.evidence[2].stage, 'shaclValidator');
  assert.equal(r.evidence[2].artefact.conforms, true);
});

test('the evidence of the input wire is kept', { skip }, async () => {
  const prior = { stage: 'upstream', status: 'tested', contract: null, assumptions: ['X.y'], artefact: null };
  const r = await f.run(await f.node('rdfsReasoner'), { graph: SOURCES, evidence: [prior] });
  assert.equal(r.evidence.length, 2);
  assert.equal(r.evidence[0], prior);
  assert.ok(r.assumptions.includes('X.y'));
});

test('a missing stage refuses to run, before any node runs', { skip }, async () => {
  const missing = (await f.stages()).find((s) => s.status === 'missing');
  const n = await f.node(missing.name);
  assert.equal(n.runnable, false);
  assert.equal(n.contract, null);
  await assert.rejects(f.run(f.pipe(await f.node('turtleDocumentReader'), n), SOURCES),
    (err) => err instanceof f.FactoidalError && /missing/.test(err.message));
});

test('an unknown stage name rejects', { skip }, async () => {
  await assert.rejects(f.node('noSuchStage'), (err) => err instanceof f.FactoidalError);
  assert.throws(() => f.pipe(), TypeError);
  assert.throws(() => f.pipe({}), TypeError);
});
