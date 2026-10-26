// The pipeline check (https://github.com/danbri/factoidal/issues/1002,
// step 1): pipe() and run() take the type check and the assumption union
// from the engine's op pipelineCheck (formal/lean4/Wasm/Ops/StageList.lean,
// computed by pipelineReport of formal/lean4/L4Factoidal/Dataflow/
// Pipeline.lean), not from JavaScript.
//
// Part 1 needs no wasm: buildNodes over a stub engine whose stageList and
// pipelineCheck return the outputs the Lean op gave for these stages
// (recorded from `#eval pipelineCheck ...`). Part 2 runs the real engine and
// fails when the loaded wasm has no pipelineCheck op.

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';
import { buildNodes } from '../lib/nodes.mjs';
import { FactoidalError } from '../lib/errors.mjs';

// ---- Part 1: the wiring, over a stub engine ----

const TW = 'L4Factoidal.Dataflow.TurtleWriterRoundTrip';
const STAGES = [
  { name: 'turtleDocumentReader', status: 'proved', contract: 'L4Factoidal.Dataflow.ReaderContract',
    assumptions: [], wireIn: 'String', wireOut: 'Dataset × PrefixList' },
  { name: 'rdfsReasoner', status: 'proved', contract: 'L4Factoidal.Dataflow.Regime.Entails',
    assumptions: [], wireIn: 'Graph', wireOut: 'Graph' },
  { name: 'turtleDocumentWriter', status: 'assumed', contract: 'L4Factoidal.Dataflow.RoundTripOn',
    assumptions: [TW], wireIn: 'Dataset', wireOut: 'String' },
].map((s) => ({ declaration: `L4Factoidal.Dataflow.${s.name}`, area: s.name, dir: 'Dataflow',
  kind: 'Stage', params: [], theorems: [], tests: [], note: '', runnable: true, ...s }));

// What the Lean op returned for these name lists.
const CHECKS = {
  'turtleDocumentReader,turtleDocumentWriter': {
    ok: true, wellTyped: true, wireIn: 'String', wireOut: 'String', mismatch: null,
    conversions: [{ at: 0, from: 'Dataset × PrefixList', to: 'Dataset' }], assumptions: [TW],
    contract: { theorem: 'L4Factoidal.Dataflow.Pipeline.guarantee_sound',
      stages: ['L4Factoidal.Dataflow.ReaderContract', 'L4Factoidal.Dataflow.RoundTripOn'] },
    stages: [] },
  'turtleDocumentWriter,rdfsReasoner': {
    ok: true, wellTyped: false, wireIn: 'Dataset', wireOut: 'Graph',
    mismatch: { at: 0, out: 'String', in: 'Graph' }, conversions: [], assumptions: [TW],
    contract: { theorem: 'L4Factoidal.Dataflow.Pipeline.guarantee_sound',
      stages: ['L4Factoidal.Dataflow.RoundTripOn', 'L4Factoidal.Dataflow.Regime.Entails'] },
    stages: [] },
};

class StubDataset {}

function stubNodes({ withOp }) {
  const calls = [];
  const engine = {
    stageList: () => JSON.stringify({ ok: true, count: STAGES.length, stages: STAGES }),
  };
  if (withOp) {
    engine.pipelineCheck = (namesJson) => {
      calls.push(JSON.parse(namesJson));
      return JSON.stringify(CHECKS[JSON.parse(namesJson).join(',')]);
    };
  }
  const api = buildNodes({
    entry: async () => engine,
    entryResult: (t) => { const r = JSON.parse(t); if (!r.ok) throw new Error(r.error); return r; },
    requireEntryFn: () => {},
    Dataset: StubDataset,
    parse: async () => new StubDataset(),
    closure: async (g) => g,
    shaclValidate: async () => ({ conforms: true, report: null }),
    query: async () => [],
    serialize: async () => 'text',
    canonicalize: async () => '',
    explain: async () => ({}),
  });
  return { api, calls };
}

test('pipe(): assumptions and wellTyped are the op\'s', async () => {
  const { api, calls } = stubNodes({ withOp: true });
  const p = api.pipe(await api.node('turtleDocumentReader'), await api.node('turtleDocumentWriter'));
  assert.deepEqual(calls, [['turtleDocumentReader', 'turtleDocumentWriter']]);
  assert.equal(p.wellTyped, true);
  assert.deepEqual([...p.assumptions], [TW]);
  assert.deepEqual([...p.check.assumptions], [TW]);
  assert.equal(p.check.contract.theorem, 'L4Factoidal.Dataflow.Pipeline.guarantee_sound');
  assert.deepEqual(p.check.conversions.map((c) => ({ ...c })), [{ at: 0, from: 'Dataset × PrefixList', to: 'Dataset' }]);
});

test('run(): assumptions equal the op\'s; prior evidence assumptions come first', async () => {
  const { api } = stubNodes({ withOp: true });
  const p = api.pipe(await api.node('turtleDocumentReader'), await api.node('turtleDocumentWriter'));
  const r = await api.run(p, '<a> <b> <c> .');
  assert.deepEqual(r.assumptions, [...p.check.assumptions]);
  assert.equal(r.wellTyped, true);
  assert.equal(r.proved, false); // the writer is assumed
  assert.deepEqual(r.uncheckedSteps, ['turtleDocumentWriter']);
  const prior = { stage: 'upstream', status: 'tested', contract: null, assumptions: ['X.y', TW], artefact: null };
  const r2 = await api.run(p, { graph: '<a> <b> <c> .', evidence: [prior] });
  assert.deepEqual(r2.assumptions, ['X.y', TW]);
});

test('run(): an ill-typed pipeline rejects before any node runs; unchecked runs it unproved', async () => {
  const { api } = stubNodes({ withOp: true });
  const p = api.pipe(await api.node('turtleDocumentWriter'), await api.node('rdfsReasoner'));
  assert.equal(p.wellTyped, false);
  await assert.rejects(api.run(p, new StubDataset()),
    (err) => err instanceof FactoidalError && err.code === 'op.failed' &&
      /not well typed: stage 0 \(turtleDocumentWriter\) writes String, stage 1 \(rdfsReasoner\) reads Graph/.test(err.message));
  const r = await api.run(p, new StubDataset(), { unchecked: true });
  assert.equal(r.wellTyped, false);
  assert.equal(r.proved, false);
  assert.deepEqual(r.assumptions, [TW]);
});

test('an engine without the op: wellTyped null, assumptions from the nodes', async () => {
  const { api } = stubNodes({ withOp: false });
  const p = api.pipe(await api.node('turtleDocumentReader'), await api.node('turtleDocumentWriter'));
  assert.equal(p.wellTyped, null);
  assert.equal(p.check, null);
  assert.deepEqual([...p.assumptions], [TW]);
  const r = await api.run(p, '<a> <b> <c> .');
  assert.equal(r.wellTyped, null);
  assert.deepEqual(r.assumptions, [TW]);
});

// ---- Part 2: the real engine ----

// The package wasm must serve the ops of this file: a missing op fails the
// cases, never skips them (https://github.com/danbri/factoidal/issues/1038, P2).
test('the package wasm serves stages, pipelineCheck, explain', async () => {
  const caps = await f.capabilities();
  assert.equal(caps.stages, true, 'capabilities().stages');
  assert.equal(caps.pipelineCheck, true, 'capabilities().pipelineCheck');
  assert.equal(caps.explain, true, 'capabilities().explain');
});

const SOURCES = `
  @prefix ex: <http://example.org/> .
  @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
  ex:alice ex:worksFor ex:acme .
  ex:worksFor rdfs:domain ex:Employee .
  ex:Employee rdfs:subClassOf ex:Person .
`;
const DESCRIPTION = `@prefix ex: <http://example.org/> .
  _:x a ex:Person . _:x ex:worksFor ex:acme .`;

test('engine: run().assumptions equals pipelineCheck\'s, reader -> reasoner -> explain', async () => {
  const p = f.pipe(await f.node('turtleDocumentReader'), await f.node('rdfsReasoner'),
    await f.node('rdfsExplainGraphStage', { description: DESCRIPTION }));
  assert.equal(p.wellTyped, true);
  assert.deepEqual(p.check.conversions.map((c) => [c.at, c.from, c.to]),
    [[0, 'Dataset × PrefixList', 'Graph'], [1, 'Graph', 'Dataset']]);
  const r = await f.run(p, SOURCES);
  assert.deepEqual(r.assumptions, [...p.check.assumptions]);
  assert.equal(r.wellTyped, true);
});

test('engine: an assumed writer\'s assumption is in pipelineCheck\'s union and in run()\'s', async () => {
  const p = f.pipe(await f.node('turtleDocumentReader'), await f.node('turtleDocumentWriter'));
  assert.ok(p.check.assumptions.includes(TW));
  const r = await f.run(p, '<http://example.org/a> <http://example.org/p> <http://example.org/b> .');
  assert.deepEqual(r.assumptions, [...p.check.assumptions]);
});

test('engine: an ill-typed pipeline is rejected', async () => {
  const p = f.pipe(await f.node('turtleDocumentWriter'), await f.node('rdfsReasoner'));
  assert.equal(p.wellTyped, false);
  assert.deepEqual({ ...p.check.mismatch }, { at: 0, out: 'String', in: 'Graph' });
  await assert.rejects(f.run(p, await f.parse(SOURCES)),
    (err) => err instanceof f.FactoidalError && err.code === 'op.failed');
});
