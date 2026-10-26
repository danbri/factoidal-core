// Node settings in the pipeline (https://github.com/danbri/factoidal/issues/975,
// https://github.com/danbri/factoidal/issues/1026): the engine's op
// pipelineCheckNodes (formal/lean4/Wasm/Ops/PipelineNodes.lean) decides each
// node's canonical settings, their digest, the settings outside the proved
// domain, and the output wire the settings select (owner, 2026-10-25: SELECT
// writes a Table, ASK an Answer, CONSTRUCT and DESCRIBE a Dataset). lib/nodes.mjs only marshals.
//
// Part 1 needs no wasm: buildNodes over a stub engine whose pipelineCheckNodes
// returns the outputs the Lean op gave for these requests (recorded with
// `#eval IO.println (pipelineCheckNodes ...)` against
// L4Factoidal.Dataflow.NodeSettings, 2026-10-25). Part 2 runs the real engine
// and SKIPS when the loaded wasm has no pipelineCheckNodes op (a module built
// before this change; it is rebuilt in danbri/factoidal-builds).

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';
import { buildNodes } from '../lib/nodes.mjs';
import { makeRecord, reasonOf } from '../lib/evidence.mjs';
import { FactoidalError } from '../lib/errors.mjs';

// ---- Part 1: the wiring, over a stub engine ----

const CSVW = 'CSVW (tabular data to RDF)';
const CQ = 'CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }';
const SQ = 'SELECT ?s WHERE { ?s ?p ?o }';
const GS = 'L4Factoidal.Dataflow.Pipeline.guarantee_sound';
const RC = 'L4Factoidal.Dataflow.ReaderContract';
const EC = 'L4Factoidal.Dataflow.EvalContract';
const LENIENT_WHY = 'the lenient parse skips the statements that fail; ReaderContract states the strict parse (parseDocumentRaw)';

const stage = (name, status, contract, wireIn, wireOut) => ({
  name, status, contract, wireIn, wireOut, declaration: null, area: name, dir: 'Dataflow',
  kind: 'Stage', params: [], theorems: [], assumptions: [], tests: [], note: '',
  runnable: status !== 'missing',
});

const STAGES = (csvwStatus) => [
  stage('turtleDocumentReader', 'proved', RC, 'String', 'Dataset × PrefixList'),
  stage('shippedEvaluator', 'proved', EC, 'Dataset', 'Answer'),
  stage(CSVW, csvwStatus, null, 'CSV', 'Dataset'),
];

// The Lean op's per-node output (recorded).
const READER = { name: 'turtleDocumentReader', status: 'proved', registryStatus: 'proved', checked: true,
  contract: RC, assumptions: [], wireIn: 'String', wireOut: 'Dataset × PrefixList',
  settings: { lenient: false },
  settingsDigest: 'sha256:8923599099e1352fd3d5a3a7a80639bff09625cb8b5d5dda7400b01b65c9cbad',
  roles: { lenient: 'narrows' }, outside: [], derived: {} };
const LENIENT = { ...READER, status: 'unproved', checked: false, settings: { lenient: true },
  settingsDigest: 'sha256:a929203d1737db0ea4984beb3d077db58a1fce5ba392ecb0c8afe82f4eebec6e',
  outside: [{ setting: 'lenient', reason: LENIENT_WHY }] };
const CONSTRUCT = { name: 'shippedEvaluator', status: 'proved', registryStatus: 'proved', checked: true,
  contract: EC, assumptions: [], wireIn: 'Dataset', wireOut: 'Dataset',
  settings: { entail: 'none', query: CQ },
  settingsDigest: 'sha256:84c08eb8384223749394e25785a4f96834eef42bb1d4a45f5aec446299d06742',
  roles: { entail: 'narrows', query: 'selects-wire' }, outside: [], derived: { form: 'CONSTRUCT' } };
const SELECT = { ...CONSTRUCT, wireOut: 'Table', settings: { entail: 'none', query: SQ },
  settingsDigest: 'sha256:1a9de45577f60c1cc62ca96529343390b302124a76c682e8c253b76a8ecef44a',
  derived: { form: 'SELECT' } };
const CSVW_NODE = { name: CSVW, status: 'tested', registryStatus: 'tested', checked: false,
  contract: null, assumptions: [], wireIn: 'CSV', wireOut: 'Dataset', settings: { metadata: '{}' },
  settingsDigest: 'sha256:f412f724e3f99b64a8d2363379495951fa01071c86045234ecab53943d5bc8ef',
  roles: { metadata: 'parameter' }, outside: [], derived: {} };

const key = (n) => `${n.stage}${JSON.stringify(n.settings)}`;
const NODE_OUT = {
  [key({ stage: 'turtleDocumentReader', settings: {} })]: READER,
  [key({ stage: 'turtleDocumentReader', settings: { lenient: true } })]: LENIENT,
  [key({ stage: 'shippedEvaluator', settings: { query: CQ } })]: CONSTRUCT,
  [key({ stage: 'shippedEvaluator', settings: { query: SQ } })]: SELECT,
  [key({ stage: CSVW, settings: { metadata: '{}' } })]: CSVW_NODE,
};
// The pipeline-level fields the op returned for these node lists.
const PIPES = {
  'turtleDocumentReader,shippedEvaluator:CONSTRUCT,shippedEvaluator:CONSTRUCT': {
    wellTyped: true, wireIn: 'String', wireOut: 'Dataset', mismatch: null,
    conversions: [{ at: 0, from: 'Dataset × PrefixList', to: 'Dataset' }] },
  'turtleDocumentReader,shippedEvaluator:SELECT,shippedEvaluator:CONSTRUCT': {
    wellTyped: false, wireIn: 'String', wireOut: 'Dataset', mismatch: { at: 1, out: 'Table', in: 'Dataset' },
    conversions: [{ at: 0, from: 'Dataset × PrefixList', to: 'Dataset' }] },
  'turtleDocumentReader,shippedEvaluator:CONSTRUCT': {
    wellTyped: true, wireIn: 'String', wireOut: 'Dataset', mismatch: null,
    conversions: [{ at: 0, from: 'Dataset × PrefixList', to: 'Dataset' }] },
};

class StubDataset {
  constructor(text = '') { this.text = text; }
  toNQuads() { return this.text; }
}

function stubNodes({ csvwStatus = 'tested', withNodeOp = true } = {}) {
  const calls = { nodes: [], csvw: [], query: [] };
  const engine = {
    stageList: () => JSON.stringify({ ok: true, count: 3, stages: STAGES(csvwStatus) }),
    pipelineCheck: (namesJson) => JSON.stringify({ ok: true, wellTyped: false, wireIn: null, wireOut: null,
      mismatch: { at: 0, out: 'Answer', in: 'Dataset' }, conversions: [], assumptions: [],
      contract: { theorem: GS, stages: [] }, stages: JSON.parse(namesJson).map(() => ({ assumptions: [] })) }),
  };
  if (withNodeOp) {
    engine.pipelineCheckNodes = (nodesJson) => {
      const items = JSON.parse(nodesJson);
      calls.nodes.push(items);
      const stages = items.map((n) => {
        const r = NODE_OUT[key(n)];
        if (!r) throw new Error(`stub: no recorded output for ${key(n)}`);
        return r;
      });
      const pkey = stages.map((s) => (s.derived.form ? `${s.name}:${s.derived.form}` : s.name)).join(',');
      const pipeFields = stages.length === 1
        ? { wellTyped: true, wireIn: stages[0].wireIn, wireOut: stages[0].wireOut, mismatch: null, conversions: [] }
        : PIPES[pkey];
      return JSON.stringify({ ok: true, ...pipeFields, assumptions: [],
        contract: { theorem: GS, stages: stages.map((s) => s.contract) }, stages });
    };
  }
  const api = buildNodes({
    entry: async () => engine,
    entryResult: (t) => { const r = JSON.parse(t); if (!r.ok) throw new Error(r.error); return r; },
    requireEntryFn: () => {},
    Dataset: StubDataset,
    parse: async (text) => new StubDataset(text),
    closure: async (g) => g,
    shaclValidate: async () => ({ conforms: true, report: null }),
    query: async (g, q) => { calls.query.push(q); return q.startsWith('CONSTRUCT') ? new StubDataset('c') : []; },
    serialize: async () => 'text',
    canonicalize: async () => '',
    explain: async () => ({}),
    csvwToRdf: async (csv, meta, opts) => { calls.csvw.push([csv, meta, opts]); return new StubDataset('csvw'); },
  });
  return { api, calls };
}

test('issue 1026: a CONSTRUCT node writes a Dataset, a SELECT node a Table; reader -> CONSTRUCT -> CONSTRUCT is well typed', async () => {
  const { api, calls } = stubNodes();
  const c1 = await api.node('shippedEvaluator', { query: CQ });
  assert.equal(c1.wireOut, 'Dataset');
  assert.equal((await api.node('shippedEvaluator', { query: SQ })).wireOut, 'Table');
  assert.deepEqual({ ...c1.derived }, { form: 'CONSTRUCT' });
  const p = api.pipe(await api.node('turtleDocumentReader'), c1, await api.node('shippedEvaluator', { query: CQ }));
  assert.equal(p.wellTyped, true);
  assert.deepEqual(calls.nodes.at(-1).map((n) => n.stage),
    ['turtleDocumentReader', 'shippedEvaluator', 'shippedEvaluator']);
  const r = await api.run(p, '<urn:a> <urn:b> <urn:c> .');
  assert.equal(r.proved, true);
  assert.deepEqual(calls.query, [CQ, CQ]);
  assert.ok(r.graph instanceof StubDataset);
});

test('issue 1026: reader -> SELECT -> CONSTRUCT is refused', async () => {
  const { api } = stubNodes();
  const p = api.pipe(await api.node('turtleDocumentReader'), await api.node('shippedEvaluator', { query: SQ }),
    await api.node('shippedEvaluator', { query: CQ }));
  assert.equal(p.wellTyped, false);
  assert.deepEqual({ ...p.check.mismatch }, { at: 1, out: 'Table', in: 'Dataset' });
  await assert.rejects(api.run(p, '<urn:a> <urn:b> <urn:c> .'),
    (err) => err instanceof FactoidalError && err.code === 'op.failed');
});

test('each record carries the node settings and their digest', async () => {
  const { api } = stubNodes();
  const r = await api.run(api.pipe(await api.node('turtleDocumentReader'),
    await api.node('shippedEvaluator', { query: CQ })), '<urn:a> <urn:b> <urn:c> .');
  assert.deepEqual(r.evidence.map((e) => [e.stage, e.status, e.checked, e.settingsDigest]), [
    ['turtleDocumentReader', 'proved', true, READER.settingsDigest],
    ['shippedEvaluator', 'proved', true, CONSTRUCT.settingsDigest],
  ]);
  assert.deepEqual(r.evidence[0].settings, { lenient: false });
  assert.deepEqual(r.evidence[1].settings, { entail: 'none', query: CQ });
  assert.equal('outside' in r.evidence[0], false);
});

test('a lenient reader is unproved: its record names the setting and the reason', async () => {
  const { api } = stubNodes();
  const n = await api.node('turtleDocumentReader', { lenient: true });
  assert.equal(n.status, 'unproved');
  assert.equal(n.registryStatus, 'proved');
  const r = await api.run(api.pipe(n, await api.node('shippedEvaluator', { query: CQ })),
    '<urn:a> <urn:b> <urn:c> .', { unchecked: true });
  assert.equal(r.proved, false);
  assert.deepEqual(r.uncheckedSteps, ['turtleDocumentReader']);
  const rec = r.evidence[0];
  assert.equal(rec.status, 'unproved');
  assert.equal(rec.checked, false);
  assert.equal(rec.registryStatus, 'proved');
  assert.deepEqual(rec.outside.map((o) => ({ ...o })), [{ setting: 'lenient', reason: LENIENT_WHY }]);
  assert.match(rec.reason, /settings outside the proved domain: lenient/);
  // without the opt-in it also runs (the stage is runnable) and is not proved
  const r2 = await api.run(api.pipe(n), '<urn:a> <urn:b> <urn:c> .');
  assert.equal(r2.proved, false);
});

test('CSVW is a bound stage: it runs csvwToRdf with its settings and gives a record', async () => {
  const { api, calls } = stubNodes();
  const s = (await api.stages()).find((x) => x.name === CSVW);
  assert.deepEqual([s.status, s.runnable, s.bound], ['tested', true, true]);
  const n = await api.node(CSVW, { metadata: '{}' });
  const r = await api.run(api.pipe(n), 'a,b\n1,2\n');
  assert.deepEqual(calls.csvw, [['a,b\n1,2\n', '{}', {}]]);
  assert.ok(r.graph instanceof StubDataset);
  assert.equal(r.evidence[0].stage, CSVW);
  assert.equal(r.evidence[0].status, 'tested');
  assert.equal(r.evidence[0].checked, false);
  assert.equal(r.evidence[0].settingsDigest, CSVW_NODE.settingsDigest);
  assert.equal(r.proved, false);
});

test('an engine that reports CSVW missing: the runner is not bound (no early pass)', async () => {
  const { api } = stubNodes({ csvwStatus: 'missing', withNodeOp: false });
  const s = (await api.stages()).find((x) => x.name === CSVW);
  assert.deepEqual([s.status, s.runnable, s.bound], ['missing', false, false]);
});

test('an engine without pipelineCheckNodes: no settings in records, the registry wire', async () => {
  const { api } = stubNodes({ withNodeOp: false });
  const n = await api.node('shippedEvaluator', { query: CQ });
  assert.equal(n.wireOut, 'Answer');
  assert.equal(n.settingsDigest, null);
  const rec = makeRecord(n, null, false);
  assert.equal('settings' in rec, false);
  assert.equal(api.pipe(await api.node('turtleDocumentReader'), n, n).wellTyped, false);
});

test('settings marshal: a Dataset is sent as its N-Quads; a function is refused', async () => {
  const { api, calls } = stubNodes({ withNodeOp: false });
  await assert.rejects(api.node('shippedEvaluator', { query: () => 1 }), TypeError);
  const n = await api.node('turtleDocumentReader', { shapes: new StubDataset('<a> <b> <c> .\n') });
  assert.deepEqual(n.settingsWire, { shapes: { $nquads: '<a> <b> <c> .\n' } });
  assert.equal(calls.nodes.length, 0);
});

test('reasonOf: an unproved node names its settings outside the domain', () => {
  const why = reasonOf({ stage: 'r', status: 'unproved', registryStatus: 'proved', assumptions: [],
    outside: [{ setting: 'lenient', reason: 'x' }] });
  assert.equal(why, 'status unproved (registry status proved); settings outside the proved domain: lenient (x)');
});

// ---- Part 2: the real engine ----

// The package wasm must serve the ops of this file: a missing op fails the
// cases, never skips them (https://github.com/danbri/factoidal/issues/1038, P2).
test('the package wasm serves stages, pipelineCheckNodes', async () => {
  const caps = await f.capabilities();
  assert.equal(caps.stages, true, 'capabilities().stages');
  assert.equal(caps.pipelineCheckNodes, true, 'capabilities().pipelineCheckNodes');
});

const DATA = '<http://example.org/a> <http://example.org/p> <http://example.org/b> .';

test('engine: reader -> CONSTRUCT -> CONSTRUCT runs, each record with settings', async () => {
  const q2 = 'CONSTRUCT { ?o ?p ?s } WHERE { ?s ?p ?o }';
  const p = f.pipe(await f.node('turtleDocumentReader'), await f.node('shippedEvaluator', { query: CQ }),
    await f.node('shippedEvaluator', { query: q2 }));
  assert.equal(p.wellTyped, true);
  const r = await f.run(p, DATA);
  assert.equal(r.proved, true);
  assert.equal(r.evidence.length, 3);
  for (const e of r.evidence) assert.match(e.settingsDigest, /^sha256:[0-9a-f]{64}$/);
  assert.deepEqual(r.evidence[1].settings, { entail: 'none', query: CQ });
  assert.equal(r.graph.size, 1);
});

test('engine: reader -> SELECT -> CONSTRUCT is not well typed', async () => {
  const p = f.pipe(await f.node('turtleDocumentReader'), await f.node('shippedEvaluator', { query: SQ }),
    await f.node('shippedEvaluator', { query: CQ }));
  assert.equal(p.wellTyped, false);
  assert.deepEqual({ ...p.check.mismatch }, { at: 1, out: 'Table', in: 'Dataset' });
});

test('engine: a query that does not parse is refused at node()', async () => {
  await assert.rejects(f.node('shippedEvaluator', { query: 'SELEKT' }), /does not parse/);
});

test('engine: CSVW runs as a node and its output feeds a CONSTRUCT', async () => {
  const p = f.pipe(await f.node(CSVW, { mode: 'minimal' }),
    await f.node('shippedEvaluator', { query: CQ }));
  assert.equal(p.wellTyped, true);
  const r = await f.run(p, 'name,height\nOne Canada Square,235\n');
  assert.equal(r.evidence[0].stage, CSVW);
  assert.equal(r.evidence[0].status, 'tested');
  assert.equal(r.proved, false);
  assert.ok(r.graph.size > 0);
});
