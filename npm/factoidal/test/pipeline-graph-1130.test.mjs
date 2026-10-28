// Pipelines as acyclic graphs with named ports
// (https://github.com/danbri/factoidal/issues/1130, stage 1b): graph() takes
// the check from the engine's op graphCheckNodes (formal/lean4/Wasm/Ops/
// GraphNodes.lean, computed by graphIssues of formal/lean4/L4Factoidal/
// Dataflow/Graph.lean), and run() runs a graph node by node.
//
// Part 1 needs no wasm: buildNodes over a stub engine whose stageList and
// graphCheckNodes return answers the Lean op gave (recorded from
// `#eval graphCheckNodes ...`), and a stub without the op.
// Part 2 runs the real engine. One case asserts that the loaded wasm serves
// graphCheckNodes and datasetMerge; the other cases run with no skip and fail
// on a wasm without them, which is correct: it names the stale wasm
// (skills/test-suites, "An npm test of a new op is a plain assertion";
// https://github.com/danbri/factoidal/issues/1038, P2).

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';
import { buildNodes } from '../lib/nodes.mjs';
import { FactoidalError } from '../lib/errors.mjs';

// ---- Part 1: the wiring, over a stub engine ----

const READER = {
  name: 'nquadsDocumentReader', declaration: 'L4Factoidal.Dataflow.nquadsDocumentReader',
  area: 'reader', dir: 'Dataflow', kind: 'RdfReader', wireIn: 'String', wireOut: 'Dataset × PrefixList',
  params: [], status: 'proved', contract: 'L4Factoidal.Dataflow.ReaderContract', theorems: [],
  assumptions: [], tests: [], note: '', runnable: true,
};

const nodeJson = (name, extra) => ({
  name, kind: 'RdfReader', status: 'proved', registryStatus: 'proved', checked: true,
  contract: 'L4Factoidal.Dataflow.ReaderContract', theorems: [], assumptions: [],
  ports: [{ name: 'in', wire: 'String' }], wireOut: 'Dataset × PrefixList',
  settings: { lenient: false }, settingsDigest: 'sha256:89', roles: { lenient: 'narrows' },
  outside: [], derived: {}, ...extra,
});
const MERGE = nodeJson('datasetMerge', {
  kind: 'PortComponent', registryStatus: null, contract: 'L4Factoidal.RDF.DatasetDen.IsMerge',
  ports: [{ name: 'left', wire: 'Dataset' }, { name: 'right', wire: 'Dataset' }], wireOut: 'Dataset',
  settings: {}, settingsDigest: 'sha256:44', roles: {},
});
const CONTRACT = { theorem: 'L4Factoidal.Dataflow.Graph.guarantee_sound',
  staticCheck: 'L4Factoidal.Dataflow.Graph.run_stage_error_only' };
const answer = (issues, nodes, wireOut) => JSON.stringify({
  ok: true, issues, wireOut, assumptions: [], contract: CONTRACT, nodes });

// What the Lean op answered for these requests (the sources of each node).
function stubAnswer(req) {
  const stages = req.nodes.map((n) => n.stage).join(',');
  const from = JSON.stringify(req.nodes.map((n) => n.from));
  if (stages === 'datasetMerge') return answer([{ kind: 'portCount', node: 0, ports: 2, sources: 0 }], [MERGE], 'Dataset');
  if (stages === 'nquadsDocumentReader,nquadsDocumentReader,datasetMerge') {
    if (from === '[[{"input":0}],[{"input":1}],[{"node":0},{"node":1}]]') {
      return answer([], [nodeJson('nquadsDocumentReader'), nodeJson('nquadsDocumentReader'), MERGE], 'Dataset');
    }
    if (from === '[[{"input":0}],[{"input":1}],[{"node":0},{"node":2}]]') {
      return answer([{ kind: 'forwardRef', node: 2, port: 1, portName: 'right', ref: 2 }],
        [nodeJson('nquadsDocumentReader'), nodeJson('nquadsDocumentReader'), MERGE], 'Dataset');
    }
  }
  return JSON.stringify({ ok: false, error: `stub: no recorded answer for ${stages} ${from}` });
}

class StubDataset {
  constructor(label) { this.label = label; }
}

function stubNodes({ withOp }) {
  const calls = [];
  const engine = {
    stageList: () => JSON.stringify({ ok: true, count: 1, stages: [READER] }),
  };
  if (withOp) {
    engine.graphCheckNodes = (text) => {
      const req = JSON.parse(text);
      calls.push(req);
      return stubAnswer(req);
    };
  }
  const merges = [];
  const api = buildNodes({
    entry: async () => engine,
    entryResult: (t) => { const r = JSON.parse(t); if (!r.ok) throw new FactoidalError(r.error); return r; },
    requireEntryFn: (e, fn, what) => {
      if (typeof e[fn] !== 'function') throw new FactoidalError(`${what}: no op ${fn}`, { code: 'op.unknown' });
    },
    Dataset: StubDataset,
    parse: async (text) => new StubDataset(text),
    closure: async (g) => g,
    shaclValidate: async () => ({ conforms: true, report: null }),
    query: async () => [],
    serialize: async () => 'text',
    canonicalize: async () => '',
    canonicalHash: async () => '',
    explain: async () => ({}),
    csvwToRdf: async () => new StubDataset('csv'),
    datasetMerge: async (a, b) => { merges.push([a.label, b.label]); return new StubDataset(`${a.label}+${b.label}`); },
  });
  return { api, calls, merges };
}

async function stubMergeGraph(api) {
  const r = await api.node('nquadsDocumentReader');
  const m = await api.node('datasetMerge');
  return { r, m, nodes: [{ node: r, from: [{ input: 0 }] }, { node: r, from: [{ input: 1 }] }] };
}

test('node(datasetMerge): a port stage read from graphCheckNodes, two named ports', async () => {
  const { api } = stubNodes({ withOp: true });
  const m = await api.node('datasetMerge');
  assert.equal(m.stage, 'datasetMerge');
  assert.equal(m.status, 'proved');
  assert.equal(m.registryStatus, null);
  assert.equal(m.contract, 'L4Factoidal.RDF.DatasetDen.IsMerge');
  assert.deepEqual(m.ports.map((p) => p.name), ['left', 'right']);
  assert.equal(m.wireIn, null);
  assert.equal(m.wireOut, 'Dataset');
  assert.equal(m.bound, true);
  const r = await api.node('nquadsDocumentReader');
  assert.deepEqual(r.ports.map((p) => ({ ...p })), [{ name: 'in', wire: 'String' }]);
});

test('graph(): the engine checks the request, and run() feeds each port its source', async () => {
  const { api, calls, merges } = stubNodes({ withOp: true });
  const { m, nodes } = await stubMergeGraph(api);
  const g = api.graph({ inputs: ['String', 'String'], nodes: [...nodes, { node: m, from: [{ node: 0 }, { node: 1 }] }] });
  assert.deepEqual(calls.at(-1).inputs, ['String', 'String']);
  assert.deepEqual(calls.at(-1).nodes.map((n) => n.from), [[{ input: 0 }], [{ input: 1 }], [{ node: 0 }, { node: 1 }]]);
  assert.equal(g.wireOut, 'Dataset');
  assert.equal(g.check.contract.theorem, 'L4Factoidal.Dataflow.Graph.guarantee_sound');
  const r = await api.run(g, ['A', 'B']);
  assert.deepEqual(merges, [['A', 'B']]);
  assert.equal(r.graph.label, 'A+B');
  assert.equal(r.values.length, 3);
  assert.deepEqual(r.evidence.map((e) => [e.stage, e.node]), [['nquadsDocumentReader', 0],
    ['nquadsDocumentReader', 1], ['datasetMerge', 2]]);
  assert.deepEqual(r.evidence[2].from.map((x) => ({ ...x })), [{ node: 0 }, { node: 1 }]);
  assert.equal(r.proved, true);
  assert.deepEqual(r.assumptions, []);
});

test('graph(): a graph with an issue is refused, with the engine\'s issues', async () => {
  const { api } = stubNodes({ withOp: true });
  const { m, nodes } = await stubMergeGraph(api);
  assert.throws(() => api.graph({ inputs: ['String', 'String'],
    nodes: [...nodes, { node: m, from: [{ node: 0 }, { node: 2 }] }] }),
  (err) => err instanceof FactoidalError && err.code === 'op.failed' &&
    /node 2 port 1 \(right\) reads node 2, which is not before it/.test(err.message) &&
    err.issues.length === 1 && err.issues[0].kind === 'forwardRef');
});

test('an engine without graphCheckNodes: graph() is refused with op.unknown, node(datasetMerge) is unknown', async () => {
  const { api } = stubNodes({ withOp: false });
  const r = await api.node('nquadsDocumentReader');
  assert.throws(() => api.graph({ inputs: ['String'], nodes: [{ node: r, from: [{ input: 0 }] }] }),
    (err) => err instanceof FactoidalError && err.code === 'op.unknown');
  await assert.rejects(api.node('datasetMerge'),
    (err) => err instanceof FactoidalError && /no registered stage named 'datasetMerge'/.test(err.message));
});

test('pipe() refuses a node with two ports; graph() refuses a malformed spec', async () => {
  const { api } = stubNodes({ withOp: true });
  const m = await api.node('datasetMerge');
  assert.throws(() => api.pipe(m), TypeError);
  assert.throws(() => api.graph({ nodes: [] }), TypeError);
  assert.throws(() => api.graph({ nodes: [{ node: {}, from: [] }] }), TypeError);
  assert.throws(() => api.graph({ inputs: [1], nodes: [{ node: m, from: [] }] }), TypeError);
});

test('run(graph): the inputs are an array, one value per graph input, on its wire', async () => {
  const { api } = stubNodes({ withOp: true });
  const { m, nodes } = await stubMergeGraph(api);
  const g = api.graph({ inputs: ['String', 'String'], nodes: [...nodes, { node: m, from: [{ node: 0 }, { node: 1 }] }] });
  await assert.rejects(api.run(g, 'A'), TypeError);
  await assert.rejects(api.run(g, ['A']), TypeError);
  await assert.rejects(api.run(g, ['A', 7]), (err) => err instanceof FactoidalError &&
    /graph input 1 is declared String, got number/.test(err.message));
});

// ---- Part 2: the real engine ----

test('the package wasm serves graphCheckNodes and datasetMerge', async () => {
  const caps = await f.capabilities();
  assert.equal(caps.graphCheck, true, 'capabilities().graphCheck');
  assert.equal(caps.datasetMerge, true, 'capabilities().datasetMerge');
});

const DOC = '_:b <http://example.org/p> <http://example.org/o> .\n';
const SELECT = 'SELECT ?s WHERE { ?s ?p ?o }';

async function mergeGraph(extra) {
  const r = await f.node('nquadsDocumentReader');
  return f.graph({
    inputs: ['String', 'String'],
    nodes: [
      { node: r, from: [{ input: 0 }] },
      { node: r, from: [{ input: 1 }] },
      { node: await f.node('datasetMerge'), from: [{ node: 0 }, { node: 1 }] },
      ...(extra || []),
    ],
  });
}

test('engine: datasetMerge() keeps the blank nodes of two documents apart', async () => {
  const a = await f.parse(DOC, 'nquads');
  const b = await f.parse(DOC, 'nquads');
  const m = await f.datasetMerge(a, b);
  assert.equal(m.size, 2);
  assert.equal((await f.query(m, SELECT)).length, 2);
  assert.equal(a.size, 1);
  assert.equal(b.size, 1);
  // the same dataset twice is still two blank nodes
  assert.equal((await f.datasetMerge(a, a)).size, 2);
});

test('engine: two readers -> datasetMerge -> SELECT gives two solutions', async () => {
  const g = await mergeGraph([{ node: await f.node('shippedEvaluator', { query: SELECT }), from: [{ node: 2 }] }]);
  assert.equal(g.wireOut, 'Table');
  assert.deepEqual([...g.assumptions], []);
  assert.deepEqual(g.check.nodes.map((n) => n.status), ['proved', 'proved', 'proved', 'proved']);
  const r = await f.run(g, [DOC, DOC]);
  assert.equal(r.graph.length, 2);
  assert.equal(r.values.length, 4);
  assert.equal(r.values[2].size, 2);
  assert.equal(r.evidence.length, 4);
  assert.equal(r.evidence[2].stage, 'datasetMerge');
  assert.equal(r.evidence[2].contract, 'L4Factoidal.RDF.DatasetDen.IsMerge');
  assert.equal(r.proved, true);
});

test('engine: fan-out, one reader feeds two writers', async () => {
  const r = await f.node('nquadsDocumentReader');
  const g = f.graph({
    inputs: ['String'],
    nodes: [
      { node: r, from: [{ input: 0 }] },
      { node: await f.node('nquadsDocumentWriter'), from: [{ node: 0 }] },
      { node: await f.node('ntriplesDocumentWriter'), from: [{ node: 0 }] },
    ],
  });
  const out = await f.run(g, ['<http://example.org/a> <http://example.org/p> <http://example.org/b> .\n'], { unchecked: true });
  assert.equal(typeof out.values[1], 'string');
  assert.equal(typeof out.values[2], 'string');
  assert.equal(out.graph, out.values[2]);
  assert.deepEqual(out.evidence.map((e) => e.node), [0, 1, 2]);
});

test('engine: each issue kind is refused before any node runs', async () => {
  const r = await f.node('nquadsDocumentReader');
  const m = await f.node('datasetMerge');
  const sel = await f.node('shippedEvaluator', { query: SELECT });
  const refused = (spec, kind) => assert.throws(() => f.graph(spec),
    (err) => err instanceof f.FactoidalError && err.code === 'op.failed' &&
      Array.isArray(err.issues) && err.issues.some((x) => x.kind === kind), kind);
  refused({ inputs: ['String'], nodes: [{ node: r, from: [{ input: 3 }] }] }, 'unknownInput');
  refused({ inputs: ['String', 'String'], nodes: [{ node: r, from: [{ input: 0 }] },
    { node: r, from: [{ input: 1 }] }, { node: m, from: [{ node: 0 }, { node: 2 }] }] }, 'forwardRef');
  refused({ inputs: ['String'], nodes: [{ node: r, from: [{ input: 0 }] }, { node: m, from: [{ node: 0 }] }] },
    'portCount');
  refused({ inputs: ['String', 'String'], nodes: [{ node: r, from: [{ input: 0 }] },
    { node: r, from: [{ input: 1 }] }, { node: m, from: [{ node: 0 }, { node: 1 }] },
    { node: sel, from: [{ node: 2 }] }, { node: m, from: [{ node: 0 }, { node: 3 }] }] }, 'wireMismatch');
});

test('engine: an unknown stage, and an unknown input wire, are refused', async () => {
  await assert.rejects(f.node('noSuchStage'), (err) => err instanceof f.FactoidalError);
  const r = await f.node('nquadsDocumentReader');
  assert.throws(() => f.graph({ inputs: ['Text'], nodes: [{ node: r, from: [{ input: 0 }] }] }),
    (err) => err instanceof f.FactoidalError && /'Text' is not a wire label/.test(err.message));
});
