// The node-composition API (https://github.com/danbri/factoidal/issues/1002,
// step 2): registered Lean stages as nodes, each carrying its contract name
// and its proof status, with evidence flowing on the wires.
//
// The stage list is the engine's (op stageList, formal/lean4/Wasm/Ops/
// StageList.lean), read from the Lean registry
// L4Factoidal.Dataflow.registry: name, interface type, wire types, status,
// contract, named assumptions, and whether the stage may run at all
// (`runnable`, false for status `missing`). This file holds no copy of it.
//
// What this file adds is the binding of a stage NAME to the package
// function that runs it (RUNNERS below; each is the function that
// foundation/entrypoints.toml maps to that stage), and the wiring: a value
// on a wire is `{ graph, evidence }`, and each node appends one evidence
// record `{ stage, status, contract, assumptions, checked, artefact }` (plus
// `unchecked` and `reason` for a step run under run()'s `unchecked` opt-in;
// the record logic is in evidence.mjs).
//
// The type check and the assumption union are the engine's (op
// pipelineCheck, formal/lean4/Wasm/Ops/StageList.lean, computed by
// pipelineReport of formal/lean4/L4Factoidal/Dataflow/Pipeline.lean): a
// pipeline is well typed when each stage's output wire is the next stage's
// input wire or converts to it, and its `assumptions` are the premises of
// Pipeline.guarantee_sound, the guarantee of any pipeline of components with
// these signatures. This file does not compute the union. With an engine
// built before the op, pipe() and run() fall back to the union of the
// nodes' fields and report `wellTyped: null`.
//
// Node settings (https://github.com/danbri/factoidal/issues/975,
// https://github.com/danbri/factoidal/issues/1026): the params of node()
// are the node's settings. When the engine has the op pipelineCheckNodes
// (formal/lean4/Wasm/Ops/PipelineNodes.lean), the engine decides, per node:
// the settings in canonical form with their SHA-256 digest, the role of each
// setting in the stage's contract, the settings outside the proved domain
// (a proved stage with one is `unproved`), and the output wire the settings
// select (SELECT gives a Table, ASK an Answer, CONSTRUCT and DESCRIBE a
// Dataset, so a CONSTRUCT node can feed the next node). This file only marshals: a Dataset setting is sent as
// {"$nquads": its N-Quads text}. With an older engine, records carry no
// settings and the evaluator's output wire is the registry's.
//
// ES module, no Node built-ins: the browser loads this file as it is.

import { FactoidalError } from './errors.mjs';
import { refusalFor, makeRecord, summarize, unionAssumptions, unionLists } from './evidence.mjs';

/**
 * @param {object} deps the package functions and the engine entry
 * @returns {{stages: Function, node: Function, pipe: Function, run: Function}}
 */
export function buildNodes(deps) {
  const { entry, entryResult, requireEntryFn, Dataset,
    parse, closure, shaclValidate, query, serialize, canonicalize, canonicalHash, explain, csvwToRdf } = deps;

  const reader = (format) => async (wire, params) => {
    if (typeof wire.graph !== 'string') {
      throw new TypeError(`node: a reader takes text on its wire (got ${typeof wire.graph})`);
    }
    const ds = await parse(wire.graph, { format, ...params });
    return { graph: ds, artefact: { format } };
  };
  const reasoner = (regime) => async (wire, params) => ({
    graph: await closure(wire.graph, regime, params),
    artefact: { regime },
  });
  // A writer's output wire is String: the text goes on the wire, so the next
  // node (a reader, say) reads it. Before 0.20.0 the input Dataset stayed on
  // the wire and only the artefact held the text.
  const writer = (format) => async (wire, params) => {
    const text = await serialize(wire.graph, { ...params, format });
    return { graph: text, artefact: { format, text } };
  };

  // Stage name (stageList `name`) -> the package function that runs it.
  // A runner answers `{ graph, artefact }`: `graph` is the value of the
  // node's output wire (FactoidalNode.wireOut, the engine's), which run()
  // checks (wireHolds); `artefact` goes in the evidence record.
  const RUNNERS = {
    ntriplesDocumentReader: reader('ntriples'),
    nquadsDocumentReader: reader('nquads'),
    turtleDocumentReader: reader('turtle'),
    trigDocumentReader: reader('trig'),
    rdfxmlDocumentReader: reader('rdfxml'),
    jsonldDocumentReader: reader('jsonld'),
    rdfsReasoner: reasoner('rdfs'),
    owlRlReasoner: reasoner('owl-rl'),
    rhoDfReasoner: reasoner('rho-df'),
    shaclValidator: async (wire, params) => {
      const { shapes, ...opts } = params;
      if (shapes === undefined) throw new TypeError('node shaclValidator: params.shapes is required');
      const r = await shaclValidate(wire.graph, shapes, opts);
      const report = { conforms: r.conforms, report: r.report };
      return { graph: report, artefact: report };
    },
    // SELECT gives a Table (the rows), ASK an Answer (a boolean), CONSTRUCT
    // and DESCRIBE a Dataset: the engine picks the wire from the query form
    // (op pipelineCheckNodes), and the value here follows it.
    shippedEvaluator: async (wire, params) => {
      const { query: sparql, ...opts } = params;
      if (typeof sparql !== 'string') throw new TypeError('node shippedEvaluator: params.query must be a string');
      const answer = await query(wire.graph, sparql, opts);
      return answer instanceof Dataset ? { graph: answer, artefact: { form: 'graph' } }
        : { graph: answer, artefact: { answer } };
    },
    ntriplesDocumentWriter: writer('ntriples'),
    nquadsDocumentWriter: writer('nquads'),
    turtleDocumentWriter: writer('turtle'),
    trigDocumentWriter: writer('trig'),
    rdfxmlDocumentWriter: writer('rdfxml'),
    // String × String: the canonical N-Quads text and its SHA-256 hex
    // (RdfcContract, Dataflow/PhaseE.lean). canonicalHash is the SHA-256 of
    // the text canonicalize answers (op datasetCanonicalHash).
    rdfcStage: async (wire, params) => {
      if (!(wire.graph instanceof Dataset)) {
        throw new TypeError(`node rdfcStage: the stage takes a Dataset on its wire (got ${describe(wire.graph)})`);
      }
      const canonical = await canonicalize(wire.graph, params);
      const sha256 = await canonicalHash(wire.graph);
      return { graph: [canonical, sha256], artefact: { canonical, sha256 } };
    },
    'CSVW (tabular data to RDF)': async (wire, params) => {
      if (typeof wire.graph !== 'string') {
        throw new TypeError(`node CSVW: the stage takes CSV text on its wire (got ${typeof wire.graph})`);
      }
      const { metadata, ...opts } = params;
      const meta = metadata === undefined || typeof metadata === 'string' ? metadata : JSON.stringify(metadata);
      return { graph: await csvwToRdf(wire.graph, meta, opts), artefact: { tabular: 'csv' } };
    },
    rdfsExplainGraphStage: async (wire, params) => {
      const { description, ...opts } = params;
      if (description === undefined) {
        throw new TypeError('node rdfsExplainGraphStage: params.description is required');
      }
      const result = await explain(wire.graph, description, { ...opts, profile: 'rdfs' });
      return { graph: result, artefact: result };
    },
  };

  // Whether `value` represents the wire type `wire` (a wire name of the
  // engine's registry, Dataflow/Wire.lean) in this package: a Dataset for the
  // graph wires, text for String, and so on. A wire this table does not name
  // needs a value that is not null or undefined.
  function wireHolds(wire, value) {
    switch (wire) {
      case 'String': return typeof value === 'string';
      case 'Dataset': case 'Graph': case 'Dataset × PrefixList': return value instanceof Dataset;
      case 'Answer': return typeof value === 'boolean';
      case 'Table': return Array.isArray(value);
      case 'String × String':
        return Array.isArray(value) && value.length === 2 && value.every((v) => typeof v === 'string');
      default: return value !== undefined && value !== null;
    }
  }

  const describe = (v) => (v instanceof Dataset ? 'a Dataset' : Array.isArray(v) ? 'an array'
    : v === null ? 'null' : typeof v);

  let stageCache = null;
  let engine = null; // the entry stages() loaded; node() calls stages(), so pipe() has it

  /**
   * The engine's stage list (op stageList), one element per registry entry.
   * @returns {Promise<object[]>}
   */
  async function stages() {
    if (!stageCache) {
      stageCache = (async () => {
        const e = await entry();
        requireEntryFn(e, 'stageList', 'stages');
        engine = e;
        const r = entryResult(e.stageList(), 'stages');
        return Object.freeze(r.stages.map((s) => Object.freeze({
          ...s,
          theorems: Object.freeze([...s.theorems]),
          assumptions: Object.freeze([...s.assumptions]),
          tests: Object.freeze([...s.tests]),
          // bound: the package has a runner AND the engine lets the stage
          // run. A runner for a stage that an older engine reports as
          // `missing` is not bound (the engine's registry decides).
          bound: s.runnable && Object.prototype.hasOwnProperty.call(RUNNERS, s.name),
        })));
      })();
      stageCache.catch(() => { stageCache = null; });
    }
    return stageCache;
  }

  const NODE = Symbol('factoidal.node');

  // The settings as the engine reads them: JSON values, a Dataset as
  // {"$nquads": text}. Anything else is refused.
  function marshal(v, path) {
    if (v === null || typeof v === 'string' || typeof v === 'boolean') return v;
    if (typeof v === 'number') {
      if (!Number.isFinite(v)) throw new TypeError(`node: setting ${path} is not a finite number`);
      return v;
    }
    if (v instanceof Dataset) return { $nquads: v.toNQuads() };
    if (Array.isArray(v)) return v.map((x, i) => marshal(x, `${path}[${i}]`));
    if (typeof v === 'object' && Object.getPrototypeOf(v) === Object.prototype) {
      const out = {};
      for (const [k, x] of Object.entries(v)) if (x !== undefined) out[k] = marshal(x, `${path}.${k}`);
      return out;
    }
    throw new TypeError(`node: setting ${path} must be a JSON value or a Dataset (got ${typeof v})`);
  }

  // The node's own copy of its settings, taken when node() checks them: plain
  // objects and arrays copied and frozen at every depth, a Dataset cloned. A
  // later change to the caller's objects does not reach the node, so the
  // settings that run are the ones the engine checked and digested.
  function snapshot(v) {
    if (v instanceof Dataset) return typeof v.clone === 'function' ? v.clone() : v;
    if (Array.isArray(v)) return Object.freeze(v.map(snapshot));
    if (v !== null && typeof v === 'object') {
      const out = {};
      for (const [k, x] of Object.entries(v)) if (x !== undefined) out[k] = snapshot(x);
      return Object.freeze(out);
    }
    return v;
  }

  // A node's settings must still be the ones it was checked with: a Dataset
  // in them (the clone node() made) can still be changed through
  // node.params. run() refuses such a node instead of running settings that
  // its evidence record would misdescribe.
  function assertSettingsUnchanged(n) {
    const now = JSON.stringify(marshal(n.params, 'params'));
    if (now !== JSON.stringify(n.settingsWire)) {
      throw new FactoidalError(`run: the settings of node ${n.stage} changed after node() checked them ` +
        '(make a new node with node() for new settings)', { code: 'op.failed' });
    }
  }

  const hasNodeCheck = () => !!engine && typeof engine.pipelineCheckNodes === 'function';

  // The engine's check of nodes with settings (op pipelineCheckNodes).
  function nodeCheck(items) {
    return entryResult(engine.pipelineCheckNodes(JSON.stringify(
      items.map((n) => ({ stage: n.stage, settings: n.settingsWire })))), 'pipelineCheckNodes');
  }

  /**
   * A node for the registered stage `name`, with its parameters (the
   * second argument of the package function it calls, e.g. `{shapes}`,
   * `{query}`, `{description}`, reader options).
   * @param {string} name a stageList `name`
   * @param {object} [params]
   * @returns {Promise<object>}
   */
  async function node(name, params) {
    if (typeof name !== 'string') throw new TypeError('node: name must be a string');
    if (params !== undefined && (params === null || typeof params !== 'object')) {
      throw new TypeError('node: params must be an object');
    }
    const info = (await stages()).find((s) => s.name === name);
    if (!info) {
      throw new FactoidalError(`node: no registered stage named '${name}' (see stages())`,
        { code: 'option.invalid-value' });
    }
    // The copy first, then its wire form: the engine checks and digests
    // exactly the settings the node keeps.
    const own = snapshot({ ...(params || {}) });
    const settingsWire = snapshot(marshal(own, 'params'));
    // The engine's reading of the settings, when it has the op.
    let s = null;
    if (hasNodeCheck()) s = nodeCheck([{ stage: info.name, settingsWire }]).stages[0];
    return Object.freeze({
      [NODE]: true,
      stage: info.name,
      kind: info.kind,
      status: s ? s.status : info.status,
      registryStatus: info.status,
      contract: info.contract,
      assumptions: info.assumptions,
      wireIn: info.wireIn,
      wireOut: s ? s.wireOut : info.wireOut,
      runnable: info.runnable,
      bound: info.bound,
      params: own,
      settingsWire,
      settings: s ? s.settings : null,
      settingsDigest: s ? s.settingsDigest : null,
      outside: Object.freeze(s ? s.outside.map((o) => Object.freeze({ ...o })) : []),
      derived: s ? Object.freeze({ ...s.derived }) : null,
    });
  }

  function nodesOf(items, who) {
    const out = [];
    for (const n of items) {
      if (n && n[NODE]) out.push(n);
      else if (n && Array.isArray(n.nodes)) out.push(...nodesOf(n.nodes, who));
      else throw new TypeError(`${who}: expected nodes from node() or pipelines from pipe()`);
    }
    return out;
  }

  /**
   * The engine's check of the stages of `nodes` in order (op pipelineCheck),
   * or null when the loaded engine has no such op.
   */
  function check(nodes) {
    let r;
    if (hasNodeCheck()) r = nodeCheck(nodes);
    else if (engine && typeof engine.pipelineCheck === 'function') {
      r = entryResult(engine.pipelineCheck(JSON.stringify(nodes.map((n) => n.stage))), 'pipelineCheck');
    } else return null;
    return Object.freeze({
      wellTyped: r.wellTyped,
      wireIn: r.wireIn,
      wireOut: r.wireOut,
      mismatch: r.mismatch === null ? null : Object.freeze({ ...r.mismatch }),
      conversions: Object.freeze(r.conversions.map((c) => Object.freeze({ ...c }))),
      assumptions: Object.freeze([...r.assumptions]),
      contract: Object.freeze({ theorem: r.contract.theorem, stages: Object.freeze([...r.contract.stages]) }),
      stages: Object.freeze(r.stages.map((s) => Object.freeze({
        ...s,
        assumptions: Object.freeze([...s.assumptions]),
        ...(s.outside ? { outside: Object.freeze(s.outside.map((o) => Object.freeze({ ...o }))) } : {}),
      }))),
    });
  }

  /**
   * A pipeline: the nodes in order (pipelines are flattened). `check` is
   * the engine's op pipelineCheck on the nodes' stages; `wellTyped` and
   * `assumptions` (the union of the nodes' named assumptions) are its
   * fields. Without the op: `check` and `wellTyped` are null and
   * `assumptions` is the union of the nodes' fields.
   * @returns {{nodes: object[], assumptions: string[], wellTyped: boolean|null, check: object|null}}
   */
  function pipe(...items) {
    const nodes = nodesOf(items, 'pipe');
    if (nodes.length === 0) throw new TypeError('pipe: no nodes');
    const c = check(nodes);
    return Object.freeze({
      nodes: Object.freeze(nodes),
      assumptions: c ? c.assumptions : Object.freeze(unionAssumptions(nodes)),
      wellTyped: c ? c.wellTyped : null,
      check: c,
    });
  }

  const isWire = (v) => v !== null && typeof v === 'object' && !(v instanceof Dataset) &&
    Object.prototype.hasOwnProperty.call(v, 'graph') && Array.isArray(v.evidence);

  /**
   * Run a node or a pipeline. `input` is a wire value `{graph, evidence}`
   * or the graph itself (text for a reader, else a Dataset or data input).
   * `options.unchecked: true` lets stages that are not `proved` run,
   * `missing` ones too when the package has a runner for them; each such
   * step's record says so (evidence.mjs). Without it, a `missing` stage
   * refuses before any node runs, and so does a pipeline that the engine's
   * check finds not well typed (op pipelineCheck); with it such a pipeline
   * runs and `proved` is false.
   * `assumptions`: the assumptions of the records on the input wire, then
   * the engine's union for this pipeline (op pipelineCheck), no duplicate.
   * @returns {Promise<{graph: any, evidence: object[], assumptions: string[],
   *   proved: boolean, uncheckedSteps: string[], wellTyped: boolean|null}>}
   */
  async function run(pipeline, input, options) {
    if (options !== undefined && (options === null || typeof options !== 'object')) {
      throw new TypeError('run: options must be an object');
    }
    const unchecked = !!(options && options.unchecked);
    const nodes = nodesOf([pipeline], 'run');
    for (const n of nodes) {
      const why = refusalFor(n, unchecked, Object.prototype.hasOwnProperty.call(RUNNERS, n.stage));
      if (why) throw why;
      assertSettingsUnchanged(n);
    }
    const c = check(nodes);
    if (c && !c.wellTyped && !unchecked) {
      const m = c.mismatch;
      throw new FactoidalError(`run: the pipeline is not well typed: stage ${m.at} ` +
        `(${nodes[m.at].stage}) writes ${m.out}, stage ${m.at + 1} (${nodes[m.at + 1].stage}) ` +
        `reads ${m.in} (pass { unchecked: true } to run it without a guarantee)`, { code: 'op.failed' });
    }
    const prior = isWire(input) ? input.evidence : [];
    let wire = isWire(input) ? { graph: input.graph, evidence: [...input.evidence] }
      : { graph: input, evidence: [] };
    let owned = null; // a Dataset an earlier node of this run made
    for (const n of nodes) {
      const out = await RUNNERS[n.stage](wire, n.params);
      // The value on the output wire must be one of the node's wireOut, the
      // wire the engine's check typed: a well-typed pipeline then cannot fail
      // between nodes for want of the value the next node reads. The output
      // wires per setting are the engine's when it has op pipelineCheckNodes;
      // with an older engine the registry wire is generic, so not checked.
      const value = out.graph === undefined ? wire.graph : out.graph;
      if (hasNodeCheck() && !wireHolds(n.wireOut, value)) {
        throw new FactoidalError(`run: node ${n.stage} declares the output wire ${n.wireOut} ` +
          `but its runner gave ${describe(value)}`, { code: 'op.failed' });
      }
      const record = makeRecord(n, out.artefact, unchecked);
      let graph = wire.graph;
      if (out.graph !== undefined && out.graph !== wire.graph) {
        if (owned && owned === wire.graph && typeof owned.dispose === 'function') owned.dispose();
        graph = out.graph;
        owned = out.graph instanceof Dataset ? out.graph : null;
      }
      wire = { graph, evidence: [...wire.evidence, record] };
    }
    const s = summarize(wire.evidence);
    if (!c) return { graph: wire.graph, evidence: wire.evidence, ...s, wellTyped: null };
    return {
      graph: wire.graph,
      evidence: wire.evidence,
      assumptions: prior.length === 0 ? [...c.assumptions]
        : unionLists([unionAssumptions(prior), c.assumptions]),
      proved: s.proved && c.wellTyped,
      uncheckedSteps: s.uncheckedSteps,
      wellTyped: c.wellTyped,
    };
  }

  return { stages, node, pipe, run };
}
