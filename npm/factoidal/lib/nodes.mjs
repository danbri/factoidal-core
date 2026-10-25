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
// record `{ stage, status, contract, assumptions, artefact }`. The result of
// a run also reports the union of the named assumptions of the nodes it
// passed: the premise list of the pipeline's soundness statement
// (Dataflow/EndToEnd.lean) as the user sees it.
//
// ES module, no Node built-ins: the browser loads this file as it is.

import { FactoidalError } from './errors.mjs';

/**
 * @param {object} deps the package functions and the engine entry
 * @returns {{stages: Function, node: Function, pipe: Function, run: Function}}
 */
export function buildNodes(deps) {
  const { entry, entryResult, requireEntryFn, Dataset,
    parse, closure, shaclValidate, query, serialize, canonicalize, explain } = deps;

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
  const writer = (format) => async (wire, params) => ({
    artefact: { format, text: await serialize(wire.graph, { ...params, format }) },
  });

  // Stage name (stageList `name`) -> the package function that runs it.
  // A runner answers `{ graph?, artefact }`; no `graph` passes the input
  // graph on unchanged.
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
      return { artefact: { conforms: r.conforms, report: r.report } };
    },
    shippedEvaluator: async (wire, params) => {
      const { query: sparql, ...opts } = params;
      if (typeof sparql !== 'string') throw new TypeError('node shippedEvaluator: params.query must be a string');
      const answer = await query(wire.graph, sparql, opts);
      return answer instanceof Dataset ? { graph: answer, artefact: { form: 'graph' } }
        : { artefact: { answer } };
    },
    ntriplesDocumentWriter: writer('ntriples'),
    nquadsDocumentWriter: writer('nquads'),
    turtleDocumentWriter: writer('turtle'),
    trigDocumentWriter: writer('trig'),
    rdfxmlDocumentWriter: writer('rdfxml'),
    rdfcStage: async (wire, params) => ({
      artefact: { canonical: await canonicalize(wire.graph, params) },
    }),
    rdfsExplainGraphStage: async (wire, params) => {
      const { description, ...opts } = params;
      if (description === undefined) {
        throw new TypeError('node rdfsExplainGraphStage: params.description is required');
      }
      return { artefact: await explain(wire.graph, description, { ...opts, profile: 'rdfs' }) };
    },
  };

  let stageCache = null;

  /**
   * The engine's stage list (op stageList), one element per registry entry.
   * @returns {Promise<object[]>}
   */
  async function stages() {
    if (!stageCache) {
      stageCache = (async () => {
        const e = await entry();
        requireEntryFn(e, 'stageList', 'stages');
        const r = entryResult(e.stageList(), 'stages');
        return Object.freeze(r.stages.map((s) => Object.freeze({
          ...s,
          theorems: Object.freeze([...s.theorems]),
          assumptions: Object.freeze([...s.assumptions]),
          tests: Object.freeze([...s.tests]),
          bound: Object.prototype.hasOwnProperty.call(RUNNERS, s.name),
        })));
      })();
      stageCache.catch(() => { stageCache = null; });
    }
    return stageCache;
  }

  const NODE = Symbol('factoidal.node');

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
    return Object.freeze({
      [NODE]: true,
      stage: info.name,
      kind: info.kind,
      status: info.status,
      contract: info.contract,
      assumptions: info.assumptions,
      wireIn: info.wireIn,
      wireOut: info.wireOut,
      runnable: info.runnable,
      bound: info.bound,
      params: Object.freeze({ ...(params || {}) }),
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

  function unionAssumptions(records) {
    const seen = new Set();
    const out = [];
    for (const r of records) {
      for (const a of r.assumptions) {
        if (!seen.has(a)) { seen.add(a); out.push(a); }
      }
    }
    return out;
  }

  /**
   * A pipeline: the nodes in order (pipelines are flattened).
   * `assumptions` is the union of the nodes' named assumptions.
   * @returns {{nodes: object[], assumptions: string[]}}
   */
  function pipe(...items) {
    const nodes = nodesOf(items, 'pipe');
    if (nodes.length === 0) throw new TypeError('pipe: no nodes');
    return Object.freeze({ nodes: Object.freeze(nodes), assumptions: Object.freeze(unionAssumptions(nodes)) });
  }

  // Refuse before anything runs: a stage with status `missing` has no
  // contract and no suite (issue 975, item 3); a stage the package has no
  // function for cannot run here.
  function refusal(n) {
    if (!n.runnable) {
      return new FactoidalError(`run: stage '${n.stage}' has status ${n.status}: ` +
        'no contract and no test suite, so it does not run as a node', { code: 'op.failed' });
    }
    if (!n.bound) {
      return new FactoidalError(`run: stage '${n.stage}' has no package function that runs it`,
        { code: 'op.unknown' });
    }
    return null;
  }

  const isWire = (v) => v !== null && typeof v === 'object' && !(v instanceof Dataset) &&
    Object.prototype.hasOwnProperty.call(v, 'graph') && Array.isArray(v.evidence);

  /**
   * Run a node or a pipeline. `input` is a wire value `{graph, evidence}`
   * or the graph itself (text for a reader, else a Dataset or data input).
   * @returns {Promise<{graph: any, evidence: object[], assumptions: string[]}>}
   */
  async function run(pipeline, input) {
    const nodes = nodesOf([pipeline], 'run');
    for (const n of nodes) {
      const why = refusal(n);
      if (why) throw why;
    }
    let wire = isWire(input) ? { graph: input.graph, evidence: [...input.evidence] }
      : { graph: input, evidence: [] };
    let owned = null; // a Dataset an earlier node of this run made
    for (const n of nodes) {
      const out = await RUNNERS[n.stage](wire, n.params);
      const record = Object.freeze({
        stage: n.stage,
        status: n.status,
        contract: n.contract,
        assumptions: n.assumptions,
        artefact: out.artefact === undefined ? null : out.artefact,
      });
      let graph = wire.graph;
      if (out.graph !== undefined && out.graph !== wire.graph) {
        if (owned && owned === wire.graph && typeof owned.dispose === 'function') owned.dispose();
        graph = out.graph;
        owned = out.graph instanceof Dataset ? out.graph : null;
      }
      wire = { graph, evidence: [...wire.evidence, record] };
    }
    return { graph: wire.graph, evidence: wire.evidence, assumptions: unionAssumptions(wire.evidence) };
  }

  return { stages, node, pipe, run };
}
