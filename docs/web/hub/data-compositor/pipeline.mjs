import { DEFAULTS } from './fixtures.mjs';
export { DEFAULTS };

const GRAPH = Object.freeze({ turtle: 'urn:studio:turtle', csv: 'urn:studio:csv', derived: 'urn:studio:derived' });
const json = value => JSON.stringify(value, null, 2);
const rowsOf = bindings => bindings.map(row => Object.fromEntries([...row].map(([key, term]) => [key, term.value])));
const adapterEvidence = (operation, note) => ({ source: 'public API adapter', operation, status: 'unproved-adapter', checked: false, proved: false, assumptions: [], note });

// Lean owns XML selection and JSON serialization. URI encoding keeps the
// public Serialized XDM string wire unambiguous (adaptive strings double quotes).
const XML_ROWS = `declare namespace s="http://www.w3.org/2005/sparql-results#";
encode-for-uri(serialize(array {
  for $r in /s:sparql/s:results/s:result
  return map:merge(for $b in $r/s:binding
    return map:entry(string($b/@name), string($b/*)))
}, map { "method": "json" }))`;
const decodeRows = result => {
  const item = result.items?.[0];
  if (result.count !== 1 || item?.type !== 'xs:string' ||
      !item.value.startsWith('"') || !item.value.endsWith('"') || item.value.slice(1, -1).includes('"'))
    throw new Error('Unexpected Lean XML-to-JSON transport result.');
  const rows = JSON.parse(decodeURIComponent(item.value.slice(1, -1)));
  if (!Array.isArray(rows) || rows.some(row => !row || typeof row !== 'object' || Array.isArray(row) ||
      Object.values(row).some(value => typeof value !== 'string')))
    throw new Error('Unexpected Lean result-row schema.');
  return rows;
};

/** Engine-backed pipeline; only strings, rows and plain evidence leave this function.
 * Query/filter use the explicit {{MIN_SCORE}} template socket; RDF inference,
 * numeric comparison, SPARQL result XML and XSLT execute in the published engine.
 */
export async function runPipeline(core, inputs = {}, onStage = () => {}) {
  const config = { ...DEFAULTS, ...inputs };
  const stages = [], owned = new Set();
  const keep = dataset => (owned.add(dataset), dataset);
  let inferredPeople = [], actualGraphNames = [];
  const stage = async (id, label, kind, work) => {
    const started = performance.now();
    onStage({ id, label, kind, status: 'running', summary: `Running ${label}` });
    try {
      const { value, ...details } = await work();
      const record = { id, label, kind, ...details, durationMs: performance.now() - started };
      stages.push(record);
      onStage({ ...record, status: 'done' });
      return value;
    } catch (error) {
      onStage({ id, label, kind, status: 'error', summary: error.message, error: error.message, durationMs: performance.now() - started });
      error.stageId = id;
      throw error;
    }
  };
  const runNode = async (name, params, input) => {
    const node = await core.node(name, params);
    const result = await core.run(node, input, { unchecked: node.status !== 'proved' });
    if (result.graph && typeof result.graph.dispose === 'function') keep(result.graph);
    const record = result.evidence.at(-1);
    return { value: result.graph, evidence: {
      source: 'core.node/run', stage: name, status: record.status, registryStatus: node.registryStatus,
      checked: record.checked, proved: result.proved, contract: record.contract,
      assumptions: result.assumptions, wellTyped: result.wellTyped,
      unchecked: !!record.unchecked, settingsDigest: node.settingsDigest,
      wireIn: node.wireIn, wireOut: node.wireOut, ports: node.ports,
      note: 'Registry/component evidence; not an end-to-end proof of this demo or its adapters.',
    } };
  };
  const textOf = dataset => dataset.serialize({ format: 'nquads' });
  const named = async (dataset, iri) => keep(await core.fromQuads([...dataset].map(q =>
    core.dataFactory.quad(q.subject, q.predicate, q.object, core.dataFactory.namedNode(iri)))));
  const bindScore = value => {
    if (typeof config.query !== 'string' || !config.query.includes('{{MIN_SCORE}}'))
      throw new TypeError('The query template must contain the {{MIN_SCORE}} socket.');
    return config.query.replaceAll('{{MIN_SCORE}}', String(value));
  };
  try {
    const turtle = await stage('turtle', 'Turtle / studio ontology', 'registered node', async () => {
      const r = await runNode('turtleDocumentReader', {}, config.turtle);
      return { ...r, input: config.turtle, text: await textOf(r.value), count: r.value.size,
        summary: `${r.value.size} source triples; names, projects and RDFS schema` };
    });
    const csv = await stage('csvw', 'CSV + CSVW metadata', 'registered node', async () => {
      const r = await runNode('CSVW (tabular data to RDF)', { metadata: config.metadata, mode: 'minimal' }, config.csv);
      return { ...r, input: json({ csv: config.csv, metadata: config.metadata }), text: await textOf(r.value), count: r.value.size,
        summary: `${r.value.size} mapped triples; schema-directed scores and project/team links`,
        note: 'CSVW conversion is not a strict validation report. The published engine may retain an invalid numeric cell as a plain literal; SPARQL numeric filtering then excludes it.' };
    });
    const merged = await stage('merge', 'Merge source graphs', 'registered graph node + adapter', async () => {
      const left = await named(turtle, GRAPH.turtle), right = await named(csv, GRAPH.csv);
      const node = await core.node('datasetMerge');
      const graph = core.graph({ inputs: ['Dataset', 'Dataset'], nodes: [{ node, from: [{ input: 0 }, { input: 1 }] }] });
      const r = await core.run(graph, [left, right]);
      const value = keep(r.graph), e = r.evidence.at(-1);
      return { value, input: json({ turtle: await textOf(left), csv: await textOf(right) }), text: await value.serialize({ format: 'trig' }), count: value.size,
        summary: `${value.size} quads in two source graphs; engine RDF merge scopes blank nodes`,
        evidence: { source: 'core.graph/run', stage: 'datasetMerge', status: e.status, checked: e.checked, proved: r.proved,
          contract: e.contract, assumptions: r.assumptions, wellTyped: r.wellTyped, wireOut: node.wireOut, ports: node.ports,
          graphCheck: { wellTyped: r.wellTyped, contract: graph.check.contract, assumptions: graph.check.assumptions, wireOut: graph.check.wireOut, issues: graph.check.issues },
          prepAdapter: adapterEvidence('fromQuads', 'Tag each source with its graph IRI; this graph assignment is not a proved adapter.') } };
    });
    let delta;
    const closed = await stage('closure', 'RDFS closure', 'registered node + selection adapter', async () => {
      const flat = keep(core.asDefaultGraph(merged));
      const r = await runNode('rdfsReasoner', {}, flat);
      delta = keep(await core.fromQuads([...r.value].filter(q => !flat.has(q))));
      return { ...r, input: await textOf(flat), text: await textOf(r.value), count: r.value.size,
        addedCount: delta.size, summary: `${delta.size} added triples, including RDFS axioms; Person follows Contributor`,
        adapter: adapterEvidence('asDefaultGraph / Dataset.has / fromQuads', 'Reason over the source-graph union; delta is closure minus this exact union. No new merge or JavaScript inference.') };
    });
    const dataset = await stage('graphs', 'Source + derived named graphs', 'public API adapter', async () => {
      const derived = await named(delta, GRAPH.derived);
      const value = keep(await core.fromQuads([...merged, ...derived]));
      actualGraphNames = core.graphs(value).map(([name, graph]) => {
        keep(graph);
        return name.value;
      });
      const memberships = await runNode('shippedEvaluator', { query: `SELECT ?person WHERE { GRAPH <${GRAPH.derived}> { ?person a <http://xmlns.com/foaf/0.1/Person> } } ORDER BY ?person` }, value);
      inferredPeople = rowsOf(memberships.value).map(row => row.person);
      return { value, input: json({ sources: await textOf(merged), added: await textOf(derived) }), text: await value.serialize({ format: 'trig' }), count: value.size,
        graphNames: actualGraphNames, designatedGraphNames: Object.values(GRAPH), inferredPeople, summary: `${actualGraphNames.length} nonempty provenance graphs; ${inferredPeople.length} inferred Person memberships`,
        evidence: adapterEvidence('fromQuads', 'Retag the delta, preserving RDF terms; source graph identity and this partition adapter are not proved.'), membershipEvidence: memberships.evidence };
    });
    await stage('query', 'SPARQL / join studio roster', 'registered node', async () => {
      const query = bindScore(0), r = await runNode('shippedEvaluator', { query }, dataset), rows = rowsOf(r.value);
      return { value: rows, input: query, text: json(rows), rows, count: rows.length, evidence: r.evidence,
        summary: `${rows.length} artists joined across the three named graphs; score socket = 0` };
    });
    let selectedQuery, filteredXML;
    const rows = await stage('filter', 'SPARQL / score filter', 'public query adapter + registered XQuery node', async () => {
      const minimum = Number(config.minScore);
      if (String(config.minScore).trim() === '' || !Number.isFinite(minimum) || minimum < 0 || minimum > 100) throw new TypeError('Minimum score must be a number from 0 to 100.');
      selectedQuery = bindScore(minimum);
      const trig = await dataset.serialize({ format: 'trig' });
      filteredXML = await core.queryRaw(trig, selectedQuery, { dataFormat: 'trig', output: 'xml', entail: 'none' });
      const projection = await runNode('xqueryEval', { query: XML_ROWS }, filteredXML);
      const rows = decodeRows(projection.value);
      return { value: rows, input: selectedQuery, text: json(rows), rows, count: rows.length,
        evidence: { ...adapterEvidence('queryRaw output:xml', 'One filtered SPARQL execution produces the shared XML. Registered Lean XQuery projects these display rows from that exact XML; JavaScript only decodes the JSON transport.'), projection: projection.evidence },
        summary: `${rows.length} eligible contributors with score ≥ ${minimum}; comparison runs in SPARQL`,
        adapter: adapterEvidence('numeric query socket', 'Finite numeric value substituted into an explicit template socket; rows are not filtered in JavaScript.') };
    });
    const xml = await stage('xml', 'SPARQL Results XML', 'public API adapter', async () => {
      return { value: filteredXML, input: 'Exact XML produced by the filter stage', text: filteredXML, count: rows.length,
        summary: 'Shared Lean SPARQL Results XML; no second filtered query execution',
        evidence: adapterEvidence('shared XML transport', 'The table projection and XSLT consume this identical XML string. No SPARQL re-execution or JavaScript XML generation.') };
    });
    const transformed = await stage('xslt', 'XSLT / compose the output', 'registered node', async () => {
      const r = await runNode('xslt4Transform', { stylesheet: config.stylesheet }, xml);
      if (r.value.method !== 'html') throw new Error(`Expected XSLT HTML output; got ${r.value.method}.`);
      return { ...r, input: json({ xml, stylesheet: config.stylesheet }), text: r.value.output,
        summary: `Engine XSLT output method: ${r.value.method}; ${r.value.messages.length} messages` };
    });
    const html = await stage('html', 'HTML / final frame', 'presentation transport', async () => ({
      value: transformed.output, text: transformed.output, count: rows.length,
      summary: `${rows.length} artist cards/rows ready for the browser preview`,
      evidence: adapterEvidence('HTML preview', 'Displays engine-generated HTML; no proof of browser rendering, styling or end-to-end semantics.') }));
    return { html, rows, stages, inferredPeople, graphNames: actualGraphNames, designatedGraphNames: Object.values(GRAPH),
      counts: { turtle: turtle.size, csvw: csv.size, merged: merged.size, closure: closed.size, derived: delta.size, selected: rows.length },
      coreVersion: core.version, proved: false,
      note: 'Component registry evidence is shown per stage. CSVW/XSLT are tested; adapters and the complete compositor are not proved.' };
  } finally {
    for (const dataset of owned) if (!dataset.disposed) dataset.dispose();
  }
}
