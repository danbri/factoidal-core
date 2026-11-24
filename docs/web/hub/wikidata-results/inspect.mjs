// The published Hub can carry an older engine than this JavaScript.
export function inspectSparql(engine, query) {
  const { ops } = engine.call('ops', []);
  if (ops.includes('parseSparqlStructure')) {
    return engine.call('parseSparqlStructure', [query, 'true', '1.1']).result;
  }
  return { form: engine.call('queryForm', [query]).kind };
}
