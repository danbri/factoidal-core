// Draft queries from a grammar's steps (tools/wikidata-explain/src/grammar.mjs).
//
// Step k's draft is the query made of every fragment from steps 0..k, in the
// order the fragments have in the whole query. It runs as it stands, so a
// stepper can show how many items each step leaves. No DOM here: the page
// script and the tests share it.

/** Fragments of steps 0..k, deduplicated, in the whole query's order. */
export function fragmentsUpTo(steps, k) {
  const seen = new Map();
  steps.slice(0, k + 1).forEach((st, i) => st.sparql.forEach((f, j) => {
    if (!seen.has(f.s)) seen.set(f.s, { ...f, i, j });
  }));
  const key = (f) => (f.at < 0 ? Number.MAX_SAFE_INTEGER : f.at);
  return [...seen.values()].sort((a, b) => key(a) - key(b) || a.i - b.i || a.j - b.j).map(f => f.s);
}

// Variables a fragment makes visible to the rest of the query. Nothing from
// MINUS or FILTER (NOT) EXISTS; only the projection of a subquery.
function visibleVars(frag) {
  if (/^(MINUS|FILTER)\b/.test(frag)) return [];
  const sub = /^\{\s*SELECT\s+(?:DISTINCT\s+|REDUCED\s+)?(.*?)\s+WHERE\s*\{/s.exec(frag);
  const text = sub ? sub[1].replace(/\([^()]*(?:\([^()]*\)[^()]*)*\s+AS\s+(\?\w+)\)/g, '$1') : frag;
  return [...text.matchAll(/\?([A-Za-z_]\w*)/g)].map(m => m[1]).filter(v => !v.includes('__'));
}

const indent = (s) => s.split('\n').map(l => '  ' + l).join('\n');

/**
 * @param g      {steps, prefixes}
 * @param k      the last step to include
 * @param opts   {count: true} for a count of the items step k lands on;
 *               {limit, labels} otherwise
 */
export function draftQuery(g, k, opts = {}) {
  const frags = fragmentsUpTo(g.steps, k);
  const body = indent(frags.join('\n'));
  const on = g.steps[k]?.v;
  const vars = [...new Set(frags.flatMap(visibleVars))];
  const pre = g.prefixes ? g.prefixes + '\n' : '';
  // Earlier sets the rows still carry (alum, beside nationality): counted too, in the same request.
  const carried = (g.steps[k]?.carries || []).filter(v => v !== on && vars.includes(v)).slice(-3);
  if (opts.count) {
    const target = on && vars.includes(on) ? `(COUNT(DISTINCT ?${on}) AS ?items) ` : '';
    const also = carried.map(v => `(COUNT(DISTINCT ?${v}) AS ?n_${v}) `).join('');
    return `${pre}SELECT ${target}${also}(COUNT(*) AS ?rows) WHERE {\n${body}\n}`;
  }
  // The landing set as a bag: each item with the number of rows that reach it.
  if (opts.top && on && vars.includes(on)) {
    const has = vars.includes(`${on}Label`);
    const label = has ? '' : `\n  OPTIONAL { ?${on} rdfs:label ?${on}Label . FILTER(LANG(?${on}Label) = "en") }`;
    const rdfs = !has && !/PREFIX rdfs:/.test(pre) ? 'PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n' : '';
    return `${pre}${rdfs}SELECT ?${on} (SAMPLE(?${on}Label) AS ?label) (COUNT(*) AS ?rows)${carried.length ? ` (COUNT(DISTINCT ?${carried[carried.length - 1]}) AS ?${carried[carried.length - 1]}s)` : ''} WHERE {\n${body}${label}\n}\nGROUP BY ?${on}\nORDER BY DESC(?rows)\nLIMIT 20`;
  }
  const labelled = (opts.labels ?? true) ? g.steps.slice(0, k + 1).map(s => s.v).filter((v, i, a) => v && vars.includes(v) && !vars.includes(`${v}Label`) && a.indexOf(v) === i).slice(-3) : [];
  const labels = labelled.map(v => `  OPTIONAL { ?${v} rdfs:label ?${v}Label . FILTER(LANG(?${v}Label) = "en") }`);
  const cols = [...vars.slice(0, 12), ...labelled.map(v => `${v}Label`)].map(v => `?${v}`).join(' ') || '*';
  const rdfs = labels.length && !/PREFIX rdfs:/.test(pre) ? 'PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n' : '';
  return `${pre}${rdfs}SELECT DISTINCT ${cols} WHERE {\n${body}${labels.length ? '\n' + labels.join('\n') : ''}\n}\nLIMIT ${opts.limit ?? 50}`;
}
