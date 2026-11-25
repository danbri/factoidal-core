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

const ns = {
  wikibase: 'PREFIX wikibase: <http://wikiba.se/ontology#>',
  rdfs: 'PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>',
  wdt: 'PREFIX wdt: <http://www.wikidata.org/prop/direct/>',
};
const withPrefixes = (pre, names) => pre + names.filter(p => !new RegExp(`PREFIX\\s+${p}:`).test(pre)).map(p => ns[p] + '\n').join('');

/** The set step k lands on, if the draft up to k can name it. */
export function landing(g, k) {
  const v = g.steps[k]?.v;
  if (!v) return null;
  const frags = fragmentsUpTo(g.steps, k);
  return frags.length && frags.flatMap(visibleVars).includes(v) ? v : null;
}

/**
 * Other ways on from the set step k lands on: every item-valued property its
 * items have ("their …", out) or are the value of ("things with them as …", in),
 * with how many of the items it reaches. Worked out on a sample of the set, so
 * a big set costs no more than a small one.
 */
export function waysQuery(g, k, { sample = 2000, limit = 60 } = {}) {
  const v = landing(g, k);
  if (!v) return null;
  const body = fragmentsUpTo(g.steps, k).join("\n").split("\n").map(l => " ".repeat(10) + l).join("\n");
  const pre = withPrefixes(g.prefixes ? g.prefixes + '\n' : '', ['wikibase', 'rdfs']);
  // QLever works out each UNION branch on its own, so each branch gets the sample.
  const sampled = `{\n        SELECT DISTINCT ?${v} WHERE {\n${body}\n        }\n        LIMIT ${sample}\n      }`;
  return `${pre}SELECT ?dir ?p (SAMPLE(?pLabel) AS ?label) ?items WHERE {
  {
    SELECT ?dir ?p (COUNT(DISTINCT ?${v}) AS ?items) WHERE {
      {
      ${sampled}
      ?${v} ?p ?o_ .
      BIND("out" AS ?dir)
      } UNION {
      ${sampled}
      ?s_ ?p ?${v} .
      BIND("in" AS ?dir)
      }
      ?prop_ wikibase:directClaim ?p ;
             wikibase:propertyType wikibase:WikibaseItem .
    }
    GROUP BY ?dir ?p
  }
  ?prop_ wikibase:directClaim ?p .
  OPTIONAL { ?prop_ rdfs:label ?pLabel . FILTER(LANG(?pLabel) = "en") }
}
GROUP BY ?dir ?p ?items
ORDER BY DESC(?items)
LIMIT ${limit}`;
}

/**
 * Take one of those ways: the draft up to step k, one more pivot along
 * `p` (a wdt: property; `inv` for "things with them as p"), and the set it
 * reaches as a bag: each item with how many of step k's items lead to it.
 */
export function wayQuery(g, k, { p, inv }, { limit = 20 } = {}) {
  const v = landing(g, k);
  if (!v) return null;
  const frags = fragmentsUpTo(g.steps, k);
  const taken = new Set(frags.flatMap(visibleVars));
  let to = 'next';
  for (let i = 2; taken.has(to) || to === v; i++) to = `next${i}`;
  const edge = inv ? `?${to} ${p} ?${v} .` : `?${v} ${p} ?${to} .`;
  const pre = withPrefixes(g.prefixes ? g.prefixes + '\n' : '', ['wdt', 'rdfs']);
  return `${pre}SELECT ?${to} (SAMPLE(?${to}Label) AS ?label) (COUNT(DISTINCT ?${v}) AS ?${v}s) WHERE {
${indent(frags.join('\n'))}
  ${edge}
  OPTIONAL { ?${to} rdfs:label ?${to}Label . FILTER(LANG(?${to}Label) = "en") }
}
GROUP BY ?${to}
ORDER BY DESC(?${v}s)
LIMIT ${limit}`;
}
