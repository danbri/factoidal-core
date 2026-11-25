// Negation as a Parallax-style facet state.
//
// Parallax narrows a set by facet values ("has P = X"). A usable negation
// is the same facet with an exclusion state, shown as a chip on one node of
// the browsing path:
//
//   exclude: has any <P>                        ?x P []            (or a fresh variable)
//   exclude: <P> includes <X>                   ?x P X
//   exclude: has a <P> whose <P2> includes <X>  ?x P/P2 X, or ?x P ?y . ?y P2 X
//   exclude: has a label in "fr"                ?x rdfs:label ?l FILTER(lang(?l) = "fr")
//   exclude: has a sitelink to en.wikipedia.org ?a schema:about ?x . ?a schema:isPartOf <…>
//   exclude: material includes something other than gold   ?x P ?m FILTER(?m != X)   ("only gold")
//   exclude: has a sitelink whose URL contains "wikipedia"   (text match on the end value; tier B)
//
// The labels say what is removed, in terms of the positive facet the user
// already sees. "<P> is not X" is avoided on purpose: for a multi-valued
// property it reads as "some P other than X", but the query removes every item
// that has X among its values.
//
// Accepted only when the negation can be one chip:
//   - exactly one variable shared with the rest of the query (the anchor), and
//     the anchor is always bound there (MINUS and NOT EXISTS disagree
//     otherwise, and a user can't predict either);
//   - the negated pattern is a single chain from the anchor of at most two
//     hops, with fixed properties, ending in a constant, "anything", or a
//     value with one test: language, "other than X", or a text match;
//   - no nested negation, union, subquery or other filter inside.
// Anything else (a negated combination "not (A and B)", a negation tied to a
// second column, a deep chain) returns a blocker that names the reason.
import { flatten } from './explain.mjs';
import { compact } from './names.mjs';
import { exprVars } from './scope.mjs';

const P31 = 'http://www.wikidata.org/prop/direct/P31';
const P279 = 'http://www.wikidata.org/prop/direct/P279';
const STATEMENT_PREFIXES = ['p', 'ps', 'pq', 'psv', 'pqv', 'pr'];
const MAX_HOPS = 2;

const isStatementIri = (iri) => STATEMENT_PREFIXES.includes(compact(iri)?.prefix) || iri === 'http://www.w3.org/ns/prov#wasDerivedFrom';

/** Steps of a property path as [{iri, inverse, closure}] or null if not a usable chain. */
function pathSteps(p, inverse = false) {
  if (p.path === 'iri') return [{ iri: p.iri, inverse }];
  if (p.path === 'inverse') { const s = pathSteps(p.p, !inverse); return s && s.reverse(); }
  if (p.path === 'sequence') {
    const a = pathSteps(p.a, inverse), b = pathSteps(p.b, inverse);
    return a && b && (inverse ? [...b, ...a] : [...a, ...b]);
  }
  // Subclass closure (P279* / P279+ / P279?): type selection, one hop.
  if (['zeroOrMore', 'oneOrMore', 'zeroOrOne'].includes(p.path) && p.p.path === 'iri' && p.p.iri === P279)
    return [{ iri: P279, inverse, closure: p.path }];
  return null;
}

/**
 * @param {object} inner   negated group pattern
 * @param {{may:Set,must:Set}} outer  scope of the rest of the query
 * @param {'minus'|'notExists'|'exists'} op
 * @param {(iri:string)=>string} [nm]  readable name for an IRI
 * @returns {{ok:true, anchor, label, needs:string[]} | {ok:false, blocker:string}}
 */
export function negationFacet(inner, outer, op, nm = (i) => compact(i) ? `${compact(i).prefix}:${compact(i).local}` : i) {
  const elems = flatten(inner);
  const edges = []; // {a, b, iri, closure} oriented from a to b as written
  const filters = [];
  const key = (t) => t.t === 'var' ? `?${t.name}` : t.t === 'bnode' ? `_${t.id}` : null;
  const constName = (t) => t.t === 'iri' ? nm(t.iri) : t.t === 'lit' ? JSON.stringify(t.lex) : '?';
  let leaf = 0;
  const node = (t) => key(t) ?? { c: t, id: `#${leaf++}` };
  for (const x of elems) {
    if (x.kind === 'triple') {
      if (x.triple.p.t !== 'iri') return { ok: false, blocker: 'negation over any property (variable predicate)' };
      edges.push({ a: node(x.triple.s), b: node(x.triple.o), steps: [{ iri: x.triple.p.iri, inverse: false }] });
    } else if (x.kind === 'path') {
      const steps = pathSteps(x.path);
      if (!steps) return { ok: false, blocker: 'negation of a complex property path' };
      edges.push({ a: node(x.s), b: node(x.o), steps });
    } else if (x.kind === 'filter') filters.push(x.cond);
    else return { ok: false, blocker: `negation containing ${x.kind}` };
  }
  if (!edges.length) return { ok: false, blocker: 'negation with no graph pattern' };

  // Anchor: the one variable shared with the rest of the query.
  // Variables in an inner FILTER count too: FILTER(lang(?l) = ?lang) ties the negation to the ?lang column.
  const innerVars = new Set([
    ...edges.flatMap(e => [e.a, e.b]).filter(n => typeof n === 'string' && n.startsWith('?')),
    ...filters.flatMap(c => [...exprVars(c)].map(v => `?${v}`)),
  ]);
  const shared = [...innerVars].filter(v => outer.may.has(v.slice(1)));
  if (!shared.length) return { ok: false, blocker: op === 'minus' ? 'exclusion that removes nothing (MINUS with no shared variable)' : 'existence test unrelated to the results' };
  if (shared.length > 1) return { ok: false, blocker: 'negation tied to two columns (correlated, not one facet)' };
  const anchor = shared[0];
  if (!outer.must.has(anchor.slice(1))) return { ok: false, blocker: 'negation on a column that may be blank' };
  if (filters.length > 1) return { ok: false, blocker: 'negation with several conditions inside' };

  // Walk a single chain out from the anchor.
  const id = (n) => typeof n === 'string' ? n : n.id;
  const unused = new Set(edges.map((_, i) => i));
  let at = anchor; const hops = []; let end = null;
  for (;;) {
    const next = [...unused].filter(i => id(edges[i].a) === at || id(edges[i].b) === at);
    if (!next.length) break;
    if (next.length > 1) return { ok: false, blocker: 'negated combination "not (A and B)" — reads ambiguously as a facet' };
    const i = next[0]; unused.delete(i);
    const e = edges[i]; const fwd = id(e.a) === at;
    const steps = fwd ? e.steps : [...e.steps].reverse().map(s => ({ ...s, inverse: !s.inverse }));
    hops.push(...steps);
    const other = fwd ? e.b : e.a;
    if (typeof other !== 'string') { end = { const: other.c }; break; }
    at = other;
  }
  if (unused.size) return { ok: false, blocker: 'negated combination "not (A and B)" — reads ambiguously as a facet' };
  // At most one condition, on the value at the end of the chain.
  let test = null;
  if (filters.length) {
    test = endTest(filters[0], at);
    if (!test || end || at === anchor) return { ok: false, blocker: 'negation with a condition inside (not one facet value)' };
  }
  // A type step followed by its subclass closure counts as one hop.
  const typeHops = hops.filter((h, i) => !(h.closure && i > 0 && hops[i - 1].iri === P31));
  if (typeHops.length > MAX_HOPS) return { ok: false, blocker: `negated chain of ${typeHops.length} hops (too deep for one facet)` };

  const needs = [];
  if (hops.some(h => isStatementIri(h.iri))) needs.push('C');
  if (hops.some(h => h.closure)) needs.push('D');
  if (test?.kind === 'text') needs.push('B');

  const label = phrase(op, hops, end, test, nm, constName);
  if (!label) return { ok: false, blocker: 'negation with a condition inside (not one facet value)' };
  return { ok: true, anchor, needs, label };
}

/** The one condition a chip can carry on the end value ?v: a language, "other than X", or a text match. */
function endTest(c, v) {
  const isV = (a) => a?.e === 'var' && `?${a.name}` === v;
  const isVText = (a) => isV(a) || (a?.e === 'str' && isV(a.args[0]));
  const lit = (a) => a?.e === 'lit' ? a.lit.lex : null;
  if (c.e === 'compare' && c.op === '=' && c.args[0]?.e === 'lang' && isV(c.args[0].args[0]) && lit(c.args[1]) != null)
    return { kind: 'lang', lang: lit(c.args[1]) };
  if (c.e === 'compare' && c.op === '!=') {
    const [x, y] = isV(c.args[0]) ? c.args : [c.args[1], c.args[0]];
    if (isV(x) && y?.e === 'iri') return { kind: 'otherThan', iri: y.iri };
  }
  const how = { contains: 'contains', strStarts: 'starts with', strEnds: 'ends with', regex: 'matches the pattern' }[c.e];
  if (how && isVText(c.args[0]) && lit(c.args[1]) != null && !(c.e === 'regex' && c.args[2]))
    return { kind: 'text', how, text: lit(c.args[1]) };
  return null;
}

const aOrAn = (w) => (/^[aeiou]/i.test(w) ? 'an' : 'a');
const PROV_DERIVED = 'http://www.w3.org/ns/prov#wasDerivedFrom';

function phrase(op, hops, end, test, nm, constName) {
  const langTest = test?.kind === 'lang' ? test : null;
  const a = (iri) => `${aOrAn(nm(iri))} ${nm(iri)}`;
  const verb = op === 'exists' ? 'require' : 'exclude';
  const c = (h) => compact(h.iri);
  const local = (h) => `${c(h)?.prefix}:${c(h)?.local}`;
  // A text match reads as a condition on the value the chain reaches.
  if (test?.kind === 'text') {
    const what = hops.length === 1 && local(hops[0]) === 'schema:about' && hops[0].inverse ? 'a sitelink whose URL'
      : hops.length === 2 && hops[0].iri === PROV_DERIVED ? `a reference whose ${nm(hops[1].iri)}`
      : `${a(hops[hops.length - 1].iri)} whose text`;
    return `${verb}: ${hops[0].iri === PROV_DERIVED ? 'this statement has' : 'has'} ${what} ${test.how} "${test.text}"`;
  }
  // "Only X": no value other than X. Said as an exclusion so it reads correctly when the property has several values.
  if (test?.kind === 'otherThan' && hops.length === 1 && !hops[0].inverse)
    return `${verb}: ${nm(hops[0].iri)} includes something other than ${nm(test.iri)}`;
  if (test?.kind === 'otherThan') return null;
  // Recognised Wikidata shapes first: they read better than the generic chain.
  if (hops.length === 2 && local(hops[0]) === 'schema:about' && hops[0].inverse) {
    const site = end?.const?.t === 'iri' ? end.const.iri.replace(/^https?:\/\//, '').replace(/\/$/, '') : null;
    if (local(hops[1]) === 'schema:isPartOf' && site) return `${verb}: has a sitelink to ${site}`;
    if (local(hops[1]) === 'schema:inLanguage' && end?.const?.t === 'lit') return `${verb}: has a Wikimedia article in language "${end.const.lex}"`;
  }
  if (hops.length === 1 && local(hops[0]) === 'rdfs:label')
    return langTest ? `${verb}: has a label in "${langTest.lang}"` : `${verb}: has any label`;
  if (hops.length === 1 && local(hops[0]) === 'schema:description' && langTest)
    return `${verb}: has a description in "${langTest.lang}"`;
  if (hops.length === 1 && c(hops[0])?.prefix === 'pq')
    return `${verb}: this statement has ${a(hops[0].iri)} qualifier${end ? ` of ${constName(end.const)}` : ''}`;
  if (hops.length === 2 && c(hops[0])?.prefix === 'p' && c(hops[1])?.prefix === 'pq')
    return `${verb}: has ${a(hops[0].iri)} statement with ${a(hops[1].iri)} qualifier${end ? ` of ${constName(end.const)}` : ''}`;
  if (hops.length === 1 && hops[0].iri === PROV_DERIVED && !end) return `${verb}: this statement has a reference`;

  const sub = { zeroOrMore: 'any subclass', oneOrMore: 'any subclass', zeroOrOne: 'a direct subclass' };
  if (hops.length === 2 && hops[0].iri === P31 && hops[1].closure && end)
    return `${verb}: is an instance of ${constName(end.const)} or of ${sub[hops[1].closure]} of it`;
  if (hops.length === 1 && hops[0].closure && end)
    return hops[0].closure === 'oneOrMore' ? `${verb}: is a subclass, at any depth, of ${constName(end.const)}`
      : `${verb}: is ${constName(end.const)} or ${hops[0].closure === 'zeroOrOne' ? 'a direct subclass of it' : 'a subclass of it, at any depth'}`;
  if (hops.length === 1 && hops[0].inverse)
    return end ? `${verb}: is the ${nm(hops[0].iri)} of ${constName(end.const)}` : `${verb}: is the ${nm(hops[0].iri)} of something`;
  if (hops.length === 1) return end ? `${verb}: ${nm(hops[0].iri)} includes ${constName(end.const)}` : `${verb}: has any value for ${nm(hops[0].iri)}`;
  if (hops.length === 2 && hops[0].inverse && !hops[1].inverse)
    return end ? `${verb}: is the ${nm(hops[0].iri)} of something whose ${nm(hops[1].iri)} includes ${constName(end.const)}`
               : `${verb}: is the ${nm(hops[0].iri)} of something with any value for ${nm(hops[1].iri)}`;
  if (hops.some(h => h.inverse)) return `${verb}: ${hops.map(h => (h.inverse ? '^' : '') + nm(h.iri)).join(' → ')}${end ? ` reaches ${constName(end.const)}` : ''}`;
  const [h1, h2] = hops;
  return end ? `${verb}: has ${a(h1.iri)} whose ${nm(h2.iri)} includes ${constName(end.const)}`
             : `${verb}: has ${a(h1.iri)} with any value for ${nm(h2.iri)}`;
}
