// Set-flow view of a query, for the Parallax hub page.
//
// The query's join tree is laid out as sets of entities: a starting set,
// narrowed by facets (property = value), from which pivots lead to related
// sets; leaf values are columns. Exclusions (negation chips) sit on the set
// they apply to. Parts that are not set browsing are listed separately as
// "beyond set browsing", so the picture never claims more than it shows.
import { flatten, recogniseLabels, exprText } from './explain.mjs';
import { compact } from './names.mjs';
import { describePath, classifyParallax } from './parallax.mjs';

const P31 = 'http://www.wikidata.org/prop/direct/P31';
const qid = (iri) => { const m = /^http:\/\/www\.wikidata\.org\/entity\/(Q\d+)$/.exec(iri || ''); return m ? m[1] : null; };
const LABEL_VAR = /(__label_value|__description_value|__label_subject)$/;

/**
 * @param q   IR query
 * @param px  classifyParallax result for q
 * @param nm  readable name for an IRI
 */
export function buildFlow(q, px, nameOf) {
  // Statement hops get their own words, so p:/ps:/pq: don't all read as the plain property.
  const SUFFIX = { p: ' statement', ps: ' value', pq: ' qualifier', pr: ' in a reference', psv: ' value (full)', pqv: ' qualifier (full)' };
  const nm = (iri) => {
    const c = compact(iri);
    const n = nameOf(iri);
    return c && SUFFIX[c.prefix] ? n.replace(/ \((P\d+)\)$/, `${SUFFIX[c.prefix]} ($1)`) : n;
  };
  const elems = flatten(q.pattern);
  const { consumed } = recogniseLabels(elems);
  // A variable shown through its label (?xLabel) counts as shown.
  const projected = (q.select === 'all' ? [] : q.select.map(it => it.var)).flatMap(v => [v, v.replace(/(Label|Description)$/, '')]);
  // Variables an "any of" OR narrows are sets, never leaf columns.
  const anchors = new Set((px.extensions || []).filter(e => e.anchor).map(e => e.anchor.slice(1)));
  const valuesOf = (v) => elems.find(x => x.kind === 'values' && x.vars.length === 1 && x.vars[0] === v)?.rows.map(r => r[0]).filter(Boolean);

  // Edges: {s, o, prop, optional, text}
  const edges = [];
  const addEdge = (s, o, prop, optional) => edges.push({ s, o, prop, optional });
  const propOfTriple = (tr) => tr.p.t === 'iri' ? nm(tr.p.iri)
    : (valuesOf(tr.p.name) ? `any of ${valuesOf(tr.p.name).map(t => nm(t.iri)).join(', ')}` : 'any property');
  const take = (x, optional) => {
    if (x.kind === 'triple') {
      if (LABEL_VAR.test(x.triple.o.name || '') || LABEL_VAR.test(x.triple.s.name || '')) return;
      addEdge(x.triple.s, x.triple.o, propOfTriple(x.triple), optional);
    } else if (x.kind === 'path') addEdge(x.s, x.o, describePath(x.path, nm), optional);
  };
  const conditions = [];
  elems.forEach((el, i) => {
    if (consumed.has(i)) return;
    if (el.kind === 'triple' || el.kind === 'path') take(el, false);
    else if (el.kind === 'optional') for (const x of flatten(el.p)) take(x, true);
    else if (el.kind === 'union') {
      // Same property, different values: one facet with several values.
      const arms = el.branches.map(b => flatten(b));
      if (arms.every(a => a.length === 1 && a[0].kind === 'triple' && a[0].triple.p.t === 'iri'
        && a[0].triple.p.iri === arms[0][0].triple.p.iri && JSON.stringify(a[0].triple.s) === JSON.stringify(arms[0][0].triple.s)
        && a[0].triple.o.t === 'iri')) {
        addEdge(arms[0][0].triple.s, { t: 'any', iris: arms.map(a => a[0].triple.o.iri) }, nm(arms[0][0].triple.p.iri), false);
      }
    } else if (el.kind === 'filter' && !/"(not)?[eE]xistsPat"/.test(JSON.stringify(el.cond))) {
      conditions.push(exprText(el.cond, { iri: nm }));
    } else if (el.kind === 'bind' && !/Label$|Description$|__/.test(el.v)) {
      conditions.push(`?${el.v} = ${exprText(el.e, { iri: nm })}`);
    }
  });

  const key = (t) => t.t === 'var' ? t.name : t.t === 'bnode' ? `_${t.id}` : null;
  const vars = new Set(edges.flatMap(e => [key(e.s), key(e.o)]).filter(Boolean));

  // Root: the projected entity set with the most structure, preferring a typed one.
  const score = (v) => edges.filter(e => !e.optional && (key(e.s) === v || key(e.o) === v)).length
    + (edges.some(e => key(e.s) === v && e.prop === nm(P31) && e.o.t === 'iri') ? 3 : 0)
    + (projected.includes(v) ? 2 : 0) + (anchors.has(v) ? 3 : 0);
  // Statement nodes (objects of p:) are never the starting set.
  const isStatement = (v) => edges.some(e => key(e.o) === v && / statement \(P\d+\)$/.test(e.prop));
  const candidates = [...vars].filter(v => !v.startsWith('_')).sort((a, b) => isStatement(a) - isStatement(b));
  const root = [...candidates].sort((a, b) => isStatement(a) - isStatement(b) || score(b) - score(a) || projected.indexOf(a) - projected.indexOf(b))[0];

  const used = new Set(), seen = new Set();
  const facetValue = (t) => {
    if (t.t === 'iri') return [{ id: qid(t.iri), text: nm(t.iri) }];
    if (t.t === 'any') return t.iris.map(i => ({ id: qid(i), text: nm(i) }));
    if (t.t === 'lit') return [{ text: JSON.stringify(t.lex) }];
    if (t.t === 'bnode') return [{ text: 'any value' }];
    return [{ text: '?' }];
  };
  const degree = (v) => edges.filter(e => key(e.s) === v || key(e.o) === v).length + (anchors.has(v) ? 1 : 0);
  const sets = [];
  const visit = (v, via) => {
    seen.add(v);
    const set = { var: v, via, facets: [], columns: [], chips: [] };
    sets.push(set);
    const mine = edges.map((e, i) => [e, i]).filter(([e, i]) => !used.has(i) && (key(e.s) === v || key(e.o) === v));
    const children = [];
    for (const [e, i] of mine) {
      if (used.has(i)) continue;
      used.add(i);
      const fwd = key(e.s) === v;
      const other = fwd ? e.o : e.s;
      const prop = fwd ? e.prop : `reverse of ${e.prop}`;
      const ok = key(other);
      // A blank node with properties of its own (a [ ps:… ; pq:… ] statement) is a set, not "any value".
      if (!ok || (ok.startsWith('_') && degree(ok) === 1)) {
        if (!fwd && other.t === 'iri') { set.facets.push({ prop: e.prop, values: facetValue(other), reverse: true, optional: e.optional }); continue; }
        set.facets.push({ prop, values: facetValue(other), optional: e.optional });
        continue;
      }
      const vals = valuesOf(ok);
      if (vals && degree(ok) === 1) { set.facets.push({ prop, values: vals.flatMap(facetValue), optional: e.optional }); continue; }
      if (seen.has(ok)) { used.delete(i); continue; } // cycle: left for "beyond"
      if (degree(ok) > 1) children.push({ v: ok, i, via: { from: v, prop, optional: e.optional } });
      else set.columns.push({ var: ok, prop, optional: e.optional });
    }
    // A child reached meanwhile by another route closes a cycle: its edge stays outside the tree.
    for (const c of children) { if (seen.has(c.v)) used.delete(c.i); else visit(c.v, c.via); }
  };
  if (root) visit(root, null);
  // Other components (a second starting set, joined by a computed value) get their own roots.
  for (const v of candidates) if (!seen.has(v) && edges.some((e, i) => !used.has(i) && (key(e.s) === v || key(e.o) === v))) visit(v, { from: null, prop: null });

  for (const set of sets) {
    const parent = set.via?.from ? sets.find(x => x.var === set.via.from) : null;
    set.depth = parent ? parent.depth + 1 : 0;
    const type = set.facets.find(f => f.prop === nm(P31) && f.values.length === 1 && f.values[0].id);
    const stmt = set.via && / statement \(P\d+\)$/.test(set.via.prop) ? set.via.prop.replace(/ \(P\d+\)$/, '') + 's' : null;
    set.title = type ? type.values[0].text : stmt || `?${set.var}`;
    set.typeId = type?.values[0].id || null;
  }
  for (const n of px.negations || []) {
    const s = sets.find(x => `?${x.var}` === n.anchor);
    (s ? s.chips : (sets[0]?.chips || [])).push({ kind: 'exclude', label: n.label.replace(/^(exclude|require): /, '') + (n.stage ? ' (inside the grouped stage)' : ''), verb: n.label.split(':')[0] });
  }
  // An "any of" OR sits on the set it narrows; with nothing else to draw, that set starts the flow.
  for (const e of (px.extensions || []).filter(e => e.anchor)) {
    let s = sets.find(x => `?${x.var}` === e.anchor);
    if (!s) { s = { var: e.anchor.slice(1), via: null, depth: 0, facets: [], columns: [], chips: [], title: e.anchor, typeId: null }; sets.unshift(s); }
    s.chips.push({ kind: 'or', verb: 'any', label: e.label.replace(/^any of: /, '') });
  }
  // Subqueries: their own sets, drawn as a grouped stage joined on its output columns.
  for (const el of elems.filter(x => x.kind === 'subselect')) {
    const inner = buildFlow(el.q, classifyParallax(el.q, nameOf), nameOf);
    const outs = (el.q.select === 'all' ? [] : el.q.select).map(it => it.var);
    inner.sets.forEach((s, k) => sets.push({ ...s, stage: k === 0 ? { joins: outs.filter(v => vars.has(v) || projected.includes(v)) } : true }));
    conditions.push(...inner.conditions);
  }
  const edgeText = new Set(edges.map(e => e.prop));
  const extensions = (px.extensions || []).filter(e => !e.anchor && !(e.kind === 'path' && edgeText.has(e.label)) && !(e.kind === 'or' && edgeText.has(e.label.replace(/^via /, ''))));
  const beyond = [...(px.blockers || [])];
  const loose = edges.filter((e, i) => !used.has(i)).map(e => `${key(e.s) ? '?' + key(e.s) : nm(e.s.iri || '')} ${e.prop} ${key(e.o) ? '?' + key(e.o) : facetValue(e.o).map(x => x.text).join(', ')}`);

  const entities = new Set();
  const collect = (text) => { for (const m of String(text).matchAll(/\((Q\d+)\)/g)) entities.add(m[1]); };
  for (const s of sets) { for (const f of s.facets) for (const v of f.values) if (v.id) entities.add(v.id); for (const c of s.chips) collect(c.label); }
  for (const e of extensions) collect(e.label);

  return {
    sets: sets.map(({ var: v, title, typeId, via, depth, facets, columns, chips, stage }) => ({ var: v, title, typeId, via, depth, stage, facets: facets.filter(f => !(f.prop === nm(P31) && f.values.length === 1 && f.values[0].id === typeId)), columns, chips })),
    conditions, extensions, beyond, loose, entities: [...entities],
    aggregate: (q.select === 'all' ? [] : q.select).some(it => it.expr?.e === 'aggregate'),
  };
}
