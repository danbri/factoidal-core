// Classify queries against the Freebase Parallax model (Huynh 2008):
// a current set of entities, narrowed by facet filters (property = value,
// several values of one facet = OR), moved by pivots along fixed properties
// (forward or inverse, chainable), shown as table / map / timeline columns,
// with set size and facet counts. No negation, closure, subqueries, cycles,
// cross products or arithmetic.
//
// Negation (MINUS, FILTER NOT EXISTS) and FILTER EXISTS are accepted when
// they fit one facet chip (see negation.mjs); they are listed in `negations`
// and don't change the tier letter.
//
// Three extensions beyond classic Parallax are accepted and listed in
// `extensions` as {kind, label}; like negations, they don't change the tier:
//   or       OR across facets or properties: a UNION whose branches are each a
//            single facet condition on the same item ("any of: …"), an
//            alternative path (P1|P2), or a predicate drawn from a VALUES list
//   path     path operators: optional steps (P131?/P17), closure of non-type
//            properties (P131*, P361+), longer fixed chains
//   derived  sets and columns computed by aggregation: a subquery that is itself
//            set browsing (a stage), MIN/MAX/SUM/AVG columns, HAVING, GROUP BY
//            an expression
//
// Tiers (lowest that fits):
//   A  core Parallax
//   B  A + literal filters (range / text / language) or computed display columns
//   C  B + traversal through statement nodes (p:/ps:/pq:), i.e. Freebase CVT-like mediators
//   D  any of the above but needing subclass closure (P31/P279*) to pick the starting type
//   N  not mappable; `blockers` says why
import { flatten, recogniseLabels, exprText } from './explain.mjs';
import { exprVars, scope } from './scope.mjs';
import { negationFacet } from './negation.mjs';
import { compact } from './names.mjs';
import { patternText, elemText } from './sparql.mjs';

const P31 = 'http://www.wikidata.org/prop/direct/P31';
const P279 = 'http://www.wikidata.org/prop/direct/P279';
const RDFS_LABEL = 'http://www.w3.org/2000/01/rdf-schema#label';

const isFixedSeq = (p) => p.path === 'iri' || (p.path === 'sequence' && isFixedSeq(p.a) && isFixedSeq(p.b)) || (p.path === 'inverse' && isFixedSeq(p.p));
const isSubclassClosure = (p) => p.path === 'sequence' && p.a.path === 'iri' && p.a.iri === P31 &&
  p.b.path === 'zeroOrMore' && p.b.p.path === 'iri' && p.b.p.iri === P279;
const STATEMENT_PREFIXES = ['p', 'ps', 'pq', 'psv', 'pqv', 'pr'];
const defaultName = (i) => { const c = compact(i); return c ? `${c.prefix}:${c.local}` : `<${i}>`; };

/** Paths built only from fixed properties (no negated property sets). */
const isFixedPath = (p) => p.path === 'iri' || (['sequence', 'alternative'].includes(p.path) && isFixedPath(p.a) && isFixedPath(p.b)) ||
  (['inverse', 'zeroOrOne', 'zeroOrMore', 'oneOrMore'].includes(p.path) && isFixedPath(p.p));

const AGG = { count: 'number of', sum: 'total of', min: 'smallest', max: 'largest', avg: 'average of', sample: 'an example', groupConcat: 'list of' };
function aggText(e) {
  const arg = e.arg?.e === 'var' ? `?${e.arg.name}` : e.arg ? 'a computed value' : 'rows';
  if (e.fn === 'sample') return `an example ${arg}`;
  return `${AGG[e.fn] || e.fn.toUpperCase()} ${e.distinct ? 'distinct ' : ''}${arg}`;
}

/** A property path in words, for a chip. */
export function describePath(p, nm = defaultName) {
  const d = (x) => describePath(x, nm);
  switch (p.path) {
    case 'iri': return nm(p.iri);
    case 'inverse': return `reverse of ${d(p.p)}`;
    case 'alternative': return `${d(p.a)} or ${d(p.b)}`;
    case 'sequence': {
      // Runs of one property (P184/P184/P184+) read as a step count.
      const steps = []; const flat = (x) => x.path === 'sequence' ? (flat(x.a), flat(x.b)) : steps.push(x); flat(p);
      const iriOf = (x) => x.path === 'iri' ? x.iri : null;
      const head = iriOf(steps[0]);
      if (steps.length > 2 && head && steps.slice(0, -1).every(x => iriOf(x) === head)) {
        const last = steps[steps.length - 1], n = steps.length - 1;
        if (last.path === 'oneOrMore' && iriOf(last.p) === head) return `${nm(head)}, ${n + 1} or more steps`;
        if (last.path === 'zeroOrMore' && iriOf(last.p) === head) return `${nm(head)}, ${n} or more steps`;
        if (iriOf(last) === head) return `${nm(head)}, exactly ${n + 1} steps`;
      }
      if (p.a.path === 'zeroOrOne') return `${d(p.b)}, directly or via ${d(p.a.p)}`;
      if (p.a.path === 'zeroOrMore') return `${d(p.b)}, directly or via ${d(p.a.p)} at any depth`;
      return `${d(p.a)} → ${d(p.b)}`;
    }
    case 'zeroOrOne': return `optionally ${d(p.p)}`;
    case 'zeroOrMore': return `${d(p.p)}, at any depth (or the item itself)`;
    case 'oneOrMore': return `${d(p.p)}, at any depth`;
    default: return '?';
  }
}
const pathIris = (p, out = []) => { if (p.path === 'iri') out.push(p.iri); for (const k of ['p', 'a', 'b']) if (p[k]) pathIris(p[k], out); return out; };

/** Node key for the join graph: variables and blank nodes are shared nodes; each constant occurrence is its own leaf. */
let leafN = 0;
const nodeKey = (t) => t.t === 'var' ? `?${t.name}` : t.t === 'bnode' ? `_${t.id}` : `#${leafN++}`;

export function classifyParallax(q, nm = defaultName) {
  const flags = new Set(), blockers = new Set();
  const negations = [], extensions = [];
  const ext = (kind, label, anchor, src) => { if (!extensions.some(e => e.kind === kind && e.label === label)) extensions.push(anchor ? { kind, label, anchor, src } : { kind, label }); };
  const extraNodes = new Set();
  const outer = scope(q.pattern);
  const negate = (p, op) => {
    const r = negationFacet(p, outer, op, nm);
    if (!r.ok) { blockers.add(r.blocker); return; }
    negations.push({ op, anchor: r.anchor, label: r.label, src: op === 'minus' ? `MINUS { ${patternText(p)} }` : `FILTER(${op === 'exists' ? '' : 'NOT '}EXISTS { ${patternText(p)} })` });
    for (const n of r.needs) flags.add(n);
  };
  const edges = []; // [a, b] undirected, between node keys
  const addEdge = (s, o) => edges.push([nodeKey(s), nodeKey(o)]);
  const statementEdge = (iri) => ['p', 'ps', 'pq', 'psv', 'pqv', 'pr'].includes(compact(iri)?.prefix);

  if (q.select === 'all') flags.add('select *');
  const elems = flatten(q.pattern);
  const { consumed } = recogniseLabels(elems);
  const optionals = [];

  const valuesOf = (v) => {
    const el = elems.find(x => x.kind === 'values' && x.vars.length === 1 && x.vars[0] === v);
    const iris = el?.rows.map(r => r[0]).filter(t => t?.t === 'iri').map(t => t.iri);
    return iris?.length && iris.length === el.rows.length ? iris : null;
  };
  const termVars = (t) => t?.t === 'var' ? [t.name] : [];
  /** Variables bound by the rest of the query, excluding element `skip`. */
  const scopeWithout = (skip) => {
    const may = new Set(), must = new Set();
    elems.forEach((x, i) => {
      if (i === skip) return;
      const vs = x.kind === 'triple' ? [x.triple.s, x.triple.p, x.triple.o].flatMap(termVars)
        : x.kind === 'path' ? [x.s, x.o].flatMap(termVars)
        : x.kind === 'values' ? x.vars
        : x.kind === 'subselect' ? (x.q.select === 'all' ? [] : x.q.select.map(it => it.var))
        : x.kind === 'union' ? [...scope({ type: 'union', ...unionNode(x.branches) }).must] : [];
      for (const v of vs) { may.add(v); must.add(v); }
      if (x.kind === 'optional') for (const v of scope(x.p).may) may.add(v);
    });
    return { may, must };
  };
  const unionNode = (branches) => branches.length === 1 ? { ...branches[0] } : { l: branches[0], r: { type: 'union', ...unionNode(branches.slice(1)) } };

  /** OR whose branches are each one facet condition on the same item. */
  const visitUnion = (el, i) => {
    let outerU = scopeWithout(i);
    let res = el.branches.map(b => negationFacet(b, outerU, 'exists', nm));
    if (res.some(r => !r.ok && /no shared variable|unrelated/.test(r.blocker))) {
      // The OR is the starting set: anchor on the one variable every branch always binds.
      const common = el.branches.map(b => scope(b).must).reduce((a, b) => new Set([...a].filter(v => b.has(v))));
      if (common.size === 1) {
        const v = [...common][0];
        outerU = { may: new Set([...outerU.may, v]), must: new Set([...outerU.must, v]) };
        res = el.branches.map(b => negationFacet(b, outerU, 'exists', nm));
      }
    }
    if (res.every(r => r.ok) && new Set(res.map(r => r.anchor)).size === 1) {
      ext('or', `any of: ${res.map(r => r.label.replace(/^require: /, '')).join(' | ')}`, res[0].anchor, elemText(el));
      for (const r of res) for (const n of r.needs) flags.add(n);
      extraNodes.add(res[0].anchor);
      return;
    }
    // The same column reached by different properties: {?x P1 ?v} UNION {?x P2 ?v}.
    const arms = el.branches.map(b => flatten(b));
    const single = arms.every(a => a.length === 1 && (a[0].kind === 'path' ? isFixedPath(a[0].path) : a[0].kind === 'triple' && a[0].triple.p.t === 'iri'));
    if (single) {
      const ends = arms.map(([x]) => x.kind === 'triple' ? [x.triple.s, x.triple.o] : [x.s, x.o]).map(e => JSON.stringify(e));
      if (new Set(ends).size === 1) {
        const [x] = arms[0];
        ext('or', `via ${arms.map(([y]) => y.kind === 'triple' ? nm(y.triple.p.iri) : describePath(y.path, nm)).join(' or ')}`);
        addEdge(x.kind === 'triple' ? x.triple.s : x.s, x.kind === 'triple' ? x.triple.o : x.o);
        return;
      }
    }
    blockers.add('OR whose branches are not single facet conditions');
  };

  /** A subquery that is itself set browsing: a stage whose output columns join the outer set. */
  const visitSubselect = (sq) => {
    const inner = classifyParallax(sq, nm);
    if (inner.tier === 'N') { blockers.add(`subquery that is not set browsing (${inner.blockers[0]})`); return; }
    for (const f of inner.flags) flags.add(f);
    if (inner.tier !== 'A') flags.add(inner.tier);
    const proj = sq.select === 'all' ? [] : sq.select;
    const keys = (sq.groupBy || []).map(g => g.var).filter(Boolean);
    const aggs = proj.filter(it => it.expr?.e === 'aggregate').map(it => `${aggText(it.expr)} as ?${it.var}`);
    const desc = keys.length ? `for each ${keys.map(k => '?' + k).join(', ')}${aggs.length ? ': ' + aggs.join(', ') : ''}` : `the set of ${proj.map(it => '?' + it.var).join(', ')}`;
    const lim = sq.limit != null ? ` (first ${sq.limit}${sq.orderBy?.length ? ' in order' : ', in no set order'})` : '';
    ext('derived', `stage: ${desc}${lim}`);
    for (const e of inner.extensions) ext(e.kind, `in stage: ${e.label}`);
    for (const n of inner.negations) negations.push({ ...n, stage: true });
    const vs = proj.map(it => it.var);
    for (const v of vs.slice(1)) edges.push([`?${vs[0]}`, `?${v}`]);
    if (vs.length === 1) extraNodes.add(`?${vs[0]}`);
  };

  const visitTriple = (tr) => {
    if (tr.p.t !== 'iri') {
      // A predicate variable drawn from a VALUES list of properties = a pivot via any of them.
      const vals = valuesOf(tr.p.name);
      if (!vals) { blockers.add('any property (unrestricted variable predicate)'); return; }
      ext('or', `via any of: ${vals.map(nm).join(', ')}`);
      if (vals.some(statementEdge)) flags.add('C');
      addEdge(tr.s, tr.o); return;
    }
    if (statementEdge(tr.p.iri) || tr.p.iri === 'http://www.w3.org/ns/prov#wasDerivedFrom') flags.add('C');
    addEdge(tr.s, tr.o);
  };
  const visitPath = (el) => {
    if (isSubclassClosure(el.path)) { flags.add('D'); addEdge(el.s, el.o); return; }
    if (isFixedSeq(el.path)) {
      if (pathIris(el.path).some(statementEdge)) flags.add('C');
      addEdge(el.s, el.o); return;
    }
    if (el.path.path === 'zeroOrOne' && el.path.p.path === 'iri' && el.path.p.iri === P279) { flags.add('D'); addEdge(el.s, el.o); return; }
    // ?c wdt:P279* / wdt:P279+ X : the classes under X — with a P31 elsewhere, "type including subclasses".
    if ((el.path.path === 'zeroOrMore' || el.path.path === 'oneOrMore') && el.path.p.path === 'iri' && el.path.p.iri === P279) {
      flags.add('D'); addEdge(el.s, el.o); return;
    }
    if (el.path.path === 'alternative' && isFixedPath(el.path)) {
      ext('or', `via ${describePath(el.path, nm)}`);
      if (pathIris(el.path).some(statementEdge)) flags.add('C');
      addEdge(el.s, el.o); return;
    }
    // P31/P279? (instance of X or of a direct subclass of X): bounded subclass selection.
    const steps = []; const seq = (x) => x.path === 'sequence' ? (seq(x.a), seq(x.b)) : steps.push(x); seq(el.path);
    const isOpt = (x, iri) => x.path === 'zeroOrOne' && x.p.path === 'iri' && (!iri || x.p.iri === iri);
    if (steps.length === 2 && steps[0].path === 'iri' && steps[0].iri === P31 && isOpt(steps[1], P279)) { flags.add('D'); addEdge(el.s, el.o); return; }
    // Other paths over fixed properties: optional steps, closure of non-type properties.
    if (isFixedPath(el.path)) {
      ext('path', describePath(el.path, nm));
      const iris = pathIris(el.path);
      if (iris.some(statementEdge)) flags.add('C');
      if (iris.includes(P279)) flags.add('D');
      addEdge(el.s, el.o); return;
    }
    blockers.add('property path with excluded properties');
  };

  elems.forEach((el, i) => {
    if (consumed.has(i)) return; // rewritten label lookups = display
    switch (el.kind) {
      case 'triple': visitTriple(el.triple); break;
      case 'path': visitPath(el); break;
      case 'optional': optionals.push(el); break;
      case 'minus': negate(el.p, 'minus'); break;
      case 'filter': {
        const c = el.cond;
        if (c.e === 'notExistsPat') negate(c.p, 'notExists');
        else if (c.e === 'not' && c.args[0]?.e === 'existsPat') negate(c.args[0].p, 'notExists');
        else if (c.e === 'existsPat') negate(c.p, 'exists');
        else if (JSON.stringify(c).match(/"(not)?[eE]xistsPat"/)) blockers.add('existence test combined with other conditions');
        else flags.add('B');
        break;
      }
      case 'bind': flags.add('B'); break; // computed display column
      case 'values': {
        // A one-variable VALUES of constants used as a facet value = multi-select facet (OR);
        // used as a predicate, it is handled with the triple.
        if (el.vars.length !== 1) blockers.add('multi-column VALUES');
        break;
      }
      case 'union': {
        // OR of the same property with different constant values = multi-select facet.
        const arms = el.branches.map(b => flatten(b));
        const sig = (arm) => arm.length === 1 && arm[0].kind === 'triple' && arm[0].triple.p.t === 'iri' && arm[0].triple.o.t === 'iri'
          ? `${JSON.stringify(arm[0].triple.s)}|${arm[0].triple.p.iri}` : null;
        const sigs = arms.map(sig);
        if (sigs.every(s => s && s === sigs[0])) { addEdge(arms[0][0].triple.s, arms[0][0].triple.o); }
        else visitUnion(el, i);
        break;
      }
      case 'subselect': visitSubselect(el.q); break;
      case 'service': blockers.add('external service'); break;
      default: blockers.add(`unsupported element: ${el.kind}`);
    }
  });

  // Optional parts: display columns hanging off the set (tree-shaped, fixed edges).
  for (const o of optionals) {
    for (const x of flatten(o.p)) {
      if (x.kind === 'triple') visitTriple(x.triple);
      else if (x.kind === 'path') visitPath(x);
      else if (x.kind === 'filter' || x.kind === 'bind') flags.add('B');
      else blockers.add(`${x.kind} inside OPTIONAL`);
    }
  }

  // Join graph must be one tree: connected, no cycles (else cross product or cycle).
  const nodes = new Set([...edges.flat(), ...extraNodes]);
  const parent = new Map([...nodes].map(n => [n, n]));
  const find = (x) => { while (parent.get(x) !== x) x = parent.get(x); return x; };
  let cycle = false;
  for (const [a, b] of edges) { const ra = find(a), rb = find(b); if (ra === rb) cycle = true; else parent.set(ra, rb); }
  const comps = new Set([...nodes].map(find)).size;
  if (cycle) blockers.add('cyclic join (not a tree from one set)');
  if (comps > 1) blockers.add('join on a computed value, or unconnected sets');
  if (!nodes.size && !blockers.size) blockers.add('no graph pattern');

  // Aggregation: set size and facet counts are Parallax; table cells may hold several values.
  const proj = q.select === 'all' ? [] : q.select;
  const aggs = proj.filter(it => it.expr?.e === 'aggregate');
  const keys = (q.groupBy || []).map(g => g.var ?? g.alias);
  for (const a of aggs) {
    const fn = a.expr.fn;
    if (fn === 'count') { if (keys.length > 2) flags.add('B'); }
    else if (fn === 'sample' || fn === 'groupConcat') { /* display of multi-valued cells */ }
    else ext('derived', `computed per group: ${aggText(a.expr)} as ?${a.var}`);
  }
  const N = { iri: nm };
  for (const h of q.having || []) ext('derived', `keep groups where ${exprText(h, N)}`);
  for (const g of (q.groupBy || []).filter(g => g.expr)) ext('derived', `group by ${exprText(g.expr, N)}${g.var ? ` (as ?${g.var})` : ''}`);
  for (const it of proj) if (it.expr && it.expr.e !== 'aggregate') flags.add('B');

  const tier = blockers.size ? 'N' : flags.has('D') ? 'D' : flags.has('C') ? 'C' : flags.has('B') ? 'B' : 'A';
  return { tier, negations, extensions, flags: [...flags].filter(f => f.length > 1), blockers: [...blockers] };
}
