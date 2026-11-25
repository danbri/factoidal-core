// Block view of a query, for queries that go beyond set browsing.
//
// Each run of set browsing (a set, then a pivot along a property, then
// the related set, …) becomes a horizontal chain of interlocking pieces.
// The operations that browsing cannot do become blocks that hold two
// or more chains, in the style of Scratch's C-shaped blocks:
//   either   OR whose branches are whole patterns
//   except   an exclusion that is not a single facet chip
//   join     separate chains joined on a computed value (or not at all)
//   loop     an extra edge that closes a cycle
//   optional a nested "where present" part
//   stage    a grouped subquery computed on its own
import { flatten, recogniseLabels } from './explain.mjs';
import { scope } from './scope.mjs';
import { negationFacet } from './negation.mjs';
import { classifyParallax } from './parallax.mjs';
import { buildFlow } from './flow.mjs';

const isWild = (prop) => /any property|^(reverse of )?any of /.test(prop || '');

/** Lay out a flow's sets (a forest) as rows of pieces; one chain per root. */
function chainsOf(flow) {
  const sets = flow.sets.filter(s => !s.stage);
  const kids = (s) => sets.filter(x => x !== s && x.via?.from === s.var);
  // A facet or column along "any property" is marked, like a wildcard pivot.
  const mark = (xs) => xs.map(x => isWild(x.prop) ? { ...x, wild: true } : x);
  const piece = (s) => {
    const p = { kind: 'set', var: s.var, title: s.title, typeId: s.typeId, facets: mark(s.facets), chips: s.chips, columns: mark(s.columns).sort((a, b) => !!b.wild - !!a.wild) };
    if ([...p.facets, ...p.columns].some(x => x.wild)) p.wild = true;
    return p;
  };
  const pivot = (s) => ({ kind: 'pivot', prop: s.via.prop, optional: !!s.via.optional, wild: isWild(s.via.prop) });
  const chains = [];
  for (const root of sets.filter(s => !s.via?.from)) {
    const rows = [];
    const walk = (s, row) => {
      row.push(piece(s));
      const [first, ...rest] = kids(s);
      for (const k of rest) { const r = [{ kind: 'from', var: s.var, title: s.title }, pivot(k)]; rows.push(r); walk(k, r); }
      if (first) { row.push(pivot(first)); walk(first, row); }
    };
    const main = [];
    rows.push(main);
    walk(root, main);
    chains.push({ rows: [main, ...rows.filter(r => r !== main)] });
  }
  return chains;
}

/** Program for a query (or a sub-pattern): {items: [{chain}|{op}], conditions}. */
export function blocksOf(q, nameOf, depth = 0) {
  const px = classifyParallax(q, nameOf);
  const flow = buildFlow(q, px, nameOf);
  const elems = flatten(q.pattern);
  const { consumed } = recogniseLabels(elems);
  const outer = scope(q.pattern);
  const sub = (p) => depth > 3 ? { items: [], conditions: [] } : blocksOf({ pattern: p, select: q.select, groupBy: [], having: [] }, nameOf, depth + 1);
  const items = [], ops = [];

  const chains = chainsOf(flow);
  const joinConds = [];
  if (chains.length > 1) {
    joinConds.push(...flow.conditions);
    ops.push({ op: 'join', label: flow.conditions.length ? 'join where' : 'every combination of', extras: flow.conditions,
      slots: chains.map(c => ({ items: [{ chain: c }], conditions: [] })) });
  } else items.push(...chains.map(c => ({ chain: c })));

  const complexOr = px.blockers.some(b => b.startsWith('OR whose branches'));
  // A union already drawn on a set (one facet with several values, or an "any of" chip) needs no block.
  const sameFacet = (el) => el.branches.map(flatten).every(a => a.length === 1 && a[0].kind === 'triple' && a[0].triple.o.t === 'iri'
    && a[0].triple.p.iri && a[0].triple.p.iri === flatten(el.branches[0])[0].triple?.p.iri);
  const orChips = px.extensions.filter(e => e.kind === 'or' && e.anchor).map(e => e.label.split(' | ').length);
  const absorbed = (el) => sameFacet(el) || (el.branches.every(b => flatten(b).length === 1) && orChips.includes(el.branches.length));
  elems.forEach((el, i) => {
    if (consumed.has(i)) return;
    if (el.kind === 'union' && complexOr && !absorbed(el)) {
      ops.push({ op: 'either', label: 'either', slots: el.branches.map(sub) });
    } else if (el.kind === 'minus' || (el.kind === 'filter' && (el.cond.e === 'notExistsPat' || (el.cond.e === 'not' && el.cond.args[0]?.e === 'existsPat')))) {
      const p = el.kind === 'minus' ? el.p : el.cond.p ?? el.cond.args[0].p;
      const r = negationFacet(p, outer, el.kind === 'minus' ? 'minus' : 'notExists', nameOf);
      const shared = [...scope(p).may].filter(v => outer.may.has(v)).map(v => `?${v}`);
      if (!r.ok) ops.push({ op: 'except', label: 'except where', why: r.blocker, extras: shared.length ? [`matched on ${shared.join(' and ')}`] : [], slots: [sub(p)] });
    } else if (el.kind === 'optional' && flatten(el.p).some(x => ['optional', 'union', 'minus'].includes(x.kind))) {
      ops.push({ op: 'optional', label: 'where present, also', slots: [sub(el.p)] });
    } else if (el.kind === 'subselect') {
      const outs = (el.q.select === 'all' ? [] : el.q.select).map(it => `?${it.var}`);
      ops.push({ op: 'stage', label: 'a separate stage, computed first', extras: outs.length ? [`hands on ${outs.join(', ')}`] : [], slots: [blocksOf(el.q, nameOf, depth + 1)] });
    }
  });
  // An edge that closes a cycle joins two sets already drawn: show it as its own short chain.
  const ref = (v) => ({ kind: 'set', var: v, title: v ? `?${v}` : '(a value)', typeId: null, facets: [], chips: [], columns: [] });
  for (const e of flow.looseEdges) ops.push({ op: 'loop', label: 'and the same items must also link up', extras: [],
    slots: [{ items: [{ chain: { rows: [[ref(e.s), { kind: 'pivot', prop: e.prop, optional: !!e.optional, wild: isWild(e.prop) }, ref(e.o)]] } }], conditions: [] }] });

  return {
    items: [...items, ...ops.map(op => ({ op }))],
    conditions: flow.conditions.filter(c => !joinConds.includes(c)),
  };
}
