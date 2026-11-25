// An abstract grammar of set browsing, and of what lies beyond it.
//
// A query becomes a Program: chains of set browsing (set, pivot, set, …),
// held together by Combine nodes for the operations browsing lacks. The
// grammar carries only data — variables, SPARQL terms and the SPARQL each
// step stands for — never wording. Words live in a separate lexicon, keyed
// by those same SPARQL terms, so any number of views (the block page, a
// bead chain as in kgx/daisychain, a DAG as in kgx/pivcab) can draw the
// same program without mixing presentation into the data. See GRAMMAR.md.
//
//   Program = { parts: (Chain | Combine)[], where: Sparql[] }
//   Chain   = { t:'chain', rows: Step[][] }         row 0 is the spine
//   Step    = Set | Pivot | From
//   Set     = { t:'set', v, type, values, narrow[], keep[], show[], sparql[] }
//   Pivot   = { t:'pivot', p, inv, opt, any, sparql }
//   From    = { t:'from', v }                       a branch row's start
//   Combine = { t:'combine', op, args: Program[], on[], out[], why, sparql }
//   op ∈ join | either | except | optional | stage | link
//
// Every Set, Pivot, Combine and the where-list carry `step` (an integer):
// the order in which a stepper adds them to a draft query. `steps` lists,
// per step, the SPARQL it adds and the variable it lands on.
import { flatten, recogniseLabels } from './explain.mjs';
import { scope } from './scope.mjs';
import { negationFacet } from './negation.mjs';
import { classifyParallax } from './parallax.mjs';
import { buildFlow } from './flow.mjs';
import { elemText, queryText, prefixesFor, exprSparql } from './sparql.mjs';

/** "birthPlace" / "birth_place" / "place2" -> "birth place" */
export const humanize = (v) => String(v).replace(/([a-z])([A-Z])/g, '$1 $2').replace(/[_\d]+/g, ' ').trim().toLowerCase() || v;
/** A set's name from its variable; short or cryptic names ("x", "obj", "q") read as "items". */
const nameOfVar = (v) => (v.length < 4 || !/[aeiou]/i.test(v)) ? 'items' : humanize(v);
const isWild = (prop) => /any property|^(reverse of )?any of /.test(prop || '');
const bareProp = (prop) => String(prop).replace(/^reverse of /, '');

/**
 * @returns {{program, steps, lex}}
 *   lex: words for the view, keyed by SPARQL term, ?variable, or blocker code.
 */
export function grammarOf(q, nameOf) {
  const lex = {};
  const full = queryText(q);
  const say = (k, text) => { if (k && text != null && !(k in lex)) lex[k] = text; };
  const program = programOf(q, nameOf, 0, say);
  const steps = [], nodes = [];
  number(program, steps, true, nodes);
  const answer = carry(q, program, steps, nodes);
  // A fragment's place in the whole query, so a draft keeps the query's own order
  // (BIND before the patterns that use its variable, VALUES first, and so on).
  const flat = (t) => t.replace(/\s+/g, ' ');
  const fullFlat = flat(full);
  for (const s of steps) s.sparql = s.sparql.map(x => ({ s: x, at: fullFlat.indexOf(flat(x)) }));
  return { program, steps, answer, prefixes: prefixesFor(full), vars: [...varsOf(program)].sort(), lex };
}

/**
 * What the rows carry, step by step, and what the query makes of them.
 *
 * After a pivot the rows are pairs (alum, nationality), not a set of
 * nationalities. Each step records `carries`: the sets reached so far. The
 * query's projection then decides the answer's shape:
 *   rows     it returns two or more of those sets: one row per combination
 *   set      it returns one, DISTINCT: each item once
 *   bag      it returns one, not DISTINCT: an item once per way of reaching it
 *   counted  it groups and counts
 * A set whose rows still carry earlier sets says so: `with` (those the answer
 * keeps beside it) and `shape`.
 */
function carry(q, program, steps, nodes) {
  const setsIn = (prog, out = []) => {
    for (const p of prog.parts) {
      if (p.t === 'chain') p.rows.flat().forEach(x => { if (x.t === 'set' && x.v) out.push(x.v); });
      else if (p.op !== 'except') { p.args.forEach(a => setsIn(a, out)); (p.out || []).forEach(v => out.push(v)); }
    }
    return out;
  };
  const chainVars = new Set(setsIn(program));
  const base = (v) => (chainVars.has(v) ? v : chainVars.has(v.replace(/(Label|Description|AltLabel)$/, '')) ? v.replace(/(Label|Description|AltLabel)$/, '') : null);
  const sel = q.select === 'all' ? null : q.select;
  const aggs = (sel || []).filter(i => i.expr && JSON.stringify(i.expr).includes('"aggregate"'));
  const counted = !!(q.groupBy?.length || aggs.length);
  const plain = sel ? sel.filter(i => !i.expr || i.expr.e === 'var').map(i => i.expr?.name ?? i.var) : [...chainVars];
  // A set is kept when the answer returns it, or a value shown on it (?coord of ?place),
  // or a value computed from either (BIND(?personLabel AS ?name)).
  const ownerOf = new Map();
  const owners = (prog) => prog.parts.forEach(p => (p.t === 'chain' ? p.rows.flat().forEach(x => (x.show || []).forEach(c => ownerOf.set(c.v, x.v))) : p.args.forEach(owners)));
  owners(program);
  const binds = new Map(flatten(q.pattern).filter(e => e.kind === 'bind').map(e => [e.v, [...JSON.stringify(e.e).matchAll(/"name":"(\w+)"/g)].map(m => m[1])]));
  const setOf = (v, depth = 0) => base(v) || (ownerOf.has(v) ? ownerOf.get(v) : null) || (depth < 3 && binds.has(v) ? binds.get(v).map(x => setOf(x, depth + 1)).find(Boolean) : null);
  const vars = [...new Set(plain.map(v => setOf(v)).filter(Boolean))];
  const countedVars = [...new Set(aggs.flatMap(i => [...JSON.stringify(i.expr).matchAll(/"name":"(\w+)"/g)].map(m => base(m[1]))).filter(Boolean))];
  // Sets the rows passed through but the answer drops: a single set reached through them
  // repeats once per path (a bag) unless DISTINCT removes the repeats.
  const dropped = [...chainVars].filter(v => !vars.includes(v));
  const projected = sel ? sel.map(i => i.var) : [];
  const columns = projected.filter(v => !base(v) && !aggs.some(i => i.var === v));
  const direct = new Set(plain.map(base).filter(Boolean));
  const shape = counted ? 'counted' : vars.length >= 2 || !vars.length ? 'rows' : dropped.length && !q.distinct ? 'bag' : 'set';
  const answer = {
    shape, vars: vars.length || counted ? vars : projected, columns: vars.length ? columns : [], via: shape === 'bag' ? dropped : [],
    counted: countedVars, distinct: !!q.distinct,
    aggregates: aggs.map(i => ({ v: i.var, sparql: exprSparql(i.expr) })),
    order: (q.orderBy || []).map(o => ({ dir: o.dir, by: exprSparql(o.expr) })),
  };
  let carried = [];
  steps.forEach((st, k) => {
    const node = nodes[k];
    const adds = st.kind === 'set' ? [st.v] : st.kind === 'pivot' ? [st.v] : node?.t === 'combine' && node.op !== 'join' ? setsIn({ parts: [node], where: [] }) : [];
    const before = carried;
    carried = [...new Set([...carried, ...adds.filter(Boolean)])];
    st.carries = carried;
    if (st.kind !== 'set' || !node) return;
    const earlier = before.filter(v => v !== st.v);
    if (!earlier.length) return;
    if (counted) {
      const per = earlier.filter(v => countedVars.includes(v));
      if (vars.includes(st.v) && per.length) { node.shape = 'counted'; node.with = per; }
    } else if (vars.includes(st.v)) {
      const kept = earlier.filter(v => vars.includes(v));
      if (kept.length) { node.shape = 'rows'; node.with = kept; }
      else { node.shape = q.distinct ? 'set' : 'bag'; node.with = earlier.slice(-1); }
    }
  });
  return answer;
}

/** Lay out a flow's sets (a forest) as rows of steps; one chain per root. */
function chainsOf(flow, say) {
  const sets = flow.sets.filter(s => !s.stage);
  const kids = (s) => sets.filter(x => x !== s && x.via?.from === s.var);
  const step = (s) => {
    say(`?${s.var}`, s.title.startsWith('?') ? nameOfVar(s.var) : s.title);
    const narrow = s.facets.map(f => {
      say(f.pt, bareProp(f.prop));
      f.values.forEach(v => say(v.term, v.text));
      return { p: f.pt, inv: !!(f.inv || f.reverse), opt: !!f.optional, any: isWild(f.prop) || undefined, o: f.values.map(v => v.term), sparql: f.src };
    });
    const keep = s.chips.map(c => { say(c.src || `#${c.label}`, c.label); return { mode: c.kind === 'or' ? 'anyOf' : c.verb, sparql: c.src || null, key: c.src || `#${c.label}` }; });
    const show = s.columns.map(c => { say(c.pt, bareProp(c.prop)); return { p: c.pt, inv: !!c.inv, opt: !!c.optional, any: isWild(c.prop) || undefined, v: c.var, sparql: c.src }; })
      .sort((a, b) => !!b.any - !!a.any);
    if (s.typeId) say(`wd:${s.typeId}`, s.title);
    s.values?.forEach(v => say(v.term, v.text));
    const set = { t: 'set', v: s.var, type: s.typeId ? `wd:${s.typeId}` : null, values: s.values?.map(v => v.term) || null,
      narrow, keep, show, sparql: [s.typeSrc, s.valuesSrc].filter(Boolean) };
    if ([...narrow, ...show].some(x => x.any)) set.any = true;
    return set;
  };
  const pivot = (s) => { say(s.via.pt, bareProp(s.via.prop)); return { t: 'pivot', p: s.via.pt, inv: !!s.via.inv, opt: !!s.via.optional, any: isWild(s.via.prop) || undefined, sparql: s.via.src }; };
  const chains = [];
  for (const root of sets.filter(s => !s.via?.from)) {
    const rows = [];
    const walk = (s, row) => {
      row.push(step(s));
      const [first, ...rest] = kids(s);
      for (const k of rest) { const r = [{ t: 'from', v: s.var }, pivot(k)]; rows.push(r); walk(k, r); }
      if (first) { row.push(pivot(first)); walk(first, row); }
    };
    const main = [];
    rows.push(main);
    walk(root, main);
    chains.push({ t: 'chain', rows: [main, ...rows.filter(r => r !== main)] });
  }
  return chains;
}

function programOf(q, nameOf, depth, say) {
  const px = classifyParallax(q, nameOf);
  const flow = buildFlow(q, px, nameOf);
  const elems = flatten(q.pattern);
  const { consumed } = recogniseLabels(elems);
  const outer = scope(q.pattern);
  const sub = (p) => depth > 3 ? { parts: [], where: [] } : programOf({ pattern: p, select: q.select, groupBy: [], having: [] }, nameOf, depth + 1, say);
  const conds = flow.conditions.map((text, i) => { const s = flow.conditionSrc[i]; say(s, text); return s; });
  const parts = [], ops = [];

  const chains = chainsOf(flow, say);
  let joinOn = [];
  if (chains.length > 1) {
    joinOn = conds;
    ops.push({ t: 'combine', op: 'join', on: conds, args: chains.map(c => ({ parts: [c], where: [] })) });
  } else parts.push(...chains);

  const complexOr = px.blockers.some(b => b.startsWith('OR whose branches'));
  // A union already drawn on a set (one facet with several values, or an "any of" chip) needs no block.
  const sameFacet = (el) => el.branches.map(flatten).every(a => a.length === 1 && a[0].kind === 'triple' && a[0].triple.o.t === 'iri'
    && a[0].triple.p.iri && a[0].triple.p.iri === flatten(el.branches[0])[0].triple?.p.iri);
  const orChips = px.extensions.filter(e => e.kind === 'or' && e.anchor).map(e => e.label.split(' | ').length);
  const absorbed = (el) => sameFacet(el) || (el.branches.every(b => flatten(b).length === 1) && orChips.includes(el.branches.length));
  const why = (code) => code;
  elems.forEach((el, i) => {
    if (consumed.has(i)) return;
    if (el.kind === 'union' && complexOr && !absorbed(el)) {
      ops.push({ t: 'combine', op: 'either', args: el.branches.map(sub), sparql: elemText(el) });
    } else if (el.kind === 'minus' || (el.kind === 'filter' && (el.cond.e === 'notExistsPat' || (el.cond.e === 'not' && el.cond.args[0]?.e === 'existsPat')))) {
      const p = el.kind === 'minus' ? el.p : el.cond.p ?? el.cond.args[0].p;
      const r = negationFacet(p, outer, el.kind === 'minus' ? 'minus' : 'notExists', nameOf);
      const shared = [...scope(p).may].filter(v => outer.may.has(v));
      if (!r.ok) ops.push({ t: 'combine', op: 'except', on: shared, why: why(r.blocker), args: [sub(p)], sparql: elemText(el) });
    } else if (el.kind === 'optional' && flatten(el.p).some(x => ['optional', 'union', 'minus'].includes(x.kind))) {
      ops.push({ t: 'combine', op: 'optional', args: [sub(el.p)], sparql: elemText(el) });
    } else if (el.kind === 'subselect') {
      const out = el.q.select === 'all' ? [] : el.q.select.map(it => it.var);
      ops.push({ t: 'combine', op: 'stage', out, args: [programOf(el.q, nameOf, depth + 1, say)], sparql: `{ ${queryText(el.q)} }` });
    }
  });
  // An edge that closes a cycle joins two sets already drawn: its own short chain.
  const ref = (v) => { if (v) say(`?${v}`, nameOfVar(v)); return { t: 'set', v, type: null, values: null, narrow: [], keep: [], show: [], sparql: [] }; };
  for (const e of flow.looseEdges) {
    say(e.pt, bareProp(e.prop));
    ops.push({ t: 'combine', op: 'link', sparql: e.src,
      args: [{ parts: [{ t: 'chain', rows: [[ref(e.s), { t: 'pivot', p: e.pt, inv: false, opt: !!e.optional, any: isWild(e.prop) || undefined, sparql: null }, ref(e.o)]] }], where: [] }] });
  }
  return { parts: [...parts, ...ops], where: conds.filter(c => !joinOn.includes(c)) };
}

/**
 * Number the steps a stepper walks, in drawing order: each set and pivot of
 * a chain, each combine as a whole (a join's chains are walked, being plain
 * conjunction), then the where-list. Steps inside other combines are not
 * numbered: the block is added to the draft in one go.
 */
function number(prog, steps, walkable, nodes = []) {
  for (const part of prog.parts) {
    if (part.t === 'chain') {
      for (const row of part.rows) row.forEach((s, at) => {
        if (s.t === 'from' || !walkable) return;
        const sparql = s.t === 'set' ? [...s.sparql, ...s.narrow.map(n => n.sparql), ...s.keep.map(k => k.sparql), ...s.show.map(c => c.sparql)] : [s.sparql];
        s.step = steps.length;
        nodes.push(s);
        // A pivot lands on the set it leads to.
        steps.push({ kind: s.t, v: s.t === 'set' ? s.v : row[at + 1]?.v ?? null, sparql: [...new Set(sparql.flat(Infinity).filter(Boolean))] });
      });
    } else if (part.op === 'join' && walkable) {
      part.args.forEach(a => number(a, steps, true, nodes));
      part.step = steps.length;
      nodes.push(part);
      steps.push({ kind: 'join', v: null, sparql: part.on });
    } else {
      part.args.forEach(a => number(a, steps, false, nodes));
      if (walkable) { part.step = steps.length; nodes.push(part); steps.push({ kind: part.op, v: null, sparql: [part.sparql].flat(Infinity).filter(Boolean) }); }
    }
  }
  if (prog.where.length && walkable) { prog.whereStep = steps.length; nodes.push(null); steps.push({ kind: 'where', v: null, sparql: prog.where }); }
  // Where-steps keep their own landing set: the last set seen so far.
  let last = null;
  for (const s of steps) { if (s.v) last = s.v; else s.v = last; }
}

/** Every variable a program shows: sets, shown columns, and ?names in conditions. */
function varsOf(prog, vs = new Set()) {
  const text = (t) => { for (const m of String(t).matchAll(/\?([A-Za-z_]\w*)/g)) if (!m[1].includes('__')) vs.add(m[1]); };
  for (const part of prog.parts) {
    if (part.t === 'chain') for (const row of part.rows) for (const s of row) { if (s.v) vs.add(s.v); for (const c of s.show || []) vs.add(c.v); }
    else { (part.on || []).forEach(part.op === 'except' ? (v) => vs.add(v) : text); (part.out || []).forEach(v => vs.add(v)); part.args.forEach(a => varsOf(a, vs)); }
  }
  prog.where.forEach(text);
  return vs;
}
