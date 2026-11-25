// Variable scope over the IR (SPARQL 1.1 §18.2.1 "in-scope variables"),
// extended with a may/must distinction:
//   must(p): variables bound in EVERY solution of p
//   may(p):  variables bound in SOME solution of p (the in-scope set)
// Variables that occur in a pattern only inside MINUS's right side or an
// EXISTS / NOT EXISTS pattern are never in scope outside it.

import { exprChildren } from './ir.mjs';

const termVars = (t) => {
  if (!t) return [];
  if (t.t === 'var') return [t.name];
  if (t.t === 'tripleTerm') return [...termVars(t.s), ...termVars(t.p), ...termVars(t.o)];
  return [];
};
const union = (...ss) => new Set(ss.flatMap(s => [...s]));
const inter = (a, b) => new Set([...a].filter(x => b.has(x)));

/** Does an expression always produce a value (never an error)? Conservative.
 *  `inner`: inside the then-branch of IF(BOUND(?v), ...), where string
 *  functions of bound variables and constants cannot fail. */
function exprAlwaysBound(e, must, inner = false) {
  if (!e) return false;
  if (e.e === 'var') return must.has(e.name);
  if (['iri', 'lit', 'bool', 'num', 'decimal', 'double'].includes(e.e)) return true;
  if (e.e === 'coalesce') return (e.args || []).some(a => exprAlwaysBound(a, must));
  // IF(BOUND(?v), f(?v, constants), g) is bound when g is: f only runs once ?v is set.
  if (e.e === 'cond' && e.args[0]?.e === 'bound') {
    const v = e.args[0].name;
    return exprAlwaysBound(e.args[2], must) && exprAlwaysBound(e.args[1], new Set([...must, v]), true);
  }
  if (inner && ['iriFn', 'concat', 'str', 'strAfter', 'strBefore', 'uCase', 'lCase'].includes(e.e))
    return (e.args || []).every(a => exprAlwaysBound(a, must, true));
  return false;
}

/** @returns {{may:Set<string>, must:Set<string>}} */
export function scope(p) {
  switch (p.type) {
    case 'bgp': {
      const vs = new Set(p.triples.flatMap(tr => [...termVars(tr.s), ...termVars(tr.p), ...termVars(tr.o)]));
      return { may: vs, must: vs };
    }
    case 'propertyPath': {
      const vs = new Set([...termVars(p.s), ...termVars(p.o)]);
      return { may: vs, must: vs };
    }
    case 'join': case 'lateral': {
      const a = scope(p.l), b = scope(p.r);
      return { may: union(a.may, b.may), must: union(a.must, b.must) };
    }
    case 'leftJoin': {
      const a = scope(p.l), b = scope(p.r);
      return { may: union(a.may, b.may), must: a.must };
    }
    case 'union': {
      const a = scope(p.l), b = scope(p.r);
      return { may: union(a.may, b.may), must: inter(a.must, b.must) };
    }
    case 'minus': return scope(p.l);
    case 'filter': return scope(p.p);
    case 'graph': {
      const a = scope(p.p), g = new Set(termVars(p.name));
      return { may: union(a.may, g), must: union(a.must, g) };
    }
    case 'bind': {
      const a = scope(p.p);
      const must = exprAlwaysBound(p.e, a.must) ? union(a.must, [p.v]) : a.must;
      return { may: union(a.may, [p.v]), must };
    }
    case 'values': {
      const must = new Set(p.vars.filter((v, i) => p.rows.length > 0 && p.rows.every(r => r[i] != null)));
      return { may: new Set(p.vars), must };
    }
    case 'service': case 'serviceVar': return scope(p.p);
    case 'subSelect': return selectScope(p.q);
    case 'empty': return { may: new Set(), must: new Set() };
    default: throw new Error(`scope: unknown pattern type ${p.type}`);
  }
}

/** Scope of a whole SELECT (its projected variables). */
export function selectScope(q) {
  const w = scope(q.pattern);
  if (q.select === 'all') return w;
  const may = new Set(), must = new Set();
  for (const it of q.select) {
    if (it.expr) {
      may.add(it.var);
      // COUNT always yields a number, even for an empty group.
      if (it.expr.e === 'aggregate' && it.expr.fn === 'count') must.add(it.var);
      else if (!q.groupBy && exprAlwaysBound(it.expr, w.must)) must.add(it.var);
    } else if (w.may.has(it.var) || (q.groupBy || []).some(g => g.var === it.var || g.alias === it.var)) {
      may.add(it.var);
      if (w.must.has(it.var)) must.add(it.var);
    }
  }
  return { may, must };
}

/** All variables an expression mentions (not descending into EXISTS). */
export function exprVars(e, out = new Set()) {
  if (!e) return out;
  if (e.e === 'var') out.add(e.name);
  if (e.e === 'bound') out.add(e.args?.[0]?.name ?? e.v);
  for (const c of exprChildren(e)) exprVars(c, out);
  return out;
}
