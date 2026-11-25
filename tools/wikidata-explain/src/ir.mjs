// The explainer's internal representation (IR) of a parsed SELECT query.
//
// It mirrors factoidal's Lean `SPARQL.Query` (L4Factoidal/SPARQL/Expr.lean,
// Algebra.lean, PropertyPath.lean) constructor for constructor, so an adapter
// from factoidal's JSON is close to the identity. Every IR node may carry
// `range: {start, end, origin}` once the parser supplies ranges
// (origin: 'exact' | 'derived' | 'synthetic').
//
// Terms (PatternTerm / Term):
//   {t:'var', name}            -- name without '?'
//   {t:'iri', iri}             -- full IRI; `pname` added when known
//   {t:'bnode', id}            -- syntax: '[]' | '_:label' | 'list' when known
//   {t:'lit', lex, datatype, lang, dir}
//   {t:'tripleTerm', s, p, o}
//
// Property paths (PropertyPath):
//   {path:'iri', iri} | {path:'inverse', p} | {path:'sequence', a, b}
//   {path:'alternative', a, b} | {path:'zeroOrMore', p} | {path:'oneOrMore', p}
//   {path:'zeroOrOne', p} | {path:'negatedSet', ps:[...]}
//
// Patterns (QueryPattern), field names as in Lean:
//   {type:'bgp', triples:[{s,p,o}]}
//   {type:'join', l, r}           {type:'leftJoin', l, r, cond}
//   {type:'filter', cond, p}      {type:'union', l, r}
//   {type:'minus', l, r}          {type:'graph', name, p}
//   {type:'lateral', l, r}        {type:'bind', e, v, p}
//   {type:'values', vars, rows}   -- rows: (term|null)[][]
//   {type:'service', endpoint, silent, p}
//   {type:'serviceVar', v, silent, p}
//   {type:'subSelect', q}
//   {type:'propertyPath', s, path, o}
//   {type:'empty'}
//
// Expressions (Expr): {e:'<ctor>', ...fields}; leaves
//   {e:'var', name} | {e:'iri', iri} | {e:'lit', ...} | {e:'bool', value}
//   | {e:'num', value} | {e:'decimal', lex} | {e:'double', lex}
//   aggregate: {e:'aggregate', fn, distinct, arg, separator?}
//   exists:    {e:'existsPat', p} | {e:'notExistsPat', p}
//   others:    {e:'<ctor>', args:[...]} in Lean argument order
//
// Query:
//   {select: 'all' | [{var} | {expr, var}], dataset, pattern, groupBy,
//    having, orderBy: [{dir:'asc'|'desc', expr}], distinct, reduced,
//    offset, limit, postValues}

export const PATTERN_CHILDREN = {
  bgp: [], join: ['l', 'r'], leftJoin: ['l', 'r'], filter: ['p'],
  union: ['l', 'r'], minus: ['l', 'r'], graph: ['p'], lateral: ['l', 'r'],
  bind: ['p'], values: [], service: ['p'], serviceVar: ['p'],
  subSelect: [], propertyPath: [], empty: [],
};

/** Child expressions of an expression node. */
export function exprChildren(x) {
  if (!x || typeof x !== 'object') return [];
  switch (x.e) {
    case 'var': case 'iri': case 'lit': case 'bool': case 'num':
    case 'decimal': case 'double': case 'existsPat': case 'notExistsPat':
      return [];
    case 'aggregate': return x.arg ? [x.arg] : [];
    default: return (x.args || []).flatMap(a => Array.isArray(a) ? a : [a]).filter(a => a && a.e);
  }
}

/** Visit every pattern node, depth-first, with its path from the root. */
export function walkPatterns(p, fn, path = '') {
  if (!p) return;
  fn(p, path);
  for (const k of PATTERN_CHILDREN[p.type] || []) walkPatterns(p[k], fn, `${path}/${p.type}.${k}`);
  if (p.type === 'subSelect') walkPatterns(p.q.pattern, fn, `${path}/subSelect.q`);
}
