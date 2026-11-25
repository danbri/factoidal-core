// Write IR (see ir.mjs) back out as SPARQL text.
//
// The grammar (grammar.mjs) gives every step the SPARQL it stands for, so
// a page can show the query growing step by step and run any prefix of it.
// IRIs are written with the prefixes of names.mjs; `prefixesFor(text)`
// declares the ones a text uses (QLever needs them declared).
import { PREFIXES, compact } from './names.mjs';

const XSD = 'http://www.w3.org/2001/XMLSchema#';
const esc = (s) => String(s).replace(/\\/g, '\\\\').replace(/"/g, '\\"').replace(/\n/g, '\\n');
const LOCAL_OK = /^[A-Za-z0-9_](?:[A-Za-z0-9_.-]*[A-Za-z0-9_-])?$/;

export function iriText(iri) {
  const c = compact(iri);
  return c && (c.local === '' || LOCAL_OK.test(c.local)) ? `${c.prefix}:${c.local}` : `<${iri}>`;
}

export function litText(l) {
  if (l.lang) return `"${esc(l.lex)}"@${l.lang}`;
  if (!l.datatype || l.datatype === XSD + 'string') return `"${esc(l.lex)}"`;
  if (l.datatype === XSD + 'integer' && /^[+-]?\d+$/.test(l.lex)) return l.lex;
  return `"${esc(l.lex)}"^^${iriText(l.datatype)}`;
}

export function termText(t) {
  if (!t) return '[]';
  switch (t.t) {
    case 'var': return `?${t.name}`;
    case 'iri': return iriText(t.iri);
    case 'lit': return litText(t);
    case 'bnode': return `_:${String(t.id).replace(/\W/g, '_')}`;
    case 'any': return '?_';
    default: return '[]';
  }
}

const PREC = { alternative: 1, sequence: 2 };
export function pathText(p, outer = 0) {
  const wrap = (s, prec) => (prec < outer ? `(${s})` : s);
  switch (p.path) {
    case 'iri': return iriText(p.iri);
    case 'inverse': return `^${pathText(p.p, 3)}`;
    case 'sequence': return wrap(`${pathText(p.a, 2)}/${pathText(p.b, 2)}`, PREC.sequence);
    case 'alternative': return wrap(`${pathText(p.a, 1)}|${pathText(p.b, 1)}`, PREC.alternative);
    case 'zeroOrMore': return `${pathText(p.p, 3)}*`;
    case 'oneOrMore': return `${pathText(p.p, 3)}+`;
    case 'zeroOrOne': return `${pathText(p.p, 3)}?`;
    case 'negatedSet': return `!(${p.ps.map(x => (x.inverse ? '^' : '') + iriText(x.iri ?? x)).join('|')})`;
    default: return '<?>';
  }
}

const FN = {
  lang: 'LANG', str: 'STR', year: 'YEAR', month: 'MONTH', day: 'DAY', hours: 'HOURS', minutes: 'MINUTES', seconds: 'SECONDS',
  coalesce: 'COALESCE', contains: 'CONTAINS', strStarts: 'STRSTARTS', strEnds: 'STRENDS', strAfter: 'STRAFTER', strBefore: 'STRBEFORE',
  regex: 'REGEX', concat: 'CONCAT', iriFn: 'IRI', substr: 'SUBSTR', uCase: 'UCASE', lCase: 'LCASE', strLen: 'STRLEN',
  isBlank: 'isBLANK', isIri: 'isIRI', isLiteral: 'isLITERAL', isNumeric: 'isNUMERIC', replace: 'REPLACE', abs: 'ABS',
  round: 'ROUND', floor: 'FLOOR', ceil: 'CEIL', now: 'NOW', datatype: 'DATATYPE', md5: 'MD5', sha1: 'SHA1', sha256: 'SHA256',
  sha384: 'SHA384', sha512: 'SHA512', encodeForUri: 'ENCODE_FOR_URI', sameTerm: 'sameTerm', langMatches: 'LANGMATCHES',
  strLang: 'STRLANG', strDt: 'STRDT', tz: 'TZ', timezone: 'TIMEZONE', uuid: 'UUID', strUuid: 'STRUUID', rand: 'RAND', cond: 'IF',
};
const AGG = { count: 'COUNT', sum: 'SUM', min: 'MIN', max: 'MAX', avg: 'AVG', sample: 'SAMPLE', groupConcat: 'GROUP_CONCAT' };

export function exprSparql(e) {
  if (!e) return '?';
  const a = e.args || [];
  const T = exprSparql;
  switch (e.e) {
    case 'var': return `?${e.name}`;
    case 'iri': return iriText(e.iri);
    case 'lit': return litText(e.lit);
    case 'bool': return String(e.value);
    case 'num': return String(e.value);
    case 'decimal': case 'double': return e.lex;
    case 'compare': return `${T(a[0])} ${e.op} ${T(a[1])}`;
    case 'arith': return `(${T(a[0])} ${e.op} ${T(a[1])})`;
    case 'and': return `(${T(a[0])} && ${T(a[1])})`;
    case 'or': return `(${T(a[0])} || ${T(a[1])})`;
    case 'not': return `!(${T(a[0])})`;
    case 'unaryMinus': return `-${T(a[0])}`;
    case 'unaryPlus': return `+${T(a[0])}`;
    case 'bound': return `BOUND(?${e.name})`;
    case 'inList': return `${T(a[0])} IN (${(a[1] || []).map(T).join(', ')})`;
    case 'notInList': return `${T(a[0])} NOT IN (${(a[1] || []).map(T).join(', ')})`;
    case 'existsPat': return `EXISTS { ${patternText(e.p)} }`;
    case 'notExistsPat': return `NOT EXISTS { ${patternText(e.p)} }`;
    case 'functionCall': return `${iriText(e.iri)}(${a.map(T).join(', ')})`;
    case 'aggregate': {
      const sep = e.fn === 'groupConcat' && e.separator != null ? `; SEPARATOR="${esc(e.separator)}"` : '';
      return `${AGG[e.fn] || e.fn.toUpperCase()}(${e.distinct ? 'DISTINCT ' : ''}${e.arg ? T(e.arg) : '*'}${sep})`;
    }
    default: return `${FN[e.e] || e.e.toUpperCase()}(${a.filter(x => x != null).map(x => (Array.isArray(x) ? x.map(T).join(', ') : T(x))).join(', ')})`;
  }
}

export const tripleText = (tr) => `${termText(tr.s)} ${tr.p.t === 'iri' ? iriText(tr.p.iri) : termText(tr.p)} ${termText(tr.o)} .`;

/** A flattened element (explain.mjs flatten) as SPARQL. */
export function elemText(el) {
  switch (el.kind) {
    case 'triple': return tripleText(el.triple);
    case 'path': return `${termText(el.s)} ${pathText(el.path)} ${termText(el.o)} .`;
    case 'optional': return `OPTIONAL { ${patternText(el.p)}${el.cond && !(el.cond.e === 'bool' && el.cond.value) ? ` FILTER(${exprSparql(el.cond)})` : ''} }`;
    case 'minus': return `MINUS { ${patternText(el.p)} }`;
    case 'filter': return `FILTER(${exprSparql(el.cond)})`;
    case 'bind': return `BIND(${exprSparql(el.e)} AS ?${el.v})`;
    case 'union': return el.branches.map(b => `{ ${patternText(b)} }`).join(' UNION ');
    case 'values': return valuesText(el.vars, el.rows);
    case 'subselect': return `{ ${queryText(el.q)} }`;
    case 'service': return `SERVICE ${el.silent ? 'SILENT ' : ''}${termText(el.endpoint?.t ? el.endpoint : { t: 'iri', iri: el.endpoint })} { ${patternText(el.p)} }`;
    default: return '';
  }
}

function valuesText(vars, rows) {
  const one = vars.length === 1;
  const row = (r) => r.map(x => (x ? termText(x) : 'UNDEF')).join(' ');
  return one ? `VALUES ?${vars[0]} { ${rows.map(row).join(' ')} }`
    : `VALUES (${vars.map(v => '?' + v).join(' ')}) { ${rows.map(r => `(${row(r)})`).join(' ')} }`;
}

/** A group pattern's body, one element per line. */
export function patternText(p, flattenFn = flatLocal) {
  return flattenFn(p).map(elemText).filter(Boolean).join('\n');
}

// A local flatten (as explain.mjs's), so this module stands on its own.
function flatLocal(p) {
  switch (p.type) {
    case 'bgp': return p.triples.map(triple => ({ kind: 'triple', triple }));
    case 'propertyPath': return [{ kind: 'path', s: p.s, path: p.path, o: p.o }];
    case 'join': case 'lateral': return [...flatLocal(p.l), ...flatLocal(p.r)];
    case 'leftJoin': return [...flatLocal(p.l), { kind: 'optional', p: p.r, cond: p.cond }];
    case 'minus': return [...flatLocal(p.l), { kind: 'minus', p: p.r }];
    case 'filter': return [...flatLocal(p.p), { kind: 'filter', cond: p.cond }];
    case 'bind': return [...flatLocal(p.p), { kind: 'bind', e: p.e, v: p.v }];
    case 'union': { const arms = (x) => (x.type === 'union' ? [...arms(x.l), ...arms(x.r)] : [x]); return [{ kind: 'union', branches: arms(p) }]; }
    case 'values': return [{ kind: 'values', vars: p.vars, rows: p.rows }];
    case 'subSelect': return [{ kind: 'subselect', q: p.q }];
    case 'service': return [{ kind: 'service', endpoint: p.endpoint, silent: p.silent, p: p.p }];
    default: return [];
  }
}

/** A whole SELECT query (without prefixes). */
export function queryText(q) {
  const sel = q.select === 'all' ? '*' : q.select.map(it => (it.expr ? `(${exprSparql(it.expr)} AS ?${it.var})` : `?${it.var}`)).join(' ');
  const parts = [`SELECT ${q.distinct ? 'DISTINCT ' : q.reduced ? 'REDUCED ' : ''}${sel} WHERE {\n${indent(patternText(q.pattern))}\n}`];
  if (q.groupBy?.length) parts.push(`GROUP BY ${q.groupBy.map(g => (g.e === 'var' ? `?${g.name}` : g.var ? `?${g.var}` : `(${exprSparql(g.expr ?? g)})`)).join(' ')}`);
  if (q.having?.length) parts.push(`HAVING ${q.having.map(h => `(${exprSparql(h)})`).join(' ')}`);
  if (q.orderBy?.length) parts.push(`ORDER BY ${q.orderBy.map(o => `${o.dir === 'desc' ? 'DESC' : 'ASC'}(${exprSparql(o.expr)})`).join(' ')}`);
  if (q.limit != null) parts.push(`LIMIT ${q.limit}`);
  if (q.offset) parts.push(`OFFSET ${q.offset}`);
  return parts.join('\n');
}

export const indent = (s, by = '  ') => s.split('\n').map(l => by + l).join('\n');

/** PREFIX lines for the prefixes a text uses. */
export function prefixesFor(text) {
  const used = Object.keys(PREFIXES).filter(p => new RegExp(`(^|[\\s(/|^!{,])${p}:`).test(text));
  return used.map(p => `PREFIX ${p}: <${PREFIXES[p]}>`).join('\n');
}
