// Build the structured explanation record (SPEC §3) from an IR query.
// Every element of the query is either handled by a describer or listed in
// `unexplained`; every caveat names its rule.

import { scope, selectScope, exprVars } from './scope.mjs';
import { compact } from './names.mjs';

const RDFS_LABEL = 'http://www.w3.org/2000/01/rdf-schema#label';
const SCHEMA_DESC = 'http://schema.org/description';
const P31 = 'http://www.wikidata.org/prop/direct/P31';
const P279 = 'http://www.wikidata.org/prop/direct/P279';
// F-HIERARCHY-PROPS (editorial list; data/wikidata-facts.json)
const HIERARCHY = new Set(['P131', 'P361', 'P279', 'P171', 'P276']);

// ---------------------------------------------------------------- flattening

/** Flatten a group graph pattern into its elements, in source order. */
export function flatten(p) {
  switch (p.type) {
    case 'bgp': return p.triples.map(triple => ({ kind: 'triple', triple }));
    case 'propertyPath': return [{ kind: 'path', s: p.s, path: p.path, o: p.o }];
    case 'join': case 'lateral': return [...flatten(p.l), ...flatten(p.r)];
    case 'leftJoin': return [...flatten(p.l), { kind: 'optional', p: p.r, cond: p.cond }];
    case 'minus': return [...flatten(p.l), { kind: 'minus', p: p.r }];
    case 'filter': return [...flatten(p.p), { kind: 'filter', cond: p.cond }];
    case 'bind': return [...flatten(p.p), { kind: 'bind', e: p.e, v: p.v }];
    case 'union': return [{ kind: 'union', branches: unionArms(p) }];
    case 'values': return [{ kind: 'values', vars: p.vars, rows: p.rows }];
    case 'subSelect': return [{ kind: 'subselect', q: p.q }];
    case 'service': return [{ kind: 'service', endpoint: p.endpoint, silent: p.silent, p: p.p }];
    case 'empty': return [];
    default: return [{ kind: 'other', node: p }];
  }
}
const unionArms = (p) => p.type === 'union' ? [...unionArms(p.l), ...unionArms(p.r)] : [p];
const isTrueCond = (c) => !c || (c.e === 'bool' && c.value === true);

// ------------------------------------------------------- label scaffolding

const LABEL_VALUE = /^(.*)__label_value$/;
const DESC_VALUE = /^(.*)__description_value$/;
const LABEL_SUBJECT = /^(.*)__label_subject$/;

/** The language in FILTER(lang(?v) = "x"), if the filter is exactly that. */
function langEq(cond) {
  if (cond?.e !== 'compare' || cond.op !== '=') return null;
  const [a, b] = cond.args;
  if (a?.e === 'lang' && a.args[0]?.e === 'var' && b?.e === 'lit') return { v: a.args[0].name, lang: b.lit.lex };
  return null;
}

/** Recognise the Factoidal label-service rewrite; returns {labels, consumed}. */
export function recogniseLabels(elems) {
  const labels = {}; // base var -> {subject, labelLangs, descLangs, labelCol, descCol}
  const consumed = new Set();
  const get = (b) => (labels[b] ||= { base: b, labelLangs: [], descLangs: [] });
  elems.forEach((el, i) => {
    if (el.kind === 'optional') {
      const inner = flatten(el.p);
      const tr = inner.find(x => x.kind === 'triple');
      const f = inner.find(x => x.kind === 'filter');
      const eq = langEq(isTrueCond(el.cond) ? f?.cond : el.cond);
      const size = isTrueCond(el.cond) ? 2 : 1;
      if (inner.length === size && tr && eq && tr.triple.o.t === 'var' && tr.triple.p.t === 'iri') {
        const lv = LABEL_VALUE.exec(tr.triple.o.name), dv = DESC_VALUE.exec(tr.triple.o.name);
        if (lv && tr.triple.p.iri === RDFS_LABEL) { get(lv[1]).labelLangs.push(eq.lang); consumed.add(i); }
        else if (dv && tr.triple.p.iri === SCHEMA_DESC) { get(dv[1]).descLangs.push(eq.lang); consumed.add(i); }
      }
    } else if (el.kind === 'bind') {
      const s = LABEL_SUBJECT.exec(el.v);
      if (s) { consumed.add(i); return; }
      const used = [...exprVars(el.e)];
      const lv = used.map(v => LABEL_VALUE.exec(v)).find(Boolean);
      const dv = used.map(v => DESC_VALUE.exec(v)).find(Boolean);
      if (lv && el.e.e === 'cond') { const L = get(lv[1]); L.labelCol = el.v; L.subject = lv[1]; consumed.add(i); }
      else if (dv && el.e.e === 'var') { const L = get(dv[1]); L.descCol = el.v; L.subject = dv[1]; consumed.add(i); }
    }
  });
  return { labels: Object.values(labels), consumed };
}

// ------------------------------------------------------------------- helpers

const termVar = (t) => (t && t.t === 'var' ? t.name : null);
const isAnon = (t) => t && t.t === 'bnode';
const termVarsOf = (t) => (t?.t === 'var' ? [t.name] : []);
const aOrAn = (w) => (/^[aeiou]/i.test(w) ? 'an' : 'a');

function elementVars(el) {
  switch (el.kind) {
    case 'triple': return [el.triple.s, el.triple.p, el.triple.o].flatMap(termVarsOf);
    case 'path': return [el.s, el.o].flatMap(termVarsOf);
    case 'bind': return [el.v];
    case 'values': return el.vars;
    case 'union': return [...new Set(el.branches.flatMap(b => [...scope(b).may]))];
    case 'subselect': return [...selectScope(el.q).may];
    case 'service': return [...scope(el.p).may];
    default: return [];
  }
}

/** Is predicate IRI functional subject→object here (one value per subject)? */
function functionalForward(iri, o, langFiltered) {
  const c = compact(iri);
  if (!c) return false;
  if (c.prefix === 'ps' || c.prefix === 'psv') return true;                  // F-PS-UNIQUE
  if ((iri === RDFS_LABEL || iri === SCHEMA_DESC) && langFiltered.has(o)) return true; // F-LABEL-UNIQUE
  const k = `${c.prefix}:${c.local}`;
  return ['schema:about', 'schema:isPartOf', 'schema:inLanguage', 'schema:name', 'wikibase:rank',
    'wikibase:propertyType', 'wikibase:directClaim', 'wikibase:sitelinks', 'wikibase:statements',
    'wikibase:identifiers'].includes(k);
}
/** Functional object→subject? */
function functionalInverse(iri) {
  const c = compact(iri);
  if (!c) return false;
  if (c.prefix === 'p') return true; // a statement node belongs to one item
  return ['wikibase:directClaim'].includes(`${c.prefix}:${c.local}`);
}

// -------------------------------------------------------------- multiplicity

/**
 * Which variables are NOT determined by `unit`; each such variable (or
 * hidden intermediate) can multiply rows for a fixed unit.
 * @returns {Array<{var:string|null, why:string, el:object}>}
 */
function repeaters(elems, unit, langFiltered, labelsConsumed, withOptional = false) {
  const det = new Set(unit);
  const base = withOptional
    ? elems.flatMap((el, i) => labelsConsumed.has(i) ? [] : el.kind === 'optional' ? flatten(el.p) : [el])
    : elems.filter((el, i) => !labelsConsumed.has(i));
  const required = base.filter(el => ['triple', 'path', 'bind', 'values', 'union', 'subselect'].includes(el.kind));
  let changed = true;
  while (changed) {
    changed = false;
    for (const el of required) {
      if (el.kind === 'triple') {
        const s = termVar(el.triple.s), o = termVar(el.triple.o), pIri = el.triple.p.iri;
        if (el.triple.p.t !== 'iri') continue;
        if (s && o && det.has(s) && !det.has(o) && functionalForward(pIri, o, langFiltered)) { det.add(o); changed = true; }
        if (s && o && det.has(o) && !det.has(s) && functionalInverse(pIri)) { det.add(s); changed = true; }
      } else if (el.kind === 'bind') {
        if (!det.has(el.v) && [...exprVars(el.e)].every(v => det.has(v))) { det.add(el.v); changed = true; }
      } else if (el.kind === 'values' && el.rows.length === 1) {
        for (const v of el.vars) if (!det.has(v)) { det.add(v); changed = true; }
      }
    }
  }
  const close = () => {
    let ch = true;
    while (ch) {
      ch = false;
      // F-SITELINK-UNIQUE: ?page schema:about ?x ; schema:isPartOf <wiki>  — one page per x per wiki
      for (const el of required) if (el.kind === 'triple' && el.triple.p.iri === 'http://schema.org/about') {
        const pg = termVar(el.triple.s), x = termVar(el.triple.o);
        if (pg && x && det.has(x) && !det.has(pg) && required.some(o => o.kind === 'triple' && termVar(o.triple.s) === pg &&
            o.triple.p.iri === 'http://schema.org/isPartOf' && o.triple.o.t === 'iri')) { det.add(pg); ch = true; }
      }
      for (const el of required) if (el.kind === 'triple' && el.triple.p.t === 'iri') {
        const s = termVar(el.triple.s), o = termVar(el.triple.o);
        if (s && o && det.has(s) && !det.has(o) && functionalForward(el.triple.p.iri, o, langFiltered)) { det.add(o); ch = true; }
        if (s && o && det.has(o) && !det.has(s) && functionalInverse(el.triple.p.iri)) { det.add(s); ch = true; }
      } else if (el.kind === 'bind' && !det.has(el.v) && [...exprVars(el.e)].every(v => det.has(v))) { det.add(el.v); ch = true; }
    }
  };
  close();
  const out = [];
  for (const el of required) {
    if (el.kind === 'triple') {
      const { s, p, o } = el.triple;
      for (const t of [s, p, o]) {
        const v = termVar(t);
        if (v && !det.has(v)) { out.push({ var: v, el }); det.add(v); close(); }
        if (isAnon(t) && t !== s) out.push({ var: null, anon: true, el });
      }
    } else if (el.kind === 'path') {
      for (const t of [el.s, el.o]) { const v = termVar(t); if (v && !det.has(v)) out.push({ var: v, el }); }
      if (el.path.path === 'sequence') out.push({ var: null, intermediate: true, el });
    } else if (el.kind === 'values') {
      for (const v of el.vars) if (!det.has(v)) out.push({ var: v, el });
    } else if (el.kind === 'union') {
      out.push({ var: null, union: true, el });
      for (const b of el.branches) for (const r of repeaters(flatten(b), [...det], langFiltered, new Set()))
        if (!r.var || !det.has(r.var)) out.push({ ...r, inUnion: true });
    }
  }
  // de-duplicate by var
  const seen = new Set();
  return out.filter(r => { const k = r.var ?? JSON.stringify(r.el).slice(0, 200) + (r.intermediate ? 'i' : r.union ? 'u' : 'a'); if (seen.has(k)) return false; seen.add(k); return true; });
}

// ------------------------------------------------------------------- explain

/**
 * @param {object} q IR query
 * @param {{names, comments, rewrites, status, id, title, audit}} ctx
 */
export function explainQuery(q, ctx) {
  const N = ctx.names;
  const rec = {
    id: ctx.id, title: ctx.title, explained_query: 'lean_replacement_query',
    row: null, columns: [], required: [], optional: [], excluded: [], filters: [],
    grouping: null, ordering: [], limit: q.limit, offset: q.offset, distinct: q.distinct,
    display: null, labels: [], subqueries: [], external: [], caveats: [],
    translation_notes: [], author_comments: [], unexplained: [],
  };
  const cav = (rule, severity, precise, extra = {}) => rec.caveats.push({ rule, severity, precise, ...extra });

  const elems = flatten(q.pattern);
  const { labels, consumed } = recogniseLabels(elems);
  rec.labels = labels.map(L => ({ subject: L.subject || L.base, column: L.labelCol, description_column: L.descCol,
    label_languages: L.labelLangs, description_languages: L.descLangs }));

  // Vars with an equality-on-lang filter in the same group (for F-LABEL-UNIQUE).
  const langFiltered = new Set(elems.filter(e => e.kind === 'filter').map(e => langEq(e.cond)?.v).filter(Boolean));

  const sc = scope(q.pattern);
  // A rewritten label column falls back to the entity ID, so it has a value
  // whenever its subject does.
  for (const L of labels) if (L.labelCol && sc.must.has(L.subject || L.base)) sc.must.add(L.labelCol);
  const truthyProps = new Set();
  // Single-variable VALUES of IRIs: a predicate variable listed there means
  // "one of these properties", not "any property".
  const valuesIris = {};
  for (const el of elems) if (el.kind === 'values' && el.vars.length === 1 && el.rows.every(r => r[0]?.t === 'iri'))
    valuesIris[el.vars[0]] = el.rows.map(r => r[0].iri);
  N.valuesIris = valuesIris;
  // Variables known to hold literals (objects of label-like or literal-valued properties).
  const literalVars = new Set();
  for (const el of elems) if (el.kind === 'triple' && el.triple.o.t === 'var' && el.triple.p.t === 'iri') {
    const id = N.wikidataId(el.triple.p.iri);
    const dt = id && N.entity(id)?.datatype;
    if ([RDFS_LABEL, SCHEMA_DESC, 'http://www.w3.org/2004/02/skos/core#altLabel'].includes(el.triple.p.iri) ||
        (compact(el.triple.p.iri)?.prefix === 'wdt' && ['monolingualtext', 'string', 'external-id'].includes(dt)))
      literalVars.add(el.triple.o.name);
  }

  // ---- describe each element
  elems.forEach((el, i) => {
    if (consumed.has(i)) return;
    switch (el.kind) {
      case 'triple': rec.required.push(describeTriple(el.triple, N, truthyProps, cav)); break;
      case 'path': rec.required.push(describePath(el, N, truthyProps, cav)); break;
      case 'optional': {
        const inner = flatten(el.p);
        const vs = [...scope(el.p).may].filter(v => !sc.must.has(v));
        rec.optional.push({
          rule: 'R-OPTIONAL',
          parts: inner.map(x => describeAny(x, N, truthyProps, cav, rec)),
          blank_if_absent: vs,
          text: `${vs.map(v => '?' + v).join(', ') || 'nothing new'} filled in if ${inner.map(x => describeAny(x, N, truthyProps, cav, rec).text).join('; ')}, otherwise left blank`,
        });
        if (!isTrueCond(el.cond)) rec.optional[rec.optional.length - 1].text += ` (only where ${exprText(el.cond, N)})`;
        if (inner.some(x => x.kind === 'triple' && x.triple.p.iri === 'http://schema.org/isPartOf' && x.triple.o.t === 'iri'))
          rec.optional[rec.optional.length - 1].text += ' — at most one such page per wiki (F-SITELINK-UNIQUE)';
        break;
      }
      case 'minus': {
        const r = scope(el.p).may;
        const left = scopeOfPrefix(elems, i);
        const shared = [...r].filter(v => left.may.has(v));
        const inner = flatten(el.p).map(x => describeAny(x, N, truthyProps, cav, rec));
        rec.excluded.push({ rule: shared.length ? 'R-MINUS' : 'R-MINUS-NOSHARED', shared, parts: inner,
          text: shared.length
            ? `excludes any result for which [${inner.map(x => x.text).join('; ')}] also holds, matching on ${shared.map(v => '?' + v).join(', ')}`
            : `this exclusion has no effect: it shares no variables with the rest of the query` });
        if (!shared.length) cav('R-MINUS-NOSHARED', 'changes_answer', 'A MINUS clause shares no variables with the rest of the query, so it removes nothing.');
        break;
      }
      case 'filter': {
        const c = el.cond;
        if (c.e === 'notExistsPat' || (c.e === 'not' && c.args[0]?.e === 'existsPat')) {
          const p = c.e === 'notExistsPat' ? c.p : c.args[0].p;
          const corr = [...patternVarsAll(p)].filter(v => sc.may.has(v));
          const innerLang = flatten(p).find(x => x.kind === 'filter' && x.cond.e === 'compare' && x.cond.op === '=' && x.cond.args[0]?.e === 'lang');
          if (innerLang) cav('R-LABEL-EXACT', 'scope', `Only a label whose language tag is exactly ${exprText(innerLang.cond.args[1], N)} counts; a "mul" (multilingual) label does not (F-MUL).`);
          const inner = flatten(p).map(x => describeAny(x, N, truthyProps, cav, rec));
          rec.excluded.push({ rule: 'R-NOTEXISTS', correlated_on: corr, parts: inner,
            text: `keeps a result only if there is no way to satisfy [${inner.map(x => x.text).join('; ')}] with this result's ${corr.map(v => '?' + v).join(', ')}` });
        } else {
          rec.filters.push({ rule: 'R-FILTER', text: `keeps only results where ${exprText(c, N)}` });
          const le = langEq(c);
          if (le) cav('R-LABEL-EXACT', 'scope', `?${le.v} must have language tag exactly "${le.lang}"; variants such as "${le.lang}-gb" and "mul" do not match.`);
        }
        break;
      }
      case 'bind':
        rec.required.push({ rule: 'R-BIND', text: `?${el.v} is ${exprText(el.e, N)}` });
        if (usesFn(el.e, 'year')) cav('R-YEAR', 'scope', `?${el.v} is a year taken from a date. Wikidata dates known only to the year still look like full dates (F-DATE-PRECISION), so the year is reliable but finer parts may not be.`);
        break;
      case 'values':
        if (valuesIris[el.vars[0]] && el.vars.length === 1 && elems.some(x => x.kind === 'triple' && x.triple.p.t === 'var' && x.triple.p.name === el.vars[0])) break;
        rec.required.push({ rule: 'R-VALUES', text: `${el.vars.map(v => '?' + v).join(', ')} take${el.vars.length > 1 ? '' : 's'} each of: ${el.rows.map(r => r.map(t => t ? termText(t, N) : 'UNDEF').join(' / ')).join('; ')}` });
        break;
      case 'union': {
        const arms = el.branches.map(b => flatten(b).map(x => describeAny(x, N, truthyProps, cav, rec).text).join('; '));
        rec.required.push({ rule: 'R-UNION', text: `either ${arms.map(a => `[${a}]`).join(' or ')}` });
        break;
      }
      case 'subselect': {
        const sub = explainQuery(el.q, { ...ctx, nested: true });
        rec.subqueries.push(sub);
        rec.required.push({ rule: 'R-SUBQUERY', text: `joined with a separately computed table of ${columnsText(el.q)} (see subquery ${rec.subqueries.length})` });
        rec.caveats.push(...sub.caveats.map(c => ({ ...c, in_subquery: rec.subqueries.length })));
        break;
      }
      case 'service': {
        rec.external.push({ rule: 'R-EXTERNAL', endpoint: el.endpoint });
        cav('R-EXTERNAL', 'changes_answer', `Part of the query is sent to ${el.endpoint} at query time; its results depend on that service.`);
        break;
      }
      default:
        rec.unexplained.push({ what: el.kind, node: el.node?.type });
    }
  });

  // ---- join drops: subquery outputs matched by a later triple
  const subOut = new Set(elems.filter(e => e.kind === 'subselect').flatMap(e => [...selectScope(e.q).may]));
  const joinDropVars = new Set();
  for (const el of elems) if (el.kind === 'triple' && el.triple.p.t === 'iri' && el.triple.o.t === 'var' && subOut.has(el.triple.o.name) && el.triple.s.t === 'var' && !subOut.has(el.triple.s.name)) {
    const v = el.triple.o.name, sv = el.triple.s.name, id = N.wikidataId(el.triple.p.iri);
    joinDropVars.add(v); joinDropVars.add(sv);
    cav('R-JOIN-DROP', 'changes_answer', `Each ?${v} from the subquery is kept only if some ?${sv} has ${id ? N.idName(id) : N.iri(el.triple.p.iri)} exactly equal to it; values with no such ?${sv} disappear from the results, and a value shared by several ?${sv} repeats.`);
  }

  // ---- truthy summary (stated once)
  if (truthyProps.size) cav('R-TRUTHY', 'scope',
    `Uses only best-ranked values (F-RANK) of ${[...truthyProps].map(p => N.iri(p)).join(', ')}: preferred-rank statements if any exist, otherwise normal-rank; deprecated statements are ignored.`);

  // ---- columns
  const proj = q.select === 'all' ? [...sc.may].map(v => ({ var: v })) : q.select;
  for (const it of proj) {
    const L = labels.find(l => l.labelCol === it.var || l.descCol === it.var);
    if (L) {
      const isDesc = L.descCol === it.var;
      rec.columns.push({ var: it.var, kind: isDesc ? 'description' : 'label', of: L.subject || L.base,
        text: isDesc
          ? `the description of ?${L.subject || L.base} in the first of ${L.descLangs.join(', ')} that has one; blank otherwise`
          : `the label of ?${L.subject || L.base} in the first of ${L.labelLangs.join(', ')} that has one; otherwise its ID` });
      continue;
    }
    if (it.expr) {
      if (usesFn(it.expr, 'year')) cav('R-YEAR', 'scope', `?${it.var} is a year taken from a date. Wikidata dates known only to the year still look like full dates (F-DATE-PRECISION), so the year is reliable but finer parts may not be.`);
      let t = exprText(it.expr, N);
      const av = it.expr.e === 'aggregate' && it.expr.arg?.e === 'var' ? it.expr.arg.name : null;
      if (av && !sc.may.has(av)) t += ' — always blank (R-SCOPE-LEAK)';
      else if (av && !sc.must.has(av) && it.expr.fn !== 'count') t += ` — blank for a group where ?${av} never has a value`;
      rec.columns.push({ var: it.var, kind: it.expr.e === 'aggregate' ? 'aggregate' : 'expression', text: t });
      continue;
    }
    const bindEl = elems.find(el => el.kind === 'bind' && el.v === it.var);
    const litBound = bindEl && ['lang', 'str'].includes(bindEl.e.e) && bindEl.e.args[0]?.e === 'var' && literalVars.has(bindEl.e.args[0].name) && sc.must.has(bindEl.e.args[0].name);
    const mayBlank = !sc.must.has(it.var) && !litBound;
    const neverBound = !sc.may.has(it.var) && !(q.groupBy || []).some(g => g.alias === it.var);
    rec.columns.push({ var: it.var, kind: 'value', may_be_blank: mayBlank, never_bound: neverBound });
  }

  // ---- scope leak: projected / aggregated vars bound only inside MINUS / EXISTS
  const negVars = new Set();
  elems.forEach(el => {
    if (el.kind === 'minus') for (const v of scope(el.p).may) negVars.add(v);
    if (el.kind === 'filter') for (const v of existsVars(el.cond)) negVars.add(v);
  });
  const usedOutside = new Set();
  for (const it of proj) { if (it.expr) exprVars(it.expr, usedOutside); else usedOutside.add(it.var); }
  for (const o of q.orderBy || []) exprVars(o.expr, usedOutside);
  for (const v of usedOutside) {
    if (!sc.may.has(v) && negVars.has(v)) {
      const col = proj.find(it => it.var === v || (it.expr && exprVars(it.expr).has(v)));
      cav('R-SCOPE-LEAK', 'changes_answer',
        `?${v} is never set: its only value is inside an exclusion (MINUS / NOT EXISTS), which does not pass values out. So ${col ? '?' + col.var : 'it'} is always blank.`);
    }
  }

  // ---- grouping and aggregates
  const aggs = proj.filter(it => it.expr?.e === 'aggregate');
  const groupKeys = (q.groupBy || []).map(g => g.var ?? g.alias).filter(Boolean);
  if (q.groupBy || aggs.length) {
    rec.grouping = { keys: groupKeys, aggregates: aggs.map(a => ({ var: a.var, fn: a.expr.fn, distinct: a.expr.distinct })),
      having: (q.having || []).map(h => exprText(h, N)) };
    if ((q.having || []).length) cav('R-HAVING', 'scope', `Only groups where ${q.having.map(h => exprText(h, N)).join(' and ')} are kept.`);
    if (groupKeys.length > 1) {
      const main = groupKeys[0];
      const labelSubj = Object.fromEntries(labels.filter(L => L.labelCol).map(L => [L.labelCol, L.subject || L.base]));
      const reps = repeaters(elems, [main], langFiltered, consumed, true);
      const notDet = new Set(reps.map(r => r.var).filter(Boolean));
      for (const k of groupKeys.slice(1)) {
        const src = labelSubj[k] || k;
        if (notDet.has(src)) cav('R-GROUP-KEY-MULT', 'changes_answer', `Grouping is by ${groupKeys.map(g => '?' + g).join(', ')}, so a ?${main} with several ?${src} values appears once for each${src !== k ? ` (each distinct ?${k})` : ''}.`);
      }
    }
    for (const k of groupKeys) if (labels.some(L => L.labelCol === k && !groupKeys.includes(L.subject || L.base))) {
      cav('R-GROUP-BY-LABEL', 'changes_answer', `Grouping includes the label column ?${k}; things with identical labels are merged into one group.`);
    }
  }
  for (const a of aggs) {
    const { fn, distinct, arg } = a.expr;
    if (fn === 'sample' && !(arg?.e === 'var' && !sc.may.has(arg.name))) cav('R-SAMPLE', 'scope', `?${a.var} is one value of ${exprText(arg, N)} chosen arbitrarily from each group; which one may vary between runs and endpoints.`);
    if (fn === 'groupConcat') cav('R-GROUPCONCAT', 'display', `?${a.var} joins all values in the group with "${a.expr.separator ?? ' '}", in no guaranteed order.`);
    if (fn === 'count' && distinct) cav('R-COUNT-DISTINCT', 'scope', `?${a.var} counts distinct values of ${exprText(arg, N)}.`);
    if (fn === 'count' && !distinct) {
      const argVar = arg?.e === 'var' ? arg.name : null;
      const unit = [...groupKeys, ...(argVar ? [argVar] : [])];
      const reps = repeaters(elems, unit, langFiltered, consumed)
        .filter(r => !(r.var && r.var === argVar));
      const stmtRep = reps.find(r => r.var && r.el.kind === 'triple' && termVar(r.el.triple.o) === r.var && compact(r.el.triple.p.iri || '')?.prefix === 'p');
      if (stmtRep) cav('R-COUNT-STMTS', 'changes_answer', `?${a.var} counts statements, not ${argVar ? '?' + argVar : 'items'}: ${argVar ? '?' + argVar : 'an item'} is counted once for each ${N.idName(N.wikidataId(stmtRep.el.triple.p.iri))} statement (?${stmtRep.var}) that qualifies.`);
      const others = reps.filter(r => r !== stmtRep);
      if (others.length) cav('R-COUNT-ROWS', 'changes_answer',
        `?${a.var} counts matching rows, not distinct ${argVar ? '?' + argVar : 'things'}. ${argVar ? '?' + argVar : 'A thing'} is counted once for each ${others.map(r => repeaterText(r, N)).join(', and each ')}.`,
        { repeat_reasons: others.map(r => repeaterText(r, N)) });
    }
  }

  // ---- row multiplicity for plain SELECT (no aggregation)
  if (!q.groupBy && !aggs.length) {
    const unit = proj.map(it => it.var);
    const LOSSY = ['year', 'month', 'day', 'hours', 'lang', 'substr', 'strBefore', 'strAfter', 'round', 'floor', 'ceil', 'lCase', 'uCase', 'strLen', 'compare', 'and', 'or', 'not', 'bound', 'isIri', 'isLiteral', 'isBlank', 'aggregate'];
    const lossy = (e) => e && (LOSSY.includes(e.e) || (e.args || []).some(a => a && a.e && lossy(a)));
    const sources = [...proj.filter(it => it.expr).map(it => it.expr),
      ...elems.filter((el, i) => !consumed.has(i) && el.kind === 'bind' && unit.includes(el.v)).map(el => el.e)];
    for (const e of sources) if (!lossy(e)) for (const v of exprVars(e)) unit.push(v);
    const reps = repeaters(elems, unit, langFiltered, consumed).filter(r => !r.var || (!unit.includes(r.var) && !joinDropVars.has(r.var)));
    // one entity, several rows: projected values not determined by the first projected variable
    const main = unit[0];
    const mainIsDerived = labels.some(L => L.labelCol === main || L.descCol === main) || proj[0]?.expr || elems.some(el => el.kind === 'bind' && el.v === main);
    const labelOf = new Set(labels.filter(L => (L.subject || L.base) === main).flatMap(L => [L.labelCol, L.descCol]));
    const projNames = proj.map(it => it.var);
    const perEntity = repeaters(elems, [main], langFiltered, consumed, true)
      .filter(r => r.var && projNames.includes(r.var) && !labelOf.has(r.var));
    const exprCols = proj.filter(it => it.expr).map(it => ({ col: it.var, vs: [...exprVars(it.expr)] }));
    const bindCols = elems.filter((el, i) => !consumed.has(i) && el.kind === 'bind' && unit.includes(el.v)).map(el => ({ col: el.v, vs: [...exprVars(el.e)] }));
    const multi = new Set(perEntity.map(r => r.var));
    for (const r of repeaters(elems, [main], langFiltered, consumed, true)) if (r.var)
      for (const c of [...exprCols, ...bindCols]) if (c.vs.includes(r.var)) multi.add(c.col);
    for (const L of labels) if (L.labelCol && projNames.includes(L.labelCol) && (L.subject || L.base) !== main &&
      repeaters(elems, [main], langFiltered, consumed, true).some(r => r.var === (L.subject || L.base))) multi.add(L.labelCol);
    for (const v of [...multi]) if (!projNames.includes(v)) multi.delete(v);
    multi.delete(main);
    if (multi.size && !mainIsDerived) cav('R-MULT-PER-ENTITY', 'scope', `A ?${main} can appear in several rows: once for each value of ${[...multi].map(v => '?' + v).join(', ')}${q.distinct ? ' (DISTINCT removes only rows that are identical in every column)' : ''}.`);
    if (!q.distinct && reps.length) {
      cav('R-MULT-DUP', 'changes_answer', `Identical rows can appear more than once: one for each ${reps.map(r => repeaterText(r, N)).join(', and each ')}.`,
        { repeat_reasons: reps.map(r => repeaterText(r, N)) });
    }
  }

  // ---- ordering and limits
  for (const o of q.orderBy || []) {
    const t = exprText(o.expr, N);
    rec.ordering.push({ dir: o.dir, key: t });
    const vs = [...exprVars(o.expr)];
    const canBeBlank = vs.some(v => !sc.must.has(v)) && !aggs.some(a => a.var === vs[0] && a.expr.fn === 'count');
    if (canBeBlank) cav('R-ORDER-UNBOUND', 'display', `Rows where ${t} is blank sort ${o.dir === 'asc' ? 'first' : 'last'}.`);
  }
  if (q.limit != null && !(q.orderBy || []).length) cav('R-LIMIT-NOORDER', 'changes_answer', `Only ${q.limit} rows are returned, chosen arbitrarily (there is no ORDER BY).`);

  // ---- deleted / redirected IDs anywhere in the query
  for (const iri of allIris(q)) {
    const id = N.wikidataId(iri); if (!id) continue;
    const e = N.entity(id);
    if (e?.missing) cav('R-DELETED-ID', 'changes_answer', `${id} no longer exists on Wikidata, so the part of the query using it matches nothing.`);
    else if (e?.redirected_to) cav('R-REDIRECT-ID', 'changes_answer', `${id} is now a redirect to ${N.idName(e.redirected_to)}; data recorded on the target is not found through ${id} (F-REDIRECT).`);
  }

  // ---- row meaning
  rec.row = rowMeaning(q, proj, aggs, groupKeys);
  if (ctx.nested) return dedupeCaveats(rec);

  // ---- item descriptions (first mention) and same-label items
  rec.glossary = {};
  const byLabel = N.labelIndex();
  for (const iri of allIris(q)) {
    const id = N.wikidataId(iri);
    if (!id || !id.startsWith('Q')) continue;
    const e = N.entity(id);
    if (e?.description) rec.glossary[id] = e.description;
    const twins = (e?.label ? byLabel.get(e.label.toLowerCase()) || [] : []).filter(x => x !== id && x.startsWith('Q'));
    if (twins.length) cav('R-AMBIGUOUS-LABEL', 'scope',
      `Several items are labelled "${e.label}". This query uses ${id} (${e.description || 'no description'}), not ${twins.map(t => `${t} (${N.entity(t)?.description || 'no description'})`).join(', or ')}.`);
  }

  // ---- context: comments, display, translation notes, audit
  for (const c of ctx.comments || []) {
    if (c.kind === 'directive' && c.name === 'title') rec.title_directive = c.value;
    else if (c.kind === 'directive' && c.name === 'defaultView') rec.display = { rule: 'R-VIEW', view: c.parsed?.view, options: c.parsed?.options };
    else if (c.kind === 'comment') rec.author_comments.push({ line: c.line, text: c.text.trim(), content: c.content, after: c.codeBefore });
  }
  for (const r of ctx.rewrites || []) rec.translation_notes.push({ rule: `${r.rule_id}/${r.variant_id}` });
  if (ctx.audit && ctx.audit.trials?.[0] && ctx.audit.trials[0].results_match === false) {
    const t = ctx.audit.trials[0];
    rec.translation_notes.push({ rule: 'endpoint_audit', text: `When tested on ${ctx.audit.date}, this version returned ${t.qlever.rows} rows against ${t.blazegraph.rows} for the original, and the rows did not match.` });
  }
  return dedupeCaveats(rec);
}

function dedupeCaveats(rec) {
  const seen = new Set();
  rec.caveats = rec.caveats.filter(c => { const k = c.rule + c.precise; if (seen.has(k)) return false; seen.add(k); return true; });
  return rec;
}

function scopeOfPrefix(elems, i) {
  const may = new Set();
  for (const el of elems.slice(0, i)) for (const v of elementVars(el)) may.add(v);
  return { may };
}
function patternVarsAll(p, out = new Set()) {
  for (const v of scope(p).may) out.add(v);
  for (const el of flatten(p)) {
    if (el.kind === 'filter') exprVars(el.cond, out);
    if (el.kind === 'bind') exprVars(el.e, out);
    if (el.kind === 'optional') { patternVarsAll(el.p, out); exprVars(el.cond, out); }
    if (el.kind === 'minus') patternVarsAll(el.p, out);
  }
  return out;
}
function existsVars(e, out = new Set()) {
  if (!e) return out;
  if (e.e === 'existsPat' || e.e === 'notExistsPat') { for (const v of scope(e.p).may) out.add(v); return out; }
  for (const a of e.args || []) if (a && a.e) existsVars(a, out);
  return out;
}
function usesFn(e, fn) { if (!e) return false; if (e.e === fn) return true; return (e.args || []).some(a => a && a.e && usesFn(a, fn)) || (e.arg ? usesFn(e.arg, fn) : false); }

function allIris(q, out = new Set()) {
  const visit = (x) => {
    if (!x || typeof x !== 'object') return;
    if (Array.isArray(x)) { x.forEach(visit); return; }
    if (typeof x.iri === 'string') out.add(x.iri);
    for (const v of Object.values(x)) if (v && typeof v === 'object') visit(v);
  };
  visit(q);
  return out;
}

function rowMeaning(q, proj, aggs, groupKeys) {
  if (aggs.length && !groupKeys.length) return { kind: 'single', text: 'The result is a single row.' };
  if (groupKeys.length) return { kind: 'group', unit: groupKeys, text: `One row per distinct combination of ${groupKeys.map(k => '?' + k).join(', ')}.` };
  // A plain SELECT returns one row per solution; saying so adds nothing.
  // Cases that need care are reported as caveats (R-MULT-DUP, R-MULT-PER-ENTITY).
  return { kind: 'match', unit: proj.map(it => it.var), text: null };
}

function columnsText(q) {
  return q.select === 'all' ? 'all its variables' : q.select.map(it => '?' + it.var).join(', ');
}

// ------------------------------------------------------------- describers

function termText(t, N) {
  if (!t) return '?';
  switch (t.t) {
    case 'var': return `?${t.name}`;
    case 'iri': return N.iri(t.iri);
    case 'bnode': return 'some value';
    case 'lit': return `"${t.lex}"${t.lang ? '@' + t.lang : ''}`;
    default: return '(triple term)';
  }
}

function describeTriple(tr, N, truthy, cav) {
  const { s, p, o } = tr;
  const S = termText(s, N), O = termText(o, N);
  if (p.t === 'var' && N.valuesIris?.[p.name]) {
    const alts = N.valuesIris[p.name].map(i => N.iri(i));
    if (o.t === 'lit') cav('R-LITERAL-EXACT', 'scope', `The ${alts.join(' or ')} must be exactly ${O} (whole string, case-sensitive${o.lang ? ', language tag exactly ' + o.lang : ''}).`);
    return { rule: 'R-VALUES-PRED', text: `${S} has ${O} as its ${alts.join(' or ')} (?${p.name})` };
  }
  if (p.t === 'var') {
    cav('R-ANYPROP', 'scope', `?${p.name} can be any property: ${S} is linked to ${O} by any predicate at all (in practice best-rank direct values, wdt:, and a few other direct links).`);
    return { rule: 'R-ANYPROP', text: `${S} is linked to ${O} by any property ?${p.name}` };
  }
  const c = compact(p.iri) || {};
  const P = N.iri(p.iri);
  const id = N.wikidataId(p.iri);
  const propName = id ? N.idName(id) : P;
  if (c.prefix === 'wdt') {
    truthy.add(p.iri);
    if (o.t === 'bnode') {
      cav('R-SOMEVALUE', 'scope', `Any ${propName} value counts here, including "unknown value"; "no value" does not count (F-SOMEVALUE, F-NOVALUE).`);
      return { rule: 'R-SOMEVALUE', text: `${S} has at least one ${propName} value` };
    }
    if (o.t === 'lit') cav('R-LITERAL-EXACT', 'scope', `${propName} must be exactly ${O} (whole string, case-sensitive${o.lang ? ', language tag exactly ' + o.lang : ''}).`);
    if (o.t === 'iri' && HIERARCHY.has(id)) cav('R-DIRECT-ONLY', 'changes_answer',
      `${propName} is matched directly: things whose ${propName} is something that is itself ${propName} ${O} (e.g. a district of it) are not included (F-HIERARCHY-PROPS).`);
    return { rule: 'R-TRUTHY', text: `${S} has ${propName} ${O}` };
  }
  if (c.prefix === 'p') {
    cav('R-FULLSTMT', 'scope', `${termText(o, N)} ranges over every ${propName} statement of any rank, including deprecated ones (F-RANK-VALUES).`);
    return { rule: 'R-FULLSTMT', text: `${O} is ${aOrAn(propName)} ${propName} statement of ${S} (any rank)` };
  }
  if (c.prefix === 'ps') return { rule: 'R-FULLSTMT', text: `${O} is the main value of statement ${S}` };
  if (c.prefix === 'pq') {
    if (o.t === 'bnode') return { rule: 'R-QUALIFIER', text: `statement ${S} has at least one ${propName} qualifier` };
    return { rule: 'R-QUALIFIER', text: `${O} is ${aOrAn(propName)} ${propName} qualifier of statement ${S}` };
  }
  if (p.iri === RDFS_LABEL || p.iri === 'http://www.w3.org/2004/02/skos/core#altLabel') {
    if (o.t === 'lit') cav('R-LITERAL-EXACT', 'scope', `${P} must be exactly ${O} (whole string, case-sensitive${o.lang ? ', language tag exactly ' + o.lang : ''}).`);
    return { rule: 'R-LABEL', text: `${O} is ${aOrAn(P)} ${P} of ${S}` };
  }
  if (c.prefix === 'schema' && c.local === 'about') return { rule: 'R-SITELINK', text: `${S} is a wiki page about ${O}` };
  if (c.prefix === 'schema' && c.local === 'isPartOf') return { rule: 'R-SITELINK', text: `wiki page ${S} is on ${O}` };
  if (c.prefix === 'wikibase' && c.local === 'badge') return { rule: 'R-SITELINK', text: `wiki page ${S} carries the badge ${O}` };
  return { rule: 'R-TRIPLE', text: `${S} ${P} ${O}` };
}

function pathText(pth, N) {
  switch (pth.path) {
    case 'iri': return N.short(pth.iri);
    case 'inverse': return `^${pathText(pth.p, N)}`;
    case 'sequence': return `${pathText(pth.a, N)}/${pathText(pth.b, N)}`;
    case 'alternative': return `(${pathText(pth.a, N)}|${pathText(pth.b, N)})`;
    case 'zeroOrMore': return `${pathText(pth.p, N)}*`;
    case 'oneOrMore': return `${pathText(pth.p, N)}+`;
    case 'zeroOrOne': return `${pathText(pth.p, N)}?`;
    default: return '(path)';
  }
}

function collectPathIris(pth, out = []) {
  if (pth.path === 'iri') out.push(pth.iri);
  for (const k of ['p', 'a', 'b']) if (pth[k]) collectPathIris(pth[k], out);
  for (const x of pth.ps || []) collectPathIris(x, out);
  return out;
}

function describePath(el, N, truthy, cav) {
  const S = termText(el.s, N), O = termText(el.o, N);
  for (const iri of collectPathIris(el.path)) if (compact(iri)?.prefix === 'wdt') truthy.add(iri);
  const pth = el.path;
  if (pth.path === 'sequence' && pth.a.path === 'iri' && pth.a.iri === P31 && pth.b.path === 'zeroOrMore' && pth.b.p.path === 'iri' && pth.b.p.iri === P279) {
    cav('R-SUBCLASS', 'scope', `${S} is an instance of ${O} or of any class that is, through any chain of "subclass of" links, a subclass of ${O}.`);
    return { rule: 'R-SUBCLASS', text: `${S} is an instance of ${O} or of any subclass of it` };
  }
  if (pth.path === 'zeroOrMore' && pth.p.path === 'iri' && pth.p.iri === P279)
    return { rule: 'R-SUBCLASS', text: `${S} is ${O} or a subclass of it (at any depth)` };
  if (pth.path === 'sequence' && pth.a.path === 'iri' && pth.b.path === 'iri' && compact(pth.a.iri)?.prefix === 'p') {
    const st = N.idName(N.wikidataId(pth.a.iri));
    const bc = compact(pth.b.iri), bn = N.wikidataId(pth.b.iri) ? N.idName(N.wikidataId(pth.b.iri)) : N.iri(pth.b.iri);
    cav('R-FULLSTMT', 'scope', `The ${st} statements here are of any rank, including deprecated ones (F-RANK-VALUES).`);
    if (bc?.prefix === 'ps') return { rule: 'R-FULLSTMT', text: `${S} has a ${st} statement (any rank) whose main value is ${O}` };
    if (bc?.prefix === 'pq') return { rule: 'R-QUALIFIER', text: `${S} has a ${st} statement (any rank) with a ${bn} qualifier ${O}` };
    return { rule: 'R-PATH', text: `${S} reaches ${O} by following ${pathText(pth, N)}` };
  }
  if (pth.path === 'sequence' && pth.a.path === 'iri' && pth.b.path === 'iri') {
    const n = (iri) => { const id = N.wikidataId(iri); return id ? N.idName(id) : N.iri(iri); };
    return { rule: 'R-PATH', text: `${S} has ${n(pth.a.iri)} some value that itself has ${n(pth.b.iri)} ${O}` };
  }
  if (pth.path === 'sequence') return { rule: 'R-PATH', text: `${S} reaches ${O} by following ${pathText(pth, N)} (each step a separate link)` };
  return { rule: 'R-PATH', text: `${S} reaches ${O} via ${pathText(pth, N)}` };
}

function describeAny(x, N, truthy, cav, rec) {
  switch (x.kind) {
    case 'triple': return describeTriple(x.triple, N, truthy, cav);
    case 'path': return describePath(x, N, truthy, cav);
    case 'filter': return { rule: 'R-FILTER', text: `only where ${exprText(x.cond, N)}` };
    case 'bind': return { rule: 'R-BIND', text: `?${x.v} is ${exprText(x.e, N)}` };
    case 'optional': {
      const parts = flatten(x.p).map(y => describeAny(y, N, truthy, cav, rec));
      return { rule: 'R-OPTIONAL', parts, text: `optionally [${parts.map(y => y.text).join('; ')}]${isTrueCond(x.cond) ? '' : ` (only where ${exprText(x.cond, N)})`}` };
    }
    case 'minus': {
      const parts = flatten(x.p).map(y => describeAny(y, N, truthy, cav, rec));
      return { rule: 'R-MINUS', parts, text: `except where [${parts.map(y => y.text).join('; ')}]` };
    }
    case 'union': {
      const arms = x.branches.map(b => flatten(b).map(y => describeAny(y, N, truthy, cav, rec).text).join('; '));
      return { rule: 'R-UNION', text: `either ${arms.map(a => `[${a}]`).join(' or ')}` };
    }
    case 'values':
      return { rule: 'R-VALUES', text: `${x.vars.map(v => '?' + v).join(', ')} take${x.vars.length > 1 ? '' : 's'} each of: ${x.rows.map(r => r.map(t => t ? termText(t, N) : 'UNDEF').join(' / ')).join('; ')}` };
    case 'subselect': {
      const sub = explainQuery(x.q, { names: N, nested: true });
      rec.subqueries.push(sub);
      rec.caveats.push(...sub.caveats.map(c => ({ ...c, in_subquery: rec.subqueries.length })));
      return { rule: 'R-SUBQUERY', text: `a separately computed table of ${columnsText(x.q)} (see subquery ${rec.subqueries.length})` };
    }
    default:
      rec.unexplained.push({ what: `${x.kind} inside a group` });
      return { rule: 'UNEXPLAINED', text: `(${x.kind})` };
  }
}

function repeaterText(r, N) {
  const el = r.el;
  if (r.union) return 'alternative it matches (UNION)';
  if (r.intermediate) return `intermediate value along ${pathText(el.path, N)} (R-MULT-PATH)`;
  if (el.kind === 'triple') {
    const id = el.triple.p.t === 'iri' ? N.wikidataId(el.triple.p.iri) : null;
    const pn = id ? N.idName(id) : (el.triple.p.t === 'iri' ? N.iri(el.triple.p.iri) : `?${el.triple.p.name}`);
    if (r.anon) return `${pn} value it has (R-MULT-VALUE)`;
    if (termVar(el.triple.s) === r.var) return `matching ?${r.var} (R-MULT-VALUE)`;
    if (el.triple.p.t === 'iri' && compact(el.triple.p.iri)?.prefix === 'p') return `${pn} statement ?${r.var} (R-MULT-VALUE)`;
    return `${pn} value ?${r.var} (R-MULT-VALUE)`;
  }
  if (el.kind === 'values') return `listed value of ?${r.var} that matches (VALUES)`;
  return `value of ?${r.var}`;
}

// -------------------------------------------------------------- expressions

const OPWORD = { '=': '=', '!=': '≠', '<': '<', '>': '>', '<=': '≤', '>=': '≥' };
export function exprText(e, N) {
  if (!e) return '?';
  const a = e.args || [];
  const T = (x) => exprText(x, N);
  switch (e.e) {
    case 'var': return `?${e.name}`;
    case 'iri': return N.iri(e.iri);
    case 'lit': return `"${e.lit.lex}"${e.lit.lang ? '@' + e.lit.lang : ''}`;
    case 'bool': return String(e.value);
    case 'num': return String(e.value);
    case 'decimal': case 'double': return e.lex;
    case 'compare': return `${T(a[0])} ${OPWORD[e.op]} ${T(a[1])}`;
    case 'arith': return `(${T(a[0])} ${e.op} ${T(a[1])})`;
    case 'and': return `${T(a[0])} and ${T(a[1])}`;
    case 'or': return `${T(a[0])} or ${T(a[1])}`;
    case 'not': return `not (${T(a[0])})`;
    case 'lang': return `the language tag of ${T(a[0])}`;
    case 'str': return `the text of ${T(a[0])}`;
    case 'year': return `the year of ${T(a[0])}`;
    case 'month': return `the month of ${T(a[0])}`;
    case 'bound': return `?${e.name} has a value`;
    case 'cond': return `if ${T(a[0])} then ${T(a[1])} else ${T(a[2])}`;
    case 'coalesce': return `the first available of ${a.map(T).join(', ')}`;
    case 'contains': return `${T(a[0])} contains ${T(a[1])} (case-sensitive)`;
    case 'strStarts': return `${T(a[0])} starts with ${T(a[1])} (case-sensitive)`;
    case 'strEnds': return `${T(a[0])} ends with ${T(a[1])} (case-sensitive)`;
    case 'strAfter': return `the part of ${T(a[0])} after ${T(a[1])}`;
    case 'strBefore': return `the part of ${T(a[0])} before ${T(a[1])}`;
    case 'regex': return `${T(a[0])} matches the regular expression ${T(a[1])}${a[2] ? ' with flags ' + T(a[2]) : ' (case-sensitive)'}`;
    case 'concat': return `the text ${a.map(T).join(' + ')} joined together`;
    case 'iriFn': return `the web address (IRI) made from ${T(a[0])}`;
    case 'substr': return `the part of ${T(a[0])} starting at character ${T(a[1])}${a[2] ? `, ${T(a[2])} characters long` : ''}`;
    case 'uCase': return `${T(a[0])} in upper case`;
    case 'lCase': return `${T(a[0])} in lower case`;
    case 'strLen': return `the number of characters in ${T(a[0])}`;
    case 'inList': return `${T(a[0])} is one of ${(a[1] || []).map(T).join(', ')}`;
    case 'notInList': return `${T(a[0])} is none of ${(a[1] || []).map(T).join(', ')}`;
    case 'unaryMinus': return `minus ${T(a[0])}`;
    case 'unaryPlus': return T(a[0]);
    case 'isBlank': return `${T(a[0])} is a blank node (in WDQS data: an "unknown value")`;
    case 'isIri': return `${T(a[0])} is a web address (IRI)`;
    case 'isLiteral': return `${T(a[0])} is a literal value`;
    case 'replace': return `${T(a[0])} with every match of the regular expression ${T(a[1])} replaced by ${T(a[2])}${a[3] ? ' (flags ' + T(a[3]) + ')' : ''}`;
    case 'abs': return `the absolute value of ${T(a[0])}`;
    case 'round': return `${T(a[0])} rounded to the nearest whole number`;
    case 'floor': return `${T(a[0])} rounded down`;
    case 'ceil': return `${T(a[0])} rounded up`;
    case 'day': return `the day of the month of ${T(a[0])}`;
    case 'now': return 'the current date and time when the query runs';
    case 'datatype': return `the datatype of ${T(a[0])}`;
    case 'sha512': case 'sha256': case 'sha1': case 'md5': case 'sha384': return `the ${e.e.toUpperCase()} hash of ${T(a[0])}`;
    case 'encodeForUri': return `${T(a[0])} percent-encoded for use in a URL`;
    case 'sameTerm': return `${T(a[0])} is the identical term to ${T(a[1])}`;
    case 'aggregate': {
      const fn = { count: 'the number of', sum: 'the sum of', min: 'the smallest', max: 'the largest', avg: 'the average of', sample: 'one (arbitrary) value of', groupConcat: 'all values, joined, of' }[e.fn];
      return `${fn} ${e.distinct ? 'distinct ' : ''}${e.arg ? T(e.arg) : 'rows'}`;
    }
    case 'existsPat': return 'a pattern exists';
    case 'notExistsPat': return 'a pattern does not exist';
    case 'functionCall': {
      const c = compact(e.iri);
      const name = c ? `${c.prefix}:${c.local}` : `<${e.iri}>`;
      if (name === 'geof:distance') return `the distance in kilometres between ${T(a[0])} and ${T(a[1])} (F-GEODIST-UNIT)`;
      if (name === 'xsd:integer') return `${T(a[0])} as an integer`;
      if (/^xsd:(decimal|double|float)$/.test(name)) return `${T(a[0])} as a number`;
      if (name === 'xsd:dateTime') return `${T(a[0])} as a date-time`;
      if (e.iri === 'http://www.w3.org/2005/xpath-functions#rand') return 'a random number (different on every run)';
      return `‹${name}›(${a.map(T).join(', ')})`;
    }
    default: return `‹${e.e}›(${a.map(x => (x && x.e) ? T(x) : Array.isArray(x) ? x.map(T).join(', ') : 'none').join(', ')})`;
  }
}
