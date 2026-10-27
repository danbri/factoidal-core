// Apache Jena ARQ expression tests, ported to SPARQL and run on @factoidal/core.
//
// Source: the one-line tests (`@Test public void NAME() { ... }`) of
// jena-arq/src/test/java/org/apache/jena/sparql/expr/*.java at Apache Jena
// commit a1164c5dc5c9e1a9c58d94766c13d870e0a8ba98. The cases are derived from
// Apache Jena, Apache License 2.0; Apache Jena: Copyright The Apache Software
// Foundation. Change (Factoidal, 2026-10-26): each Java call is rewritten as a
// SPARQL expression and a check kind by tools/jena-facade-study/extract.py into
// fixtures/jena-arq-expr/cases.json. See fixtures/NOTICE.
// Record: docs/designissues/2026-10-25-jena-style-facade-feasibility.md (stage 0)
// and docs/20261026-jena-expr-port.md.
//
// Each case is one SPARQL SELECT. The engine computes the result (?r) and the
// check (?ok) inside the query; JS only reads ?ok. A case has one of three
// verdicts (fixtures/jena-arq-expr/verdicts.json):
//   - no entry: a plain assertion (Jena and the specification agree).
//   - "defect": Factoidal differs from the SPARQL specification. Expected
//     failure that names an open issue; it FAILS when the case starts to pass.
//   - "divergence": Jena's expectation is a Jena extension, or Jena differs
//     from the specification. Not a failure of this engine. The case FAILS if
//     Jena's expectation starts to hold, so that the verdict is checked again.
// The specification decides, not Jena: each verdict group cites the section.

import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import * as f from '../index.mjs';

const dir = new URL('./fixtures/jena-arq-expr/', import.meta.url);
const { cases, counts } = JSON.parse(readFileSync(new URL('cases.json', dir), 'utf8'));
const verdicts = JSON.parse(readFileSync(new URL('verdicts.json', dir), 'utf8'));

const XSD = 'http://www.w3.org/2001/XMLSchema#';
const GLOBAL = `PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
PREFIX xsd: <${XSD}>
PREFIX owl: <http://www.w3.org/2002/07/owl#>
PREFIX fn: <http://www.w3.org/2005/xpath-functions#>
PREFIX sparql: <http://www.w3.org/ns/sparql#>
PREFIX op: <http://www.w3.org/2005/xpath-functions#>
PREFIX math: <http://www.w3.org/2005/xpath-functions/math#>
PREFIX afn: <http://jena.apache.org/ARQ/function#>
PREFIX apf: <http://jena.apache.org/ARQ/property#>
`;
// The parser context of each Jena test class (prefixes and base).
const PROLOGUE = {
  // TestExpressions: its own Query object (base and prefixes set in the class).
  // Jena also declares the prefix "x." there, which is not a SPARQL PN_PREFIX.
  TestExpressions: `BASE <http://base/>
PREFIX ex: <http://example.org/>
PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
PREFIX : <http://default/>
PREFIX select: <http://select/>
`,
  // ARQConstants.getGlobalPrefixMap(). Jena resolves relative IRIs against
  // the system base; the port gives a fixed base.
  global: 'BASE <http://example/base/>\n' + GLOBAL,
  // LibTestExpr: the global map plus lfn:
  lib: 'BASE <http://example/base/>\n' + GLOBAL + 'PREFIX lfn: <http://www.dotnetrdf.org/leviathan#>\n',
};
const INTEGER_TYPES = ['integer', 'nonPositiveInteger', 'negativeInteger', 'long', 'int', 'short', 'byte',
  'nonNegativeInteger', 'unsignedLong', 'unsignedInt', 'unsignedShort', 'unsignedByte', 'positiveInteger']
  .map((t) => `<${XSD}${t}>`).join(', ');
const dbl = (v) => `"${v}"^^<${XSD}double>`;

// The SPARQL check of each kind, over ?r (the result of the Jena expression).
function check(p) {
  switch (p.kind) {
    case 'boolean': return `BOUND(?r) && datatype(?r) = <${XSD}boolean> && ?r = ${p.expected}`;
    case 'integer': return `BOUND(?r) && datatype(?r) IN (${INTEGER_TYPES}) && ?r = ${p.expected}`;
    // Jena NodeValue.isDecimal is true for xsd:integer and xsd:decimal;
    // isDouble is true for every numeric (NodeValueInteger/Decimal/Float/Double).
    case 'decimal': return `BOUND(?r) && datatype(?r) IN (${INTEGER_TYPES}, <${XSD}decimal>) && ?r = ${p.expected}`;
    case 'double': return `BOUND(?r) && isNumeric(?r) && ?r = ${dbl(p.expected)}`;
    case 'string': return `BOUND(?r) && datatype(?r) = <${XSD}string> && str(?r) = ${JSON.stringify(p.expected)}`;
    case 'anyString': return `BOUND(?r) && datatype(?r) = <${XSD}string>`;
    case 'iri': return `BOUND(?r) && isIRI(?r) && str(?r) = ${JSON.stringify(p.expected)}`;
    case 'evalError': case 'error': return '!BOUND(?r)';
    case 'bound': return 'BOUND(?r)';
    case 'parses': case 'parseError': return 'true';
    case 'ebv': return `IF(?r, true, false) = ${p.expected}`;
    case 'sameTerm': return `sameTerm(?r, ${p.expected})`;
    case 'sameValueSameDatatype':
      return 'BOUND(?r) && BOUND(?e) && (sameTerm(?r, ?e) || (isLiteral(?r) && datatype(?r) = datatype(?e) && ?r = ?e))';
    case 'nan': return `BOUND(?r) && datatype(?r) = <${XSD}double> && ?r != ?r`;
    case 'doubleNear':
      if (p.expectedTerm !== undefined) {
        return `BOUND(?r) && (?r = ${p.expectedTerm} || (isNumeric(?r) && ABS(?r - ${p.expectedTerm}) <= ${dbl(p.delta)}))`;
      }
      return `BOUND(?r) && isNumeric(?r) && (?r = ${dbl(p.expected)} || ABS(?r - ${dbl(p.expected)}) <= ${dbl(p.delta)})`;
    case 'check': return `BOUND(?r) && ${p.check}`;
    default: throw new Error(`unknown kind ${p.kind}`);
  }
}

function query(p) {
  const vars = { ...(p.env || {}), ...(p.bind || {}) };
  const values = Object.entries(vars).filter(([, t]) => t !== 'BNODE()');
  const bnodes = Object.entries(vars).filter(([, t]) => t === 'BNODE()');
  let body = '';
  if (values.length) {
    body += `  VALUES (${values.map(([v]) => '?' + v).join(' ')}) { (${values.map(([, t]) => t).join(' ')}) }\n`;
  }
  for (const [v] of bnodes) body += `  BIND(BNODE() AS ?${v})\n`;
  if (p.parseTail) body += `  OPTIONAL { <urn:jena:s> <urn:jena:p> ${p.parseTail} }\n`;
  body += `  BIND((${p.expr}) AS ?r)\n`;
  if (p.kind === 'sameValueSameDatatype') body += `  BIND((${p.expected}) AS ?e)\n`;
  body += `  BIND((${check(p)}) AS ?ok)\n`;
  return `${PROLOGUE[p.ctx]}SELECT ?r ?ok WHERE {\n${body}}`;
}

function show(t) {
  if (t === undefined) return '(unbound)';
  if (t.termType === 'NamedNode') return `<${t.value}>`;
  if (t.termType === 'BlankNode') return `_:${t.value}`;
  if (t.termType === 'Literal') {
    const s = JSON.stringify(t.value);
    if (t.language) return `${s}@${t.language}${t.direction ? '--' + t.direction : ''}`;
    return t.datatype.value === XSD + 'string' ? s : `${s}^^<${t.datatype.value}>`;
  }
  return String(t.value ?? t);
}

const ds = await f.parse('', { format: 'nquads' });

// Run one case: { holds, detail }. "holds" means Jena's expectation holds.
async function run(c) {
  const p = c.port;
  const text = query(p);
  let rows;
  try {
    rows = await ds.query(text, { version: '1.2' });
  } catch (err) {
    const msg = String(err && err.message);
    const parseErr = /parse/i.test(msg);
    if (p.kind === 'parseError' || (p.kind === 'error' && parseErr)) {
      return { holds: parseErr, detail: msg.slice(0, 200) };
    }
    return { holds: false, detail: `query refused: ${msg.slice(0, 200)}` };
  }
  if (p.kind === 'parseError') return { holds: false, detail: `query parsed; ?r = ${show(rows[0]?.get('r'))}` };
  const ok = rows.length === 1 && rows[0].get('ok')?.value === 'true';
  let detail = `rows ${rows.length}; ?r = ${show(rows[0]?.get('r'))}`;
  if (!ok && p.kind === 'sameTerm') {
    // Diagnostic only: is the result the same value and datatype, with a
    // different lexical form?
    const v = await ds.query(query({ ...p, kind: 'check', check: `isLiteral(?r) && datatype(?r) = datatype(${p.expected}) && ?r = ${p.expected}` }), { version: '1.2' });
    if (v[0]?.get('ok')?.value === 'true') detail += '; same value and datatype, other lexical form';
  }
  return { holds: ok, detail };
}

const report = [];
const groupOf = (id) => verdicts.cases[id];

for (const c of cases) {
  if (!c.port) continue;
  const g = groupOf(c.id);
  const v = g && verdicts.groups[g];
  if (g) assert.ok(v, `verdicts.json: case ${c.id} names unknown group ${g}`);
  if (!v) {
    test(`${c.id}: ${c.port.expr}`, async () => {
      const r = await run(c);
      report.push({ id: c.id, holds: r.holds, detail: r.detail, query: query(c.port) });
      assert.ok(r.holds, `Jena: ${c.java}\nquery:\n${query(c.port)}\n${r.detail}`);
    });
  } else if (v.class === 'defect') {
    test(`xfail: ${c.id}: ${c.port.expr} (${v.issue})`, async (t) => {
      const r = await run(c);
      report.push({ id: c.id, group: g, holds: r.holds, detail: r.detail, query: query(c.port) });
      t.diagnostic(`${v.spec}: ${r.detail}`);
      assert.ok(!r.holds, `unexpected pass: ${c.id} now meets the specification; flip it to an assertion (remove it from verdicts.json) and update ${v.issue}`);
    });
  } else if (v.class === 'divergence') {
    test(`divergence: ${c.id}: ${c.port.expr} (${v.spec})`, async (t) => {
      const r = await run(c);
      report.push({ id: c.id, group: g, holds: r.holds, detail: r.detail, query: query(c.port) });
      t.diagnostic(`${v.gloss}: ${r.detail}`);
      assert.ok(!r.holds, `Jena's expectation now holds for ${c.id}; check the verdict "${g}" again (${v.spec})`);
    });
  } else {
    throw new Error(`verdicts.json: group ${g} has unknown class ${v.class}`);
  }
}

test('every one-line Jena expression test is ported or has a reason', () => {
  const unported = cases.filter((c) => !c.port);
  assert.equal(cases.length, counts.oneLineDeclarations);
  assert.equal(unported.length, counts.unported);
  for (const c of unported) assert.ok(c.unported && c.unported.length > 0, c.id);
  for (const id of Object.keys(verdicts.cases)) assert.ok(cases.some((c) => c.id === id && c.port), `verdicts.json: no ported case ${id}`);
});

if (process.env.JENA_EXPR_REPORT) {
  process.on('exit', () => writeFileSync(process.env.JENA_EXPR_REPORT, JSON.stringify(report, null, 1)));
}
