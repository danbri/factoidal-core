// Mechanical port of Jena ARQ one-line expression tests (jena-arq
// src/test/java/org/apache/jena/sparql/expr) to SPARQL ASK queries run by
// @factoidal/core. The comparison is done by the engine inside the query;
// JS only reads the boolean. Feasibility probe, not a shipped test.
import { readFileSync, writeFileSync } from 'node:fs';
import * as f from '/home/user/factoidal-core/npm/factoidal/index.mjs';
const cases = JSON.parse(readFileSync(process.argv[2], 'utf8'));
const P = `PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>
PREFIX owl: <http://www.w3.org/2002/07/owl#>
PREFIX fn: <http://www.w3.org/2005/xpath-functions#>
PREFIX op: <http://www.w3.org/2005/xpath-functions#>
PREFIX sparql: <http://www.w3.org/ns/sparql#>
PREFIX math: <http://www.w3.org/2005/xpath-functions/math#>
PREFIX afn: <http://jena.apache.org/ARQ/function#>
PREFIX apf: <http://jena.apache.org/ARQ/property#>
`;
const same = 'BOUND(?a) && BOUND(?b) && ((isLiteral(?a) && isLiteral(?b) && datatype(?a) = datatype(?b) && lang(?a) = lang(?b) && ?a = ?b) || sameTerm(?a, ?b))';
function q(c) {
  switch (c.kind) {
    case 'bool': return `ASK { BIND((${c.expr}) AS ?a) BIND(${c.exp} AS ?b) FILTER(${same}) }`;
    case 'num':  return `ASK { BIND((${c.expr}) AS ?a) BIND(${c.exp} AS ?b) FILTER(${same}) }`;
    case 'str':  return `ASK { BIND((${c.expr}) AS ?a) BIND(${JSON.stringify(c.exp)} AS ?b) FILTER(BOUND(?a) && str(?a) = ?b) }`;
    case 'err':  return `ASK { BIND((${c.expr}) AS ?a) FILTER(!BOUND(?a)) }`;
    case 'nvparse': return `ASK { BIND((${c.expr}) AS ?a) BIND((${c.exp}) AS ?b) FILTER(${same}) }`;
    case 'nv': {
      const t = { Integer: 'xsd:integer', String: 'xsd:string', Boolean: 'xsd:boolean', Double: 'xsd:double', Decimal: 'xsd:decimal' }[c.type];
      return `ASK { BIND((${c.expr}) AS ?a) BIND(STRDT(${JSON.stringify(c.exp)}, ${t}) AS ?b) FILTER(${same}) }`;
    }
  }
}
const ds = await f.openDataset('', { format: 'ntriples' });
const res = { pass: [], fail: [], error: [] };
const t0 = Date.now();
for (const c of cases) {
  const text = P + q(c);
  try {
    const r = await ds.query("BASE <http://example/base/>\n" + text, { version: "1.2" });
    const ok = r === true || r?.boolean === true || (Array.isArray(r) && r.length > 0 && r[0] === true);
    (ok ? res.pass : res.fail).push({ ...c, got: r });
  } catch (e) {
    res.error.push({ ...c, err: String(e.message).slice(0, 160) });
  }
}
const by = (xs) => xs.reduce((m, c) => (m[c.cls] = (m[c.cls] || 0) + 1, m), {});
console.log(`pass ${res.pass.length}, fail ${res.fail.length}, error ${res.error.length} (out of ${cases.length}); ${Date.now() - t0} ms`);
console.log('pass by class', by(res.pass)); console.log('fail by class', by(res.fail)); console.log('error by class', by(res.error));
writeFileSync(process.argv[3], JSON.stringify(res, null, 1));
