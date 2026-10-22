// Public Wasm regressions for the standards-reuse integration. Native Lean
// guards and refinement proofs do not establish the packaged adapter behavior.
import test from 'node:test';
import assert from 'node:assert/strict';
import * as Factoidal from '../index.mjs';

const XSD = 'http://www.w3.org/2001/XMLSchema#';
const query = (text) => Factoidal.query('', `PREFIX xsd: <${XSD}> ${text}`,
  { format: 'nquads' });

for (const [name, values, operation, lexical, datatype] of [
  ['SUM retains float rounding', '"16777216"^^xsd:float 1', 'SUM', '16777216', 'float'],
  ['SUM promotes float plus double', '"16777216"^^xsd:float "1"^^xsd:double', 'SUM', '16777217', 'double'],
  ['MIN returns the original rounded float term', '"16777217"^^xsd:float "16777217"^^xsd:double', 'MIN', '16777217', 'float'],
  ['MAX returns the original double term', '"16777217"^^xsd:double "16777217"^^xsd:float', 'MAX', '16777217', 'double'],
]) {
  test(`shared semantics: ${name}`, async () => {
    const rows = await query(`SELECT (${operation}(?x) AS ?value) WHERE { VALUES ?x { ${values} } }`);
    assert.equal(rows.length, 1);
    const value = rows[0].get('value');
    assert.equal(value.datatype.value, XSD + datatype);
    if (operation === 'SUM') assert.equal(Number(value.value), Number(lexical));
    else assert.equal(value.value, lexical); // MIN/MAX preserve term spelling.
  });
}

test('shared semantics: grouping keeps term-distinct integer spellings', async () => {
  const rows = await query('SELECT ?x (COUNT(*) AS ?n) WHERE { VALUES ?x { "01"^^xsd:integer "1"^^xsd:integer } } GROUP BY ?x');
  assert.deepEqual(rows.map(r => [r.get('x').value, r.get('n').value]).sort(),
    [['01', '1'], ['1', '1']]);
});

test('shared semantics: aggregate DISTINCT uses RDF term identity', async () => {
  const rows = await query('SELECT (COUNT(DISTINCT ?x) AS ?n) WHERE { VALUES ?x { "01"^^xsd:integer "1"^^xsd:integer "1"^^xsd:integer } }');
  assert.equal(rows[0].get('n').value, '2');
});

test('shared semantics: repeated-anchor profile refusal is an expression error', async () => {
  // The regular expression is valid in the standard; refusal is a documented
  // capability gap. Returning a false match would conceal that gap.
  const rows = await query('SELECT (REGEX("a", "^^a") AS ?unsupported) (REGEX("a", "^a$") AS ?supported) WHERE {}');
  assert.equal(rows[0].has('unsupported'), false);
  assert.equal(rows[0].get('supported').value, 'true');
});

const metadata = pattern => JSON.stringify({ url: 'data.csv', tableSchema: {
  columns: [{ name: 'value', datatype: { base: 'string', format: pattern } }],
} });

test('shared semantics: CSVW unsupported format cannot produce a complete Dataset', async () => {
  const accepted = await Factoidal.csvwToRdf('value\na\n', metadata('^a$'));
  assert.ok(accepted.size > 0);
  await assert.rejects(Factoidal.csvwToRdf('value\na\n', metadata('(?=a)a')),
    /unsupported-syntax/);
});

test('shared semantics: public RIF refuses unresolved imports', async () => {
  const rules = `<Document xmlns="http://www.w3.org/2007/rif#">
    <directive><Import><location>https://example.test/missing</location></Import></directive>
    <payload><Group/></payload></Document>`;
  await assert.rejects(Factoidal.rifEval('', rules, { format: 'nquads' }),
    /unsupported-syntax.*imports require a resolver/);
});
