// Stage 1 of https://github.com/danbri/factoidal/issues/713: every
// F*-engine main-entry function that the Lean library implements, run
// over the Lean engine (require('../index.js')) with the INPUTS AND
// EXPECTED RESULTS of the existing F*-engine tests:
//
//   api.test.js        jsonldToRdf, jsonldFromRdf, parse(jsonld), rmlMap,
//                      csvwToRdf, rifEval, xmlWellformed, xpathEval
//   jsonschema.test.js, schematron.test.js, xslt.test.js, mathml.test.js,
//   xforms.test.js, toan.test.js, hdt.test.js, extension-functions.test.js
//   fn.test.js         rifEval with the DOCTYPE and entity form
//   smoke.js           queryRaw
//
// tableauMaterialise, tableauDlInconsistent and the SERVICE endpoint
// registry have no F* npm test; their cases here are new and say what
// they pin.
//
// Skips wholesale when the Lean wasm assets are not resolvable, and a
// test skips when the resolved wasm predates its op (same pattern as
// l4-core.test.js).

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

const lean = require('../index.js');
const { Dataset, dataFactory: df } = lean;

// The ops the loaded wasm serves (its `ops` reflection). Since 0.9.0 the
// wasm in l4-assets/ is the package's only engine, so it must serve every op
// a case uses: a missing op FAILS the case, naming the op (it is not a skip).
let leanOpsPromise = null;
function leanOps() {
  if (!leanOpsPromise) {
    leanOpsPromise = require('../index.js').loadEngine().then((eng) => eng.call('ops', []).ops);
  }
  return leanOpsPromise;
}

function skipUnlessAvailable(_t) {
  return false;
}

async function skipUnlessOps(_t, ...ops) {
  const have = await leanOps();
  const missing = ops.filter((op) => !have.includes(op));
  assert.deepEqual(missing, [], `the loaded Lean wasm lacks ${missing.join(', ')} (ops reflection)`);
  return false;
}

const REPO = path.join(__dirname, '..', '..', '..');

// ---------------------------------------------------------------------
// capabilities(): the families this stage adds are reported, from the
// loaded entry's real functions.
// ---------------------------------------------------------------------

test('capabilities: the stage-1, stage-2 and stage-3 families are reported true', async (t) => {
  if (await skipUnlessOps(t, 'jsonldToRdf', 'rmlMap', 'csvwToRdf', 'rifEval',
    'xmlWellformed', 'xpathEval', 'xsltTransform', 'schematronValidate',
    'jsonSchemaValidate', 'mathmlEval', 'xformsRecalc', 'tableauMaterialise',
    'tableauDlInconsistent', 'toanSummation', 'shaclValidate', 'shexValidate',
    'queryDataset12', 'datasetQuery12', 'storeOpen', 'parseDocument')) return;
  const caps = await lean.capabilities();
  for (const key of ['jsonld', 'jsonldFromRdf', 'rml', 'csvw', 'rif', 'xml',
    'xpath', 'xslt', 'mathml', 'xforms', 'jsonSchema', 'schematron', 'toan',
    'tableau']) {
    assert.equal(caps[key], true, `capabilities().${key}`);
  }
  // Stage 3 serves SHACL and ShEx (Wasm/Ops/Validate.lean); COTTAS left
  // the package, so its flag is gone; lenient parse is served by the op
  // parseDocument (Wasm/Ops/Lenient.lean,
  // https://github.com/danbri/factoidal/issues/716).
  for (const key of ['shacl', 'shex', 'matrix', 'sigmoid', 'vcCrypto', 'didKey',
    'entailment', 'hdt', 'sparql12', 'store', 'datasetHandles', 'turtlePrefixes',
    'parseDiagnostics']) {
    assert.equal(caps[key], true, `capabilities().${key}`);
  }
  assert.equal('cottasBytesStore' in caps, false, 'no COTTAS flag');
});

// ---------------------------------------------------------------------
// JSON-LD (api.test.js)
// ---------------------------------------------------------------------

test('parse: jsonld (expanded/inline-context form) through the Lean ABI', async (t) => {
  if (await skipUnlessOps(t, 'parseToDatasetJson', 'jsonldToRdf')) return;
  const jsonld = JSON.stringify({
    '@context': { foaf: 'http://xmlns.com/foaf/0.1/', name: 'foaf:name' },
    '@id': 'http://example.org/alice',
    name: 'Alice',
  });
  const ds = await lean.parse(jsonld, { format: 'jsonld' });
  assert.equal(ds.size, 1);
  const [q] = [...ds];
  assert.equal(q.subject.value, 'http://example.org/alice');
  assert.equal(q.predicate.value, 'http://xmlns.com/foaf/0.1/name');
  assert.equal(q.object.value, 'Alice');
});

test('jsonldToRdf: parses JSON-LD with an explicit base option', async (t) => {
  if (await skipUnlessOps(t, 'jsonldToRdf')) return;
  const jsonld = JSON.stringify({
    '@context': { foaf: 'http://xmlns.com/foaf/0.1/', name: 'foaf:name' },
    '@id': 'alice',
    name: 'Alice',
  });
  const ds = await lean.jsonldToRdf(jsonld, { base: 'http://example.org/' });
  assert.equal(ds.size, 1);
  assert.equal([...ds][0].subject.value, 'http://example.org/alice');
});

test('jsonldToRdf: a remote @context is an error (no document loader)', async (t) => {
  if (await skipUnlessOps(t, 'jsonldToRdf')) return;
  await assert.rejects(
    () => lean.jsonldToRdf('{"@context":"http://example.org/ctx","@id":"http://e/a"}'),
    /jsonldToRdf: .*remote context/);
});

test('jsonldToRdf: text that is not JSON-LD rejects', async (t) => {
  if (await skipUnlessOps(t, 'jsonldToRdf')) return;
  await assert.rejects(() => lean.jsonldToRdf('not json'), /jsonldToRdf/);
  await assert.rejects(() => lean.jsonldToRdf(42), TypeError);
});

test('jsonldFromRdf: N-Quads serialize to expanded JSON-LD (reverse of jsonldToRdf)', async (t) => {
  if (await skipUnlessOps(t, 'jsonldFromRdf')) return;
  const jld = await lean.jsonldFromRdf('<http://ex/s> <http://ex/p> "o" .', { format: 'nquads' });
  assert.ok(Array.isArray(jld), 'expanded JSON-LD is an array of node objects');
  assert.equal(jld.length, 1);
  assert.equal(jld[0]['@id'], 'http://ex/s');
  assert.deepEqual(jld[0]['http://ex/p'], [{ '@value': 'o' }]);
});

test('jsonldFromRdf: useNativeTypes turns xsd:integer into a JSON number', async (t) => {
  if (await skipUnlessOps(t, 'jsonldFromRdf')) return;
  const nq = '<http://ex/s> <http://ex/p> "5"^^<http://www.w3.org/2001/XMLSchema#integer> .';
  const plain = await lean.jsonldFromRdf(nq, { format: 'nquads' });
  assert.deepEqual(plain[0]['http://ex/p'][0],
    { '@value': '5', '@type': 'http://www.w3.org/2001/XMLSchema#integer' });
  const native = await lean.jsonldFromRdf(nq, { format: 'nquads', useNativeTypes: true });
  assert.deepEqual(native[0]['http://ex/p'][0], { '@value': 5 });
});

// ---------------------------------------------------------------------
// RML and CSVW (api.test.js)
// ---------------------------------------------------------------------

test('rmlMap: evaluates an RML mapping graph against JSON source data', async (t) => {
  if (await skipUnlessOps(t, 'rmlMap')) return;
  const mapping = `
    @prefix rml: <http://w3id.org/rml/> .
    @prefix foaf: <http://xmlns.com/foaf/0.1/> .
    @prefix ex:   <http://example.org/> .
    ex:TM a rml:TriplesMap ;
      rml:logicalSource [ a rml:LogicalSource ;
        rml:iterator "$.people[*]" ;
        rml:referenceFormulation rml:JSONPath ;
        rml:source [ a rml:RelativePathSource ; rml:root rml:MappingDirectory ; rml:path "x" ] ] ;
      rml:subjectMap [ rml:template "http://example.org/person/{$.id}" ] ;
      rml:predicateObjectMap [ rml:predicate foaf:name ; rml:objectMap [ rml:reference "$.name" ] ] .
  `;
  const source = JSON.stringify({
    people: [{ id: '1', name: 'Alice' }, { id: '2', name: 'Bob' }],
  });
  const ds = await lean.rmlMap(mapping, source, 'json');
  assert.ok(ds instanceof Dataset);
  assert.equal(ds.size, 2);
  assert.equal(
    ds.match(df.namedNode('http://example.org/person/1'),
      df.namedNode('http://xmlns.com/foaf/0.1/name')).size,
    1);
});

test('rmlMap: rejects a bad sourceKind and source text that is not JSON', async (t) => {
  if (await skipUnlessOps(t, 'rmlMap')) return;
  const mapping = '<http://e/TM> a <http://w3id.org/rml/TriplesMap> .';
  await assert.rejects(() => lean.rmlMap(mapping, '{}', 'xml'), TypeError);
  await assert.rejects(() => lean.rmlMap(mapping, 7, 'json'), TypeError);
  const full = `
    @prefix rml: <http://w3id.org/rml/> .
    @prefix ex: <http://example.org/> .
    ex:TM a rml:TriplesMap ;
      rml:logicalSource [ a rml:LogicalSource ; rml:iterator "$.p[*]" ;
        rml:referenceFormulation rml:JSONPath ;
        rml:source [ a rml:RelativePathSource ; rml:root rml:MappingDirectory ; rml:path "x" ] ] ;
      rml:subjectMap [ rml:template "http://example.org/{$.id}" ] .
  `;
  await assert.rejects(() => lean.rmlMap(full, 'not json', 'json'), /rmlMap/);
});

const CSVW_DIR = path.join(REPO, 'third_party', 'testing', 'csvw', 'tests');
const HAVE_CSVW = fs.existsSync(path.join(CSVW_DIR, 'tree-ops.csv'));

test('csvwToRdf: converts a vendored W3C CSVW fixture (minimal mode)',
  { skip: !HAVE_CSVW && 'CSVW fixtures not found' }, async (t) => {
    if (await skipUnlessOps(t, 'csvwToRdf')) return;
    const csv = fs.readFileSync(path.join(CSVW_DIR, 'tree-ops.csv'), 'utf8');
    const meta = fs.readFileSync(
      path.join(CSVW_DIR, 'test027-user-metadata.json'), 'utf8');
    const ds = await lean.csvwToRdf(csv, meta,
      { mode: 'minimal', base: 'http://example.org/' });
    assert.ok(ds instanceof Dataset);
    // 2 data rows x 5 columns, bare cell triples only in minimal mode.
    assert.equal(ds.size, 10);
    const subj = df.namedNode('http://example.org/tree-ops.csv#gid-1');
    assert.equal(ds.match(subj).size, 5);
    const street = ds.match(subj,
      df.namedNode('http://example.org/tree-ops.csv#on_street'));
    assert.equal(street.size, 1);
    assert.equal([...street][0].object.value, 'ADDISON AV');
    const nq = ds.toNQuads();
    assert.match(nq,
      /<http:\/\/example\.org\/tree-ops\.csv#gid-2> <http:\/\/example\.org\/tree-ops\.csv#species> "Liquidambar styraciflua"/);
  });

test('csvwToRdf: standard mode emits the csvw:TableGroup wrapper; no metadata infers from header',
  { skip: !HAVE_CSVW && 'CSVW fixtures not found' }, async (t) => {
    if (await skipUnlessOps(t, 'csvwToRdf')) return;
    const csv = fs.readFileSync(path.join(CSVW_DIR, 'tree-ops.csv'), 'utf8');
    const ds = await lean.csvwToRdf(csv, '',
      { base: 'http://example.org/', url: 'tree-ops.csv' });
    assert.ok(ds instanceof Dataset);
    const groupType = [...ds].filter((q) =>
      q.predicate.value === 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type' &&
      q.object.value === 'http://www.w3.org/ns/csvw#TableGroup');
    assert.equal(groupType.length, 1, 'standard mode wraps in a csvw:TableGroup');
    const rownums = [...ds].filter((q) =>
      q.predicate.value === 'http://www.w3.org/ns/csvw#rownum');
    assert.equal(rownums.length, 2, 'one csvw:rownum per data row');
  });

test('csvwToRdf: bad metadata and bad mode reject', async (t) => {
  if (await skipUnlessOps(t, 'csvwToRdf')) return;
  await assert.rejects(() => lean.csvwToRdf('a,b\n1,2\n', 'not json'), /csvwToRdf/);
  await assert.rejects(() => lean.csvwToRdf('a,b\n1,2\n', '', { mode: 'weird' }), /mode/);
  await assert.rejects(() => lean.csvwToRdf(5, ''), TypeError);
});

// ---------------------------------------------------------------------
// RIF (api.test.js, fn.test.js)
// ---------------------------------------------------------------------

const RIF_BODY = `
<Document xmlns="http://www.w3.org/2007/rif#">
  <payload>
    <Group>
      <sentence>
        <Forall>
          <declare><Var>x</Var></declare>
          <declare><Var>y</Var></declare>
          <formula>
            <Implies>
              <if>
                <Frame>
                  <object><Var>x</Var></object>
                  <slot ordered="yes">
                    <Const type="http://www.w3.org/2007/rif#iri">http://xmlns.com/foaf/0.1/knows</Const>
                    <Var>y</Var>
                  </slot>
                </Frame>
              </if>
              <then>
                <Frame>
                  <object><Var>y</Var></object>
                  <slot ordered="yes">
                    <Const type="http://www.w3.org/2007/rif#iri">http://xmlns.com/foaf/0.1/knows</Const>
                    <Var>x</Var>
                  </slot>
                </Frame>
              </then>
            </Implies>
          </formula>
        </Forall>
      </sentence>
    </Group>
  </payload>
</Document>`;
const RIF_DATA = '@prefix foaf: <http://xmlns.com/foaf/0.1/> . ' +
  '@prefix ex: <http://example.org/> . ex:alice foaf:knows ex:bob .';

async function assertSymmetricKnows(saturated) {
  assert.ok(saturated instanceof Dataset);
  assert.equal(
    saturated.match(df.namedNode('http://example.org/bob'),
      df.namedNode('http://xmlns.com/foaf/0.1/knows'),
      df.namedNode('http://example.org/alice')).size,
    1, 'the symmetric rule derives bob foaf:knows alice');
}

test('rifEval: RIF Core saturation materializes derived triples', async (t) => {
  if (await skipUnlessOps(t, 'rifEval')) return;
  await assertSymmetricKnows(await lean.rifEval(RIF_DATA,
    `<?xml version="1.0" encoding="UTF-8"?>${RIF_BODY}`));
});

test('rifEval: accepts the DOCTYPE and entity form real RIF fixtures use', async (t) => {
  if (await skipUnlessOps(t, 'rifEval')) return;
  const withEntities = `<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE Document [
  <!ENTITY rif "http://www.w3.org/2007/rif#">
]>${RIF_BODY.replace(/type="http:\/\/www\.w3\.org\/2007\/rif#iri"/g, 'type="&rif;iri"')}`;
  await assertSymmetricKnows(await lean.rifEval(RIF_DATA, withEntities));
});

test('rifEval: rules that do not parse reject', async (t) => {
  if (await skipUnlessOps(t, 'rifEval')) return;
  await assert.rejects(() => lean.rifEval(RIF_DATA, '<not rif'), /rifEval/);
  await assert.rejects(() => lean.rifEval(RIF_DATA, 7), TypeError);
});

// ---------------------------------------------------------------------
// XML, XPath, XSLT (api.test.js, xslt.test.js)
// ---------------------------------------------------------------------

test('xmlWellformed: accepts well-formed, rejects malformed', async (t) => {
  if (await skipUnlessOps(t, 'xmlWellformed')) return;
  assert.equal(await lean.xmlWellformed('<a><b/></a>'), true);
  assert.equal(await lean.xmlWellformed('<a><b></a>'), false);
  await assert.rejects(() => lean.xmlWellformed(1), TypeError);
});

test('xpathEval: XPath 1.0 over an XML document', async (t) => {
  if (await skipUnlessOps(t, 'xpathEval')) return;
  const r = await lean.xpathEval('<r><a>1</a><a>2</a></r>', 'count(/r/a)');
  assert.equal(r.resultType, 'number');
  assert.equal(Number(r.value), 2);
  const nodes = await lean.xpathEval('<r><a>1</a><a>2</a></r>', '/r/a');
  assert.equal(nodes.resultType, 'nodeset');
  assert.equal(nodes.count, 2);
  assert.equal(nodes.stringValue, '1');
  assert.deepEqual(nodes.nodes[1], { kind: 'element', name: 'a', value: '2' });
  const b = await lean.xpathEval('<r><a>1</a></r>', 'boolean(/r/a)');
  assert.deepEqual([b.resultType, b.value], ['boolean', true]);
  const s = await lean.xpathEval('<r><a>1</a></r>', 'string(/r/a)');
  assert.deepEqual([s.resultType, s.value], ['string', '1']);
});

test('xpathEval: a bad expression and bad XML reject', async (t) => {
  if (await skipUnlessOps(t, 'xpathEval')) return;
  await assert.rejects(() => lean.xpathEval('<r/>', 'count('), /xpathEval/);
  await assert.rejects(() => lean.xpathEval('<r>', '/r'), /xpathEval/);
});

const STYLESHEET = `<xsl:stylesheet version="1.0"
    xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
  <xsl:template match="/">
    <greeting><xsl:value-of select="/doc/name"/></greeting>
  </xsl:template>
</xsl:stylesheet>`;
const XSLT_SOURCE = '<doc><name>World</name></doc>';

test('xsltTransform: value-of into a literal result element', async (t) => {
  if (await skipUnlessOps(t, 'xsltTransform')) return;
  const out = await lean.xsltTransform(STYLESHEET, XSLT_SOURCE);
  assert.equal(typeof out, 'string');
  assert.match(out, /greeting/);
  assert.match(out, /World/);
});

test('xsltTransform: identity-style xsl:copy-of', async (t) => {
  if (await skipUnlessOps(t, 'xsltTransform')) return;
  const ss = `<xsl:stylesheet version="1.0"
      xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
    <xsl:template match="/"><xsl:copy-of select="/doc/name"/></xsl:template>
  </xsl:stylesheet>`;
  const out = await lean.xsltTransform(ss, XSLT_SOURCE);
  assert.match(out, /<name>World<\/name>/);
});

test('xsltTransform: rejects malformed XML', async (t) => {
  if (await skipUnlessOps(t, 'xsltTransform')) return;
  await assert.rejects(() => lean.xsltTransform('<not well formed', XSLT_SOURCE));
});

// ---------------------------------------------------------------------
// Schematron, JSON Schema (schematron.test.js, jsonschema.test.js)
// ---------------------------------------------------------------------

const SCHEMATRON = `<schema xmlns="http://purl.oclc.org/dsdl/schematron">
  <pattern>
    <rule context="doc">
      <assert test="@ok">doc must carry an ok attribute</assert>
    </rule>
  </pattern>
</schema>`;

test('schematronValidate: failing assert produces a finding', async (t) => {
  if (await skipUnlessOps(t, 'schematronValidate')) return;
  const r = await lean.schematronValidate(SCHEMATRON, '<doc/>');
  assert.ok(Array.isArray(r.findings));
  assert.ok(r.findings.length >= 1);
  const f = r.findings.find((x) => x.type === 'assert-fail');
  assert.ok(f, 'expected an assert-fail finding');
  assert.match(f.message, /ok attribute/);
});

test('schematronValidate: satisfied assert produces no assert-fail', async (t) => {
  if (await skipUnlessOps(t, 'schematronValidate')) return;
  const r = await lean.schematronValidate(SCHEMATRON, '<doc ok="yes"/>');
  assert.equal(r.findings.filter((x) => x.type === 'assert-fail').length, 0);
});

test('jsonSchemaValidate: {type:"integer"} accepts an integer', async (t) => {
  if (await skipUnlessOps(t, 'jsonSchemaValidate')) return;
  const r = await lean.jsonSchemaValidate('{"type":"integer"}', '5');
  assert.equal(r.valid, true);
  assert.equal(r.result, 'pass');
  assert.deepEqual(r.errors, []);
});

test('jsonSchemaValidate: {type:"integer"} rejects a string', async (t) => {
  if (await skipUnlessOps(t, 'jsonSchemaValidate')) return;
  const r = await lean.jsonSchemaValidate('{"type":"integer"}', '"hello"');
  assert.equal(r.valid, false);
  assert.notEqual(r.result, 'pass');
  assert.ok(r.errors.length >= 1);
});

// ---------------------------------------------------------------------
// MathML, XForms (mathml.test.js, xforms.test.js)
// ---------------------------------------------------------------------

const MATHML_NS = 'http://www.w3.org/1998/Math/MathML';

test('mathmlEval: 2 + 3 = 5/1 (exact rational)', async (t) => {
  if (await skipUnlessOps(t, 'mathmlEval')) return;
  const xml = `<math xmlns="${MATHML_NS}">
    <apply><plus/><cn>2</cn><cn>3</cn></apply>
  </math>`;
  const v = await lean.mathmlEval(xml, {});
  assert.equal(v.kind, 'rat');
  assert.equal(v.num, 5);
  assert.equal(v.den, 1);
});

test('mathmlEval: division by zero is undef, not a bogus number', async (t) => {
  if (await skipUnlessOps(t, 'mathmlEval')) return;
  const xml = `<math xmlns="${MATHML_NS}">
    <apply><divide/><cn>1</cn><cn>0</cn></apply>
  </math>`;
  const v = await lean.mathmlEval(xml, {});
  assert.equal(v.kind, 'undef');
  assert.equal(typeof v.reason, 'string');
});

test('mathmlEval: ci bindings, a boolean value, and a vector value', async (t) => {
  if (await skipUnlessOps(t, 'mathmlEval')) return;
  const times = `<math xmlns="${MATHML_NS}"><apply><times/><ci>x</ci><cn>2</cn></apply></math>`;
  assert.deepEqual(await lean.mathmlEval(times, { x: '3' }), { kind: 'rat', num: 6, den: 1 });
  assert.deepEqual(await lean.mathmlEval(times, { x: 3 }), { kind: 'rat', num: 6, den: 1 });
  const lt = `<math xmlns="${MATHML_NS}"><apply><lt/><cn>1</cn><cn>2</cn></apply></math>`;
  assert.deepEqual(await lean.mathmlEval(lt), { kind: 'bool', value: true });
  const vec = `<math xmlns="${MATHML_NS}"><vector><cn>1</cn><cn>2</cn></vector></math>`;
  assert.deepEqual(await lean.mathmlEval(vec), { kind: 'vector', value: [[1, 1], [2, 1]] });
});

test('mathmlEval: a bindings value that is not a numeral rejects', async (t) => {
  if (await skipUnlessOps(t, 'mathmlEval')) return;
  const xml = `<math xmlns="${MATHML_NS}"><ci>x</ci></math>`;
  await assert.rejects(() => lean.mathmlEval(xml, { x: 'abc' }), /mathmlEval/);
  await assert.rejects(() => lean.mathmlEval(xml, 5), TypeError);
});

const XFORMS_INSTANCE = '<data><x>5</x><y>0</y></data>';

test('xformsRecalc: constant calculate writes the leaf', async (t) => {
  if (await skipUnlessOps(t, 'xformsRecalc')) return;
  const r = await lean.xformsRecalc(XFORMS_INSTANCE, [{ target: 'y', calculate: '7' }]);
  assert.equal(typeof r.instance, 'string');
  assert.ok(Array.isArray(r.validity));
  assert.match(r.instance, /<y>7<\/y>/);
  const yv = r.validity.find((v) => v.target === 'y');
  assert.ok(yv, 'expected a validity entry for y');
  assert.equal(yv.value, '7');
});

test('xformsRecalc: no binds leaves the instance well-formed', async (t) => {
  if (await skipUnlessOps(t, 'xformsRecalc')) return;
  const r = await lean.xformsRecalc(XFORMS_INSTANCE, []);
  assert.equal(typeof r.instance, 'string');
  assert.deepEqual(r.validity, []);
});

test('xformsRecalc: a constraint and a type MIP are reported per node', async (t) => {
  if (await skipUnlessOps(t, 'xformsRecalc')) return;
  const r = await lean.xformsRecalc('<data><n>abc</n></data>',
    [{ target: 'n', type: 'integer', constraint: 'string-length(.) > 5' }]);
  const nv = r.validity.find((v) => v.target === 'n');
  assert.equal(nv.typeValid, false);
  assert.equal(nv.constraint, false);
  assert.equal(nv.valid, false);
});

// ---------------------------------------------------------------------
// TOAN (toan.test.js)
// ---------------------------------------------------------------------

const TOAN_BODY = {
  app: 'plus',
  args: [
    { sym: 'x' },
    { app: 'times', args: [{ sym: 'i' }, { sym: 'y' }] },
  ],
};

test('toanSummation: sum_{i=1}^{4} (x + i*y) = 4x + 10y', async (t) => {
  if (await skipUnlessOps(t, 'toanSummation')) return;
  const mathml = await lean.toanSummation(TOAN_BODY, 'i', 1, 4);
  assert.equal(typeof mathml, 'string');
  assert.match(mathml, /<cn[^>]*>4<\/cn>/);
  assert.match(mathml, /<cn[^>]*>10<\/cn>/);
  assert.match(mathml, /<ci>x<\/ci>/);
  assert.match(mathml, /<ci>y<\/ci>/);
});

test('toanProduct: product_{i=1}^{3} i = 6', async (t) => {
  if (await skipUnlessOps(t, 'toanProduct')) return;
  const mathml = await lean.toanProduct({ sym: 'i' }, 'i', 1, 3);
  assert.match(mathml, /<cn[^>]*>6<\/cn>/);
});

test('toanSimplify: 2 + 3 collapses to 5', async (t) => {
  if (await skipUnlessOps(t, 'toanSimplify')) return;
  const mathml = await lean.toanSimplify(
    { app: 'plus', args: [{ int: 2 }, { int: 3 }] });
  assert.match(mathml, /<cn[^>]*>5<\/cn>/);
});

test('toanDiff: d/dx (x*x) mentions x', async (t) => {
  if (await skipUnlessOps(t, 'toanDiff')) return;
  const mathml = await lean.toanDiff(
    { app: 'times', args: [{ sym: 'x' }, { sym: 'x' }] }, 'x');
  assert.equal(typeof mathml, 'string');
  assert.match(mathml, /math/);
});

test('toanSubst: (x + 1)[x := 4] mentions 4', async (t) => {
  if (await skipUnlessOps(t, 'toanSubst')) return;
  const mathml = await lean.toanSubst(
    { app: 'plus', args: [{ sym: 'x' }, { int: 1 }] }, 'x', { int: 4 });
  assert.match(mathml, /<cn[^>]*>4<\/cn>/);
});

// ---------------------------------------------------------------------
// HDT (hdt.test.js)
// ---------------------------------------------------------------------

const FIXTURE_HDT = path.join(
  REPO, 'third_party', 'testing', 'hdt', 'rml-core-ontology.hdt');
const HAVE_HDT = fs.existsSync(FIXTURE_HDT);

test('queryHdt: SELECT COUNT(*) over the RML-Core HDT fixture is 343',
  { skip: !HAVE_HDT && 'HDT fixture not found' }, async (t) => {
    if (await skipUnlessOps(t, 'queryHdt')) return;
    const bytes = fs.readFileSync(FIXTURE_HDT);
    const rows = await lean.queryHdt(bytes, 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }');
    assert.equal(rows.length, 1);
    assert.equal(rows[0].get('n').value, '343');
  });

test('queryHdt: ASK over the same fixture is true',
  { skip: !HAVE_HDT && 'HDT fixture not found' }, async (t) => {
    if (await skipUnlessOps(t, 'queryHdt')) return;
    const bytes = fs.readFileSync(FIXTURE_HDT);
    assert.equal(await lean.queryHdt(bytes, 'ASK { ?s ?p ?o }'), true);
    assert.equal(await lean.queryHdt(bytes,
      'ASK { <http://example.org/none> <http://example.org/none> ?o }'), false);
  });

test('queryHdt: SELECT bindings carry real RDF/JS terms (owl:Class labels)',
  { skip: !HAVE_HDT && 'HDT fixture not found' }, async (t) => {
    if (await skipUnlessOps(t, 'queryHdt')) return;
    const bytes = fs.readFileSync(FIXTURE_HDT);
    const query = `PREFIX owl: <http://www.w3.org/2002/07/owl#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
SELECT ?class ?label WHERE {
  ?class a owl:Class ; rdfs:label ?label .
} ORDER BY ?label`;
    const rows = await lean.queryHdt(bytes, query);
    assert.ok(rows.length >= 20, `expected >= 20 class rows, got ${rows.length}`);
    const labels = rows.map((r) => r.get('label').value);
    for (const expected of ['Triples Map', 'Subject Map', 'Object Map']) {
      assert.ok(labels.includes(expected), `missing class label ${expected}`);
    }
    assert.equal(rows[0].get('class').termType, 'NamedNode');
  });

test('queryHdt: accepts an ArrayBuffer, not just a Buffer/Uint8Array',
  { skip: !HAVE_HDT && 'HDT fixture not found' }, async (t) => {
    if (await skipUnlessOps(t, 'queryHdt')) return;
    const buf = fs.readFileSync(FIXTURE_HDT);
    const ab = buf.buffer.slice(buf.byteOffset, buf.byteOffset + buf.byteLength);
    const rows = await lean.queryHdt(ab, 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }');
    assert.equal(rows[0].get('n').value, '343');
  });

test('queryHdt: CONSTRUCT rejects (SELECT/ASK only over HDT)',
  { skip: !HAVE_HDT && 'HDT fixture not found' }, async (t) => {
    if (await skipUnlessOps(t, 'queryHdt')) return;
    const bytes = fs.readFileSync(FIXTURE_HDT);
    await assert.rejects(
      () => lean.queryHdt(bytes, 'CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }'),
      /SELECT\/ASK only/);
  });

test('queryHdt: bytes that are not an HDT file reject', async (t) => {
  if (await skipUnlessOps(t, 'queryHdt')) return;
  await assert.rejects(
    () => lean.queryHdt(Buffer.from('this is not an HDT file'), 'ASK { ?s ?p ?o }'),
    /queryHdt: .*HDT/);
  await assert.rejects(() => lean.queryHdt(42, 'ASK { ?s ?p ?o }'), TypeError);
});

// ---------------------------------------------------------------------
// SPARQL 1.1 section 17.6 extension functions (extension-functions.test.js)
// ---------------------------------------------------------------------

const EX = 'http://example.org/fn#';
const EXT_DATA = `
@prefix : <http://example.org/> .
:alice :name "Alice" ; :age 30 .
:bob   :name "Bob"   ; :age 7 .
`;

test('extension functions: sync and async functions, errors, unregister, clear', async (t) => {
  if (await skipUnlessOps(t, 'extRegister', 'extUnregister', 'extClear')) return;
  const { query, registerExtensionFunction, unregisterExtensionFunction,
    clearExtensionFunctions } = lean;
  await clearExtensionFunctions();
  try {
    // unknown IRI: FILTER drops every row, BIND leaves the variable unbound
    assert.deepEqual(await query(EXT_DATA, `
      PREFIX fn: <${EX}>
      SELECT ?s WHERE { ?s <http://example.org/name> ?n .
                        FILTER(fn:noSuchFunction(?n)) }`), []);
    const unbound = await query(EXT_DATA, `
      PREFIX fn: <${EX}>
      SELECT ?s ?x WHERE { ?s <http://example.org/name> ?n .
                           BIND(fn:noSuchFunction(?n) AS ?x) }`);
    assert.equal(unbound.length, 2);
    for (const row of unbound) assert.equal(row.get('x'), undefined);

    // sync, boolean return, in FILTER
    await registerExtensionFunction(`${EX}isAdult`, (args) => {
      assert.equal(args.length, 1);
      assert.equal(args[0].type, 'literal');
      return Number(args[0].value) >= 18;
    });
    const adults = await query(EXT_DATA, `
      PREFIX fn: <${EX}>
      SELECT ?s WHERE { ?s <http://example.org/age> ?a . FILTER(fn:isAdult(?a)) }`);
    assert.equal(adults.length, 1);
    assert.equal(adults[0].get('s').value, 'http://example.org/alice');

    // sync, string return, in BIND
    await registerExtensionFunction(`${EX}shout`, (args) =>
      String(args[0].value).toUpperCase());
    const loud = await query(EXT_DATA, `
      PREFIX fn: <${EX}>
      SELECT ?loud WHERE { ?s <http://example.org/name> ?n . BIND(fn:shout(?n) AS ?loud) }
      ORDER BY ?loud`);
    assert.deepEqual(loud.map((r) => r.get('loud').value), ['ALICE', 'BOB']);

    // sync, number return, in a SELECT expression
    await registerExtensionFunction(`${EX}double`, (args) => 2 * Number(args[0].value));
    const doubled = await query(EXT_DATA, `
      PREFIX fn: <${EX}>
      SELECT ?s (fn:double(?a) AS ?d)
      WHERE { ?s <http://example.org/age> ?a } ORDER BY ?d`);
    assert.deepEqual(doubled.map((r) => r.get('d').value), ['14', '60']);

    // async in FILTER, resolved by the re-evaluation trampoline
    await registerExtensionFunction(`${EX}isAdultAsync`, async (args) => {
      await new Promise((resolve) => setTimeout(resolve, 5));
      return Number(args[0].value) >= 18;
    });
    const asyncAdults = await query(EXT_DATA, `
      PREFIX fn: <${EX}>
      SELECT ?s WHERE { ?s <http://example.org/age> ?a . FILTER(fn:isAdultAsync(?a)) }`);
    assert.equal(asyncAdults.length, 1);
    assert.equal(asyncAdults[0].get('s').value, 'http://example.org/alice');

    // async, term-object return with a datatype
    await registerExtensionFunction(`${EX}category`, async (args) => ({
      type: 'literal',
      value: Number(args[0].value) >= 18 ? 'adult' : 'child',
      datatype: 'http://www.w3.org/2001/XMLSchema#string',
    }));
    const cats = await query(EXT_DATA, `
      PREFIX fn: <${EX}>
      SELECT ?s ?c WHERE { ?s <http://example.org/age> ?a . BIND(fn:category(?a) AS ?c) }
      ORDER BY ?s`);
    assert.deepEqual(cats.map((r) => r.get('c').value), ['adult', 'child']);

    // two async functions chain across rounds
    await registerExtensionFunction(`${EX}plusOne`, async (args) => Number(args[0].value) + 1);
    await registerExtensionFunction(`${EX}timesTen`, async (args) => Number(args[0].value) * 10);
    const chained = await query(EXT_DATA, `
      PREFIX fn: <${EX}>
      SELECT ?s (fn:timesTen(fn:plusOne(?a)) AS ?v)
      WHERE { ?s <http://example.org/age> ?a } ORDER BY ?v`);
    assert.deepEqual(chained.map((r) => r.get('v').value), ['80', '310']);

    // uri return
    await registerExtensionFunction(`${EX}toIri`, (args) => ({
      type: 'uri',
      value: 'http://example.org/minted/' + args[0].value,
    }));
    const minted = await query(EXT_DATA, `
      PREFIX fn: <${EX}>
      SELECT (fn:toIri(?n) AS ?i)
      WHERE { <http://example.org/alice> <http://example.org/name> ?n }`);
    assert.equal(minted[0].get('i').termType, 'NamedNode');
    assert.equal(minted[0].get('i').value, 'http://example.org/minted/Alice');

    // throwing and rejecting functions are the 17.6 error, not a crash
    await registerExtensionFunction(`${EX}boom`, () => { throw new Error('sync boom'); });
    await registerExtensionFunction(`${EX}boomAsync`, async () => { throw new Error('async boom'); });
    const boom = await query(EXT_DATA, `
      PREFIX fn: <${EX}>
      SELECT ?s ?x ?y WHERE { ?s <http://example.org/name> ?n .
                              BIND(fn:boom(?n) AS ?x)
                              BIND(fn:boomAsync(?n) AS ?y) }`);
    assert.equal(boom.length, 2);
    for (const row of boom) {
      assert.equal(row.get('x'), undefined);
      assert.equal(row.get('y'), undefined);
    }

    // unregister restores the unknown-IRI error
    const transient = `${EX}transient`;
    await registerExtensionFunction(transient, () => true);
    const before = await query(EXT_DATA, `
      SELECT ?s WHERE { ?s <http://example.org/name> ?n . FILTER(<${transient}>(?n)) }`);
    assert.equal(before.length, 2);
    await unregisterExtensionFunction(transient);
    assert.deepEqual(await query(EXT_DATA, `
      SELECT ?s WHERE { ?s <http://example.org/name> ?n . FILTER(<${transient}>(?n)) }`), []);

    // built-ins keep precedence: an xsd cast IRI is never offered to the registry
    let called = false;
    await registerExtensionFunction(
      'http://www.w3.org/2001/XMLSchema#integer', () => { called = true; return 999; });
    const cast = await query(EXT_DATA, `
      PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>
      SELECT (xsd:integer("41") AS ?v) WHERE {}`);
    assert.equal(cast[0].get('v').value, '41');
    assert.equal(called, false);

    // clear removes every registration
    await clearExtensionFunctions();
    assert.deepEqual(await query(EXT_DATA, `
      PREFIX fn: <${EX}>
      SELECT ?s WHERE { ?s <http://example.org/age> ?a . FILTER(fn:isAdult(?a)) }`), []);
  } finally {
    await clearExtensionFunctions();
  }
});

test('registerExtensionFunction: argument checks', async (t) => {
  if (await skipUnlessOps(t, 'extRegister')) return;
  await assert.rejects(() => lean.registerExtensionFunction('not an iri', () => 1), TypeError);
  await assert.rejects(() => lean.registerExtensionFunction(`${EX}f`, 'nope'), TypeError);
});

// ---------------------------------------------------------------------
// SPARQL SERVICE endpoint registry (no F* npm test: new here)
// ---------------------------------------------------------------------

test('registerServiceEndpoint: SERVICE resolves against a registered snapshot until cleared', async (t) => {
  if (await skipUnlessOps(t, 'registerServiceEndpoint', 'clearServiceEndpoints')) return;
  const ENDPOINT = 'http://example.org/sparql';
  const q = `SELECT ?s ?o WHERE { SERVICE <${ENDPOINT}> { ?s <http://e/p> ?o } }`;
  const local = '<http://e/x> <http://e/q> <http://e/y> .';
  await lean.clearServiceEndpoints();
  try {
    // SPARQL 1.1 Federated Query 2.3: with SILENT, a failed call is one
    // solution with no bindings. Without SILENT the query fails: the
    // case below (issue 717).
    const silent = await lean.query(local,
      `SELECT * WHERE { SERVICE SILENT <${ENDPOINT}> { ?s <http://e/p> ?o } }`,
      { format: 'ntriples' });
    assert.equal(silent.length, 1);
    assert.equal([...silent[0].keys()].length, 0);
    const reg = await lean.registerServiceEndpoint(ENDPOINT,
      '<http://e/a> <http://e/p> "v" .', { format: 'ntriples' });
    assert.equal(reg.ok, true);
    assert.equal(reg.count, 1);
    const rows = await lean.query(local, q, { format: 'ntriples' });
    assert.equal(rows.length, 1);
    assert.equal(rows[0].get('s').value, 'http://e/a');
    assert.equal(rows[0].get('o').value, 'v');
    // a dataset handle sees the same registry
    const handle = await lean.openDataset(local, { format: 'ntriples' });
    const viaHandle = await handle.query(q);
    assert.equal(viaHandle.length, 1);
    handle.dispose();
    // registering the same IRI again replaces the snapshot
    await lean.registerServiceEndpoint(ENDPOINT, '<http://e/a> <http://e/p> "w" .',
      { format: 'ntriples' });
    const replaced = await lean.query(local, q, { format: 'ntriples' });
    assert.deepEqual(replaced.map((r) => r.get('o').value), ['w']);
    await lean.clearServiceEndpoints();
  } finally {
    await lean.clearServiceEndpoints();
  }
});

// SPARQL 1.1 Federated Query 2.3: "If the SILENT keyword is not present,
// the query will stop and return the error." Was an expected failure until
// https://github.com/danbri/factoidal/issues/717 was fixed.
test('SERVICE without SILENT to an unreachable endpoint fails the query (issue 717)', async (t) => {
  if (await skipUnlessOps(t, 'clearServiceEndpoints')) return;
  await lean.clearServiceEndpoints();
  await assert.rejects(() => lean.query('<http://e/x> <http://e/q> <http://e/y> .',
    'SELECT * WHERE { SERVICE <http://unregistered.example/sparql> { ?s ?p ?o } }',
    { format: 'ntriples' }),
  /SERVICE <http:\/\/unregistered\.example\/sparql> failed/);
  // the same call with SILENT answers one solution with no bindings
  const silent = await lean.query('<http://e/x> <http://e/q> <http://e/y> .',
    'SELECT * WHERE { SERVICE SILENT <http://unregistered.example/sparql> { ?s ?p ?o } }',
    { format: 'ntriples' });
  assert.equal(silent.length, 1);
  assert.equal([...silent[0].keys()].length, 0);
});

// SPARQL 1.1 Federated Query 2.3 and 3.2. Were expected failures until
// https://github.com/danbri/factoidal/issues/735 was fixed.
test('SERVICE without SILENT inside FILTER EXISTS fails the query (issue 735)', async (t) => {
  if (await skipUnlessOps(t, 'clearServiceEndpoints')) return;
  await lean.clearServiceEndpoints();
  await assert.rejects(() => lean.query('<http://e/x> <http://e/q> <http://e/y> .',
    'SELECT * WHERE { ?s ?p ?o FILTER EXISTS { SERVICE <http://unregistered.example/sparql> { ?a ?b ?c } } }',
    { format: 'ntriples' }),
  /SERVICE <http:\/\/unregistered\.example\/sparql> failed/);
  // the same call with SILENT is one solution with no bindings, so the
  // EXISTS is true and the local row stays
  const silent = await lean.query('<http://e/x> <http://e/q> <http://e/y> .',
    'SELECT * WHERE { ?s ?p ?o FILTER EXISTS { SERVICE SILENT <http://unregistered.example/sparql> { ?a ?b ?c } } }',
    { format: 'ntriples' });
  assert.equal(silent.length, 1);
  assert.equal(silent[0].get('s').value, 'http://e/x');
});

test('an outer SERVICE SILENT covers a failed nested SERVICE (issue 735)', async (t) => {
  if (await skipUnlessOps(t, 'registerServiceEndpoint', 'clearServiceEndpoints')) return;
  const OUTER = 'http://example.org/outer-sparql';
  await lean.clearServiceEndpoints();
  try {
    await lean.registerServiceEndpoint(OUTER, '<http://e/a> <http://e/p> "v" .', { format: 'ntriples' });
    const rows = await lean.query('<http://e/x> <http://e/q> <http://e/y> .',
      `SELECT * WHERE { SERVICE SILENT <${OUTER}> { SERVICE <http://unregistered.example/sparql> { ?a ?b ?c } } }`,
      { format: 'ntriples' });
    assert.equal(rows.length, 1);
    assert.equal([...rows[0].keys()].length, 0);
    // without SILENT on the outer call the query fails
    await assert.rejects(() => lean.query('<http://e/x> <http://e/q> <http://e/y> .',
      `SELECT * WHERE { SERVICE <${OUTER}> { SERVICE <http://unregistered.example/sparql> { ?a ?b ?c } } }`,
      { format: 'ntriples' }),
    /SERVICE <http:\/\/unregistered\.example\/sparql> failed/);
  } finally {
    await lean.clearServiceEndpoints();
  }
});

test('registerServiceEndpoint: argument checks', async (t) => {
  if (await skipUnlessOps(t, 'registerServiceEndpoint')) return;
  await assert.rejects(() => lean.registerServiceEndpoint('nope', '<a:b> <a:c> <a:d> .',
    { format: 'ntriples' }), TypeError);
});

// ---------------------------------------------------------------------
// OWL tableau (no F* npm test: new here)
// ---------------------------------------------------------------------

const OWL = 'http://www.w3.org/2002/07/owl#';
const RDF_TYPE = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type';

test('tableauMaterialise: adds the membership a hasValue restriction defines', async (t) => {
  if (await skipUnlessOps(t, 'tableauMaterialise')) return;
  const ttl = `
    @prefix owl: <${OWL}> .
    @prefix ex: <http://e/> .
    ex:C owl:equivalentClass [ a owl:Restriction ; owl:onProperty ex:p ; owl:hasValue ex:v ] .
    ex:i ex:p ex:v .
  `;
  const before = await lean.parse(ttl);
  const { dataset, addedCount, budgetHit } = await lean.tableauMaterialise(ttl);
  assert.ok(dataset instanceof Dataset);
  assert.equal(addedCount, 1);
  assert.equal(dataset.size, before.size + 1);
  assert.equal(budgetHit, false);
  const typed = [...dataset].filter((q) =>
    q.subject.value === 'http://e/i' && q.predicate.value === RDF_TYPE);
  assert.equal(typed.length, 1);
});

test('tableauMaterialise: a graph with nothing to add adds nothing', async (t) => {
  if (await skipUnlessOps(t, 'tableauMaterialise')) return;
  const r = await lean.tableauMaterialise('<http://e/a> a <http://e/C> .');
  assert.equal(r.addedCount, 0);
});

test('tableauDlInconsistent: the tableau finds a clash the RL closure alone does not', async (t) => {
  if (await skipUnlessOps(t, 'tableauDlInconsistent')) return;
  const dlOnly = `
    @prefix owl: <${OWL}> .
    @prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
    @prefix ex: <http://e/> .
    ex:K owl:equivalentClass [ a owl:Restriction ; owl:onProperty ex:p ;
         owl:minCardinality "1"^^xsd:nonNegativeInteger ] ;
       owl:disjointWith ex:D .
    ex:i ex:p ex:v ; a ex:D .
  `;
  assert.deepEqual(await lean.tableauDlInconsistent(dlOnly),
    { inconsistent: true, rlAlone: false });
  const rlClash = `
    @prefix owl: <${OWL}> .
    @prefix ex: <http://e/> .
    ex:C owl:disjointWith ex:D . ex:a a ex:C, ex:D .
  `;
  assert.deepEqual(await lean.tableauDlInconsistent(rlClash),
    { inconsistent: true, rlAlone: true });
  assert.deepEqual(await lean.tableauDlInconsistent('<http://e/a> a <http://e/C> .'),
    { inconsistent: false, rlAlone: false });
});

// ---------------------------------------------------------------------
// queryRaw (smoke.js)
// ---------------------------------------------------------------------

const RAW_DATA = `
  @prefix ex:   <http://example.org/> .
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:age 30 ; foaf:knows ex:bob .
  ex:bob   a foaf:Person ; foaf:name "Bob"   ; foaf:age 42 ; foaf:knows ex:alice .
  ex:carol a foaf:Person ; foaf:name "Carol"@en ; foaf:age 27 .
`;
const RAW_NAMES = `
  PREFIX foaf: <http://xmlns.com/foaf/0.1/>
  SELECT ?name WHERE { ?p foaf:name ?name } ORDER BY ?name`;

test('queryRaw: SELECT with the default options returns SPARQL results JSON', async (t) => {
  if (await skipUnlessOps(t, 'queryRaw')) return;
  const r = await lean.queryRaw(RAW_DATA, `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    SELECT ?name WHERE { ?p foaf:name ?name }`);
  assert.deepEqual(r.head.vars, ['name']);
  assert.deepEqual(r.results.bindings.map((b) => b.name.value).sort(),
    ['Alice', 'Bob', 'Carol']);
});

test('queryRaw: dataFormat ntriples and ASK', async (t) => {
  if (await skipUnlessOps(t, 'queryRaw')) return;
  const r = await lean.queryRaw(
    '<http://example.org/alice> <http://xmlns.com/foaf/0.1/name> "Alice" .\n' +
    '<http://example.org/bob>   <http://xmlns.com/foaf/0.1/name> "Bob"   .\n',
    'SELECT * WHERE { ?s ?p ?o }', { dataFormat: 'ntriples' });
  assert.equal(r.results.bindings.length, 2);
  const ask = await lean.queryRaw(RAW_DATA, `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    PREFIX ex:   <http://example.org/>
    ASK { ex:alice foaf:knows ex:bob }`);
  assert.ok(ask.head);
  assert.equal(ask.boolean, true);
});

test('queryRaw: entail RDFS adds the subclass instance', async (t) => {
  if (await skipUnlessOps(t, 'queryRaw')) return;
  const data = `
    @prefix schema: <http://schema.org/> .
    @prefix rdfs:   <http://www.w3.org/2000/01/rdf-schema#> .
    @prefix ex:     <http://example.org/> .
    schema:Place   a rdfs:Class .
    schema:Hotel   rdfs:subClassOf schema:Place .
    ex:motel6      a schema:Hotel ; schema:name "Motel 6" .
  `;
  const q = 'PREFIX schema: <http://schema.org/> SELECT ?s WHERE { ?s a schema:Place }';
  const none = await lean.queryRaw(data, q);
  const rdfs = await lean.queryRaw(data, q, { entail: 'RDFS' });
  assert.equal(none.results.bindings.length, 0);
  assert.ok(rdfs.results.bindings.length >= 1);
});

test('queryRaw: output formats csv, tsv, xml and table return strings', async (t) => {
  if (await skipUnlessOps(t, 'queryRaw')) return;
  const csv = await lean.queryRaw(RAW_DATA, RAW_NAMES, { output: 'csv' });
  assert.equal(typeof csv, 'string');
  assert.ok(csv.startsWith('name'), 'CSV has the header');
  assert.ok(csv.includes('Alice'));
  const tsv = await lean.queryRaw(RAW_DATA, RAW_NAMES, { output: 'tsv' });
  assert.ok(tsv.startsWith('?name'));
  const xml = await lean.queryRaw(RAW_DATA, RAW_NAMES, { output: 'xml' });
  assert.match(xml, /<sparql xmlns="http:\/\/www\.w3\.org\/2005\/sparql-results#">/);
  const table = await lean.queryRaw(RAW_DATA, RAW_NAMES, { output: 'table' });
  assert.equal(typeof table, 'string');
  assert.ok(table.length > 0);
});

test('queryRaw: a bad query rejects with diagnostic fields; bad options are TypeErrors', async (t) => {
  if (await skipUnlessOps(t, 'queryRaw')) return;
  let threw = null;
  try {
    await lean.queryRaw(RAW_DATA, 'SELECT WITHOUT WHERE BUT MALFORMED');
  } catch (e) {
    threw = e;
  }
  assert.ok(threw instanceof Error);
  assert.ok(threw.exitCode !== 0 || threw.stderr || threw.stdout,
    'error should carry diagnostic info');
  await assert.rejects(() => lean.queryRaw(RAW_DATA, RAW_NAMES, { output: 'yaml' }), TypeError);
  await assert.rejects(() => lean.queryRaw(RAW_DATA, RAW_NAMES, { entail: 'x-nope' }), TypeError);
  await assert.rejects(() => lean.queryRaw(RAW_DATA, RAW_NAMES, { dataFormat: 'nope' }), TypeError);
  await assert.rejects(() => lean.queryRaw(1, RAW_NAMES), TypeError);
});
