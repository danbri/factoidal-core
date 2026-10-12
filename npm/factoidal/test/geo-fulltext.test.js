// text:query (jena-text, slice 1) and the GeoSPARQL non-topological
// functions geof:distance and geof:envelope, through the npm API
// (https://github.com/danbri/factoidal/issues/727).
//
// The package's query entry tries the backend runners first; a query that
// holds a text:query pattern is answered by the reference evaluator. The
// ASK, COUNT(*) and LIMIT cases below are the shapes whose backend fast
// path would read the pattern as an ordinary triple and answer nothing
// (the F* engine's defect on them is
// https://github.com/danbri/factoidal/issues/774).
//
// Design record: docs/designissues/2026-10-10-lean-geo-distance-fulltext.md
const { xfail } = require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');

const { parse, query } = require('..');

const METRES_ISSUE = 'https://github.com/danbri/factoidal/issues/772';

const FT_TTL = `
  @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
  @prefix dc:   <http://purl.org/dc/elements/1.1/> .
  @prefix ex:   <http://example.org/> .
  ex:panel1 rdfs:label "Solar panel array" ; dc:title "Rooftop installation" ; ex:status "active" .
  ex:panel2 rdfs:label "Solar panel kit" ; dc:title "Backyard installation" ; ex:status "active" .
  ex:heater rdfs:label "Water heater" ; dc:title "Boiler room unit" ; ex:status "retired" .
  ex:battery rdfs:label "Battery storage panel" ; dc:title "Energy storage unit" ; ex:status "retired" .
  ex:controlpanel rdfs:label "Interface unit" ; dc:title "Control panel interface" ; ex:status "active" .
`;

const PRE = `
  PREFIX text: <http://jena.apache.org/text#>
  PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
  PREFIX dc:   <http://purl.org/dc/elements/1.1/>
  PREFIX ex:   <http://example.org/>
`;

const subjects = (rows) => {
  const out = [];
  for (const b of rows) out.push(b.get('s').value.replace('http://example.org/', ''));
  return out.sort();
};

test('text:query: bare string searches every literal', async () => {
  const ds = await parse(FT_TTL, { format: 'turtle' });
  const rows = await query(ds, `${PRE} SELECT ?s WHERE { ?s text:query "panel" }`);
  assert.deepEqual(subjects(rows), ['battery', 'controlpanel', 'panel1', 'panel2']);
});

test('text:query: several words match only a literal holding all of them', async () => {
  const ds = await parse(FT_TTL, { format: 'turtle' });
  const rows = await query(ds, `${PRE} SELECT ?s WHERE { ?s text:query "PANEL solar" }`);
  assert.deepEqual(subjects(rows), ['panel1', 'panel2']);
});

test('text:query: a field restricts the predicate; tokens are not substrings', async () => {
  const ds = await parse(FT_TTL, { format: 'turtle' });
  let rows = await query(ds, `${PRE} SELECT ?s WHERE { ?s text:query (dc:title "panel") }`);
  assert.deepEqual(subjects(rows), ['controlpanel']);
  rows = await query(ds, `${PRE} SELECT ?s WHERE { ?s text:query "pane" }`);
  assert.deepEqual(subjects(rows), []);
});

test('text:query: a limit keeps the first n matches in document order', async () => {
  const ds = await parse(FT_TTL, { format: 'turtle' });
  const rows = await query(ds, `${PRE} SELECT ?s WHERE { ?s text:query (rdfs:label "panel" 2) }`);
  assert.deepEqual(subjects(rows), ['panel1', 'panel2']);
});

test('text:query: joins with an ordinary triple pattern', async () => {
  const ds = await parse(FT_TTL, { format: 'turtle' });
  const rows = await query(ds, `${PRE} SELECT ?s WHERE { ?s text:query "panel" . ?s ex:status "retired" }`);
  assert.deepEqual(subjects(rows), ['battery']);
});

test('text:query: ASK, COUNT(*) and a solution LIMIT see the matches', async () => {
  const ds = await parse(FT_TTL, { format: 'turtle' });
  assert.equal(await query(ds, `${PRE} ASK { ?s text:query (dc:title "control interface") }`), true);
  assert.equal(await query(ds, `${PRE} ASK { ?s text:query "zzzz" }`), false);
  const count = await query(ds, `${PRE} SELECT (COUNT(*) AS ?n) WHERE { ?s text:query "panel" }`);
  assert.equal([...count][0].get('n').value, '4');
  const one = await query(ds, `${PRE} SELECT ?s WHERE { ?s text:query "panel" } LIMIT 1`);
  assert.equal([...one].length, 1);
});

test('text:query: an object that is not the jena-text argument is a parse error', async () => {
  const ds = await parse(FT_TTL, { format: 'turtle' });
  await assert.rejects(query(ds, `${PRE} SELECT ?s WHERE { ?s text:query ?o }`));
});

const GEO_TTL = `
  @prefix ex:  <http://example.org/> .
  @prefix geo: <http://www.opengis.net/ont/geosparql#> .
  ex:London ex:g "POINT(-0.1278 51.5074)"^^geo:wktLiteral .
  ex:Manchester ex:g "POINT(-2.2426 53.4808)"^^geo:wktLiteral .
  ex:Box ex:g "POLYGON((-0.5 51.3, 0.3 51.3, 0.3 51.7, -0.5 51.7, -0.5 51.3))"^^geo:wktLiteral .
  ex:Grid ex:g "<http://www.opengis.net/def/crs/EPSG/0/27700> POINT(530000 180000)"^^geo:wktLiteral .
`;

const GPRE = `
  PREFIX ex:   <http://example.org/>
  PREFIX geof: <http://www.opengis.net/def/function/geosparql/>
  PREFIX uom:  <http://www.opengis.net/def/uom/OGC/1.0/>
`;

async function distance(args) {
  const ds = await parse(GEO_TTL, { format: 'turtle' });
  const rows = [...await query(ds, `${GPRE}
    SELECT ?d WHERE { ex:London ex:g ?a . ex:Manchester ex:g ?b . ex:Box ex:g ?box . ex:Grid ex:g ?grid
      BIND(geof:distance(${args}) AS ?d) }`)];
  assert.equal(rows.length, 1);
  return rows[0].get('d');
}

test('geof:distance: point to point, an xsd:double in the CRS units', async () => {
  const d = await distance('?a, ?b');
  assert.equal(d.value, '2.89252253232364639');
  assert.equal(d.datatype.value, 'http://www.w3.org/2001/XMLSchema#double');
  assert.equal((await distance('?a, ?b, uom:degree')).value, '2.89252253232364639');
});

test('geof:distance: refused for a polygon, two reference systems, and a unit other than the CRS unit', async () => {
  assert.equal(await distance('?a, ?box'), undefined);
  assert.equal(await distance('?a, ?grid'), undefined);
  assert.equal(await distance('?a, ?b, uom:radian'), undefined);
  assert.equal(await distance('?a, ?b, uom:metre'), undefined);
});

xfail('geof:distance in metres between two CRS84 points (geodesic, about 262 km)', METRES_ISSUE, async () => {
  const d = await distance('?a, ?b, uom:metre');
  assert.ok(d, 'no value');
  const m = Number(d.value);
  assert.ok(m > 260000 && m < 264500, `got ${d.value}`);
});

test('geof:envelope: the bounding box as a geo:wktLiteral POLYGON; refused for a non-geometry', async () => {
  const ds = await parse(GEO_TTL, { format: 'turtle' });
  const rows = [...await query(ds, `${GPRE}
    SELECT ?e ?bad WHERE { ex:London ex:g ?a BIND(geof:envelope(?a) AS ?e) BIND(geof:envelope("x") AS ?bad) }`)];
  assert.equal(rows.length, 1);
  assert.equal(rows[0].get('e').value,
    'POLYGON((-0.1278 51.5074, -0.1278 51.5074, -0.1278 51.5074, -0.1278 51.5074, -0.1278 51.5074))');
  assert.equal(rows[0].get('e').datatype.value, 'http://www.opengis.net/ont/geosparql#wktLiteral');
  assert.equal(rows[0].get('bad'), undefined);
});
