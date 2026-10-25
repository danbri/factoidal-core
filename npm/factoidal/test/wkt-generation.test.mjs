// GeoSPARQL WKT literals made from other data, on the shipped wasm: in a
// SPARQL query (SELECT, a sub-SELECT feeding geof:sfWithin, an INSERT then
// geof:sfWithin over the stored literal), from a CSVW column whose datatype
// object names geo:wktLiteral, and from an RML object map with a constant
// datatype. These features exist already; the Lean #guards of the same cases
// are in formal/lean4/Wasm/Ops/Query.lean and Wasm/Ops/Formats.lean.

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';

const WKT = 'http://www.opengis.net/ont/geosparql#wktLiteral';
const PRE = 'PREFIX geo: <http://www.opengis.net/ont/geosparql#>\n' +
  'PREFIX geof: <http://www.opengis.net/def/function/geosparql/>\n' +
  'PREFIX ex: <http://e/>\n';
const DATA = '@prefix ex: <http://e/> .\n' +
  'ex:L ex:lon -0.1278 ; ex:lat 51.5074 .\n' +
  'ex:M ex:lon -2.2426 ; ex:lat 53.4808 .\n';
const MK = 'STRDT(CONCAT("POINT(", STR(?lon), " ", STR(?lat), ")"), geo:wktLiteral)';
const BOX = '"POLYGON((-1 51, 1 51, 1 52, -1 52, -1 51))"^^geo:wktLiteral';

const subjects = (rows) => rows.map((r) => r.get('x').value).sort();

test('(a) STRDT(CONCAT(...), geo:wktLiteral) in SELECT', async () => {
  const rows = await f.query(DATA, PRE +
    `SELECT ?w WHERE { ex:L ex:lon ?lon ; ex:lat ?lat BIND(${MK} AS ?w) }`);
  assert.equal(rows.length, 1);
  const w = rows[0].get('w');
  assert.equal(w.termType, 'Literal');
  assert.equal(w.value, 'POINT(-0.1278 51.5074)');
  assert.equal(w.datatype.value, WKT);
});

test('(b) the WKT literal of a sub-SELECT feeds geof:sfWithin', async () => {
  const rows = await f.query(DATA, PRE +
    `SELECT ?x WHERE { { SELECT ?x ?w WHERE { ?x ex:lon ?lon ; ex:lat ?lat BIND(${MK} AS ?w) } }` +
    ` FILTER(geof:sfWithin(?w, ${BOX})) }`);
  assert.deepEqual(subjects(rows), ['http://e/L']);
});

test('(c) INSERT the WKT literal, then geof:sfWithin over the stored value', async () => {
  const ds = await f.parse(DATA, { format: 'turtle' });
  const out = await f.update(ds, PRE +
    `INSERT { ?x geo:asWKT ?w } WHERE { ?x ex:lon ?lon ; ex:lat ?lat BIND(${MK} AS ?w) }`);
  assert.equal(out.size, 6);
  const rows = await f.query(out, PRE +
    `SELECT ?x WHERE { ?x geo:asWKT ?w FILTER(geof:sfWithin(?w, ${BOX})) }`);
  assert.deepEqual(subjects(rows), ['http://e/L']);
  const all = await f.query(out, PRE + 'SELECT ?w WHERE { ex:M geo:asWKT ?w }');
  assert.equal(all[0].get('w').value, 'POINT(-2.2426 53.4808)');
  assert.equal(all[0].get('w').datatype.value, WKT);
  for (const d of [ds, out]) d.dispose();
});

test('(d) a CSVW datatype object {"@id": geo:wktLiteral, "base": "string"}', async () => {
  const meta = JSON.stringify({
    '@context': 'http://www.w3.org/ns/csvw', url: 't.csv',
    tableSchema: {
      aboutUrl: 'http://e/r/{id}',
      columns: [
        { name: 'id', suppressOutput: true },
        { name: 'wkt', propertyUrl: 'http://www.opengis.net/ont/geosparql#asWKT',
          datatype: { '@id': WKT, base: 'string' } },
      ],
    },
  });
  const ds = await f.csvwToRdf('id,wkt\n1,POINT(1 2)\n', meta, { url: 'http://e/t.csv', mode: 'minimal' });
  const rows = await f.query(ds, 'SELECT ?w WHERE { <http://e/r/1> <http://www.opengis.net/ont/geosparql#asWKT> ?w }');
  assert.equal(rows.length, 1);
  assert.equal(rows[0].get('w').value, 'POINT(1 2)');
  assert.equal(rows[0].get('w').datatype.value, WKT);
  ds.dispose();
});

const RML_HEAD = '@prefix rml: <http://w3id.org/rml/> .\n' +
  '@prefix geo: <http://www.opengis.net/ont/geosparql#> .\n' +
  '<#tm> a rml:TriplesMap ;\n' +
  '  rml:logicalSource [ rml:source "d.csv" ; rml:referenceFormulation rml:CSV ] ;\n' +
  '  rml:subjectMap [ rml:template "http://e/r/{id}" ] ;\n' +
  '  rml:predicateObjectMap [ rml:predicate geo:asWKT ; rml:objectMap [ rml:reference "wkt" ; ';

for (const [label, dt] of [
  ['the rml:datatype shortcut', 'rml:datatype geo:wktLiteral'],
  ['a rml:datatypeMap with rml:constant', 'rml:datatypeMap [ rml:constant geo:wktLiteral ]'],
]) {
  test(`(e) RML: ${label} gives geo:wktLiteral values`, async () => {
    const mapping = await f.parse(RML_HEAD + dt + ' ] ] .\n',
      { format: 'turtle', baseIRI: 'http://e/map.ttl' });
    const ds = await f.rmlMap(mapping, 'id,wkt\n1,POINT(1 2)\n', 'csv');
    const rows = await f.query(ds, 'SELECT ?w WHERE { <http://e/r/1> <http://www.opengis.net/ont/geosparql#asWKT> ?w }');
    assert.equal(rows.length, 1);
    assert.equal(rows[0].get('w').value, 'POINT(1 2)');
    assert.equal(rows[0].get('w').datatype.value, WKT);
    for (const d of [mapping, ds]) d.dispose();
  });
}
