// Pins every live cell of docs/web/hub/sparql.md (see
// hub_rdf_syntaxes_test.mjs for the harness shape).

import test from 'node:test';
import assert from 'node:assert/strict';

import { extractObservableCells, runReactivePost, pretty, xfail, HUB_PAGE_DIR } from './_helpers.mjs';
import * as Factoidal from '../../npm/factoidal/index.mjs';

const cells = extractObservableCells('sparql.md', HUB_PAGE_DIR);
const post = runReactivePost(cells, { Factoidal, fn: Factoidal.default, pretty });
const values = (rows, v) => rows.map((r) => r.get(v) && r.get(v).value);

test('sparql: paths, aggregates, results document', async () => {
  const partOf = await post.value('partOf');
  assert.equal(partOf.length, 3, 'cafe<park, kiosk<cafe, kiosk<park');
  const counted = await post.value('counted');
  assert.equal(counted[0].get('whole').value, 'http://example.org/park');
  assert.equal(counted[0].get('n').value, '2');
});

test('sparql: ASK, CONSTRUCT, Update on a clone', async () => {
  assert.equal(await post.value('hasKiosk'), true);
  const c = await post.value('constructed');
  assert.equal(c.size, 2);
  assert.deepEqual(await post.value('updated'), ['http://example.org/park']);
  const places = await post.value('places');
  const still = await places.query('SELECT ?w WHERE { <http://example.org/kiosk> <http://example.org/partOf> ?w }');
  assert.deepEqual(values(still, 'w'), ['http://example.org/cafe'], 'the original dataset is unchanged');
});

test('sparql: GeoSPARQL sfWithin and distance', async () => {
  const rows = await post.value('inPark');
  const byPlace = Object.fromEntries(rows.map((r) => [r.get('place').value.split('/').pop(), r]));
  assert.equal(byPlace.cafe.get('inside').value, 'true');
  assert.equal(byPlace.station.get('inside').value, 'false');
  assert.ok(Math.abs(Number(byPlace.station.get('distance').value) - Math.sqrt(13)) < 1e-6);
});

test('sparql: text:query', async () => {
  const rows = await post.value('textHits');
  assert.deepEqual(values(rows, 's'), ['http://example.org/park']);
});

test('sparql: JavaScript and WebAssembly extension functions', async () => {
  const rows = await post.value('jsFunction');
  assert.ok(values(rows, 'initials').includes('Ps'));
  assert.equal(await post.value('wasmAdd'), '42');
});

test('sparql: SERVICE against a registered endpoint', async () => {
  const rows = await post.value('federated');
  assert.deepEqual(values(rows, 'perHour'), ['24']);
});

test('sparql: SPARQL 1.2 triple-term patterns and functions', async () => {
  const rows = await post.value('whoSaidWhat');
  assert.deepEqual(values(rows, 'drink'), ['http://example.org/tea', 'http://example.org/coffee']);
  const fns = await post.value('tripleFunctions');
  assert.equal(fns[0].get('isTriple').value, 'true');
  assert.equal(fns[0].get('o').value, 'http://example.org/tea');
});

xfail('sparql: geof:distance in metres for CRS84 points', 'https://github.com/danbri/factoidal/issues/772', async () => {
  const places = await post.value('places');
  const rows = await places.query(`PREFIX geof: <http://www.opengis.net/def/function/geosparql/>
PREFIX geo: <http://www.opengis.net/ont/geosparql#>
SELECT ?d WHERE { BIND(geof:distance("POINT(0 51.5)"^^geo:wktLiteral, "POINT(1 51.5)"^^geo:wktLiteral,
  <http://www.opengis.net/def/uom/OGC/1.0/metre>) AS ?d) }`);
  const d = Number(rows[0].get('d').value);
  assert.ok(d > 69000 && d < 70000, `distance ${d}`);
});

test('sparql: SPARQL 1.2 reifier and annotation patterns', async () => {
  const rows = await post.value('annotations');
  assert.deepEqual(values(rows, 'reifier'), ['http://example.org/claim1']);
  assert.deepEqual(values(rows, 'source'), ['http://example.org/diary']);
});

test('sparql: string-function types and XSD casts (0.17.0, 0.18.0)', async () => {
  const [row] = await post.value('stringsAndCasts');
  assert.equal(row.get('sub').value, '12');
  assert.equal(row.get('lengthOfNumber'), undefined);
  assert.equal(row.get('byte').value, '12');
  assert.equal(row.get('byte').datatype.value, 'http://www.w3.org/2001/XMLSchema#byte');
  assert.equal(row.get('byteOutOfRange'), undefined);
  assert.equal(row.get('date').value, '2026-10-27Z');
});

test('sparql: base direction in string functions (0.18.0)', async () => {
  const [row] = await post.value('baseDirection');
  assert.equal(row.get('before').value, 'a');
  assert.equal(row.get('before').language, 'en');
  assert.equal(row.get('before').direction, 'ltr');
  assert.equal(row.get('mixedDirections'), undefined);
  assert.equal(row.get('sameDirection').value, 'true');
});
