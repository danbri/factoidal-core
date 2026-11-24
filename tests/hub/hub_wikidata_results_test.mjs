import assert from 'node:assert/strict';
import { test } from 'node:test';
import { readFile } from 'node:fs/promises';
import { groups } from '../../docs/web/hub/wikidata-results/example.mjs';
import { batchSize, qleverUrl, queryQlever, runBatch } from '../../docs/web/hub/wikidata-results/qlever.mjs';
import {
  axisColumn, commonsImage, displayedVars, graphData, highlightTokens, mapGeometry, numberValue, viewDirectives, viewNames,
} from '../../docs/web/hub/wikidata-results/view-data.mjs';
import { createResultViews } from '../../docs/web/hub/wikidata-results/views.mjs';

const london = groups.find(group => group.id === 'london');
const orbits = groups.find(group => group.id === 'orbits');
const planets = groups.find(group => group.id === 'planets');
const { head: { vars }, results: { bindings } } = orbits.preview.data;
const wkt = value => ({ datatype: 'http://www.opengis.net/ont/geosparql#wktLiteral', value });

test('all documented WDQS views and the graph builder have replaceable handlers', () => {
  const registry = createResultViews();
  assert.deepEqual([...registry.keys()].sort(), Object.keys(viewNames).sort());
  assert.ok([...registry.values()].every(view => typeof view === 'function'));
  const custom = () => {};
  assert.equal(createResultViews([['Graph', custom]]).get('Graph'), custom);
});

test('the gallery has a separate card for each view and shares six distinct queries', () => {
  const cards = groups.flatMap(group => group.views.map(view => view.id));
  assert.deepEqual(cards.sort(), [...Object.keys(viewNames), 'Ask', 'Rdf'].sort());
  assert.equal(new Set(groups.map(group => group.query)).size, 6);
  assert.ok(groups.every(group => !/\b(?:hint:|SERVICE)\b/.test(group.query)));
});

test('view tags read options from comments and ignore literal strings and IRIs', () => {
  const query = london.query + '\n#view:Map{"layer":"?placeLabel"}\n' +
    'BIND("""\n#defaultView:Tree\n""" AS ?example) <https://example.org/#defaultView>\n';
  const config = viewDirectives(query);
  assert.equal(config.title, 'London landmarks');
  assert.equal(config.defaultView, 'Map');
  assert.deepEqual(config.options.get('Map'), { hide: ['?coord', '?image'], layer: '?placeLabel' });
  assert.equal(viewDirectives('#defaultView:Table').hasDefaultView, true);
  assert.equal(viewDirectives('#view:Map{}').hasDefaultView, false);
  assert.equal(viewDirectives('#defaultView:Words').unknownView, 'Words');
  assert.equal(viewDirectives('#view:Map{broken}').invalidOptions, true);
  assert.deepEqual(displayedVars(['place', 'coord', 'score'], { hide: ['?coord', '$score'] }), ['place']);
});

test('graph edges follow the projected item order and share nodes across rows', () => {
  const model = graphData(vars, bindings);
  assert.equal(model.nodes.length, 9);
  assert.deepEqual(model.edges[0], { source: 'Q525', target: 'Q2', label: 'orbited by' });
  assert.ok(model.edges.some(edge => edge.source === 'Q2' && edge.target === 'Q405'));
  const swapped = graphData(vars, bindings, ['body', 'parent'], '');
  assert.equal(swapped.edges[0].source, 'Q2');
  assert.equal(swapped.edges[0].target, 'Q525');
});

test('map accepts CRS84 shapes without swapping longitude and latitude', () => {
  assert.deepEqual(mapGeometry(london.preview.data.results.bindings[0].coord),
    { type: 'Point', coordinates: [-.12457, 51.50067] });
  assert.deepEqual(mapGeometry(wkt('LINESTRING(-2 1, 3 4)')),
    { type: 'LineString', coordinates: [[-2, 1], [3, 4]] });
  assert.deepEqual(mapGeometry(wkt('<http://www.opengis.net/def/crs/OGC/1.3/CRS84> POLYGON((0 0, 3 0, 3 3, 0 0))')),
    { type: 'Polygon', coordinates: [[[0, 0], [3, 0], [3, 3], [0, 0]]] });
  assert.deepEqual(mapGeometry(wkt('MULTIPOINT((1 2),(3 4))'))?.coordinates, [[1, 2], [3, 4]]);
  assert.equal(mapGeometry(wkt('LINESTRING((1 2), (3 4))')), null);
  assert.equal(mapGeometry(wkt('POINT(380 120)')), null);
  assert.equal(mapGeometry(wkt('<urn:another-crs>POINT(30 40)')), null);
});

test('chart axes distinguish numbers, dates and labels', () => {
  const rows = planets.preview.data.results.bindings;
  const dates = groups.find(group => group.id === 'apollo').preview.data.results.bindings;
  assert.equal(axisColumn(rows, 'diameterKm').value(rows[0].diameterKm), 4879);
  assert.equal(axisColumn(dates, 'landing').format(Date.parse(dates[0].landing.value)), '1969-07-20');
  assert.equal(axisColumn(rows, 'planet').value(rows[1].planet), 1);
  assert.equal(axisColumn(bindings, 'body'), null);
  assert.equal(numberValue({ ...rows[0].diameterKm, value: 'NaN' }), null);
});

test('live batches are capped at five, paced and sequential, and stop on backpressure', async () => {
  const events = [];
  const run = async ({ id }) => {
    events.push('start ' + id);
    await Promise.resolve();
    events.push('finish ' + id);
  };
  const pause = () => events.push('pause');
  await runBatch(groups, run, pause);
  assert.deepEqual(events, groups.slice(0, batchSize).flatMap(({ id }, index) =>
    [...(index ? ['pause'] : []), 'start ' + id, 'finish ' + id]));
  const limited = [];
  await runBatch(groups, async ({ id }) => { limited.push(id); return false; }, pause);
  assert.deepEqual(limited, ['london']);
});

test('SELECT, ASK and CONSTRUCT share the QLever transport', async () => {
  let requests = 0;
  for (const group of [london, groups[4], groups[5]]) {
    const expected = group.preview;
    const rdf = expected.kind === 'rdf';
    const actual = await queryQlever(group.query, { fetchResult: async (url, options) => {
      requests += 1;
      assert.equal(url.split('?')[0], qleverUrl);
      assert.equal(new URL(url).searchParams.get('query'), group.query);
      assert.equal(options.method, 'GET');
      return new Response(rdf ? expected.data : JSON.stringify(expected.data), { headers: {
        'Content-Type': rdf ? expected.contentType : 'application/sparql-results+json; charset=utf-8',
      }});
    }});
    assert.deepEqual(actual, expected);
  }
  assert.equal(requests, 3);
  await assert.rejects(queryQlever('ASK {}', {
    fetchResult: async () => new Response('Try later', { status: 429 }),
  }), { status: 429 });
});

test('image grid recognises Commons file URLs', () => {
  const media = { type: 'uri', value: 'http://commons.wikimedia.org/wiki/Special:FilePath/Example.jpg' };
  assert.equal(commonsImage(media), 'https://commons.wikimedia.org/wiki/Special:FilePath/Example.jpg?width=500');
  assert.equal(commonsImage({ ...media, value: 'https://commons.wikimedia.org.example.org/wiki/Special:FilePath/Example.jpg' }), null);
  assert.equal(commonsImage({ ...media, value: 'https://commons.wikimedia.org:8080/wiki/Special:FilePath/Example.jpg' }), null);
});

test('every saved London photo has a local JPEG and Commons attribution', async () => {
  for (const row of london.preview.data.results.bindings) {
    const photo = london.thumbnails.get(row.image.value);
    assert.ok(photo.author);
    assert.match(photo.license, /^(3|4)\.0$/);
    const bytes = await readFile(new URL(photo.src));
    assert.deepEqual([...bytes.subarray(0, 2)], [255, 216]);
  }
});

test('query editor colours comments, keywords, literals, IRIs and variables', () => {
  const source = '# note\nSELECT ?x WHERE { BIND("SELECT" AS ?x) wd:Q42 ?p <urn:example> }';
  const tokens = highlightTokens(source);
  assert.deepEqual(tokens.map(({ text, kind }) => [text, kind]), [
    ['# note', 'comment'], ['SELECT', 'keyword'], ['?x', 'variable'], ['WHERE', 'keyword'],
    ['BIND', 'keyword'], ['"SELECT"', 'string'], ['AS', 'keyword'], ['?x', 'variable'],
    ['wd:Q42', 'iri'], ['?p', 'variable'], ['<urn:example>', 'iri'],
  ]);
  assert.ok(tokens.every(({ at, text }) => source.slice(at, at + text.length) === text));
});
