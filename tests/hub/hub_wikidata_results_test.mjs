import assert from 'node:assert/strict';
import { test } from 'node:test';
import { exampleQuery, exampleResults } from '../../docs/web/hub/wikidata-results/example.mjs';
import {
  axisColumn, commonsImage, displayedVars, graphData, highlightTokens, mapGeometry, numberValue, viewDirectives, viewNames,
} from '../../docs/web/hub/wikidata-results/view-data.mjs';
import { createResultViews } from '../../docs/web/hub/wikidata-results/views.mjs';

const { head: { vars }, results: { bindings } } = exampleResults;
const wkt = value => ({ datatype: 'http://www.opengis.net/ont/geosparql#wktLiteral', value });

test('all documented WDQS views and the graph builder have replaceable handlers', () => {
  const registry = createResultViews();
  assert.deepEqual([...registry.keys()].sort(), Object.keys(viewNames).sort());
  assert.ok([...registry.values()].every(view => typeof view === 'function'));
  const custom = () => {};
  assert.equal(createResultViews([['Graph', custom]]).get('Graph'), custom);
});

test('view tags read options from comments and ignore literal strings and IRIs', () => {
  const query = exampleQuery + '\n#view:Map{"layer":"?placeLabel"}\n' +
    'BIND("""\n#defaultView:Tree\n""" AS ?example) <https://example.org/#defaultView>\n';
  const config = viewDirectives(query);
  assert.equal(config.title, 'Three cities in England');
  assert.equal(config.defaultView, 'Graph');
  assert.deepEqual(config.options.get('Map'), { hide: '?coord', layer: '?placeLabel' });
  assert.equal(viewDirectives('#defaultView:Table').hasDefaultView, true);
  assert.equal(viewDirectives('#view:Map{}').hasDefaultView, false);
  assert.equal(viewDirectives('#defaultView:Words').unknownView, 'Words');
  assert.equal(viewDirectives('#view:Map{broken}').invalidOptions, true);
  assert.deepEqual(displayedVars(['place', 'coord', 'score'], { hide: ['?coord', '$score'] }), ['place']);
});

test('graph edges follow the projected item order and share nodes across rows', () => {
  const model = graphData(vars, bindings);
  assert.deepEqual(model.nodes.map(node => node.label), ['England', 'London', 'Liverpool', 'Manchester']);
  assert.deepEqual(model.edges, ['Q84', 'Q24826', 'Q18125'].map(target => ({
    source: 'Q21', target, label: 'contains',
  })));
  const swapped = graphData(vars, bindings, ['place', 'region'], '');
  assert.equal(swapped.edges[0].source, 'Q84');
  assert.equal(swapped.edges[0].target, 'Q21');
});

test('map accepts CRS84 shapes without swapping longitude and latitude', () => {
  assert.deepEqual(mapGeometry(bindings[0].coord), { type: 'Point', coordinates: [-.128, 51.507] });
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
  assert.equal(axisColumn(bindings, 'score').value(bindings[0].score), 4);
  assert.equal(axisColumn(bindings, 'year').format(Date.parse(bindings[0].year.value)), '1801-01-01');
  assert.equal(axisColumn(bindings, 'placeLabel').value(bindings[1].placeLabel), 1);
  assert.equal(axisColumn(bindings, 'coord'), null);
  assert.equal(numberValue({ ...bindings[0].score, value: 'NaN' }), null);
});

test('image grid recognises Commons file URLs', () => {
  const media = { type: 'uri', value: 'http://commons.wikimedia.org/wiki/Special:FilePath/Example.jpg' };
  assert.equal(commonsImage(media), 'https://commons.wikimedia.org/wiki/Special:FilePath/Example.jpg?width=480');
  assert.equal(commonsImage({ ...media, value: 'https://commons.wikimedia.org.example.org/wiki/Special:FilePath/Example.jpg' }), null);
  assert.equal(commonsImage({ ...media, value: 'https://commons.wikimedia.org:8080/wiki/Special:FilePath/Example.jpg' }), null);
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
