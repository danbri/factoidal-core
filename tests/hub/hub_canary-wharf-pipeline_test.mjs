// Pins every live cell of docs/web/hub/canary-wharf-pipeline.md (see
// hub_rdf_syntaxes_test.mjs for the harness shape). The page runs the npm
// release named in docs/_data/factoidalRelease.js; this test runs
// npm/factoidal/ of this checkout (hub_checked-pipelines_test.mjs checks that
// the two are the same version). Source 1 is an extract of the kgx graph
// version https://kgx.foaf.tv/id/graphbuildings41263dc7cc077db2
// (danbri/londat; ODbL-derived, attribution in the page).

import test from 'node:test';
import assert from 'node:assert/strict';

import { extractObservableCells, runReactivePost, pretty, xfail, HUB_PAGE_DIR } from './_helpers.mjs';
import { analyzeCell } from '../../docs/web/hub/reactive-cells.mjs';
import * as Factoidal from '../../npm/factoidal/index.mjs';

const cells = extractObservableCells('canary-wharf-pipeline.md', HUB_PAGE_DIR);
const post = runReactivePost(cells, { Factoidal, fn: Factoidal.default, pretty });
const CW = 'https://example.org/canary-wharf/';
const col = (rows, v) => rows.map((r) => r.get(v) && r.get(v).value);
const local = (iri) => (iri.startsWith(CW) ? iri.slice(CW.length) : iri);
const row = (r, vars) => vars.map((v) => local(r.get(v).value)).join(' | ');

// Every named cell evaluates. A cell that no other test reads is still
// checked here: on 2026-10-25 the cell buildingsEvidence failed in the browser
// (https://github.com/danbri/factoidal/issues/690) while every test passed,
// because no test read it.
test('canary-wharf: every named cell evaluates', async () => {
  const names = cells.map((c) => analyzeCell(c).name).filter(Boolean);
  assert.ok(names.length >= 25);
  for (const n of names) await post.value(n);
  const ev = await post.value('buildingsEvidence');
  assert.deepEqual(ev.rows.map((r) => r[0]), ['turtleDocumentReader', 'shippedEvaluator']);
});

// The metres per level come from the 24 kgx buildings with both a height and
// a number of levels: a least-squares fit through the origin, per use.
test('canary-wharf: metres per level, fitted per use and per height band', async () => {
  assert.equal((await post.value('calibration')).size, 90);
  assert.equal((await post.value('calibrationPoints')).length, 24);
  assert.deepEqual(await post.value('perLevel'), { other: 4.56, residential: 3.42 });
  const bands = await post.value('perUseAndHeight');
  assert.deepEqual(bands.map((r) => ['use', 'band', 'buildings', 'metresPerLevel'].map((v) => r.get(v).value).join(' | ')), [
    'other | 100 m or more | 9 | 4.58',
    'other | under 100 m | 9 | 4.47',
    'residential | 100 m or more | 2 | 3.44',
    'residential | under 100 m | 4 | 3.32',
  ]);
  const err = (await post.value('estimateError'))[0];
  assert.deepEqual([err.get('flat3point5').value, err.get('byUse').value], ['21.9', '8.6']);
});

test('canary-wharf: the kgx extract, heights measured or estimated, towers classified', async () => {
  assert.equal((await post.value('buildingsCheck')).wellTyped, true);
  const run = await post.value('buildingsRun');
  assert.deepEqual(run.evidence.map((e) => [e.stage, e.status]),
    [['turtleDocumentReader', 'proved'], ['shippedEvaluator', 'proved']]);
  const classify = await post.value('classifyRun');
  assert.equal(classify.proved, true);
  assert.equal(classify.graph.size, 84);
  const towers = await post.value('towers');
  assert.deepEqual(towers.map((r) => row(r, ['name', 'height', 'estimated'])), [
    'Landmark Pinnacle | 256.5 | true',
    'One Canada Square | 235 | false',
    'One Park Drive | 205 | false',
    '8 Canada Square | 199.5 | false',
    'Newfoundland | 198.36 | true',
  ]);
});

test('canary-wharf: CSVW is a plain function, not a registered stage', async () => {
  assert.equal((await post.value('fromCsvw')).size, 7);
  assert.deepEqual(await post.value('csvwStage'),
    { name: 'CSVW (tabular data to RDF)', status: 'missing', bound: false, runnable: false });
  const run = await post.value('linesRun');
  assert.deepEqual(run.evidence.map((e) => [e.stage, e.status]), [['shippedEvaluator', 'proved']]);
  assert.equal(run.graph.size, 13);
});

test('canary-wharf: one named graph per source, and the walking-distance join', async () => {
  const perGraph = await post.value('perGraph');
  assert.deepEqual(perGraph.map((r) => row(r, ['g', 'triples'])), ['graph/buildings | 84', 'graph/lines | 13']);
  const answer = await post.value('answer');
  assert.deepEqual(answer.map((r) => row(r, ['tower', 'height', 'estimated', 'lines', 'entrances'])), [
    'One Canada Square | 235 | false | Elizabeth, DLR, Jubilee | 5',
    'One Park Drive | 205 | false | Jubilee, DLR | 3',
    '8 Canada Square | 199.5 | false | Elizabeth, DLR, Jubilee | 5',
    'Newfoundland | 198.36 | true | DLR | 1',
  ]);
  const answerRun = await post.value('answerRun');
  assert.equal(answerRun.proved, true);
  const nt = answerRun.graph.toString('ntriples');
  assert.ok(nt.includes(`<https://kgx.foaf.tv/id/cwb0590> <${CW}lineWithin300m> <${CW}line/DLR>`));
  assert.ok(!nt.includes('<https://kgx.foaf.tv/id/cwb0577>'), 'Landmark Pinnacle has no station building within 300 m');
});

test('canary-wharf: the pipeline record queried as RDF, back to the kgx graph version', async () => {
  const steps = await post.value('stepsPerGraph');
  assert.deepEqual(steps.map((r) => row(r, ['graph', 'stage', 'status'])), [
    'data/csvw-output | CSVW (tabular data to RDF) | missing',
    'data/heights | turtleDocumentReader | proved',
    'data/heights | shippedEvaluator | proved',
    'graph/answer | shippedEvaluator | proved',
    'graph/buildings | shippedEvaluator | proved',
    'graph/lines | shippedEvaluator | proved',
  ]);
  const lineage = await post.value('answerLineage');
  assert.deepEqual([...new Set(col(lineage, 'activity').map(local))].sort(),
    ['activity/answer', 'activity/classify', 'activity/csvw', 'activity/heights', 'activity/lines']);
  const sources = await post.value('answerSources');
  assert.deepEqual(sources.map((r) => `${local(r.get('source').value)} ${r.get('derivedFrom') ? r.get('derivedFrom').value : '-'}`), [
    'source/buildings.ttl https://kgx.foaf.tv/id/graphbuildings41263dc7cc077db2',
    'source/station-lines.csv -',
  ]);
  const allProved = await post.value('allProved');
  assert.deepEqual(allProved.map((r) => row(r, ['graph', 'allProved'])),
    ['graph/answer | false', 'graph/buildings | true', 'graph/lines | false']);
  const caveats = await post.value('answerCaveats');
  assert.deepEqual(caveats.map((r) => row(r, ['tower', 'stage', 'status'])), [
    '8 Canada Square | CSVW (tabular data to RDF) | missing',
    'Newfoundland | CSVW (tabular data to RDF) | missing',
    'One Canada Square | CSVW (tabular data to RDF) | missing',
    'One Park Drive | CSVW (tabular data to RDF) | missing',
  ]);
});

test('canary-wharf: the N-Quads for the store', async () => {
  const s = await post.value('nquadsSummary');
  assert.equal(s.proved, true);
  assert.equal(s.quads, 156);
  assert.deepEqual(s.graphs.map(local), ['graph/answer', 'graph/buildings', 'graph/lines', 'graph/provenance']);
});

// The page states four shortfalls; each is an expected failure that turns
// the suite red when it starts to pass.
xfail('canary-wharf: a CONSTRUCT node can be followed by another node',
  'https://github.com/danbri/factoidal/issues/1026', async () => {
    assert.equal((await post.value('chainedCheck')).wellTyped, true);
  });

xfail('canary-wharf: npm packs the dataset into an SBM11 generation',
  'https://github.com/danbri/factoidal/issues/1009', async () => {
    assert.ok((await post.value('sbm11PackInNpm')).length > 0);
  });

xfail('canary-wharf: run() gives its evidence as an RDF graph',
  'https://github.com/danbri/factoidal/issues/563', async () => {
    const run = await post.value('buildingsRun');
    const graphs = Object.values(run).filter((v) => v && typeof v.query === 'function' && v !== run.graph);
    assert.ok(graphs.length > 0);
  });

xfail('canary-wharf: CSVW is a bound pipeline stage',
  'https://github.com/danbri/factoidal/issues/975', async () => {
    assert.equal((await post.value('csvwStage')).bound, true);
  });
