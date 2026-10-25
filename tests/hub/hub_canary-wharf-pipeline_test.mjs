// Pins every live cell of docs/web/hub/canary-wharf-pipeline.md (see
// hub_rdf_syntaxes_test.mjs for the harness shape). The page runs the npm
// release named in docs/_data/factoidalRelease.js; this test runs
// npm/factoidal/ of this checkout (hub_checked-pipelines_test.mjs checks that
// the two are the same version).

import test from 'node:test';
import assert from 'node:assert/strict';

import { extractObservableCells, runReactivePost, pretty, xfail, HUB_PAGE_DIR } from './_helpers.mjs';
import { analyzeCell } from '../../docs/web/hub/reactive-cells.mjs';
import * as Factoidal from '../../npm/factoidal/index.mjs';

const cells = extractObservableCells('canary-wharf-pipeline.md', HUB_PAGE_DIR);
const post = runReactivePost(cells, { Factoidal, fn: Factoidal.default, pretty });
const CW = 'https://example.org/canary-wharf/';
const col = (rows, v) => rows.map((r) => r.get(v) && r.get(v).value);
const local = (iri) => iri.slice(CW.length);

// Every named cell evaluates. A cell that no other test reads is still
// checked here: on 2026-10-25 the cell buildingsEvidence failed in the browser
// (https://github.com/danbri/factoidal/issues/690) while every test passed,
// because no test read it.
test('canary-wharf: every named cell evaluates', async () => {
  const names = cells.map((c) => analyzeCell(c).name).filter(Boolean);
  assert.ok(names.length >= 20);
  for (const n of names) await post.value(n);
  const ev = await post.value('buildingsEvidence');
  assert.deepEqual(ev.rows.map((r) => r[0]), ['turtleDocumentReader', 'rdfsReasoner', 'shippedEvaluator']);
});

test('canary-wharf: the buildings pipeline is well typed and every step is proved', async () => {
  const c = await post.value('buildingsCheck');
  assert.equal(c.wellTyped, true);
  const run = await post.value('buildingsRun');
  assert.deepEqual(run.evidence.map((e) => [e.stage, e.status]),
    [['turtleDocumentReader', 'proved'], ['rdfsReasoner', 'proved'], ['shippedEvaluator', 'proved']]);
  assert.equal(run.proved, true);
  // The RDFS closure typed Newfoundland (rdfs:domain) and One Canada Square
  // (rdfs:subClassOf) as cw:Building, so the CONSTRUCT kept all four.
  const nt = run.graph.toString('ntriples');
  for (const b of ['newfoundland', 'oneCanadaSquare', 'eightCanadaSquare', 'crossrailPlace']) {
    assert.ok(nt.includes(`<${CW}${b}> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <${CW}Building>`), b);
  }
  assert.match(nt, new RegExp(`<${CW}newfoundland> <${CW}heightBand> "tall"`));
});

test('canary-wharf: CSVW is a plain function, not a registered stage', async () => {
  assert.equal((await post.value('fromCsvw')).size, 16);
  assert.deepEqual(await post.value('csvwStage'),
    { name: 'CSVW (tabular data to RDF)', status: 'missing', bound: false, runnable: false });
  const run = await post.value('stationsRun');
  assert.deepEqual(run.evidence.map((e) => [e.stage, e.status]), [['shippedEvaluator', 'proved']]);
  assert.equal(run.graph.size, 24);
});

test('canary-wharf: one named graph per source, and the join across them', async () => {
  const perGraph = await post.value('perGraph');
  assert.deepEqual(col(perGraph, 'g').map(local), ['graph/buildings', 'graph/stations']);
  assert.deepEqual(col(perGraph, 'triples'), ['22', '24']);
  const answer = await post.value('answer');
  assert.deepEqual(col(answer, 'building'), ['One Canada Square', '8 Canada Square']);
  assert.deepEqual(col(answer, 'lines'), ['Jubilee', 'Elizabeth, Jubilee']);
  assert.deepEqual(col(answer, 'entries'), ['38.2', '64.6']);
  const answerRun = await post.value('answerRun');
  assert.equal(answerRun.proved, true);
  const nt = answerRun.graph.toString('ntriples');
  assert.ok(nt.includes(`<${CW}oneCanadaSquare> <${CW}answerTo> <${CW}question>`));
  assert.ok(!nt.includes(`<${CW}newfoundland>`));
  assert.ok(!nt.includes(`<${CW}crossrailPlace>`));
});

test('canary-wharf: the pipeline record queried as RDF', async () => {
  const steps = await post.value('stepsPerGraph');
  assert.deepEqual(steps.map((r) => `${local(r.get('graph').value)} ${r.get('stage').value} ${r.get('status').value}`), [
    'data/csvw-output CSVW (tabular data to RDF) missing',
    'graph/answer shippedEvaluator proved',
    'graph/buildings turtleDocumentReader proved',
    'graph/buildings rdfsReasoner proved',
    'graph/buildings shippedEvaluator proved',
    'graph/stations shippedEvaluator proved',
  ]);
  const lineage = await post.value('answerLineage');
  assert.deepEqual([...new Set(col(lineage, 'activity').map(local))].sort(),
    ['activity/answer', 'activity/buildings', 'activity/csvw', 'activity/stations']);
  const allProved = await post.value('allProved');
  assert.deepEqual(allProved.map((r) => `${local(r.get('graph').value)} ${r.get('allProved').value}`),
    ['graph/answer false', 'graph/buildings true', 'graph/stations false']);
  const caveats = await post.value('answerCaveats');
  assert.deepEqual(caveats.map((r) => `${r.get('building').value} | ${r.get('stage').value} | ${r.get('status').value}`), [
    '8 Canada Square | CSVW (tabular data to RDF) | missing',
    'One Canada Square | CSVW (tabular data to RDF) | missing',
  ]);
});

test('canary-wharf: the N-Quads for the store', async () => {
  const s = await post.value('nquadsSummary');
  assert.equal(s.proved, true);
  assert.deepEqual(s.graphs.map(local), ['graph/answer', 'graph/buildings', 'graph/provenance', 'graph/stations']);
  assert.ok(s.quads > 46);
});

// The page states two shortfalls; each is an expected failure that turns
// the suite red when it starts to pass.
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
