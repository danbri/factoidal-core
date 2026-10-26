// Pins every live cell of docs/web/hub/checked-pipelines.md (see
// hub_rdf_syntaxes_test.mjs for the harness shape).
//
// The page runs the published release named in docs/_data/factoidalRelease.js
// (from the npm CDN); this test runs npm/factoidal/ of this checkout. The
// two agree while that directory holds the released files: at 0.15.0 every
// file of the published package except package.json (its repository field)
// was byte-identical to npm/factoidal/, and the wasm was the published one
// (sha256 06c67c27...cdc4).

import test from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';

import { extractObservableCells, runReactivePost, pretty, HUB_PAGE_DIR } from './_helpers.mjs';
import * as Factoidal from '../../npm/factoidal/index.mjs';

const require = createRequire(import.meta.url);
const release = require('../../docs/_data/factoidalRelease.js');

const cells = extractObservableCells('checked-pipelines.md', HUB_PAGE_DIR);
const post = runReactivePost(cells, { Factoidal, fn: Factoidal.default, pretty });

const sources = `@prefix ex: <http://example.org/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:alice ex:worksFor ex:acme .`;

// Fails when npm/factoidal/ of this checkout is not the version the page
// loads: then this test does not check what the page runs.
test('checked-pipelines: the page loads the version this test runs', async () => {
  assert.match(release.version, /^\d+\.\d+\.\d+$/);
  assert.equal(release.browserUrl, `https://cdn.jsdelivr.net/npm/@factoidal/core@${release.version}/browser.js`);
  assert.equal(await post.value('release'), release.version);
});

test('checked-pipelines: an entailed description, all steps proved, no assumptions', async () => {
  const ev = await post.value('entailedEvidence');
  assert.deepEqual(ev.rows.map((r) => r[0]), ['turtleDocumentReader', 'rdfsReasoner', 'rdfsExplainGraphStage']);
  assert.ok(ev.rows.every((r) => r[1] === 'proved'));
  const v = await post.value('entailedVerdict');
  assert.equal(v.entailed, true);
  assert.match(v.mapping, /^_:d1_d\d+_x -> <http:\/\/example\.org\/alice>$/); // the label counter is per engine
  assert.deepEqual(v.verdictAssumptions, []);
  assert.deepEqual(v.runAssumptions, []);
  assert.equal(v.proved, true);
});

test('checked-pipelines: the derivation without the reasoner uses rdfs2 then rdfs9', async () => {
  const d = await post.value('derivation');
  const rules = d.rows.map((r) => r[1]);
  assert.deepEqual(rules, ['base', 'base', 'base', 'rdfs2', 'rdfs9']);
  assert.equal(d.rows[4][2], 'ex:alice a ex:Person .');
  assert.equal(d.rows[4][3], '3 2');
});

test('checked-pipelines: a description that is not entailed names closure completeness', async () => {
  const v = await post.value('notEntailedVerdict');
  assert.equal(v.entailed, false);
  assert.equal(v.rejection, 'noMatch');
  assert.match(v.triple, /<http:\/\/example\.org\/worksFor> <http:\/\/example\.org\/globex> \.$/);
  assert.equal(v.verdictAssumptions.length, 1);
  assert.match(v.verdictAssumptions[0], /^RDFS closure completeness/);
  // The page states that the run-level union is empty in 0.15.0; when the
  // registry starts to carry the reasoner's completeness assumption this
  // fails, and the page's paragraph must change with it.
  assert.deepEqual(v.runAssumptions, []);
});

test('checked-pipelines: an assumed writer step and a missing stage', async () => {
  const w = await post.value('writerRun');
  assert.equal(w.proved, false);
  assert.deepEqual(w.uncheckedSteps, ['turtleDocumentWriter']);
  assert.equal(w.status, 'assumed');
  assert.equal(w.contract, 'L4Factoidal.Dataflow.RoundTripOn');
  assert.equal(w.reason, 'status assumed; assumptions: L4Factoidal.Dataflow.TurtleWriterRoundTrip');
  assert.match(w.text, /^@prefix ex: <http:\/\/example\.org\/> \.\n[\s\S]*ex:alice ex:worksFor ex:acme \./);
  const m = await post.value('missingStage');
  assert.equal(m.code, 'op.failed');
  assert.match(m.message, /has status missing: no contract and no test suite/);
});

test('checked-pipelines: without the opt-in a well-typed pipeline with an assumed step still runs (0.15.0)', async () => {
  const p = Factoidal.pipe(await Factoidal.node('turtleDocumentReader'), await Factoidal.node('turtleDocumentWriter'));
  assert.equal(p.wellTyped, true);
  const r = await Factoidal.run(p, sources);
  assert.equal(r.proved, false);
  assert.equal(r.wellTyped, true);
  assert.deepEqual(r.assumptions, ['L4Factoidal.Dataflow.TurtleWriterRoundTrip']);
  assert.deepEqual(r.uncheckedSteps, ['turtleDocumentWriter']);
  assert.equal(r.evidence[1].reason, undefined);
});

test('checked-pipelines: the registry table', async () => {
  const c = await post.value('statusCounts');
  assert.equal(c.entries, c.proved + c.tested + c.assumed + c.missing);
  assert.ok(c.proved > 0 && c.assumed > 0 && c.missing > 0);
  const bound = await post.value('boundStages');
  const names = bound.rows.map((r) => r[0]);
  for (const n of ['turtleDocumentReader', 'rdfsReasoner', 'shippedEvaluator', 'turtleDocumentWriter', 'rdfsExplainGraphStage']) {
    assert.ok(names.includes(n), n);
  }
  const writer = bound.rows.find((r) => r[0] === 'turtleDocumentWriter');
  assert.deepEqual(writer.slice(1), ['RdfWriter', 'assumed', 'TurtleWriterRoundTrip']);
  const missing = await post.value('missingAreas');
  assert.ok(missing.rows.some((r) => r[0] === 'ShEx validation'));
});

test('checked-pipelines: a SPARQL step', async () => {
  const s = await post.value('sparqlResult');
  assert.equal(s.stage, 'shippedEvaluator');
  assert.equal(s.status, 'proved');
  assert.equal(s.contract, 'L4Factoidal.Dataflow.EvalContract');
  assert.deepEqual(s.who, ['http://example.org/alice']);
  assert.equal(s.proved, true);
  assert.deepEqual(s.assumptions, []);
});

// 0.15.0 compares one node's output type with the next node's input type
// (the engine's op pipelineCheck, https://github.com/danbri/factoidal/issues/1002
// step 1): a writer (text out) followed by a reasoner (Graph in) is refused
// without the opt-in. In 0.14.0 it ran; this case was an xfail.
test('checked-pipelines: the type check of an ill-typed pipeline', async () => {
  const c = await post.value('illTypedCheck');
  assert.equal(c.wellTyped, false);
  assert.deepEqual(c.mismatch, { at: 1, out: 'String', in: 'Graph' });
  assert.equal(c.theorem, 'L4Factoidal.Dataflow.Pipeline.guarantee_sound');
  const r = await post.value('illTypedRun');
  assert.equal(r.code, 'op.failed');
  assert.match(r.message, /^run: the pipeline is not well typed: stage 1 \(turtleDocumentWriter\) writes String, stage 2 \(rdfsReasoner\) reads Graph/);
  const u = await post.value('illTypedUnchecked');
  assert.equal(u.wellTyped, false);
  assert.equal(u.proved, false);
  assert.deepEqual(u.uncheckedSteps, ['turtleDocumentWriter']);
});

test('checked-pipelines: run refuses an ill-typed pipeline without the opt-in', async () => {
  const p = Factoidal.pipe(
    await Factoidal.node('turtleDocumentReader'),
    await Factoidal.node('turtleDocumentWriter'),
    await Factoidal.node('rdfsReasoner'),
  );
  await assert.rejects(Factoidal.run(p, sources), /not well typed/);
});
