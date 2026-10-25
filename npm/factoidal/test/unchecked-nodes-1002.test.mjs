// Unchecked composition (https://github.com/danbri/factoidal/issues/1002;
// owner-approved: issue 975 comment 6393905605 item 3). Part 1 is pure JS
// (lib/evidence.mjs) and needs no wasm. Part 2 runs the engine and is
// skipped when the wasm is absent.

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';
import { FactoidalError } from '../lib/errors.mjs';
import { isChecked, reasonOf, refusalFor, makeRecord, summarize, recordChecked }
  from '../lib/evidence.mjs';

const mk = (stage, status, assumptions = [], runnable = status !== 'missing') => ({
  stage, status, contract: status === 'proved' ? `C.${stage}` : null, assumptions, runnable,
});

// ---- Part 1: pure logic, no wasm ----

test('isChecked: only proved', () => {
  assert.equal(isChecked('proved'), true);
  for (const s of ['tested', 'assumed', 'missing']) assert.equal(isChecked(s), false, s);
});

test('reasonOf: status and named assumptions; "no contract" for missing', () => {
  assert.equal(reasonOf(mk('w', 'assumed', ['A.x', 'A.y'])), 'status assumed; assumptions: A.x, A.y');
  assert.equal(reasonOf(mk('t', 'tested')), 'status tested');
  assert.equal(reasonOf(mk('m', 'missing')), 'no contract');
});

test('refusalFor: missing refuses without opt-in (op.failed); no runner refuses op.unknown', () => {
  const m = mk('m', 'missing');
  const e1 = refusalFor(m, false, true);
  assert.ok(e1 instanceof FactoidalError);
  assert.equal(e1.code, 'op.failed');
  assert.equal(refusalFor(m, true, true), null);
  const e2 = refusalFor(m, true, false);
  assert.equal(e2.code, 'op.unknown');
  assert.equal(refusalFor(mk('a', 'assumed', ['X']), false, true), null);
  assert.equal(refusalFor(mk('a', 'assumed', ['X']), false, false).code, 'op.unknown');
});

test('makeRecord: checked iff proved; unchecked and reason only for a non-proved step under the opt-in', () => {
  const p = makeRecord(mk('p', 'proved'), { a: 1 }, true);
  assert.equal(p.checked, true);
  assert.equal('unchecked' in p, false);
  assert.equal('reason' in p, false);
  const a = mk('a', 'assumed', ['A.x']);
  const without = makeRecord(a, undefined, false);
  assert.equal(without.checked, false);
  assert.equal('unchecked' in without, false);
  assert.equal(without.artefact, null);
  const withOpt = makeRecord(a, 'x', true);
  assert.equal(withOpt.checked, false);
  assert.equal(withOpt.unchecked, true);
  assert.equal(withOpt.reason, 'status assumed; assumptions: A.x');
  assert.ok(Object.isFrozen(withOpt));
});

test('summarize: proved only when every record is checked; assumptions are the union', () => {
  const all = [makeRecord(mk('a', 'proved'), null, false), makeRecord(mk('b', 'proved'), null, false)];
  assert.deepEqual(summarize(all), { assumptions: [], proved: true, uncheckedSteps: [] });
  const mixed = [makeRecord(mk('a', 'proved'), null, true),
    makeRecord(mk('w', 'assumed', ['A.x']), null, true),
    makeRecord(mk('v', 'assumed', ['A.x', 'A.y']), null, true)];
  assert.deepEqual(summarize(mixed), { assumptions: ['A.x', 'A.y'], proved: false, uncheckedSteps: ['w', 'v'] });
});

test('a prior record without `checked` falls back to its status', () => {
  const prior = { stage: 'up', status: 'tested', contract: null, assumptions: [], artefact: null };
  assert.equal(recordChecked(prior), false);
  assert.equal(recordChecked({ ...prior, status: 'proved' }), true);
  assert.equal(summarize([prior]).proved, false);
});

// ---- Part 2: the engine ----

let skip = 'wasm engine not built';
try {
  const caps = await f.capabilities();
  skip = caps.stages && caps.explain ? false : 'wasm has no stageList op';
} catch (_err) { /* engine did not load: skip */ }

const TTL = '<http://example.org/a> <http://example.org/p> <http://example.org/b> .';

test('a pipeline of proved nodes: proved true, no unchecked steps', { skip }, async () => {
  const proved = (await f.stages()).find((s) => s.bound && s.status === 'proved');
  assert.ok(proved, 'no bound proved stage');
  const r = await f.run(f.pipe(await f.node('turtleDocumentReader'), await f.node('rdfsReasoner')),
    TTL);
  const statuses = r.evidence.map((e) => e.status);
  assert.equal(r.proved, statuses.every((s) => s === 'proved'));
  assert.deepEqual(r.uncheckedSteps, r.evidence.filter((e) => !e.checked).map((e) => e.stage));
  for (const e of r.evidence) assert.equal(e.checked, e.status === 'proved');
});

test('a pipeline through an assumed writer: proved false and the stage is listed', { skip }, async () => {
  const w = (await f.stages()).find((s) => s.name === 'turtleDocumentWriter');
  assert.equal(w.status, 'assumed');
  const r = await f.run(f.pipe(await f.node('turtleDocumentReader'), await f.node('turtleDocumentWriter')), TTL);
  assert.equal(r.proved, false);
  assert.ok(r.uncheckedSteps.includes('turtleDocumentWriter'));
  assert.ok(r.assumptions.length > 0);
  // Not under the opt-in: checked is false, but no unchecked/reason marker.
  assert.equal(r.evidence[1].checked, false);
  assert.equal('unchecked' in r.evidence[1], false);
});

test('with the opt-in an assumed step is marked unchecked with its reason', { skip }, async () => {
  const r = await f.run(f.pipe(await f.node('turtleDocumentReader'), await f.node('turtleDocumentWriter')),
    TTL, { unchecked: true });
  const rec = r.evidence.find((e) => e.stage === 'turtleDocumentWriter');
  assert.equal(rec.unchecked, true);
  assert.match(rec.reason, /assumed/);
  assert.equal(r.proved, false);
});

test('a missing stage without the opt-in still refuses', { skip }, async () => {
  const missing = (await f.stages()).find((s) => s.status === 'missing');
  const n = await f.node(missing.name);
  await assert.rejects(f.run(f.pipe(await f.node('turtleDocumentReader'), n), TTL),
    (err) => err instanceof FactoidalError && err.code === 'op.failed');
});

test('a missing stage with the opt-in and no runner refuses op.unknown', { skip }, async () => {
  const missing = (await f.stages()).find((s) => s.status === 'missing' && !s.bound);
  const n = await f.node(missing.name);
  await assert.rejects(f.run(f.pipe(await f.node('turtleDocumentReader'), n), TTL, { unchecked: true }),
    (err) => err instanceof FactoidalError && err.code === 'op.unknown');
});
