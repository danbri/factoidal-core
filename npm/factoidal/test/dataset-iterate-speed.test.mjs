// Dataset iteration reads the engine's byte region (op datasetQuadsBin,
// formal/lean4/L4Factoidal/RDF/QuadsBin.lean,
// https://github.com/danbri/factoidal/issues/900). For 60,000 quads it must take
// at most 1.2 times the engine's N-Quads writer op on the same handle plus a
// line split (the path before https://github.com/danbri/factoidal/issues/894).
// This was an expected failure until 2026-10-21.

import test from 'node:test';
import assert from 'node:assert/strict';
import * as api from '../index.mjs';

function median(xs) { const s = xs.slice().sort((a, b) => a - b); return s[Math.floor(s.length / 2)]; }

async function trialOnce() {
  let text = '';
  for (let i = 0; i < 60000; i++) {
    const g = i % 3 === 0 ? ` <http://e/g${i % 7}>` : '';
    const o = i % 2 === 0 ? `"value ${i}"@en` : `<http://e/o${i % 1000}>`;
    text += `<http://e/s${i % 5000}> <http://e/p${i % 13}> ${o}${g} .\n`;
  }
  const ds = await api.parse(text, { format: 'nquads' });
  const iter = [];
  const base = [];
  for (let r = 0; r < 5; r++) {
    const c = ds.clone();
    let t0 = performance.now();
    let n = 0;
    for (const _q of c) n++;
    iter.push(performance.now() - t0);
    t0 = performance.now();
    const nq = c._ctx.e.datasetSerialize(c.handle, 'nquads');
    let lines = 0;
    for (const line of JSON.parse(nq).nquads.split('\n')) if (line) lines++;
    base.push(performance.now() - t0);
    assert.equal(n, lines);
    c.dispose();
  }
  ds.dispose();
  return [median(iter), median(base)];
}

// npm test runs the test files at the same time, so one trial can be slowed by
// another file; the bound must hold in one of three trials of five runs.
async function check() {
  let last = '';
  for (let trial = 0; trial < 3; trial++) {
    const [it, nq] = await trialOnce();
    if (it <= 1.2 * nq) return;
    last = `iteration ${it.toFixed(0)} ms, N-Quads writer ${nq.toFixed(0)} ms`;
  }
  assert.fail(last);
}

test('Dataset iteration within 1.2x the N-Quads writer (https://github.com/danbri/factoidal/issues/900)', check);
