// Known cost, recorded as an expected failure (CLAUDE.md, owner 2026-09-07):
// iterating a Dataset reads the engine's term objects (op datasetQuadsJson,
// https://github.com/danbri/factoidal/issues/894). For 60,000 quads it is
// slower than the engine's N-Quads writer plus a JS tokeniser, which was the
// path before. https://github.com/danbri/factoidal/issues/900 tracks it.
// The check: the iteration takes at most 1.2 times the N-Quads writer op on
// the same handle plus a line split. When it passes, the harness fails: flip
// it to an assertion and close the issue.

import test from 'node:test';
import assert from 'node:assert/strict';
import * as api from '../index.mjs';

const ISSUE = 'https://github.com/danbri/factoidal/issues/900';

function median(xs) { const s = xs.slice().sort((a, b) => a - b); return s[Math.floor(s.length / 2)]; }

async function check() {
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
  assert.ok(median(iter) <= 1.2 * median(base),
    `iteration ${median(iter).toFixed(0)} ms, N-Quads writer ${median(base).toFixed(0)} ms`);
}

test(`xfail: Dataset iteration within 1.2x the N-Quads writer (${ISSUE})`, async () => {
  let failed = false;
  try { await check(); } catch (_e) { failed = true; }
  assert.ok(failed, `unexpected pass: flip this xfail to an assertion and close ${ISSUE}`);
});
