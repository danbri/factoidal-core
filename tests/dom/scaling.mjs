// tests/dom/scaling.mjs — time growth of DOM arena operations over the size of
// one child list (skill danbri-function-precrime-checkers: the n / 4n
// assertion). For each case, l4dom runs a script at n and at 4n children of
// one element; the time ratio must be at most 6 (linear growth gives about 4,
// quadratic about 16).
//
//   node tests/dom/scaling.mjs L4DOM_BINARY
//
// Expected failure (https://github.com/danbri/factoidal/issues/1216): `remove`
// of half the children of one element. The arena keeps the children of a node
// in an array, so one removal costs time proportional to the number of
// siblings. When the ratio becomes linear, the case is STALE and the run fails.
import { spawnSync } from 'node:child_process';
import { writeFileSync, mkdtempSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const bin = process.argv[2];
const dir = mkdtempSync(join(tmpdir(), 'l4dom-scale-'));

// handles: 0 Document, 1 html, 2 head, 3 body; then the created nodes
function script(n, tail) {
  const l = ['script', 'html ='];
  for (let i = 0; i < n; i++) l.push(i % 3 === 0 ? 'text =' : 'text =61', `append 3 ${4 + i}`);
  l.push(...tail(n));
  return l.join('\n') + '\n';
}
function time(n, tail) {
  const f = join(dir, `s${n}.txt`);
  writeFileSync(f, script(n, tail));
  let best = Infinity;
  for (let r = 0; r < 3; r++) {
    const t0 = process.hrtime.bigint();
    const p = spawnSync(bin, ['ops', f], { encoding: 'utf8', maxBuffer: 1 << 30 });
    if (p.status !== 0) throw new Error(`l4dom exited ${p.status}`);
    best = Math.min(best, Number(process.hrtime.bigint() - t0) / 1e6);
  }
  return best;
}
const cases = [
  { name: 'append', n: 40000, tail: () => [], xfail: false },
  { name: 'append then normalize', n: 40000, tail: () => ['normalize 3'], xfail: false },
  { name: 'append then textContent', n: 40000, tail: () => ['gettext 3'], xfail: false },
  { name: 'append then deep clone', n: 40000, tail: () => ['clone 3 1'], xfail: false },
  { name: 'append then remove half', n: 10000,
    tail: (n) => Array.from({ length: n / 2 }, (_, i) => `remove ${4 + 2 * i}`), xfail: true },
];
let rc = 0;
for (const c of cases) {
  const a = time(c.n, c.tail), b = time(4 * c.n, c.tail);
  const ratio = b / a, ok = ratio <= 6;
  const line = `${c.name}: n=${c.n} ${a.toFixed(0)} ms, 4n ${b.toFixed(0)} ms, ratio ${ratio.toFixed(1)}`;
  if (c.xfail) {
    if (ok) { console.log(`STALE expected failure: ${line} (linear now; update https://github.com/danbri/factoidal/issues/1216)`); rc = 1; }
    else console.log(`expected failure: ${line} (https://github.com/danbri/factoidal/issues/1216)`);
  } else {
    console.log(`${ok ? 'pass' : 'FAIL'}: ${line}`);
    if (!ok) rc = 1;
  }
}
process.exit(rc);
