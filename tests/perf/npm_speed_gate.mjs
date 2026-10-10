// npm speed gate: the Lean engine of @factoidal/core against the F* engine
// (https://github.com/danbri/factoidal/issues/713 stage 5).
//
// For each row of tests/perf/l4_vs_fstar_wasm_bench.mjs, at the middle of
// its three sizes, the gate runs the Lean engine and both F* npm-entry
// bundles (each in its own child process, median of 5 runs after 1 warmup)
// and requires
//
//     Lean time <= 2 x the time of the faster F* bundle.
//
// A row that does not meet the bound today is in XFAIL with the open issue
// that tracks it: the gate reports it as an expected failure while it
// fails, and FAILS when it passes ("unexpected pass"), so that the issue is
// closed and the row moved out of XFAIL (CLAUDE.md, "A stated shortfall is a
// failing test plus an open issue").
//
// The F* bundles are not in the package (issue 713 stage 3); install them
// with `tools/fetch-builds.sh --set web` (docs/fstar-extracted/). Without
// them the gate exits 2 and measures nothing.
//
// Usage (from npm/factoidal: `npm run test:speed`; not part of `npm test`):
//   node tests/perf/npm_speed_gate.mjs [--size small|middle|large] [--rows a,b]
// Exit: 0 every row as expected, 1 a row failed or passed unexpectedly,
//       2 the F* bundles are absent.

import { existsSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { ROWS, runMatrix } from './l4_vs_fstar_wasm_bench.mjs';

const ROOT = new URL('../../', import.meta.url);
const BOUND = 2.0;

/**
 * Rows the Lean engine does not yet run within BOUND times the F* engine.
 * Each names the open issue that tracks it. The coordinator replaces the
 * placeholder URLs with the issues it opens.
 */
export const XFAIL = {
};

const args = process.argv.slice(2);
const arg = (name) => { const i = args.indexOf(name); return i >= 0 ? args[i + 1] : undefined; };
const sizeIndex = { small: 0, middle: 1, large: 2 }[arg('--size') || 'middle'];
if (sizeIndex === undefined) {
  console.error('npm_speed_gate: --size is small, middle or large');
  process.exit(2);
}
const rows = arg('--rows') ? arg('--rows').split(',') : Object.keys(ROWS);

for (const bundle of ['docs/fstar-extracted/factoidal-npm-entry.js',
  'docs/fstar-extracted/factoidal-npm-entry.wasm.js']) {
  if (!existsSync(fileURLToPath(new URL(bundle, ROOT)))) {
    console.error(`npm_speed_gate: ${bundle} is absent; run tools/fetch-builds.sh --set web`);
    process.exit(2);
  }
}

const results = runMatrix({
  rows,
  engines: ['l4', 'fstar-wasm', 'fstar-js'],
  sizesFor: (row) => [ROWS[row][sizeIndex]],
  log: (r) => console.log(JSON.stringify(r)),
});

let failed = 0;
let xfailed = 0;
let passed = 0;
const lines = [];
for (const row of rows) {
  const of = (engine) => results.find((r) => r.row === row && r.engine === engine);
  const lean = of('l4');
  const fstar = [of('fstar-wasm'), of('fstar-js')].filter((r) => r && r.ms !== undefined);
  const issue = XFAIL[row];
  if (!lean || lean.ms === undefined) {
    failed += 1;
    lines.push(`FAIL  ${row}: the Lean engine did not answer (${lean && lean.error})`);
    continue;
  }
  if (fstar.length === 0) {
    failed += 1;
    lines.push(`FAIL  ${row}: no F* bundle answered; nothing to compare with`);
    continue;
  }
  const best = Math.min(...fstar.map((r) => r.ms));
  const ratio = lean.ms / Math.max(best, 0.1);
  const what = `${row} (${lean.triples} triples): Lean ${lean.ms} ms, best F* ${best} ms, ratio ${ratio.toFixed(2)}`;
  const ok = ratio <= BOUND;
  if (issue) {
    if (ok) {
      failed += 1;
      lines.push(`FAIL  unexpected pass: ${what}; move the row out of XFAIL and close ${issue}`);
    } else {
      xfailed += 1;
      lines.push(`xfail ${what} (${issue})`);
    }
  } else if (ok) {
    passed += 1;
    lines.push(`ok    ${what}`);
  } else {
    failed += 1;
    lines.push(`FAIL  ${what}; above the bound ${BOUND}`);
  }
}
console.log('');
for (const l of lines) console.log(l);
console.log(`npm_speed_gate: ${passed} pass, ${failed} fail, ${xfailed} expected failures ` +
  `(out of ${rows.length}); bound: Lean <= ${BOUND} x the faster F* bundle`);
process.exit(failed > 0 ? 1 : 0);
