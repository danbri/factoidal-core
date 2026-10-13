// npm speed gate: the Lean engine of @factoidal/core against the F* engine
// (https://github.com/danbri/factoidal/issues/713 stage 5).
//
// For each row of tests/perf/l4_vs_fstar_wasm_bench.mjs, at the middle of
// its three sizes (and at any other size an XFAIL key names, `row@large`),
// the gate runs the Lean engine and both F* npm-entry bundles (each in its
// own child process, median of 5 runs after 1 warmup) and requires
//
//     the Lean engine answers, and
//     Lean time <= 2 x the time of the faster F* bundle.
//
// It also runs the Lean engine alone for each MEMORY and MEMORY_XFAIL key and compares
// the wasm module's linear memory high-water mark with the key's bound, and
// for each SCALING and SCALING_XFAIL row compares its large size (4 times the
// input) with its middle size.
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
import { cpus, loadavg } from 'node:os';
import { fileURLToPath } from 'node:url';
import { ROWS, runMatrix } from './l4_vs_fstar_wasm_bench.mjs';

const ROOT = new URL('../../', import.meta.url);
const BOUND = 2.0;

/**
 * Rows the Lean engine does not yet answer, or does not answer within BOUND
 * times the F* engine. A key is a row name (at the gate's size) or
 * `row@small|middle|large`. Each names the open issue that tracks it. The
 * coordinator replaces the placeholder URLs with the issues it opens.
 */
export const XFAIL = {
  // Empty since 2026-10-10. The first matrix run measured order-by and
  // group-by at 3,000 triples at 2.17 and 2.03 times the faster F* bundle; after
  // the rowsJoined repair (SPARQL/ResultsJson.lean: the Results JSON writer
  // copied the rest of the document once per row) and at a lower load the same
  // rows are 1.27 and 1.43 (design record § 10).
};

/**
 * Memory bounds, Lean engine only: the wasm module's linear memory at the
 * end of the row (its high-water mark over the warmup and the five runs), in
 * MB. A key in MEMORY is asserted: it fails when the memory is above the
 * bound. A key in MEMORY_XFAIL is an expected failure naming its issue while
 * the bound is not met, and fails when it passes.
 */
export const MEMORY = {
  // parse() of 48,000 triples: 641 MB after one call and 1,227 MB after six
  // on 2026-10-10 (https://github.com/danbri/factoidal/issues/744). The
  // envelope's JSON string was written by escapeString through a character
  // list and a string per character (JSON/Serialize.lean, escapeStringFast
  // since 2026-10-12: 257 MB after one call), and objects above the 4 MiB
  // segment size fragmented the allocator's 32 MiB arenas across calls
  // (Wasm/l4_shim.c sets 128 MiB arenas after the first: 184 MB after six
  // calls). Design record: docs/designissues/2026-10-10-lean-vs-fstar-performance.md
  // section 11.
  'parse-turtle@large': { boundMB: 256 },
};
export const MEMORY_XFAIL = {};

/**
 * Scaling bounds, Lean engine only: time at the large size (4 times the
 * input) at most 9 times the time at the middle size
 * (skills/danbri-function-precrime-checkers, the n/4n assertion). A row in
 * SCALING is asserted: it fails when it is above the bound. A row in
 * SCALING_XFAIL is an expected failure naming its issue while the bound is not
 * met, and fails when it passes.
 */
export const SCALING = [
  // canonicalize of 24,000 blank-node quads took 16.9 s and of 6,000 0.76 s
  // (22 times for 4 times the input, 2026-10-10): the first-degree hash of
  // every blank node filtered every quad
  // (https://github.com/danbri/factoidal/issues/745). After the blank node to
  // quads map of RDFC-1.0 section 4.4 step 2 (RDF/Canonical.lean,
  // bnodeQuadIndex) the row is asserted here. Both F* bundles fail the
  // 24,000-quad input (stack overflow), so there is no F* time to compare.
  'canonicalize',
];
export const SCALING_XFAIL = {};
const SCALING_BOUND = 9.0;

const SIZE_NAMES = ['small', 'middle', 'large'];

const args = process.argv.slice(2);
const arg = (name) => { const i = args.indexOf(name); return i >= 0 ? args[i + 1] : undefined; };
const sizeIndex = { small: 0, middle: 1, large: 2 }[arg('--size') || 'middle'];
if (sizeIndex === undefined) {
  console.error('npm_speed_gate: --size is small, middle or large');
  process.exit(2);
}
const rows = arg('--rows') ? arg('--rows').split(',') : Object.keys(ROWS);
// (row, size index) pairs: the gate's size for every row, and the size of
// every XFAIL key that names one.
const cases = [];
for (const row of rows) {
  cases.push([row, sizeIndex]);
  for (const key of Object.keys(XFAIL)) {
    const [r, size] = key.split('@');
    if (r === row && size && SIZE_NAMES.indexOf(size) !== sizeIndex) {
      cases.push([row, SIZE_NAMES.indexOf(size)]);
    }
  }
}

for (const bundle of ['docs/fstar-extracted/factoidal-npm-entry.js',
  'docs/fstar-extracted/factoidal-npm-entry.wasm.js']) {
  if (!existsSync(fileURLToPath(new URL(bundle, ROOT)))) {
    console.error(`npm_speed_gate: ${bundle} is absent; run tools/fetch-builds.sh --set web`);
    process.exit(2);
  }
}

const results = [];
for (const [row, si] of cases) {
  results.push(...runMatrix({
    rows: [row],
    engines: ['l4', 'fstar-wasm', 'fstar-js'],
    sizesFor: (r) => [ROWS[r][si]],
    log: (r) => console.log(JSON.stringify(r)),
  }).map((r) => ({ ...r, sizeName: SIZE_NAMES[si] })));
}

let failed = 0;
let xfailed = 0;
let passed = 0;
const lines = [];

// Scaling: the Lean engine alone, middle and large sizes.
const scalingRows = [...SCALING.map((r) => [r, undefined]), ...Object.entries(SCALING_XFAIL)];
for (const [row, issue] of scalingRows) {
  if (!rows.includes(row)) continue;
  const rs = runMatrix({ rows: [row], engines: ['l4'], sizesFor: (x) => [ROWS[x][1], ROWS[x][2]],
    log: (x) => console.log(JSON.stringify(x)) });
  const [m, l] = rs;
  const ok = m && l && m.ms !== undefined && l.ms !== undefined &&
    l.ms <= SCALING_BOUND * Math.max(m.ms, 50);
  const what = `scaling ${row}: Lean ${m && m.ms} ms at ${m && m.triples} triples, ` +
    `${l && l.ms} ms at ${l && l.triples} triples, bound ${SCALING_BOUND} times`;
  if (issue === undefined) {
    if (ok) {
      passed += 1;
      lines.push(`ok    ${what}`);
    } else {
      failed += 1;
      lines.push(`FAIL  ${what}; above the bound`);
    }
  } else if (ok) {
    failed += 1;
    lines.push(`FAIL  unexpected pass: ${what}; move the row out of SCALING_XFAIL and close ${issue}`);
  } else {
    xfailed += 1;
    lines.push(`xfail ${what} (${issue})`);
  }
}

// Memory: the Lean engine alone, at the size each key names.
const memoryRows = [...Object.entries(MEMORY).map(([k, v]) => [k, v.boundMB, undefined]),
  ...Object.entries(MEMORY_XFAIL).map(([k, v]) => [k, v.boundMB, v.issue])];
for (const [key, boundMB, issue] of memoryRows) {
  const [row, size] = key.split('@');
  if (!rows.includes(row)) continue;
  const si = SIZE_NAMES.indexOf(size);
  const [r] = runMatrix({ rows: [row], engines: ['l4'], sizesFor: (x) => [ROWS[x][si]],
    log: (x) => console.log(JSON.stringify(x)) });
  const mb = r && r.wasmMemoryBytes ? r.wasmMemoryBytes / 1048576 : null;
  const ok = mb !== null && mb <= boundMB;
  const what = `memory ${key} (${r && r.triples} triples): Lean linear memory ${mb === null ? 'unknown' : mb.toFixed(0) + ' MB'}, bound ${boundMB} MB`;
  if (issue === undefined) {
    if (ok) {
      passed += 1;
      lines.push(`ok    ${what}`);
    } else {
      failed += 1;
      lines.push(`FAIL  ${what}; above the bound`);
    }
  } else if (ok) {
    failed += 1;
    lines.push(`FAIL  unexpected pass: ${what}; move the row out of MEMORY_XFAIL and close ${issue}`);
  } else {
    xfailed += 1;
    lines.push(`xfail ${what} (${issue})`);
  }
}
for (const [row, si] of cases) {
  const sizeName = SIZE_NAMES[si];
  const of = (engine) => results.find((r) => r.row === row && r.engine === engine &&
    r.sizeName === sizeName);
  const lean = of('l4');
  const fstar = [of('fstar-wasm'), of('fstar-js')].filter((r) => r && r.ms !== undefined);
  const issue = XFAIL[`${row}@${sizeName}`] || (si === sizeIndex ? XFAIL[row] : undefined);
  if (!lean || lean.ms === undefined) {
    const why = `${row}@${sizeName}: the Lean engine did not answer (${lean && lean.error})`;
    if (issue) {
      xfailed += 1;
      lines.push(`xfail ${why} (${issue})`);
    } else {
      failed += 1;
      lines.push(`FAIL  ${why}`);
    }
    continue;
  }
  if (fstar.length === 0) {
    failed += 1;
    lines.push(`FAIL  ${row}@${sizeName}: no F* bundle answered; nothing to compare with`);
    continue;
  }
  const best = Math.min(...fstar.map((r) => r.ms));
  const ratio = lean.ms / Math.max(best, 0.1);
  const what = `${row}@${sizeName} (${lean.triples} triples): Lean ${lean.ms} ms, best F* ${best} ms, ratio ${ratio.toFixed(2)}`;
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
const memoryCases = memoryRows.filter(([k]) => rows.includes(k.split('@')[0])).length +
  scalingRows.filter(([k]) => rows.includes(k)).length;
console.log(`npm_speed_gate: ${passed} pass, ${failed} fail, ${xfailed} expected failures ` +
  `(out of ${cases.length + memoryCases}); bound: Lean <= ${BOUND} x the faster F* bundle; ` +
  `load average ${loadavg()[0].toFixed(2)} on ${cpus().length} CPUs (a load above the CPU count ` +
  'makes the ratios unreliable)');
process.exit(failed > 0 ? 1 : 0);
