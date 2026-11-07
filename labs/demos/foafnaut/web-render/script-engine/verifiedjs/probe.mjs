#!/usr/bin/env node
// Stage 2 of docs/designissues/2026-11-07-verifiedjs-page-scripts.md: run every
// fixture at each VerifiedJS level and compare with Node. Usage:
//   probe.mjs <verifiedjs binary> <report.json>
import { spawnSync } from 'node:child_process';
import { mkdtempSync, readFileSync, writeFileSync, existsSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { FIXTURES, FEATURES, ISSUE, PASSING, STUB } from './fixtures.mjs';

const [binary, report] = process.argv.slice(2);
const work = mkdtempSync(join(tmpdir(), 'vjs-probe-'));
const run = (command, args, timeout = 20000) => {
  const r = spawnSync(command, args, { timeout, encoding: 'utf8', maxBuffer: 1 << 24 });
  return { rc: r.status, timedOut: r.error?.code === 'ETIMEDOUT', out: (r.stdout ?? '').trim(), err: (r.stderr ?? '').trim().slice(0, 400) };
};
const results = [];
const cases = [
  ...FEATURES.map(([n, s]) => ['feature', n, s]),
  ...FIXTURES.map(([n, s]) => ['fixture', n, STUB + s]),
  ...FIXTURES.map(([n, s]) => ['raw', n, s])
];
for (const [kind, name, source] of cases) {
  const file = join(work, `${kind}-${name}.js`), wasm = file.replace(/\.js$/, '.wasm');
  writeFileSync(file, source);
  const node = kind === 'raw' ? { rc: null, out: '(document is not bound)' } : run('node', [file], 5000);
  const entry = { kind, name, node: { rc: node.rc, out: node.out }, levels: {} };
  const parse = run(binary, [file, '--parse-only']);
  entry.levels.parse = parse.rc === 0 ? 'ok' : `error: ${parse.err}`;
  for (const level of ['core', 'flat', 'anf']) {
    const r = run(binary, [file, `--run=${level}`]);
    entry.levels[level] = { same: !r.timedOut && r.out === node.out, rc: r.rc, timedOut: r.timedOut, out: r.out.slice(0, 400), err: r.err };
  }
  const compile = run(binary, [file, '-o', wasm]);
  entry.levels.compile = compile.rc === 0 ? 'ok' : `error: ${compile.err}`;
  if (compile.rc === 0 && existsSync(wasm)) {
    const r = run('wasmtime', ['run', wasm], 10000);
    entry.levels.wasm = { same: !r.timedOut && r.out === node.out && (r.rc === 0) === (node.rc === 0), rc: r.rc, timedOut: r.timedOut, out: r.out.slice(0, 400), err: r.err };
  }
  results.push(entry);
  const cell = level => {
    const v = entry.levels[level];
    return !v ? '-' : v === 'ok' ? 'ok' : typeof v === 'string' ? 'ERR' : v.timedOut ? 'TIME' : v.same ? 'same' : 'DIFF';
  };
  console.log([kind.padEnd(7), name.padEnd(26), ...['parse', 'core', 'flat', 'anf', 'compile', 'wasm'].map(l => `${l}=${cell(l)}`.padEnd(13))].join(' '));
  for (const l of ['core', 'flat', 'anf', 'wasm']) {
    const v = entry.levels[l];
    if (v && typeof v === 'object' && !v.same) console.log(`    ${l} rc=${v.rc} out=${JSON.stringify(v.out.slice(0, 200))} err=${JSON.stringify(v.err.slice(0, 160))} node=${JSON.stringify(node.out.slice(0, 80))}`);
  }
  for (const l of ['parse', 'compile']) if (typeof entry.levels[l] === 'string' && entry.levels[l] !== 'ok') console.log(`    ${l}: ${entry.levels[l].slice(0, 200)}`);
}
// The whole host interface of a compiled module.
const shape = join(work, 'shape.js');
writeFileSync(shape, 'console.log(1 + 2);');
run(binary, [shape, '-o', `${shape}.wasm`]);
const module = new WebAssembly.Module(readFileSync(`${shape}.wasm`));
console.log(`MODULE imports ${JSON.stringify(WebAssembly.Module.imports(module))} exports ${JSON.stringify(WebAssembly.Module.exports(module))}`);
if (report) writeFileSync(report, JSON.stringify(results, null, 1));
const count = (kind, level) => {
  const set = results.filter(r => r.kind === kind);
  return `${set.filter(r => r.levels[level]?.same).length} same as Node, ${set.filter(r => !r.levels[level]?.same).length} not (out of ${set.length})`;
};
for (const kind of ['feature', 'fixture']) for (const level of ['core', 'flat', 'anf', 'wasm']) console.log(`SUMMARY ${kind} ${level}: ${count(kind, level)}`);
let unexpected = 0;
for (const level of ['core', 'wasm']) for (const entry of results.filter(r => r.kind === 'fixture')) {
  const same = Boolean(entry.levels[level]?.same), listed = PASSING[level].includes(entry.name);
  if (same && !listed) { unexpected++; console.log(`XPASS ${level} ${entry.name}: flip the case and close ${ISSUE}`); }
  else if (!same && listed) { unexpected++; console.log(`FAIL ${level} ${entry.name}`); }
  else console.log(`${same ? 'pass' : 'xfail'} ${level} ${entry.name}${same ? '' : ` (${ISSUE})`}`);
}
process.exitCode = unexpected ? 1 : 0;
