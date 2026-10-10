// Benchmark: the Lean 4 engine of @factoidal/core (npm/factoidal, the
// package's own typed API over its wasm in npm/factoidal/l4-assets/) vs
// the F*-extracted npm-entry bundles, loaded BY PATH from
// docs/fstar-extracted/ (installed by `tools/fetch-builds.sh --set web`;
// since 0.9.0 they are not in the package, issue 713): wasm_of_ocaml
// (factoidal-npm-entry.wasm.js, WasmGC) and js_of_ocaml
// (factoidal-npm-entry.js). The F* bundles are driven through the same
// typed wrappers (lib/api.mjs buildApi) the package uses, as
// tests/engine-compare/engines.mjs does, so every engine runs the same
// function on the same text.
//
// Rows (issue 713 stage 5), each at three sizes. K is a number of people;
// person i has a :name, an :age (18 + i mod 60) and an rdf:type :Person, so
// the data has 3K triples:
//
//   parse-turtle     parse() of the Turtle text
//   parse-nquads     parse() of the same data as N-Quads
//   select-join      SELECT ?s ?n ?a WHERE { ?s :name ?n ; :age ?a }
//   order-by         SELECT ?s ?n WHERE { ?s :name ?n } ORDER BY ?n
//   group-by         SELECT ?a (COUNT(?s) AS ?c) WHERE { ?s :age ?a } GROUP BY ?a
//   count-distinct   SELECT (COUNT(DISTINCT ?a) AS ?c) WHERE { ?s :age ?a }
//   canonicalize     canonicalize() (RDFC-1.0) of the data with every person
//                    a blank node, as N-Quads
//   shacl            shaclValidate() of the data against a shape with a
//                    sh:targetClass, sh:minCount, sh:datatype and
//                    sh:maxInclusive (every 50th person violates the last)
//
// The query rows parse once (not timed) and time query(); canonicalize
// times the whole call from N-Quads text; shacl parses both graphs once and
// times shaclValidate() on the two Datasets.
//
// Measurement discipline (skills/perf-benchmarking):
// - each (engine, row, size) runs in its OWN child process, so memory
//   figures are not contaminated by another engine or row;
// - engine load is timed apart (`loadMs`, one one-triple parse);
// - the row's time is the median of 5 runs after 1 warmup (`ms`), with all
//   runs listed (`runsMs`) and the CPU time of the whole child (`cpuMs`);
//   a row whose warmup takes more than 5 s is measured once;
// - memory: `wasmMemoryBytes` is the Lean module's linear memory at the end
//   of the child. Linear memory only grows, so it is the high-water mark of
//   the engine's heap. `maxRssMB` is the peak resident set of the child
//   (process.resourceUsage), for every engine; the F* bundles have no linear
//   memory to report (js_of_ocaml uses the JavaScript heap, wasm_of_ocaml
//   WasmGC);
// - the 1-minute load average is recorded with each row.
// An engine whose bundle is absent, or a row it cannot run, reports {error}
// and the driver goes on.
//
// Usage:
//   node tests/perf/l4_vs_fstar_wasm_bench.mjs [--rows a,b] [--engines l4,fstar-wasm]
//        [--sizes-scale F] [--json-out FILE]          # driver: all rows, report
//   node tests/perf/l4_vs_fstar_wasm_bench.mjs --child <engine> <row> <K>
// Engines: l4 (the full engine, '@factoidal/core'), l4-core (the core
// engine, '@factoidal/core/core'), fstar-wasm, fstar-js.
// tests/perf/npm_speed_gate.mjs imports runMatrix() from this file.

import { spawnSync } from 'node:child_process';
import { existsSync, writeFileSync } from 'node:fs';
import { loadavg } from 'node:os';
import { fileURLToPath } from 'node:url';

const ROOT = new URL('../../', import.meta.url);
const p = (rel) => fileURLToPath(new URL(rel, ROOT));
const SELF = fileURLToPath(import.meta.url);

const EX = 'http://example.org/';
const RDF_TYPE = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type';
const XSD = 'http://www.w3.org/2001/XMLSchema#';

/** The rows and their three sizes (K people; 3K triples). */
export const ROWS = {
  'parse-turtle': [1000, 4000, 16000],
  'parse-nquads': [1000, 4000, 16000],
  'select-join': [1000, 4000, 16000],
  'order-by': [1000, 4000, 16000],
  'group-by': [1000, 4000, 16000],
  'count-distinct': [1000, 4000, 16000],
  canonicalize: [500, 2000, 8000],
  shacl: [500, 2000, 8000],
};

export const ENGINES = ['l4', 'fstar-wasm', 'fstar-js'];

const QUERIES = {
  'select-join': `PREFIX : <${EX}> SELECT ?s ?n ?a WHERE { ?s :name ?n ; :age ?a }`,
  'order-by': `PREFIX : <${EX}> SELECT ?s ?n WHERE { ?s :name ?n } ORDER BY ?n`,
  'group-by': `PREFIX : <${EX}> SELECT ?a (COUNT(?s) AS ?c) WHERE { ?s :age ?a } GROUP BY ?a`,
  'count-distinct': `PREFIX : <${EX}> SELECT (COUNT(DISTINCT ?a) AS ?c) WHERE { ?s :age ?a }`,
};

// The expected number of solutions, so a row that answers wrongly is an
// error rather than a fast time.
const EXPECTED_ROWS = {
  'select-join': (k) => k,
  'order-by': (k) => k,
  'group-by': (k) => Math.min(k, 60),
  'count-distinct': () => 1,
};

function turtleOf(k, bnodes = false) {
  const lines = [`@prefix : <${EX}> .`];
  for (let i = 0; i < k; i++) {
    const s = bnodes ? `_:p${i}` : `:p${i}`;
    lines.push(`${s} a :Person ; :name "Person ${i}" ; :age ${18 + (i % 60)} .`);
  }
  return lines.join('\n') + '\n';
}

function nquadsOf(k, bnodes = false) {
  const out = [];
  for (let i = 0; i < k; i++) {
    const s = bnodes ? `_:p${i}` : `<${EX}p${i}>`;
    out.push(`${s} <${RDF_TYPE}> <${EX}Person> .`);
    out.push(`${s} <${EX}name> "Person ${i}" .`);
    out.push(`${s} <${EX}age> "${18 + (i % 60)}"^^<${XSD}integer> .`);
  }
  return out.join('\n') + '\n';
}

const SHAPES = `@prefix sh: <http://www.w3.org/ns/shacl#> .
@prefix xsd: <${XSD}> .
@prefix : <${EX}> .
:PersonShape a sh:NodeShape ;
  sh:targetClass :Person ;
  sh:property [ sh:path :name ; sh:minCount 1 ; sh:datatype xsd:string ] ;
  sh:property [ sh:path :age ; sh:datatype xsd:integer ; sh:maxInclusive 76 ] .
`;

const median = (xs) => [...xs].sort((a, b) => a - b)[Math.floor(xs.length / 2)];
const now = () => performance.now();

async function loadApi(engine) {
  if (engine === 'l4') return import(new URL('npm/factoidal/index.mjs', ROOT).href);
  if (engine === 'l4-core') return import(new URL('npm/factoidal/core.mjs', ROOT).href);
  const { createRequire } = await import('node:module');
  const { buildApi } = await import(new URL('npm/factoidal/lib/api.mjs', ROOT).href);
  const require = createRequire(import.meta.url);
  const bundle = p(engine === 'fstar-wasm'
    ? 'docs/fstar-extracted/factoidal-npm-entry.wasm.js'
    : 'docs/fstar-extracted/factoidal-npm-entry.js');
  if (!existsSync(bundle)) throw new Error(`${bundle} is absent: run tools/fetch-builds.sh --set web`);
  // The wasm_of_ocaml bundle finds its code file as
  // dirname(require.main.filename) + '/factoidal-npm-entry.wasm.assets/...'.
  // Under an ES module main `require.main` is undefined and the load throws
  // (TypeError: reading 'filename'), so name the bundle itself as the main
  // module; its assets directory is beside it.
  if (!process.mainModule) process.mainModule = { filename: bundle };
  return buildApi({
    engineName: engine,
    loadEntry: async () => {
      const mod = require(bundle);
      // The wasm_of_ocaml bundle registers its entry once the module has
      // compiled; wait for it (10 s cap).
      for (let i = 0; i < 200; i += 1) {
        const abi = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
        if (abi) return abi;
        await new Promise((r) => setTimeout(r, 50));
      }
      throw new Error(`${bundle} registered no factoidalNpmEntry`);
    },
  });
}

/** Run one row at one size in this process and return the measurement. */
export async function runChild(engine, row, k) {
  const out = { engine, row, people: k, triples: 3 * k, node: process.version };
  const t0 = now();
  const api = await loadApi(engine);
  await api.parse(`<${EX}a> <${EX}b> "c" .`, { format: 'ntriples' });
  out.loadMs = +(now() - t0).toFixed(1);

  let op;
  if (row === 'parse-turtle') {
    const text = turtleOf(k);
    op = async () => {
      const ds = await api.parse(text, { format: 'turtle' });
      if (ds.size !== 3 * k) throw new Error(`parse-turtle: ${ds.size} quads, expected ${3 * k}`);
    };
  } else if (row === 'parse-nquads') {
    const text = nquadsOf(k);
    op = async () => {
      const ds = await api.parse(text, { format: 'nquads' });
      if (ds.size !== 3 * k) throw new Error(`parse-nquads: ${ds.size} quads, expected ${3 * k}`);
    };
  } else if (QUERIES[row]) {
    const ds = await api.parse(turtleOf(k), { format: 'turtle' });
    const want = EXPECTED_ROWS[row](k);
    op = async () => {
      const rows = await api.query(ds, QUERIES[row]);
      const n = Array.isArray(rows) ? rows.length : rows.results.bindings.length;
      if (n !== want) throw new Error(`${row}: ${n} solutions, expected ${want}`);
    };
  } else if (row === 'canonicalize') {
    const text = nquadsOf(k, true);
    op = async () => {
      const nq = await api.canonicalize(text, { format: 'nquads' });
      const lines = nq.split('\n').filter(Boolean).length;
      if (lines !== 3 * k) throw new Error(`canonicalize: ${lines} lines, expected ${3 * k}`);
    };
  } else if (row === 'shacl') {
    const data = await api.parse(turtleOf(k), { format: 'turtle' });
    const shapes = await api.parse(SHAPES, { format: 'turtle' });
    // Person i violates sh:maxInclusive 76 when i mod 60 = 59.
    const conforms = k < 60;
    op = async () => {
      const r = await api.shaclValidate(data, shapes);
      if (r.conforms !== conforms) throw new Error(`shacl: conforms ${r.conforms}, expected ${conforms}`);
    };
  } else {
    throw new Error(`unknown row '${row}'`);
  }

  const tw = now();
  await op(); // warmup, and the answer check
  out.warmupMs = +(now() - tw).toFixed(1);
  // A run of more than 5 s is measured once: the F* bundles are quadratic
  // on the larger inputs, and five runs of a minute each would hold the
  // matrix for hours. `runsMs` lists what was measured.
  const runs = out.warmupMs > 5000 ? 1 : 5;
  const times = [];
  for (let i = 0; i < runs; i += 1) {
    const t = now();
    await op();
    times.push(now() - t);
  }
  out.ms = +median(times).toFixed(1);
  out.runsMs = times.map((t) => +t.toFixed(1));
  if (engine === 'l4' || engine === 'l4-core') {
    const eng = await api.loadEngine();
    out.wasmMemoryBytes = eng._module && eng._module.HEAPU8 ? eng._module.HEAPU8.byteLength : null;
  }
  const ru = process.resourceUsage();
  out.cpuMs = Math.round((ru.userCPUTime + ru.systemCPUTime) / 1000);
  out.maxRssMB = +(ru.maxRSS / 1024).toFixed(1);
  out.load1 = +loadavg()[0].toFixed(2);
  return out;
}

/** One run longer than this at one size skips the engine at the next size. */
export const SKIP_AFTER_MS = 10000;

/** Run every (row, size, engine) in its own child; answer the results. */
export function runMatrix({ rows = Object.keys(ROWS), engines = ENGINES, scale = 1,
  sizesFor = (row) => ROWS[row], timeoutMs = 600000, log = () => {} } = {}) {
  const results = [];
  for (const row of rows) {
    const slow = new Map(); // engine -> the result whose warmup passed SKIP_AFTER_MS
    for (const k0 of sizesFor(row)) {
      const k = Math.max(1, Math.round(k0 * scale));
      for (const engine of engines) {
        // An engine whose previous size of this row took more than
        // SKIP_AFTER_MS for one run is not run at the next size (4 times
        // the input): the F* wasm_of_ocaml bundle is quadratic in parse(),
        // 12 s at 12,000 triples, and its larger runs would hold the matrix
        // for an hour. The row records why.
        if (slow.has(engine)) {
          const prev = slow.get(engine);
          const res = { engine, row, people: k, triples: 3 * k,
            skipped: `not run: ${prev.warmupMs} ms for one run at ${prev.triples} triples` };
          results.push(res);
          log(res);
          continue;
        }
        const r = spawnSync(process.execPath, [SELF, '--child', engine, row, String(k)],
          { encoding: 'utf8', timeout: timeoutMs, maxBuffer: 16 * 1024 * 1024 });
        let res;
        const line = (r.stdout || '').trim().split('\n').filter(Boolean).pop();
        if (r.status === 0 && line) {
          res = JSON.parse(line);
        } else {
          const why = r.error ? String(r.error.message || r.error)
            : (r.stderr || 'nonzero exit').trim().split('\n').slice(-3).join(' | ');
          res = { engine, row, people: k, triples: 3 * k, error: why.slice(0, 400) };
        }
        results.push(res);
        log(res);
        if (res.warmupMs > SKIP_AFTER_MS) slow.set(engine, res);
      }
    }
  }
  return results;
}

/** The markdown table of a result list: one line per (row, size). */
export function reportTable(results) {
  const key = (r) => `${r.row} ${r.people}`;
  const by = new Map();
  for (const r of results) {
    if (!by.has(key(r))) by.set(key(r), { row: r.row, people: r.people, triples: r.triples });
    by.get(key(r))[r.engine] = r;
  }
  const ms = (r) => (r && r.ms !== undefined ? r.ms.toFixed(1)
    : (r && r.skipped ? 'not run' : (r ? 'error' : '-')));
  const lines = [
    '| Row | Triples | Lean ms | F* wasm ms | F* js ms | Lean / best F* | Lean wasm memory MB | Lean max RSS MB | F* wasm max RSS MB |',
    '|---|---:|---:|---:|---:|---:|---:|---:|---:|',
  ];
  for (const v of by.values()) {
    const l = v.l4;
    const fs = [v['fstar-wasm'], v['fstar-js']].filter((x) => x && x.ms !== undefined).map((x) => x.ms);
    const best = fs.length ? Math.min(...fs) : null;
    const ratio = l && l.ms !== undefined && best ? (l.ms / Math.max(best, 0.1)).toFixed(2) : '-';
    const mem = l && l.wasmMemoryBytes ? (l.wasmMemoryBytes / 1048576).toFixed(0) : '-';
    lines.push(`| ${v.row} | ${v.triples} | ${ms(l)} | ${ms(v['fstar-wasm'])} | ${ms(v['fstar-js'])} | ${ratio} | ${mem} | ${l && l.maxRssMB ? l.maxRssMB : '-'} | ${v['fstar-wasm'] && v['fstar-wasm'].maxRssMB ? v['fstar-wasm'].maxRssMB : '-'} |`);
  }
  return lines.join('\n');
}

function argValue(args, name) {
  const i = args.indexOf(name);
  return i >= 0 ? args[i + 1] : undefined;
}

async function main(args) {
  if (args[0] === '--child') {
    const [, engine, row, k] = args;
    console.log(JSON.stringify(await runChild(engine, row, Number(k))));
    return;
  }
  const rows = argValue(args, '--rows') ? argValue(args, '--rows').split(',') : Object.keys(ROWS);
  const engines = argValue(args, '--engines') ? argValue(args, '--engines').split(',') : ENGINES;
  const scale = argValue(args, '--sizes-scale') ? Number(argValue(args, '--sizes-scale')) : 1;
  const results = runMatrix({ rows, engines, scale, log: (r) => console.log(JSON.stringify(r)) });
  const out = argValue(args, '--json-out');
  if (out) writeFileSync(out, JSON.stringify(results, null, 1) + '\n');
  console.log('\n' + reportTable(results));
}

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) {
  await main(process.argv.slice(2));
}
