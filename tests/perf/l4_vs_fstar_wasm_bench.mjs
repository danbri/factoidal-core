// Benchmark: the Lean 4 engine of @factoidal/core (npm/factoidal, the
// package's own typed API over its wasm in npm/factoidal/l4-assets/) vs
// the F*-extracted npm-entry bundles, loaded BY PATH from
// docs/fstar-extracted/ (installed by `tools/fetch-builds.sh --set web`;
// since 0.9.0 they are not in the package, issue 713): wasm_of_ocaml
// (factoidal-npm-entry.wasm.js, WasmGC) and js_of_ocaml
// (factoidal-npm-entry.js). The F* bundles are driven through the same
// typed wrappers (lib/api.mjs buildApi) the package uses, as
// tests/engine-compare/engines.mjs does, so all three engines run
// parse() then query() on the same Turtle text.
//
// Workload: K people, each with a :name and an :age triple (2K triples
// total); the query is the two-pattern join from hub post 36
// (?s :name ?n . ?s :age ?a) — the same shape on all three engines.
//
// Measurement discipline (skills/perf-benchmarking):
// - each engine runs in its OWN child process, so RSS deltas are not
//   contaminated by a sibling engine's heap;
// - init, data ingestion (parseMs), and query are timed separately;
// - query time is the median of 5 runs after 1 warmup.
// An engine whose bundle is absent reports {error} and the driver goes on.
//
// Usage:
//   node tests/perf/l4_vs_fstar_wasm_bench.mjs            # driver: all engines, K=100,1000,4000
//   node tests/perf/l4_vs_fstar_wasm_bench.mjs <engine> <K>   # one engine, one size (child mode)
// Engines: l4 | fstar-wasm | fstar-js

import { spawnSync } from 'node:child_process';
import { statSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

const HERE = fileURLToPath(new URL('.', import.meta.url));
const ROOT = new URL('../../', import.meta.url);
const p = (rel) => fileURLToPath(new URL(rel, ROOT));

const EX = 'http://example.org/';
const XSD_INT = 'http://www.w3.org/2001/XMLSchema#integer';

function makeData(K) {
  const triples = [];
  const ttlLines = [`@prefix : <${EX}> .`];
  for (let i = 0; i < K; i++) {
    const s = { type: 'uri', value: `${EX}p${i}` };
    triples.push({ subject: s, predicate: { type: 'uri', value: EX + 'name' },
      object: { type: 'literal', value: `Person ${i}` } });
    triples.push({ subject: s, predicate: { type: 'uri', value: EX + 'age' },
      object: { type: 'literal', value: String(18 + (i % 60)), datatype: XSD_INT } });
    ttlLines.push(`:p${i} :name "Person ${i}" ; :age ${18 + (i % 60)} .`);
  }
  return { triples, ttl: ttlLines.join('\n') };
}

const BGP = [
  { subject: { type: 'var', value: 's' }, predicate: { type: 'uri', value: EX + 'name' }, object: { type: 'var', value: 'n' } },
  { subject: { type: 'var', value: 's' }, predicate: { type: 'uri', value: EX + 'age' }, object: { type: 'var', value: 'a' } },
];
const SPARQL = `PREFIX : <${EX}> SELECT ?s ?n ?a WHERE { ?s :name ?n ; :age ?a }`;

const median = (xs) => [...xs].sort((a, b) => a - b)[Math.floor(xs.length / 2)];
const now = () => performance.now();
const mem = () => { const m = process.memoryUsage(); return { rss: m.rss, heapUsed: m.heapUsed }; };

async function runChild(engine, K) {
  const { triples, ttl } = makeData(K);
  const out = { engine, people: K, triples: 2 * K, node: process.version };
  const m0 = mem();

  const t0 = now();
  let factoidal;
  if (engine === 'l4') {
    factoidal = (await import(new URL('npm/factoidal/index.mjs', ROOT).href)).default;
  } else {
    const { createRequire } = await import('node:module');
    const { existsSync } = await import('node:fs');
    const { buildApi } = await import(new URL('npm/factoidal/lib/api.mjs', ROOT).href);
    const require = createRequire(import.meta.url);
    const bundle = p(engine === 'fstar-wasm'
      ? 'docs/fstar-extracted/factoidal-npm-entry.wasm.js'
      : 'docs/fstar-extracted/factoidal-npm-entry.js');
    if (!existsSync(bundle)) throw new Error(`${bundle} is absent: run tools/fetch-builds.sh --set web`);
    factoidal = buildApi({
      engineName: engine,
      loadEntry: async () => {
        const mod = require(bundle);
        // The wasm_of_ocaml bundle registers its entry once the module
        // has compiled; wait for it (10 s cap).
        for (let i = 0; i < 200; i += 1) {
          const abi = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
          if (abi) return abi;
          await new Promise((r) => setTimeout(r, 50));
        }
        throw new Error(`${bundle} registered no factoidalNpmEntry`);
      },
    });
  }
  // First parse forces engine init; time it apart from data size by
  // parsing one triple first.
  await factoidal.parse(`<${EX}a> <${EX}b> "c" .`, { format: 'ntriples', baseIRI: EX });
  out.initMs = +(now() - t0).toFixed(1);
  const tp = now();
  const dataset = await factoidal.parse(ttl, { format: 'turtle', baseIRI: EX });
  out.parseMs = +(now() - tp).toFixed(1);
  const queryOnce = async () => {
    const rows = await factoidal.query(dataset, SPARQL);
    return Array.isArray(rows) ? rows.length : rows.results.bindings.length;
  };

  const m1 = mem();
  out.rows = await queryOnce(); // warmup + sanity
  const times = [];
  for (let i = 0; i < 5; i++) { const t = now(); await queryOnce(); times.push(now() - t); }
  out.queryMsMedian = +median(times).toFixed(1);
  out.queryMsAll = times.map((t) => +t.toFixed(1));
  const m2 = mem();
  out.rssAfterInitMB = +((m1.rss - m0.rss) / 1048576).toFixed(1);
  out.rssAfterQueriesMB = +((m2.rss - m0.rss) / 1048576).toFixed(1);
  out.heapAfterQueriesMB = +((m2.heapUsed - m0.heapUsed) / 1048576).toFixed(1);
  console.log(JSON.stringify(out));
}

function driver() {
  const sizes = process.env.BENCH_SIZES ? process.env.BENCH_SIZES.split(',').map(Number) : [100, 1000, 4000];
  const engines = ['l4', 'fstar-wasm', 'fstar-js'];
  const artifacts = {
    'l4 wasm': ['npm/factoidal/l4-assets/l4factoidal.wasm', 'npm/factoidal/l4-assets/l4factoidal.mjs', 'npm/factoidal/l4-assets/l4factoidal.js'],
    'fstar wasm_of_ocaml': ['docs/fstar-extracted/factoidal-npm-entry.wasm.js', 'docs/fstar-extracted/factoidal-npm-entry.wasm.assets'],
    'fstar js_of_ocaml': ['docs/fstar-extracted/factoidal-npm-entry.js'],
  };
  console.log('# artifact sizes (bytes)');
  for (const [name, files] of Object.entries(artifacts)) {
    let total = 0;
    for (const f of files) {
      try {
        const st = statSync(p(f));
        if (st.isDirectory()) {
          const { readdirSync } = require('node:fs');
        }
        total += st.size;
      } catch { /* directory: measured below via du in the report */ }
    }
    console.log(JSON.stringify({ artifact: name, files, knownFileBytes: total }));
  }
  for (const K of sizes) for (const e of engines) {
    const r = spawnSync(process.execPath, [fileURLToPath(import.meta.url), e, String(K)], { encoding: 'utf8', timeout: 600000 });
    process.stdout.write(r.stdout || '');
    if (r.status !== 0) console.log(JSON.stringify({ engine: e, people: K, error: (r.stderr || 'nonzero exit').slice(0, 300) }));
  }
}

const [, , engineArg, kArg] = process.argv;
if (engineArg) await runChild(engineArg, Number(kArg ?? 1000));
else driver();
