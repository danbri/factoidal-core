// tests/perf/npm_costs.mjs: the cost of each public operation of
// @factoidal/core, run against the built package in npm/factoidal (key
// result 2.3 of https://github.com/danbri/factoidal/issues/901).
//
// Operations, each on an input of 10,000 and of 100,000 quads:
//   parse        parse(N-Quads text) -> Dataset
//   iterate      for (const q of ds) over every quad
//   size         ds.size
//   query-count  ds.query("SELECT (COUNT(*) AS ?c) ...")
//   query-bound  ds.query(the statements of one subject)
//   serialize-nquads, serialize-turtle   await ds.serialize({format})
//   toString-nquads                      ds.toString("nquads")
//   serve-store  one SPARQL 1.1 Protocol GET (COUNT) to serveStore over a
//                store packed from the same input (pack time not counted)
//   lws-put, lws-get  one PUT of the input as N-Triples, one GET of it,
//                to the lws-serve host (lws/server.mjs, insecureNoAuth)
//
// Each operation runs once to warm up and then RUNS times (default 5) in one
// Node process; the result is the median and the minimum in milliseconds.
// The 1-minute load average is recorded before each operation.
//
// Comparison: the medians are compared with the committed results
// (docs/test-results/npm-costs.json). An operation fails when its median is
// more than (1 + TOLERANCE) times the committed median plus SLACK_MS
// (defaults 0.20 and 5 ms). A failing operation is measured once more
// before it fails, and its minimum is used for the second verdict.
//
// Override for a noisy machine: NPM_COSTS_TOLERANCE=0.5 widens the bound;
// NPM_COSTS_NO_FAIL=1 reports regressions without failing (write the
// reason in the commit message). The gate also refuses to fail when the
// load average during a failing operation was above the CPU count; it
// prints "NOISY" for such a row and exits 0 for it.
//
// Usage:
//   node tests/perf/npm_costs.mjs              measure and compare
//   node tests/perf/npm_costs.mjs --write      measure and write the results
//   node tests/perf/npm_costs.mjs --sizes 10000 --ops parse,iterate
// Exit: 0 no regression, 1 a regression, 2 setup error.

import { execFileSync } from 'node:child_process';
import { mkdtempSync, readFileSync, rmSync, writeFileSync, existsSync } from 'node:fs';
import { cpus, loadavg, tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = fileURLToPath(new URL('../../', import.meta.url));
const PKG = join(ROOT, 'npm/factoidal');
const RESULTS = join(ROOT, 'docs/test-results/npm-costs.json');
const RUNS = Number(process.env.NPM_COSTS_RUNS ?? 5);
const TOLERANCE = Number(process.env.NPM_COSTS_TOLERANCE ?? 0.20);
const SLACK_MS = Number(process.env.NPM_COSTS_SLACK_MS ?? 5);
const NO_FAIL = process.env.NPM_COSTS_NO_FAIL === '1';

const args = process.argv.slice(2);
const opt = (name) => { const i = args.indexOf(name); return i >= 0 ? args[i + 1] : undefined; };
const WRITE = args.includes('--write');
const SIZES = (opt('--sizes') ?? '10000,100000').split(',').map(Number);
const ONLY = opt('--ops') ? new Set(opt('--ops').split(',')) : null;

if (!existsSync(join(PKG, 'l4-assets/l4factoidal.wasm'))) {
  console.error('npm_costs: npm/factoidal/l4-assets/l4factoidal.wasm missing (tools/fetch-builds.sh --set web)');
  process.exit(2);
}
const f = await import(join(PKG, 'index.mjs'));
const { listen: lwsListen } = await import(join(PKG, 'lws/server.mjs'));
const CLI = join(PKG, 'bin/factoidal.mjs');
const EX = 'http://example.org/';

/** n quads: IRIs, plain, language-tagged and typed literals, blank nodes,
 *  four named graphs plus the default graph; 20 statements per subject. */
function genNQuads(n, graphs = true) {
  const out = [];
  for (let i = 0; i < n; i++) {
    const s = `<${EX}s${Math.floor(i / 20)}>`;
    const p = `<${EX}p${i % 20}>`;
    let o;
    switch (i % 5) {
      case 0: o = `<${EX}o${i}>`; break;
      case 1: o = `"value ${i}"`; break;
      case 2: o = `"label ${i}"@en`; break;
      case 3: o = `"${i}"^^<http://www.w3.org/2001/XMLSchema#integer>`; break;
      default: o = `_:b${i}`;
    }
    const g = !graphs || i % 5 === 4 ? '' : ` <${EX}g${i % 4}>`;
    out.push(`${s} ${p} ${o}${g} .`);
  }
  return out.join('\n') + '\n';
}

function median(xs) {
  const s = [...xs].sort((a, b) => a - b);
  const m = s.length >> 1;
  return s.length % 2 ? s[m] : (s[m - 1] + s[m]) / 2;
}

async function timeOp(fn) {
  await fn(); // warm-up
  const ms = [];
  const load = loadavg()[0];
  for (let i = 0; i < RUNS; i++) {
    const t0 = process.hrtime.bigint();
    await fn();
    ms.push(Number(process.hrtime.bigint() - t0) / 1e6);
  }
  return { median_ms: +median(ms).toFixed(2), min_ms: +Math.min(...ms).toFixed(2),
           all_ms: ms.map((x) => +x.toFixed(2)), load1: +load.toFixed(2) };
}

async function measureSize(n) {
  const text = genNQuads(n);
  const answers = {};
  const ops = {};
  const want = (op) => !ONLY || ONLY.has(op);
  const ds = await f.parse(text, { format: 'nquads' });
  answers.size = ds.size;
  const subj = `${EX}s0`;
  const cases = {
    parse: async () => { const d = await f.parse(text, { format: 'nquads' }); d.dispose(); },
    iterate: async () => { let k = 0; for (const _q of ds) k++; answers.iterate = k; },
    size: async () => { answers.sizeProp = ds.size; },
    'query-count': async () => {
      const r = await ds.query('SELECT (COUNT(*) AS ?c) WHERE { { ?s ?p ?o } UNION { GRAPH ?g { ?s ?p ?o } } }');
      answers.queryCount = Number([...r][0].get('c').value);
    },
    'query-bound': async () => {
      const r = await ds.query(`SELECT ?p ?o WHERE { GRAPH ?g { <${subj}> ?p ?o } }`);
      answers.queryBound = [...r].length;
    },
    'serialize-nquads': async () => { answers.serNq = (await ds.serialize({ format: 'nquads' })).length; },
    'serialize-turtle': async () => {
      answers.serTtl = (await ds.match(null, null, null, null).serialize({ format: 'trig' })).length;
    },
    'toString-nquads': async () => { answers.toStr = ds.toString('nquads').length; },
  };
  for (const [op, fn] of Object.entries(cases)) {
    if (!want(op)) continue;
    ops[op] = await timeOp(fn);
    process.stderr.write(`[${n} ${op}] ${ops[op].median_ms} ms (min ${ops[op].min_ms}) load ${ops[op].load1}\n`);
  }
  ds.dispose();

  const dir = mkdtempSync(join(tmpdir(), 'npm-costs-'));
  try {
    if (want('serve-store')) {
      const src = join(dir, 'd.nq');
      writeFileSync(src, text);
      const st = join(dir, 'st');
      execFileSync(process.execPath, [CLI, 'pack', src, join(st, 'gen-1'), '--quiet'], { stdio: 'inherit' });
      execFileSync(process.execPath, [CLI, 'activate', st, 'gen-1', '--quiet'], { stdio: 'inherit' });
      const s = await f.serveStore(st);
      try {
        const q = 'SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?p ?o } }';
        ops['serve-store'] = await timeOp(async () => {
          const r = await fetch(`${s.url}?query=${encodeURIComponent(q)}`,
            { headers: { accept: 'application/sparql-results+json' } });
          if (r.status !== 200) throw new Error(`serveStore answered ${r.status}`);
          const j = await r.json();
          answers.serveCount = Number(j.results.bindings[0].c.value);
        });
      } finally { await s.close(); }
      process.stderr.write(`[${n} serve-store] ${ops['serve-store'].median_ms} ms\n`);
    }
    if (want('lws-put') || want('lws-get')) {
      // the same statements in one graph: an LWS resource is one RDF graph
      const nt = genNQuads(n, false);
      const lws = await lwsListen({ engine: await f.loadEngine(), port: 0, insecureNoAuth: true });
      const url = `${lws.origin}/data.nt`;
      try {
        let k = 0;
        ops['lws-put'] = await timeOp(async () => {
          const r = await fetch(`${lws.origin}/d${k++}.nt`, {
            method: 'PUT', headers: { 'content-type': 'application/n-triples' }, body: nt });
          if (r.status >= 300) throw new Error(`lws PUT answered ${r.status}: ${await r.text()}`);
          await r.arrayBuffer();
        });
        const put = await fetch(url, { method: 'PUT', headers: { 'content-type': 'application/n-triples' }, body: nt });
        if (put.status >= 300) throw new Error(`lws PUT answered ${put.status}`);
        ops['lws-get'] = await timeOp(async () => {
          const r = await fetch(url, { headers: { accept: 'application/n-triples' } });
          if (r.status !== 200) throw new Error(`lws GET answered ${r.status}`);
          answers.lwsGetBytes = (await r.arrayBuffer()).byteLength;
        });
      } finally { await lws.close(); }
      process.stderr.write(`[${n} lws] put ${ops['lws-put'].median_ms} ms, get ${ops['lws-get'].median_ms} ms\n`);
    }
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
  return { quads: n, input_bytes: Buffer.byteLength(text), answers, ops };
}

const version = JSON.parse(readFileSync(join(PKG, 'package.json'), 'utf8')).version;
let wasmBuild = null;
try { wasmBuild = JSON.parse(readFileSync(join(PKG, 'l4-assets/version.json'), 'utf8')).release ?? null; } catch { /* placeholder */ }
const result = {
  kind: 'npm-costs', time: new Date().toISOString(), package: `@factoidal/core ${version}`,
  wasm_build: wasmBuild, node: process.version, cpus: cpus().length, runs: RUNS, sizes: {},
};
for (const n of SIZES) result.sizes[n] = await measureSize(n);

if (WRITE) {
  writeFileSync(RESULTS, JSON.stringify(result, null, 1) + '\n');
  console.log(`npm_costs: wrote ${RESULTS}`);
  process.exit(0);
}
if (!existsSync(RESULTS)) {
  console.error(`npm_costs: ${RESULTS} missing; run with --write first`);
  process.exit(2);
}
const prev = JSON.parse(readFileSync(RESULTS, 'utf8'));
let fails = 0; let pass = 0;
for (const [n, cur] of Object.entries(result.sizes)) {
  for (const [op, r] of Object.entries(cur.ops)) {
    const p = prev.sizes?.[n]?.ops?.[op];
    if (!p) { console.log(`NEW  ${n} ${op}: ${r.median_ms} ms (no committed row)`); continue; }
    const bound = (1 + TOLERANCE) * p.median_ms + SLACK_MS;
    let v = r.median_ms;
    if (v > bound) {
      // measured once more; the minimum of the repeat decides
      const again = await measureSize(Number(n)).then((x) => x.ops[op]);
      v = Math.min(again.min_ms, v);
      r.load1 = Math.max(r.load1, again.load1);
    }
    const tag = v <= bound ? 'PASS' : (r.load1 > cpus().length ? 'NOISY' : 'FAIL');
    if (tag === 'FAIL') fails++; else pass++;
    console.log(`${tag} ${n} ${op}: ${v} ms (committed ${p.median_ms} ms, bound ${bound.toFixed(1)} ms, load ${r.load1})`);
  }
}
console.log(`npm_costs: ${pass} pass, ${fails} fail (out of ${pass + fails})`);
process.exit(fails && !NO_FAIL ? 1 : 0);
