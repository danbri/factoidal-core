// node-bench.mjs — instantiation and call times of one build of the
// Factoidal subset in Node, on the inputs of bench/data.
//
//   node node-bench.mjs jco <dir-with-subset.js> <doc> <format> <query> [n]
//   node node-bench.mjs emcc <dir-with-fxsubset.mjs> <doc> <format> <query> [n]
//
// Prints one JSON line: importMs (fetch, compile and instantiate the module),
// initMs (first call on a one-triple document; Lean's module initialisers run
// here), and the median parse and query times in ms over n runs.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { performance } from 'node:perf_hooks';

const [kind, dir, docPath, format, queryPath, nArg] = process.argv.slice(2);
const n = Number(nArg ?? 5);
const doc = readFileSync(docPath, 'utf8');
const query = readFileSync(queryPath, 'utf8');
const median = (v) => v.sort((a, b) => a - b)[Math.floor(v.length / 2)];

let t0 = performance.now();
let parse, run;
if (kind === 'jco') {
  const { rdf } = await import(pathToFileURL(`${dir}/subset.js`).href);
  parse = (text, fmt) => rdf.parse(text, fmt, '');        // throws ComponentError on err
  run = (nq, q) => rdf.query(nq, q);
} else if (kind === 'emcc') {
  const factory = (await import(pathToFileURL(`${dir}/fxsubset.mjs`).href)).default;
  const M = await factory();
  const call = (name, args) => {
    const r = M.ccall(name, 'number', args.map(() => 'string'), args);
    const s = M.UTF8ToString(r);
    M._free(r);
    return s;
  };
  parse = (text, fmt) => {
    const s = call('fx_parse_c', [text, fmt, '']);
    if (s.startsWith('E')) throw new Error(s.slice(1));
    return s.slice(1);
  };
  run = (nq, q) => call('fx_query_c', [nq, q]);
} else throw new Error(`unknown kind ${kind}`);
const importMs = performance.now() - t0;

t0 = performance.now();
parse('<urn:s> <urn:p> <urn:o> .', 'ntriples');
const initMs = performance.now() - t0;

const p = [], q = [];
let nq = '', answer = '';
for (let i = 0; i < n; i++) {
  t0 = performance.now(); nq = parse(doc, format); p.push(performance.now() - t0);
  t0 = performance.now(); answer = run(nq, query); q.push(performance.now() - t0);
}
console.log(JSON.stringify({
  kind, importMs: +importMs.toFixed(1), initMs: +initMs.toFixed(1),
  parseMs: +median(p).toFixed(1), queryMs: +median(q).toFixed(1),
  nquadsBytes: nq.length, answerBytes: answer.length,
  answerSha: (await import('node:crypto')).createHash('sha256').update(answer).digest('hex').slice(0, 16),
}));
