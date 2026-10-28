// node-bench.mjs — the same measurements for the Emscripten module and for
// the jco-transpiled component, in Node.
//
//   node node-bench.mjs emcc <emcc .mjs> <ttl> <rq> [reps]
//   node node-bench.mjs jco  <jco dir/engine.js> <ttl> <rq> [reps]
//
// Prints one JSON line: instantiate_ms (load + compile + instantiate +
// Lean module initialisers, run by one empty call for the component), first-call times, median parse and query
// times over `reps` calls, and a SHA-256 of each answer, so that the
// builds can be checked to give the same bytes.
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { pathToFileURL } from 'node:url';

const [mode, mod, ttlPath, rqPath, repsArg] = process.argv.slice(2);
const ttl = readFileSync(ttlPath, 'utf8');
const rq = readFileSync(rqPath, 'utf8');
const reps = Number(repsArg ?? 5);
const sha = (s) => createHash('sha256').update(s).digest('hex').slice(0, 16);
const median = (xs) => xs.length ? [...xs].sort((a, b) => a - b)[Math.floor(xs.length / 2)] : NaN;

let parse, query;
const t0 = performance.now();
if (mode === 'emcc') {
  const { default: create } = await import(pathToFileURL(mod).href);
  const M = await create();
  if (!M._wc_init()) throw new Error('wc_init failed');
  const put = (s) => {
    const n = M.lengthBytesUTF8(s) + 1, p = M._malloc(n);
    M.stringToUTF8(s, p, n);
    return p;
  };
  const call = (fn, a, b) => {
    const pa = put(a), pb = put(b);
    try {
      const r = fn(pa, pb);
      try { return M.UTF8ToString(r); } finally { M._wc_free(r); }
    } finally { M._free(pa); M._free(pb); }
  };
  parse = (t) => call(M._wc_turtle_to_nquads_c, t, '');
  query = (t, q) => call(M._wc_query_turtle_c, t, q);
} else if (mode === 'jco') {
  const { rdf } = await import(pathToFileURL(mod).href);
  parse = (t) => rdf.turtleToNquads(t, undefined);
  query = (t, q) => rdf.query(t, q);
  // The component initialises Lean on its first call (wc_shim.c wc_init);
  // make that call here so instantiate_ms covers the same work as emcc's.
  parse('');
} else {
  throw new Error(`unknown mode ${mode}`);
}
const instantiate = performance.now() - t0;

const time = (f) => { const s = performance.now(); const r = f(); return [performance.now() - s, r]; };
const [p1, nq] = time(() => parse(ttl));
const [q1, ans] = time(() => query(ttl, rq));
const ps = [], qs = [];
for (let i = 0; i < reps; i++) { ps.push(time(() => parse(ttl))[0]); qs.push(time(() => query(ttl, rq))[0]); }
console.log(JSON.stringify({
  mode, instantiate_ms: +instantiate.toFixed(1),
  first_parse_ms: +p1.toFixed(1), first_query_ms: +q1.toFixed(1),
  parse_ms: +median(ps).toFixed(1), query_ms: +median(qs).toFixed(1),
  nquads_sha: sha(nq), nquads_bytes: Buffer.byteLength(nq), answer_sha: sha(ans),
  answer: ans.length < 400 ? ans : ans.slice(0, 400) + '…',
}));
