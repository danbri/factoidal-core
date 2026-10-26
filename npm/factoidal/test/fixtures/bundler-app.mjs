// Fixture bundled by test/bundler-esbuild.test.mjs and by
// tests/web-demos/bundler_csp_smoke.sh (issue #682). It imports the typed
// API (`@factoidal/core/api`) and the Lean engine's loader
// (`@factoidal/core/l4-assets/l4factoidal.js`), both static imports, and
// hands the loader an instantiateWasm hook, so the page decides where the
// wasm comes from:
//
//   - globalThis.__FACTOIDAL_WASM_BYTES__ (the Node test sets it): the
//     bytes, compiled with WebAssembly.instantiate;
//   - otherwise fetch() of globalThis.__FACTOIDAL_WASM_URL__, or of
//     './l4factoidal.wasm' next to the page, compiled with
//     WebAssembly.instantiateStreaming.
//
// No `new Function`, no eval: a page with
// `Content-Security-Policy: script-src 'self' 'wasm-unsafe-eval'` runs it.
// Both callers bundle this file with esbuild (bundle: true, platform:
// 'browser', format: 'esm') and run the output: the Node test reads the
// `ROW_COUNT:N` line; the browser script reads `document.title`.

import { createApi } from '@factoidal/core/api';
import { loadL4 } from '@factoidal/core/l4-assets/l4factoidal.js';

function instantiateWasm(imports) {
  const bytes = globalThis.__FACTOIDAL_WASM_BYTES__;
  if (bytes) return WebAssembly.instantiate(bytes, imports);
  const url = globalThis.__FACTOIDAL_WASM_URL__ || new URL('./l4factoidal.wasm', document.baseURI).href;
  return WebAssembly.instantiateStreaming(fetch(url), imports);
}

const factoidal = createApi(() => loadL4({ instantiateWasm }));

const TTL = `
  @prefix ex:   <http://example.org/> .
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows ex:bob .
  ex:bob   a foaf:Person ; foaf:name "Bob" .
  ex:carol a foaf:Person ; foaf:name "Carol" .
`;

export const EXPECTED_ROW_COUNT = 3;

const ds = await factoidal.parse(TTL, { format: 'turtle' });
const rows = await factoidal.query(ds,
  'PREFIX foaf: <http://xmlns.com/foaf/0.1/> SELECT ?p WHERE { ?p a foaf:Person }');

export const rowCount = rows.length;

// eslint-disable-next-line no-console -- the Node driver's assertion surface
console.log('ROW_COUNT:' + rowCount);

if (typeof document !== 'undefined') {
  document.title = String(rowCount);
}
