// @factoidal/core/api — the typed API over a Lean engine the caller loads.
//
// index.mjs and browser.js find and load the engine themselves. A bundler
// build, or a page with its own asset layout, may want to load it another
// way: import the loader, instantiate the module however the page needs,
// and hand the result here.
//
//   import { createApi } from '@factoidal/core/api';
//   import { loadL4 } from '@factoidal/core/l4-assets/l4factoidal.js';
//   const factoidal = createApi(() => loadL4());
//   const ds = await factoidal.parse('<a> <b> "c" .', { format: 'ntriples' });
//
// `engine` is the handle loadL4() resolves to (an object with
// call(op, args)), a Promise of one, or a zero-argument function answering
// either. Nothing here fetches or evaluates code; WebAssembly compilation
// happens in the loader, which a Content-Security-Policy page allows with
// 'wasm-unsafe-eval'.
//
// openStore() here takes a reader function only: there is no file system.

import { buildApi, ParseError, DatasetHandle, Store } from './lib/api.mjs';
import { entryFromEngine } from './lib/lean-entry.mjs';
import { Dataset, dataFactory } from './rdfjs.mjs';
import { version } from './lib/version.mjs';

function isThenable(x) {
  return !!x && (typeof x === 'object' || typeof x === 'function') &&
    typeof x.then === 'function';
}

/**
 * The typed API (the functions index.mjs exports) over a Lean engine.
 * @param {object|Promise<object>|(() => object|Promise<object>)} engine
 * @param {{engineName?: string}} [options]
 */
export function createApi(engine, options) {
  const opts = options || {};
  // A plain handle is checked now, so a wrong argument fails here and not
  // at the first query.
  let entry = (typeof engine !== 'function' && !isThenable(engine))
    ? entryFromEngine(engine)
    : undefined;
  return buildApi({
    engineName: opts.engineName || 'lean4-wasm',
    loadEntry: async () => {
      if (entry !== undefined) return entry;
      const produced = typeof engine === 'function' ? engine() : engine;
      entry = entryFromEngine(await produced);
      return entry;
    },
  });
}

export { buildApi, entryFromEngine, ParseError, DatasetHandle, Store, Dataset, dataFactory, version };
export default createApi;
