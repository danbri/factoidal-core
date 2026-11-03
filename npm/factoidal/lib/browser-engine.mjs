// Loading a Lean engine in the browser: one of the two modules of
// l4-assets/ (issue 713 stage 4), named by its basename:
//
//   'l4factoidal'       the full engine (browser.js)
//   'l4factoidal-core'  the core engine (core-browser.js)
//
// Each engine is three files that keep their names together: the loader
// <name>.js, Emscripten's glue <name>.mjs and the module <name>.wasm. The
// loader is imported from the assets directory; the wasm is fetched and
// compiled with WebAssembly.instantiateStreaming (a server that does not
// send `Content-Type: application/wasm` gets WebAssembly.instantiate over
// the fetched bytes instead).
//
// No Node built-ins: the browser imports this file as it is.

import { checkEngineStamp } from './engine-integrity.mjs';

// version.json next to the engine, or null (absent, unreadable, not JSON).
async function stampOf(url) {
  try {
    const r = await fetch(url);
    return r.ok ? await r.json() : null;
  } catch {
    return null;
  }
}

async function instantiate(url, imports) {
  try {
    return await WebAssembly.instantiateStreaming(fetch(url), imports);
  } catch (err) {
    // instantiateStreaming refuses a response without the application/wasm
    // media type with a TypeError; compile from the bytes then. Any other
    // failure (network, a corrupt module) is the caller's.
    if (!(err instanceof TypeError)) throw err;
    const response = await fetch(url);
    if (!response.ok) {
      throw new Error(`factoidal: fetching ${url} failed: ${response.status} ${response.statusText}`);
    }
    return WebAssembly.instantiate(await response.arrayBuffer(), imports);
  }
}

/**
 * The asset-directory setters and the engine loader of one engine.
 * @param {string} name 'l4factoidal' or 'l4factoidal-core'
 * @param {string} defaultAssetsUrl the directory URL to load from until
 *        setAssetsUrl() names another
 */
export function browserEngine(name, defaultAssetsUrl) {
  let assetsUrl = defaultAssetsUrl;
  let enginePromise = null;

  function setAssetsUrl(url) {
    if (enginePromise) {
      throw new Error('setAssetsUrl: the engine is already loaded from ' + assetsUrl);
    }
    const text = String(url);
    assetsUrl = new URL(text.endsWith('/') ? text : text + '/', globalThis.location?.href).href;
  }

  function getAssetsUrl() {
    return assetsUrl;
  }

  function loadEngine() {
    if (enginePromise) return enginePromise;
    enginePromise = (async () => {
      const loader = await import(new URL(`${name}.js`, assetsUrl).href);
      // The content-hash version keeps a cached wasm from pairing with a
      // newer loader (the loader's own locateFile does the same).
      const version = loader.wasmVersion ? `?v=${loader.wasmVersion}` : '';
      const wasmUrl = new URL(`${name}.wasm`, assetsUrl).href + version;
      // The release stamp check (engine-integrity.mjs, issue 1106): with a
      // stamped version.json next to the full engine, its bytes are hashed
      // before they are compiled (no streaming compile then). Without one,
      // the streaming path as before.
      const stamp = name === 'l4factoidal'
        ? await stampOf(new URL('version.json', assetsUrl).href + version) : null;
      if (!stamp || stamp.stamped !== true) {
        return loader.loadL4({ instantiateWasm: (imports) => instantiate(wasmUrl, imports) });
      }
      const response = await fetch(wasmUrl);
      if (!response.ok) {
        throw new Error(`factoidal: fetching ${wasmUrl} failed: ${response.status} ${response.statusText}`);
      }
      const bytes = new Uint8Array(await response.arrayBuffer());
      await checkEngineStamp(bytes, stamp, { where: wasmUrl });
      return loader.loadL4({ instantiateWasm: (imports) => WebAssembly.instantiate(bytes, imports) });
    })();
    enginePromise.catch(() => { enginePromise = null; });
    return enginePromise;
  }

  return { setAssetsUrl, getAssetsUrl, loadEngine };
}
