// @factoidal/core in the browser (ES module). One engine: the Lean 4
// library L4Factoidal compiled to WebAssembly, the same module index.mjs
// loads under Node.
//
//   <script type="module">
//     import { parse, query } from 'https://cdn.jsdelivr.net/npm/@factoidal/core/browser.js';
//     const rows = await query('<http://e/a> <http://e/p> "v" .', 'SELECT * WHERE { ?s ?p ?o }',
//       { format: 'ntriples' });
//   </script>
//
// The engine loads on the first call: the loader l4-assets/l4factoidal.js
// is imported, and the wasm is fetched and compiled with
// WebAssembly.instantiateStreaming (a server that does not send
// `Content-Type: application/wasm` gets WebAssembly.instantiate over the
// fetched bytes instead). setAssetsUrl() names another directory holding
// l4factoidal.js, l4factoidal.mjs and l4factoidal.wasm.
//
// The exports and their types are index.mjs's (index.d.ts), except
// sampleStorePath, and openStore() takes a reader function, (path) =>
// bytes, because a page has no file system:
//
//   const store = await openStore((p) => fetch(base + p).then((r) => r.arrayBuffer()));
//
// A Content-Security-Policy page needs 'wasm-unsafe-eval' in script-src.

import { buildApi } from './lib/api.mjs';
import { entryFromEngine } from './lib/lean-entry.mjs';

let assetsUrl = new URL('./l4-assets/', import.meta.url).href;
let enginePromise = null;

/**
 * The directory the engine's three files are loaded from. Call before the
 * first operation; the engine loads once per page.
 * @param {string|URL} url a directory URL (a trailing '/' is added)
 */
export function setAssetsUrl(url) {
  if (enginePromise) {
    throw new Error('setAssetsUrl: the engine is already loaded from ' + assetsUrl);
  }
  const text = String(url);
  assetsUrl = new URL(text.endsWith('/') ? text : text + '/', globalThis.location?.href).href;
}

/** The directory the engine's files are loaded from. */
export function getAssetsUrl() {
  return assetsUrl;
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
 * The loaded Lean engine handle (call, callBlob, callBlobIO, version), for
 * the dispatch ops this package does not wrap.
 * @returns {Promise<object>}
 */
export function loadEngine() {
  if (enginePromise) return enginePromise;
  enginePromise = (async () => {
    const loader = await import(new URL('l4factoidal.js', assetsUrl).href);
    // The content-hash version keeps a cached wasm from pairing with a
    // newer loader (the loader's own locateFile does the same).
    const version = loader.wasmVersion ? `?v=${loader.wasmVersion}` : '';
    const wasmUrl = new URL('l4factoidal.wasm', assetsUrl).href + version;
    return loader.loadL4({ instantiateWasm: (imports) => instantiate(wasmUrl, imports) });
  })();
  enginePromise.catch(() => { enginePromise = null; });
  return enginePromise;
}

const api = buildApi({
  engineName: 'lean4-wasm',
  loadEntry: async () => entryFromEngine(await loadEngine()),
});

// RDF and SPARQL
export const parse = api.parse;
export const query = api.query;
export const update = api.update;
export const serialize = api.serialize;
export const canonicalize = api.canonicalize;
export const graphs = api.graphs;
export const canonicalHash = api.canonicalHash;
export const openDataset = api.openDataset;
export const queryRaw = api.queryRaw;
export const queryHdt = api.queryHdt;
export const registerExtensionFunction = api.registerExtensionFunction;
export const unregisterExtensionFunction = api.unregisterExtensionFunction;
export const clearExtensionFunctions = api.clearExtensionFunctions;
export const registerServiceEndpoint = api.registerServiceEndpoint;
export const clearServiceEndpoints = api.clearServiceEndpoints;

// The persisted store
export const openStore = api.openStore;
export const queryStore = api.queryStore;
export const listStores = api.listStores;

// Validation and reasoning
export const shaclValidate = api.shaclValidate;
export const shexValidate = api.shexValidate;
export const owlClosure = api.owlClosure;
export const coreRdfsClosure = api.coreRdfsClosure;
export const coreRdfsCheck = api.coreRdfsCheck;
export const rdfsPlusClosure = api.rdfsPlusClosure;
export const rhoDfClosure = api.rhoDfClosure;
export const rhoDfFragmentCheck = api.rhoDfFragmentCheck;
export const tableauMaterialise = api.tableauMaterialise;
export const tableauDlInconsistent = api.tableauDlInconsistent;
export const owlIsConsistent = api.owlIsConsistent;
export const owlEntails = api.owlEntails;
export const rifEval = api.rifEval;

// Mappings and other formats
export const rmlMap = api.rmlMap;
export const csvwToRdf = api.csvwToRdf;
export const jsonldToRdf = api.jsonldToRdf;
export const jsonldFromRdf = api.jsonldFromRdf;
export const xmlWellformed = api.xmlWellformed;
export const xpathEval = api.xpathEval;
export const xsltTransform = api.xsltTransform;
export const schematronValidate = api.schematronValidate;
export const jsonSchemaValidate = api.jsonSchemaValidate;
export const mathmlEval = api.mathmlEval;
export const xformsRecalc = api.xformsRecalc;

// Common Logic
export const clParse = api.clParse;
export const clSerialize = api.clSerialize;
export const clAlphaNorm = api.clAlphaNorm;
export const clNormalize = api.clNormalize;

// Maths
export const toanSummation = api.toanSummation;
export const toanProduct = api.toanProduct;
export const toanSimplify = api.toanSimplify;
export const toanDiff = api.toanDiff;
export const toanSubst = api.toanSubst;
export const matrixDeterminant = api.matrixDeterminant;
export const matrixScalarProduct = api.matrixScalarProduct;
export const matrixVectorProduct = api.matrixVectorProduct;
export const matrixOuterProduct = api.matrixOuterProduct;
export const sigmoidPoints = api.sigmoidPoints;
export const sigmoidFormulaMathml = api.sigmoidFormulaMathml;

// Verifiable Credentials and DID
export const vcSha256Hex = api.vcSha256Hex;
export const vcEd25519SecretToPublic = api.vcEd25519SecretToPublic;
export const vcEd25519Sign = api.vcEd25519Sign;
export const vcEd25519Verify = api.vcEd25519Verify;
export const vcEddsaCreateFromCanonical = api.vcEddsaCreateFromCanonical;
export const vcEddsaVerifyFromCanonical = api.vcEddsaVerifyFromCanonical;
export const vcCheckCredential = api.vcCheckCredential;
export const vcCheckCredentialSubject = api.vcCheckCredentialSubject;
export const vcCheckNoDataLoss = api.vcCheckNoDataLoss;
export const vcCheckRelatedResourceDigests = api.vcCheckRelatedResourceDigests;
export const didKeyResolve = api.didKeyResolve;

// Types, probes and metadata
export const capabilities = api.capabilities;
export const Dataset = api.Dataset;
export const DatasetHandle = api.DatasetHandle;
export const Store = api.Store;
export const ParseError = api.ParseError;
export const dataFactory = api.dataFactory;
export const version = api.version;
export const engine = api.engine;
export default api;
