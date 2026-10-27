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
// The exports and their types are index.mjs's (index.d.ts), and openStore() takes a reader function, (path) =>
// bytes, because a page has no file system:
//
//   const store = await openStore((p) => fetch(base + p).then((r) => r.arrayBuffer()));
//
// A Content-Security-Policy page needs 'wasm-unsafe-eval' in script-src.

import { buildApi } from './lib/api.mjs';
import { entryFromEngine } from './lib/lean-entry.mjs';
import { browserEngine } from './lib/browser-engine.mjs';
import { indexedDbDeltaLogStore } from './lib/delta-log-hosts.mjs';
import { sbm11Api, registerSbm11Source, mapReader } from './lib/sbm11.mjs';
import { lwsSbm11Reader } from './lib/sbm11-lws.mjs';

const l4Engine = browserEngine('l4factoidal', new URL('./l4-assets/', import.meta.url).href);

/**
 * The directory the engine's three files are loaded from. Call before the
 * first operation; the engine loads once per page.
 * @param {string|URL} url a directory URL (a trailing '/' is added)
 */
export function setAssetsUrl(url) {
  l4Engine.setAssetsUrl(url);
}

/** The directory the engine's files are loaded from. */
export function getAssetsUrl() {
  return l4Engine.getAssetsUrl();
}

/**
 * The loaded Lean engine handle (call, callBlob, callBlobIO, version), for
 * the dispatch ops this package does not wrap.
 * @returns {Promise<object>}
 */
export function loadEngine() {
  return l4Engine.loadEngine();
}

const api = buildApi({
  engineName: 'lean4-wasm',
  loadEntry: async () => entryFromEngine(await loadEngine()),
  // The deltaLog* functions keep their records in IndexedDB (hub post 18).
  deltaLogStore: indexedDbDeltaLogStore(),
});

// SBM11, the Shardborough store, through host positioned reads
// (lib/sbm11.mjs; https://github.com/danbri/factoidal/issues/1009). In a
// browser every source needs a registered synchronous reader, for example
// over OPFS FileSystemSyncAccessHandle in a dedicated worker.
const sbm11 = sbm11Api(loadEngine);
export const openSbm11 = sbm11.openSbm11;
// Pack a document into the files of an SBM11 generation in memory, and a
// reader over such files (issue 1009 stage 2).
export const packSbm11 = sbm11.packSbm11;
export { registerSbm11Source, mapReader };
// A reader of an SBM11 generation held as LWS resources (issue 1010 KR3). In
// a browser worker its default transport is a synchronous XMLHttpRequest.
export { lwsSbm11Reader };

// RDF and SPARQL
export const parse = api.parse;
export const query = api.query;
export const update = api.update;
export const serialize = api.serialize;
export const canonicalize = api.canonicalize;
export const graphs = api.graphs;
export const canonicalHash = api.canonicalHash;
export const isomorphic = api.isomorphic;
export const fromQuads = api.fromQuads;
export const ready = api.ready;
export const engineTables = api.engineTables;
export const openDataset = api.openDataset;
export const closure = api.closure;
export const formats = api.formats;
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

// The durable update log (hub post 18)
export const deltaLogOpen = api.deltaLogOpen;
export const deltaLogAppend = api.deltaLogAppend;
export const deltaLogReadAllHex = api.deltaLogReadAllHex;
export const deltaLogMerge = api.deltaLogMerge;
export const deltaLogInspect = api.deltaLogInspect;
export const deltaLogDestroy = api.deltaLogDestroy;
export const _deltaLogCorruptLastForTest = api._deltaLogCorruptLastForTest;

// Validation and reasoning
export const shaclValidate = api.shaclValidate;
export const shexValidate = api.shexValidate;
export const owlClosure = api.owlClosure;
export const coreRdfsClosure = api.coreRdfsClosure;
export const coreRdfsCheck = api.coreRdfsCheck;
export const explain = api.explain;
export const stages = api.stages;
export const node = api.node;
export const pipe = api.pipe;
export const run = api.run;
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

// Verifiable Credentials and DID
export const vcSha256Hex = api.vcSha256Hex;
export const vcEd25519SecretToPublic = api.vcEd25519SecretToPublic;
export const vcEd25519Sign = api.vcEd25519Sign;
export const vcEd25519Verify = api.vcEd25519Verify;

// XML Encryption 1.1 and JWE; AES through WebCrypto (lib/cipher-host.mjs)
export const xmlDecrypt = api.xmlDecrypt;
export const xmlEncrypt = api.xmlEncrypt;
export const jweDecrypt = api.jweDecrypt;
export const jweEncrypt = api.jweEncrypt;
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
export const Store = api.Store;
export const FactoidalError = api.FactoidalError;
export const dataFactory = api.dataFactory;
export const version = api.version;
export const engine = api.engine;
export default api;

// Pure functions over engine ops added in 0.10.0 (lib/pure.mjs).
import { buildPure } from './lib/pure.mjs';
const pure = buildPure(loadEngine);
export const aeadSeal = pure.aeadSeal;
export const aeadOpen = pure.aeadOpen;
export const hpkeSeal = pure.hpkeSeal;
export const hpkeOpen = pure.hpkeOpen;
export const proofCheck = pure.proofCheck;
export const proofInspect = pure.proofInspect;
export const canonicalizeNQuads = pure.canonicalizeNQuads;
export const normalizeNQuads = pure.normalizeNQuads;
