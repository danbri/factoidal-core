// @factoidal/core/core — the Node entry (ES module) of the CORE engine,
// l4factoidal-core.wasm (issue 713 stage 4,
// https://github.com/danbri/factoidal/issues/713).
//
//   import { parse, query } from '@factoidal/core/core';
//   const ds = await parse('@prefix : <http://ex/> . :a :p :b .');
//   const rows = await query(ds, 'SELECT * WHERE { ?s ?p ?o }');
//
// The core engine is the Lean 4 library compiled to WebAssembly with a
// dispatch table that reaches a subset of it: parse and serialise Turtle,
// TriG, N-Triples, N-Quads (RDF 1.1 and 1.2) and RDF/XML, the lenient parse,
// SPARQL 1.1 and 1.2 query and update over text and dataset handles,
// RDFC-1.0 canonicalisation, the RDFS, RDFS-Plus and OWL 2 RL closures, and
// SHACL. The linker drops the rest of the library, so the module is smaller
// than the full engine's (sizes: README.md). A function outside that subset
// rejects with an error that names '@factoidal/core', whose full engine
// serves it; capabilities() reports profile 'core' and false for each
// function the module does not serve.
//
// The exports and their types are index.mjs's (index.d.ts). The engine's
// three files are l4-assets/l4factoidal-core.{js,mjs,wasm};
// $FACTOIDAL_L4_ASSETS names another directory holding them (bin/engine.mjs).
// core.js gives the same module to require(); core-browser.js is the
// browser entry.

import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { buildApi } from './lib/api.mjs';
import { entryFromEngine } from './lib/lean-entry.mjs';

/**
 * The loaded Lean engine handle: `call(op, args)`, `callBlob`,
 * `callBlobIO`, `version()`, over the dispatch ABI of
 * formal/lean4/Wasm/Dispatch.lean. For the ops this package does not wrap
 * (the `ops` op lists every name). Loaded once per process.
 * @returns {Promise<object>}
 */
export async function loadEngine() {
  // A dynamic import: bin/engine.mjs reads files through store-host/, which
  // picks its Node or Deno implementation with a top-level await, and a
  // module that require() loads may not have one in its static graph.
  const mod = await import('./bin/engine.mjs');
  return mod.loadEngine('l4factoidal-core');
}

const api = buildApi({
  engineName: 'lean4-wasm-core',
  loadEntry: async () => entryFromEngine(await loadEngine()),
  storeReaderFor: (root) => (path) => readFileSync(join(root, path)),
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
// The sample store this package carries (sample-store/, IPTC NewsCodes,
// CC BY 4.0): openStore(sampleStorePath()) answers with no download.
export { sampleStorePath, sampleStoreFacts } from './sample-store.mjs';

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

/** As index.mjs serveStore. The server loads the full engine (the store ops are not in the core module). */
export async function serveStore(root, options = {}) {
  const { listen } = await import('./bin/serve.mjs');
  const s = await listen(root, options);
  return { url: `${s.origin}${options.queryPath ?? "/sparql"}`, port: s.port, close: () => s.close() };
}
