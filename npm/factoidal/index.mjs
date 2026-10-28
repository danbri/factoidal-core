// @factoidal/core — the Node entry (ES module). One engine: the Lean 4
// library L4Factoidal (formal/lean4) compiled to WebAssembly.
//
//   import { parse, query } from '@factoidal/core';
//   const ds = await parse('@prefix : <http://ex/> . :a :p :b .');
//   const rows = await query(ds, 'SELECT * WHERE { ?s ?p ?o }');
//
// The engine loads on the first call. Its three files sit in this
// package's l4-assets/ (l4factoidal.js, l4factoidal.mjs,
// l4factoidal.wasm); $FACTOIDAL_L4_ASSETS names another directory with
// the same three files, and a repository checkout falls back to
// docs/web/hub/assets/l4/ (bin/engine.mjs resolves them, for this module
// and for the `factoidal` command, so both share one engine instance).
//
// index.js gives the same module to require(). browser.js is the browser
// entry; api.mjs takes an engine the caller loaded itself.
//
// Types: index.d.ts. Every function is in lib/api.mjs.

import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { buildApi } from './lib/api.mjs';
import { entryFromEngine } from './lib/lean-entry.mjs';
import { sbm11Api, registerSbm11Source, setDefaultSbm11Reader, mapReader } from './lib/sbm11.mjs';
import { nodeDefaultReaderFactory } from './lib/sbm11-node.mjs';
import { lwsSbm11Reader as lwsSbm11ReaderWith } from './lib/sbm11-lws.mjs';
import { nodeSyncTransport } from './lib/sync-http-node.mjs';

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
  return mod.loadEngine();
}

const api = buildApi({
  engineName: 'lean4-wasm',
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
export const asDefaultGraph = api.asDefaultGraph;
export const isomorphic = api.isomorphic;
export const datasetMerge = api.datasetMerge;
export const fromQuads = api.fromQuads;
// Literal values (https://github.com/danbri/factoidal/issues/1051): synchronous
// after the engine is loaded.
export const literalValue = api.literalValue;
export const isValidLiteral = api.isValidLiteral;
export const canonicalLiteral = api.canonicalLiteral;
export const literalFromValue = api.literalFromValue;
export const ready = api.ready;
export const engineTables = api.engineTables;
export const sameValue = api.sameValue;
export const syntaxFor = api.syntaxFor;
export const splitIri = api.splitIri;
export const isNCName = api.isNCName;
export const vocabularies = api.vocabularies;
export const memberIri = api.memberIri;
export const memberOrdinal = api.memberOrdinal;
export const openDataset = api.openDataset;
export const closure = api.closure;
export const sparqlRlInfer = api.sparqlRlInfer;
export const formats = api.formats;
export const queryRaw = api.queryRaw;
export const queryHdt = api.queryHdt;
export const registerExtensionFunction = api.registerExtensionFunction;
export const unregisterExtensionFunction = api.unregisterExtensionFunction;
export const clearExtensionFunctions = api.clearExtensionFunctions;
export const registerServiceEndpoint = api.registerServiceEndpoint;
export const clearServiceEndpoints = api.clearServiceEndpoints;

// SBM11, the Shardborough store, through host positioned reads
// (lib/sbm11.mjs; https://github.com/danbri/factoidal/issues/1009). In Node a
// source with no registered reader is a directory.
setDefaultSbm11Reader(nodeDefaultReaderFactory());
const sbm11 = sbm11Api(loadEngine);
export const openSbm11 = sbm11.openSbm11;
// Pack a document into the files of an SBM11 generation in memory, and a
// reader over such files (issue 1009 stage 2).
export const packSbm11 = sbm11.packSbm11;
export { registerSbm11Source, mapReader };

// A reader of an SBM11 generation held as LWS resources (lib/sbm11-lws.mjs;
// https://github.com/danbri/factoidal/issues/1010 KR3). In Node the default
// synchronous transport is a fetch in a worker thread (lib/sync-http-node.mjs),
// stopped by the reader's close().
export function lwsSbm11Reader(url, opts = {}) {
  if (typeof opts.transport === 'function') return lwsSbm11ReaderWith(url, opts);
  const transport = nodeSyncTransport({ timeoutMs: opts.timeoutMs });
  return lwsSbm11ReaderWith(url, { ...opts, transport, onClose: () => transport.close() });
}

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
export const graph = api.graph;
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

/**
 * Serve an activated store (a collection root that holds CURRENT) over the
 * SPARQL 1.1 Protocol, the Graph Store Protocol and the Service
 * Description: the same server as `factoidal serve STORE`. Node only.
 * With `{tdb2: true}`, `root` is an Apache Jena TDB2 database directory,
 * read in place and served read only (updates answer 501;
 * https://github.com/danbri/factoidal/issues/834).
 * @param {string} root
 * @param {{port?: number, host?: string, queryPath?: string, gspPath?: string,
 *          tdb2?: boolean}} [options] port 0 (default) picks one
 * @returns {Promise<{url: string, port: number, close: () => Promise<void>}>}
 */
export async function serveStore(root, options = {}) {
  const { listen } = await import('./bin/serve.mjs');
  const s = await listen(root, { ...options, engine: await loadEngine() });
  return { url: `${s.origin}${options.queryPath ?? "/sparql"}`, port: s.port, close: () => s.close() };
}

// A small store packed on demand from triples held in sample-store.mjs (no
// data file ships; owner, 2026-10-20). Node only.
export { sampleStorePath, sampleStoreFacts } from './sample-store.mjs';
