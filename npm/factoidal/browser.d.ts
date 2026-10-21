// TypeScript declarations for '@factoidal/core/browser' (browser.js): the
// functions of the main entry (index.d.ts), loaded in the browser. The
// engine's wasm is fetched and compiled with WebAssembly.instantiateStreaming
// on the first call. openStore() takes a StoreReader: a page has no file
// system, so a path string rejects.

export type {
  FactoidalErrorCode,
  FactoidalErrorPosition,
  NamedNode, BlankNode, Literal, Variable, DefaultGraph, Quad, Term, DataFactory,
  DataFormat, EntailRegime, Bindings, DataInput, QueryInput, ParseOptions,
  QueryOptions, SerializeOptions, StoreReader, OpenStoreOptions,
  DeltaLogHandle, DeltaLogInspection,
} from './index';

export {
  parse,
  query,
  update,
  serialize,
  canonicalize,
  graphs,
  canonicalHash,
  isomorphic,
  fromQuads,
  ready,
  engineTables,
  openDataset,
  closure,
  formats,
  queryRaw,
  queryHdt,
  registerExtensionFunction,
  unregisterExtensionFunction,
  clearExtensionFunctions,
  registerServiceEndpoint,
  clearServiceEndpoints,
  openStore,
  queryStore,
  listStores,
  deltaLogOpen,
  deltaLogAppend,
  deltaLogReadAllHex,
  deltaLogMerge,
  deltaLogInspect,
  deltaLogDestroy,
  _deltaLogCorruptLastForTest,
  shaclValidate,
  shexValidate,
  owlClosure,
  coreRdfsClosure,
  coreRdfsCheck,
  rdfsPlusClosure,
  rhoDfClosure,
  rhoDfFragmentCheck,
  tableauMaterialise,
  tableauDlInconsistent,
  owlIsConsistent,
  owlEntails,
  rifEval,
  rmlMap,
  csvwToRdf,
  jsonldToRdf,
  jsonldFromRdf,
  xmlWellformed,
  xpathEval,
  xsltTransform,
  schematronValidate,
  jsonSchemaValidate,
  mathmlEval,
  xformsRecalc,
  clParse,
  clSerialize,
  clAlphaNorm,
  clNormalize,
  toanSummation,
  toanProduct,
  toanSimplify,
  toanDiff,
  toanSubst,
  vcSha256Hex,
  vcEd25519SecretToPublic,
  vcEd25519Sign,
  vcEd25519Verify,
  vcEddsaCreateFromCanonical,
  vcEddsaVerifyFromCanonical,
  vcCheckCredential,
  vcCheckCredentialSubject,
  vcCheckNoDataLoss,
  vcCheckRelatedResourceDigests,
  didKeyResolve,
  capabilities,
  Dataset,
  DatasetHandle,
  Store,
  FactoidalError,
  dataFactory,
  version,
  engine,
  loadEngine,
} from './index';

/**
 * The directory the engine's three files (l4factoidal.js, l4factoidal.mjs,
 * l4factoidal.wasm) are loaded from. Default: this package's l4-assets/,
 * next to browser.js. Call before the first operation.
 */
export function setAssetsUrl(url: string | URL): void;

/** The directory the engine's files are loaded from. */
export function getAssetsUrl(): string;

export { default } from './index';

// Added in 0.10.0 (lib/pure.mjs).
export function aeadSeal(a: { key: Uint8Array; nonce: Uint8Array; plaintext?: Uint8Array; aad?: Uint8Array }): Promise<Uint8Array>;
export function aeadOpen(a: { key: Uint8Array; nonce: Uint8Array; ciphertext: Uint8Array; aad?: Uint8Array }): Promise<Uint8Array>;
export function hpkeSeal(a: { skE: Uint8Array; pkR: Uint8Array; plaintext?: Uint8Array; info?: Uint8Array; aad?: Uint8Array }): Promise<{ message: Uint8Array; enc: Uint8Array; ciphertext: Uint8Array }>;
export function hpkeOpen(a: { skR: Uint8Array; message: Uint8Array; info?: Uint8Array; aad?: Uint8Array }): Promise<Uint8Array>;
export function proofCheck(bundleJson: string): Promise<Record<string, unknown>>;
export function proofInspect(bundleJson: string): Promise<Record<string, unknown>>;
export function canonicalizeNQuads(nquads: string): Promise<string>;
export function normalizeNQuads(nquads: string): Promise<string>;
