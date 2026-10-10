// TypeScript declarations for 'factoidal/l4-core' — the typed core
// API served by the Lean 4 engine (L4Factoidal compiled to
// WebAssembly) instead of the F* extraction. Assets resolve through
// the 'factoidal/l4' ladder: @factoidal/lean, $FACTOIDAL_L4_ASSETS,
// then the repository checkout.

import {
  DataFactory,
  DataInput,
  DataFormat,
  Dataset,
  ParseOptions,
  QueryOptions,
  SerializeOptions,
  Bindings,
  ShaclValidateResult,
  DatasetHandle,
  ParseError,
  QueryInput,
} from './index';

export {
  Dataset,
  DataFactory,
  DataInput,
  DataFormat,
  ParseOptions,
  QueryOptions,
  SerializeOptions,
  Bindings,
  DatasetHandle,
  ParseError,
  QueryInput,
};

export function parse(text: string, options?: ParseOptions): Promise<Dataset>;
export function query(
  data: QueryInput,
  sparql: string,
  options?: QueryOptions
): Promise<Bindings[] | boolean | Dataset>;
/** `data` must NOT be a DatasetHandle -- call `handle.update()` directly instead. */
export function update(data: DataInput, sparql: string): Promise<Dataset>;
/**
 * Open a dataset handle against the Lean engine (issue #680). A Turtle or
 * TriG document's prefixes are recorded on the handle and used by
 * `handle.serialize({format: 'turtle'})`; `handle.serialize()` takes the
 * `prefixes` and `literalShorthand` options; a parse failure rejects with a
 * `ParseError` carrying `line`, `column` and `offset`
 * (https://github.com/danbri/factoidal/issues/685).
 */
export function openDataset(
  data: DataInput,
  options?: { format?: DataFormat; baseIRI?: string }
): Promise<DatasetHandle>;
export function serialize(
  data: QueryInput,
  options?: SerializeOptions
): Promise<string>;
export function canonicalize(data: QueryInput): Promise<string>;
export function graphs(data: DataInput): Promise<string[]>;
export function canonicalHash(data: DataInput): Promise<string>;
export function owlClosure(
  data: DataInput,
  options?: { regime?: 'RDFS' | 'OWL-RL' }
): Promise<Dataset>;
export function coreRdfsClosure(data: DataInput): Promise<Dataset>;
export function coreRdfsCheck(data: DataInput): Promise<boolean>;
export function rhoDfClosure(data: DataInput): Promise<Dataset>;
export function rhoDfFragmentCheck(data: DataInput): Promise<boolean>;
export function rdfsPlusClosure(data: DataInput): Promise<Dataset>;

// Lean-only: formal/fstar has no CL/IKL parser, so `clParse` does not
// exist on index.d.ts/wasm.d.ts. Reads Common Logic Interchange Format
// text (ISO/IEC 24707:2018), with the IKL `that`-operator extension,
// and reports its shape -- it never produces RDF. `pureCL` is a
// DIALECT flag, not a validity or quality signal: true while the text
// stays inside ISO/IEC 24707 Common Logic, false once it uses IKL's
// `that` operator. A CLIF text that fails to parse rejects instead of
// returning either value.
export function clParse(clifText: string): Promise<{
  ok: boolean;
  sentences: number;
  pureCL: boolean;
  normalized: string;
}>;

// Lean-only, same reason as clParse. Reads CLIF text and writes it
// back out in canonical spacing. `roundTripProved` is ALWAYS `false`:
// `clif_roundTrip` (CL/ClifAdequacy.lean) is an OPEN lemma -- the
// fragment boundary `marksLexable` is MEASURED, not proved. The field
// is surfaced, not dropped or defaulted away, so a caller does not
// have to go find that out.
export function clSerialize(clifText: string): Promise<{
  ok: boolean;
  clif: string;
  sentences: number;
  roundTripProved: false;
}>;

// Lean-only, same reason as clParse. Alpha-normalises CLIF text: the
// canonical representative of each sentence's bound-variable-renaming
// equivalence class -- IKL GUIDE Appendix B condition (1), renaming a
// bound variable does not change the proposition expressed. Two
// sentences that differ only in bound-variable names produce
// byte-identical `clif` output.
export function clAlphaNorm(clifText: string): Promise<{
  ok: boolean;
  clif: string;
  sentences: number;
}>;

// Lean-only, same reason as clParse. Hayes's reduction of IKL to
// Common Logic (danbri/factoidal#625), over a whole text.
//
// `preserves: "satisfiability"` -- the reduction preserves
// satisfiability, NOT equivalence. It suits entailment and consistency
// testing; it is not a transformation to apply to data you intend to
// keep.
//
// `noIntrusion` IS the proof hypothesis `CL.noIntrSs [] []` decides,
// not a paraphrase of it. The transformation runs and returns output
// either way; when `noIntrusion` is `false`, `tails_satisfiable` /
// `normalize_preserves` do not cover that output.
export function clNormalize(clifText: string): Promise<{
  ok: boolean;
  head: string[];
  tail: string[];
  clif: string;
  sentences: number;
  thatCount: number;
  noIntrusion: boolean;
  preserves: 'satisfiability';
  provedUnder: string;
}>;

// clFiniteSat is DEFERRED from this typed surface (owner decision,
// 2026-08-26), not excluded: it takes a caller-supplied finite-
// interpretation JSON encoding that has no user yet. Reachable only
// through the raw dispatch ABI (`l4.call('clFiniteSat', [interpJson,
// clifText])`), which needs no typed shape commitment here.

// Present on the surface, NOT implemented by the Lean engine: each
// rejects with an engine-capability error so an engine swap fails
// loudly rather than with `undefined is not a function`.
// capabilities() reports the truth per feature.
export function shaclValidate(
  data: DataInput,
  shapes: DataInput
): Promise<ShaclValidateResult>;
export function shexValidate(
  data: DataInput,
  schema: string,
  shapeMap: string
): Promise<unknown>;
// Served by the Lean engine when the resolved wasm carries the ops
// (dispatch ABI `owlIsConsistent` / `owlEntails`, formal/lean4 issue
// 586); same three-valued envelopes as index.d.ts. An older bundle
// rejects with an "unknown op" error.
export function owlIsConsistent(
  data: DataInput,
  options?: { format?: string; fuel?: number | string }
): Promise<{ consistent: boolean | null; reason?: string }>;
export function owlEntails(
  premise: DataInput,
  conclusion: DataInput,
  options?: { format?: string; fuel?: number | string }
): Promise<{
  entailed: boolean | null;
  via: 'closure' | 'refutation';
  reason?: string;
}>;

// Issue 713 stage 1: the rest of the F* main entry that the Lean
// library implements. Signatures and result shapes are index.d.ts's,
// so a caller can swap engines by import path alone; the typeof form
// keeps the two declarations from drifting. Differences in what the
// Lean engine answers are stated per function below.
export const queryHdt: typeof import('./index').queryHdt;
export const registerExtensionFunction: typeof import('./index').registerExtensionFunction;
export const unregisterExtensionFunction: typeof import('./index').unregisterExtensionFunction;
export const clearExtensionFunctions: typeof import('./index').clearExtensionFunctions;
export const registerServiceEndpoint: typeof import('./index').registerServiceEndpoint;
export const clearServiceEndpoints: typeof import('./index').clearServiceEndpoints;
/** `output: 'table'` and `'ntriples'` are display formats; see Wasm/Ops/QueryExtras.lean. */
export const queryRaw: typeof import('./index').queryRaw;
/** Adds `budgetHit` to the F* result: true when the materialisation work budget ran out. */
export function tableauMaterialise(
  data: DataInput,
  options?: { format?: DataFormat }
): Promise<{ dataset: Dataset; addedCount: number; budgetHit?: boolean }>;
export const tableauDlInconsistent: typeof import('./index').tableauDlInconsistent;
export const rmlMap: typeof import('./index').rmlMap;
export const csvwToRdf: typeof import('./index').csvwToRdf;
export const jsonldToRdf: typeof import('./index').jsonldToRdf;
export const jsonldFromRdf: typeof import('./index').jsonldFromRdf;
export const xmlWellformed: typeof import('./index').xmlWellformed;
export const xpathEval: typeof import('./index').xpathEval;
export const rifEval: typeof import('./index').rifEval;
export const xsltTransform: typeof import('./index').xsltTransform;
/**
 * As index.d.ts, plus two value kinds the F* engine had no value for: the
 * Lean evaluator also evaluates Content MathML `vector` and `matrix`
 * elements. Entries are `[numerator, denominator]` pairs.
 */
export function mathmlEval(
  contentMathmlXml: string,
  bindings?: Record<string, string>
): Promise<
  | { kind: 'rat'; num: number; den: number }
  | { kind: 'bool'; value: boolean }
  | { kind: 'undef'; reason: string }
  | { kind: 'vector'; value: Array<[number, number]> }
  | { kind: 'matrix'; value: Array<Array<[number, number]>> }
>;
export const xformsRecalc: typeof import('./index').xformsRecalc;
export const jsonSchemaValidate: typeof import('./index').jsonSchemaValidate;
export const schematronValidate: typeof import('./index').schematronValidate;
export const toanSummation: typeof import('./index').toanSummation;
export const toanProduct: typeof import('./index').toanProduct;
export const toanSimplify: typeof import('./index').toanSimplify;
export const toanDiff: typeof import('./index').toanDiff;
export const toanSubst: typeof import('./index').toanSubst;

export function capabilities(): Promise<Record<string, boolean | string>>;
export const dataFactory: DataFactory;
export const engine: 'lean4-wasm';
export function available(): boolean;
export const version: string;

// ---------------------------------------------------------------------
// Stage 2 of https://github.com/danbri/factoidal/issues/713: maths, VC and
// DID, served by the Lean dispatch ops (Wasm/Ops/Maths.lean, Wasm/Ops/Vc.lean).
// The signatures and result shapes are the ones index.d.ts declares for the
// F* engine. The VC wrappers need no initialisation call: the Ed25519
// operations go through the HACL* build linked into the wasm module.
// ---------------------------------------------------------------------
import type {
  MatrixCell,
  MatrixResult,
  SigmoidParams,
  ScaledValue,
} from './index';

export function matrixDeterminant(matrix: MatrixCell[][]): Promise<MatrixResult>;
export function matrixScalarProduct(a: MatrixCell[], b: MatrixCell[]): Promise<MatrixResult>;
export function matrixVectorProduct(a: MatrixCell[], b: MatrixCell[]): Promise<MatrixResult>;
export function matrixOuterProduct(a: MatrixCell[], b: MatrixCell[]): Promise<MatrixResult>;
export function sigmoidPoints(
  params: SigmoidParams
): Promise<Array<{ x: ScaledValue; y: ScaledValue }>>;
export function sigmoidFormulaMathml(): Promise<string>;

/** SHA-256 of the UTF-8 bytes of `message`, as lowercase hex. */
export function vcSha256Hex(message: string): Promise<string>;
/** Ed25519 public key (hex) of a 32-byte secret key (hex). */
export function vcEd25519SecretToPublic(secretKeyHex: string): Promise<string>;
/** Ed25519 signature (hex) over a hex-encoded message. */
export function vcEd25519Sign(secretKeyHex: string, messageHex: string): Promise<string>;
/**
 * Ed25519 verification. Wrong key, tampered signature, altered message or a
 * malformed-length input all resolve to false.
 */
export function vcEd25519Verify(
  publicKeyHex: string,
  messageHex: string,
  signatureHex: string
): Promise<boolean>;
export function vcEddsaCreateFromCanonical(
  secretKeyHex: string,
  canonicalDocument: string,
  canonicalConfig: string
): Promise<string>;
export function vcEddsaVerifyFromCanonical(
  publicKeyHex: string,
  canonicalDocument: string,
  canonicalConfig: string,
  proofValue: string
): Promise<boolean>;
export function vcCheckCredential(
  v2ctxJson: string,
  credentialJson: string
): Promise<{ valid: boolean; reason?: string }>;
export function vcCheckCredentialSubject(
  credentialJson: string
): Promise<{ valid: boolean; reason?: string }>;
export function vcCheckNoDataLoss(
  credentialJson: string
): Promise<{ valid: boolean; reason?: string }>;
export function vcCheckRelatedResourceDigests(
  registryJson: string,
  credentialJson: string
): Promise<{ valid: boolean; reason?: string }>;
export function didKeyResolve(didString: string): Promise<Dataset>;
