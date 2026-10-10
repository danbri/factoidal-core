// factoidal — Node entry point for the **Lean 4** engine.
//
// The same typed public API shape as index.js / wasm.js (parse /
// query / update / serialize / canonicalize / dataFactory / Dataset /
// the closure and checker family), served by the Lean 4 extraction
// compiled to WebAssembly (L4Factoidal — formal/lean4/) instead of
// the F* extraction. Asset resolution is l4.js's three-step ladder:
// @factoidal/lean, $FACTOIDAL_L4_ASSETS, then the repository checkout.
//
//   const factoidal = require('@factoidal/core/l4-core');
//   const ds = await factoidal.parse('<a> <b> "c" .', { format: 'ntriples' });
//
// Surface: the subset capabilities() reports. Operations the Lean
// engine does not implement yet (SHACL, ShEx, COTTAS, entailment-regime
// query modes) reject with a clear engine-capability error rather than
// silently falling back to the F* engine -- the point of this entry is
// that everything it answers came through the Lean extraction. See
// ./select.js (factoidal/select) for an explicit, observable
// lean/fstar/lean1st/fstar1st/slowcompareboth switch built on top of
// this and ./index.js (issue #618); this module itself never falls
// back. owlIsConsistent / owlEntails ARE served (the three-valued OWL
// DL verdict, formal/lean4 issue 586) when the resolved wasm carries
// the ops -- an older bundle answers "unknown op", which surfaces as
// the entryResult error, so probe the `ops` reflection before relying
// on them.
//
// https://github.com/danbri/factoidal/issues/713 stage 1 added the rest
// of the F* main entry that the Lean library already implements:
// jsonldToRdf, jsonldFromRdf, rmlMap, csvwToRdf, xmlWellformed,
// xpathEval, xsltTransform, schematronValidate, jsonSchemaValidate,
// mathmlEval, xformsRecalc, rifEval, queryHdt, tableauMaterialise,
// tableauDlInconsistent, queryRaw, the extension-function and
// SERVICE-endpoint registries, and the five toan* functions. Their
// signatures and result shapes are index.d.ts's; the Lean dispatch ops
// behind them are formal/lean4/Wasm/Ops/Formats.lean, Reasoning.lean,
// QueryExtras.lean and ServiceReg.lean. Stage 2 added the maths, VC and
// DID functions (STAGE2_OPS below). The export list mirrors wasm.js so
// callers can swap engines by import path alone.

'use strict';

const { buildApi } = require('./lib/api.js');
const rdfjs = require('./rdfjs.js');
const l4 = require('./l4.js');
const pkg = require('./package.json');

const NOT_SUPPORTED =
  'factoidal/l4-core: this operation is not implemented by the Lean 4 ' +
  'engine (see capabilities()); use the F* engine entry points for it. ' +
  'If the Lean assets are missing, npm install @factoidal/lean or set ' +
  'FACTOIDAL_L4_ASSETS.';

// The entry-ABI method names lib/api.js dispatches on, mapped onto the
// Lean wasm module's single dispatch export. Methods absent from this
// list are deliberately absent from the entry object: api.js
// typeof-guards each one and capabilities() reports the truth.
//
// The resolved wasm's full dispatch surface has 23 ops
// (`bin/linux-x86_64/l4factoidal ops`, re-measured 2026-09-16); this
// list wires 21 of them, up from 16 once the 5 dataset-handle ops
// below joined it (issues #344/#680/#681).
// `clParse` reads CLIF text into a CL syntax tree and reports its
// shape (sentence count, CL-vs-IKL dialect, canonical re-serialisation)
// -- it never produces RDF, so it is NOT part of the IKL-to-RDF
// projection family below. `clSerialize`, `clAlphaNorm` and
// `clNormalize` join it as the same kind of entry (CLIF text in, CLIF/
// CL text out, never RDF) -- see lib/api.js's doc comments on each for
// what their answers are worth (clSerialize's `roundTripProved: false`,
// clNormalize's `preserves`/`noIntrusion`). All four are Lean-only
// entries in the typed capability table (formal/fstar has no CL/IKL
// parser at all); see ./select.js, which throws on `backend:'fstar'`
// for each rather than answering from Lean silently.
//
// `clFiniteSat` (the fifth CL/IKL op) is DEFERRED from this typed
// layer, not excluded (owner decision, 2026-08-26): it takes a
// caller-supplied finite-interpretation JSON encoding that has no user
// yet, and a typed wrapper would freeze that shape before we know
// whether it is right. It stays reachable only through the raw
// dispatch ABI (`l4.call('clFiniteSat', [interpJson, clifText])`) --
// see lib/api.js's comment next to the other three clNormalize/
// clAlphaNorm/clSerialize wrappers for the same note.
//
// The IKL-to-RDF projection ("direction B": `clToDataset`,
// `queryWithIklService`) was removed from the engine source on
// 2026-08-26 (https://github.com/danbri/factoidal/issues/626): both
// ops went through the deleted `CL/ToRdf.lean`, whose content-addressed
// proposition graph names were never asked for. They had already been held off this JS surface by owner
// decision (https://github.com/danbri/factoidal/issues/618 — "I don't
// want npm code for direction b at this stage ... Take it out of npm
// for now."), and there is now nothing to wire. The compiled wasm
// artifact still CONTAINS both ops until it is rebuilt
// (https://github.com/danbri/factoidal/issues/627) — it is ahead of
// its source. The same #618 ruling is why an x-ikl-<suffix>
// entailment-regime family is rejected in lib/api.js's query() and
// fn.js's entail().
//
// CORRECTION 2026-08-26: an earlier version of this comment listed
// `clParse` alongside those two and cited #618 as the reason for all
// three. That misattributed a decision the owner did not make --
// `clParse` was unwired only because nobody had decided to wrap it,
// which is why it is wired above instead of here.
//
// A second group WAS withheld for an unrelated, non-owner reason, and
// is now wired (issues #344/#680/#681 landed a typed handle shape in
// lib/api.js -- openDataset()/DatasetHandle):
//
//   - dataset handles (`datasetOpen`/`datasetQuery`/`datasetUpdate`/
//     `datasetSerialize`/`datasetClose`): ordinary RDF dataset
//     handles, not part of the CL/IKL decision above. Since
//     https://github.com/danbri/factoidal/issues/685 (stage 2 of
//     https://github.com/danbri/factoidal/issues/713) the Lean engine's
//     strict-parse error envelope carries line/column/offset/format,
//     `datasetOpen` records `prefixes`, and `datasetSerializeWith` is
//     served (wired in STAGE2_OPS below). `datasetQuery12` stays
//     unserved: the Lean side has no SPARQL 1.2 tokenizer yet.
const OPS = [
  'parseToDatasetJson',
  'queryDataset',
  'updateDataset',
  'serializeNQuads',
  'serializeTurtle',
  'canonicalizeToNQuads',
  'owlClosure',
  'owlIsConsistent',
  'owlEntails',
  'rhoDfClosure',
  'rhoDfFragmentCheck',
  'rdfsPlusClosure',
  'clParse',
  'clSerialize',
  'clAlphaNorm',
  'clNormalize',
  // Dataset handles (issue #680) -- wired now that lib/api.js has a
  // typed wrapper shape (openDataset/DatasetHandle). datasetQuery12 stays
  // unwired (no SPARQL 1.2 tokenizer on this side yet);
  // datasetSerializeWith is in STAGE2_OPS below.
  'datasetOpen',
  'datasetQuery',
  'datasetUpdate',
  'datasetSerialize',
  'datasetClose',
  // Stage 1 of https://github.com/danbri/factoidal/issues/713: the
  // format, transform and reasoning operations (Wasm/Ops/Formats.lean,
  // Wasm/Ops/Reasoning.lean) ...
  'jsonldToRdf',
  'jsonldFromRdf',
  'rmlMap',
  'csvwToRdf',
  'xmlWellformed',
  'xpathEval',
  'xsltTransform',
  'schematronValidate',
  'jsonSchemaValidate',
  'mathmlEval',
  'xformsRecalc',
  'rifEval',
  'tableauMaterialise',
  'tableauDlInconsistent',
  // ... the SPARQL SERVICE endpoint registry (Wasm/Ops/ServiceReg.lean) ...
  'registerServiceEndpoint',
  'clearServiceEndpoints',
  // ... and the "think of a number" algebra (Wasm/Ops/Toan.lean), which
  // the table already served but this list did not wire.
  'toanSummation',
  'toanProduct',
  'toanSimplify',
  'toanDiff',
  'toanSubst',
];

// ---------------------------------------------------------------------
// Stage 2 of https://github.com/danbri/factoidal/issues/713: ops the F* entry
// serves that the Lean dispatch ABI now serves too, under the same names and
// the same envelope shapes. lib/api.js already holds the typed wrappers
// (matrixDeterminant, vcEd25519Verify, didKeyResolve, ...) and calls them as
// `entry[name](...)`, so listing the name here is the whole wiring.
//   maths (Wasm/Ops/Maths.lean): matrix*, sigmoid*
//   VC and DID (Wasm/Ops/Vc.lean): vc*, didKeyResolve
//   envelope parity (Wasm/Ops/Parse.lean, Handles.lean, issue 685):
//     serializeTurtleWith, datasetSerializeWith
// An older wasm answers "unknown op" for a name it lacks, which api.js
// surfaces as the entryResult error; capabilities() probes these names.
const STAGE2_OPS = [
  'matrixDeterminant',
  'matrixScalarProduct',
  'matrixVectorProduct',
  'matrixOuterProduct',
  'sigmoidPoints',
  'sigmoidFormulaMathml',
  'vcSha256Hex',
  'vcEd25519SecretToPublic',
  'vcEd25519Sign',
  'vcEd25519Verify',
  'vcEddsaCreateFromCanonical',
  'vcEddsaVerifyFromCanonical',
  'vcCheckCredential',
  'vcCheckCredentialSubject',
  'vcCheckNoDataLoss',
  'vcCheckRelatedResourceDigests',
  'didKeyResolve',
  'serializeTurtleWith',
  'datasetSerializeWith',
  // parse(text, {lenient:true}): the recovery-mode parse
  // (formal/lean4/Wasm/Ops/Lenient.lean,
  // https://github.com/danbri/factoidal/issues/716). Listing it makes
  // capabilities().parseDiagnostics true.
  'parseDocument',
];
OPS.push(...STAGE2_OPS);

async function loadLeanEntry() {
  const eng = await l4.loadL4();
  if (typeof eng.call !== 'function') {
    throw new Error(
      'factoidal/l4-core: the resolved Lean wasm module predates the ' +
      'dispatch ABI (no call export); update @factoidal/lean or ' +
      'FACTOIDAL_L4_ASSETS to a build with l4_call'
    );
  }
  const entry = { abiVersion: '1' };
  for (const op of OPS) {
    // lib/api.js's entryResult() takes the envelope as a JSON STRING
    // (entry_jsoo.ml's wire shape). The Lean loader's call() parses the
    // envelope and throws on {"ok":false}; re-encode both outcomes so
    // this entry object is wire-compatible with the F* one.
    entry[op] = (...args) => {
      try {
        return JSON.stringify(eng.call(op, args.map(String)));
      } catch (err) {
        // The loader's Error carries the whole envelope (`.envelope`). Keep
        // its other members -- a parse failure's line, column, offset and
        // format -- so api.js's entryResult() can throw a positioned
        // ParseError (https://github.com/danbri/factoidal/issues/685). The
        // message stays the loader's own, "l4factoidal: <error>".
        const env = err && err.envelope;
        if (env && typeof env === 'object' && env.ok === false) {
          return JSON.stringify({ ...env, error: String(err.message) });
        }
        return JSON.stringify({
          ok: false,
          error: String((err && err.message) || err),
        });
      }
    };
  }
  installExtensionBridge(eng, entry);
  installByteOps(eng, entry);
  return entry;
}

// ---------------------------------------------------------------------
// SPARQL 1.1 section 17.6 extension functions.
//
// lib/api.js owns the registry, the memo table and the async
// re-evaluation trampoline (they are engine independent). It hands the
// entry `registerExtensionFunction(iri, bridge)`, where `bridge(iri,
// argsJson)` answers a term object, a JavaScript primitive, null (the
// section 17.6 error) or the pending marker for an unresolved promise.
// The Lean module asks its host through ONE global,
// `globalThis.__factoidalExtCall(iri, argsJson)`, which must answer one
// SPARQL Results JSON binding-value object as a JSON string, or the
// empty string for "no value" (formal/lean4/Wasm/ExtHost.lean).
// `bin/ext.mjs` documents the same contract for the Lean command-line
// host; this adapter turns lib/api.js's bridge answers into that wire
// form. It makes no semantic decision: which IRIs reach the host and
// what an absent answer means are decided in Lean.
// ---------------------------------------------------------------------

const XSD = 'http://www.w3.org/2001/XMLSchema#';
const EXT_PENDING_MARKER = '__FACTOIDAL_EXT_PENDING__';

function encodeExtAnswer(out) {
  if (out === null || out === undefined || out === EXT_PENDING_MARKER) return '';
  if (typeof out === 'boolean') {
    return JSON.stringify({ type: 'literal', value: out ? 'true' : 'false', datatype: XSD + 'boolean' });
  }
  if (typeof out === 'number') {
    if (!Number.isFinite(out)) return '';
    return Number.isInteger(out)
      ? JSON.stringify({ type: 'literal', value: String(out), datatype: XSD + 'integer' })
      : JSON.stringify({ type: 'literal', value: String(out), datatype: XSD + 'double' });
  }
  if (typeof out === 'string') return JSON.stringify({ type: 'literal', value: out });
  if (typeof out === 'object' && typeof out.type === 'string') return JSON.stringify(out);
  return '';
}

function okEnvelope(extra) {
  return JSON.stringify({ ok: true, ...(extra || {}) });
}

function failEnvelope(err) {
  return JSON.stringify({ ok: false, error: String((err && err.message) || err) });
}

function installExtensionBridge(eng, entry) {
  const bridges = new Map(); // iri -> lib/api.js bridge
  const hostCall = (iri, argsJson) => {
    const bridge = bridges.get(String(iri));
    if (!bridge) return '';
    try {
      return encodeExtAnswer(bridge(String(iri), String(argsJson)));
    } catch (_err) {
      return '';
    }
  };
  entry.registerExtensionFunction = (iri, bridge) => {
    try {
      eng.call('extRegister', [String(iri)]);
      bridges.set(String(iri), bridge);
      globalThis.__factoidalExtCall = hostCall;
      return okEnvelope();
    } catch (err) {
      return failEnvelope(err);
    }
  };
  entry.unregisterExtensionFunction = (iri) => {
    try {
      eng.call('extUnregister', [String(iri)]);
      bridges.delete(String(iri));
      return okEnvelope();
    } catch (err) {
      return failEnvelope(err);
    }
  };
  entry.clearExtensionFunctions = () => {
    try {
      eng.call('extClear', []);
      bridges.clear();
      return okEnvelope();
    } catch (err) {
      return failEnvelope(err);
    }
  };
}

// ---------------------------------------------------------------------
// Ops that carry a byte region. queryHdt reads a whole .hdt file; the
// dispatch ABI moves bytes as a blob (l4_call_blob), not as text, so a
// multi-megabyte file is not doubled by an encoding.
// ---------------------------------------------------------------------

function installByteOps(eng, entry) {
  if (typeof eng.callBlob !== 'function') return;
  entry.queryHdt = (bytes, sparql) => {
    try {
      return JSON.stringify(eng.callBlob('queryHdt', [String(sparql)], bytes));
    } catch (err) {
      return failEnvelope(err);
    }
  };
}

// ---------------------------------------------------------------------
// queryRaw: one call, serialised answer. index.js keeps it as a legacy
// export that drives the F* command-line bundle; here it is the
// `queryRaw` dispatch op (Wasm/Ops/QueryExtras.lean). Same validation,
// same result: parsed SPARQL results JSON for output 'json' (the
// default), the raw text for every other output format.
// ---------------------------------------------------------------------

const RAW_OUTPUT_FORMATS = new Set(['json', 'csv', 'tsv', 'xml', 'table', 'ntriples']);
const RAW_ENTAIL_VALUES = new Set(['none', 'RDFS', 'OWL-RL']);
const RAW_DATA_FORMATS = {
  turtle: 'turtle', ttl: 'turtle', ntriples: 'ntriples', nt: 'ntriples',
  nquads: 'nquads', nq: 'nquads', trig: 'trig', rdfxml: 'rdfxml',
  'rdf-xml': 'rdfxml', rdf: 'rdfxml',
};

async function queryRaw(dataString, queryString, options) {
  if (typeof dataString !== 'string') {
    throw new TypeError('queryRaw: dataString must be a string');
  }
  if (typeof queryString !== 'string') {
    throw new TypeError('queryRaw: queryString must be a string');
  }
  const opts = options || {};
  const dataFormat = String(opts.dataFormat || 'turtle').toLowerCase();
  const entail = opts.entail || 'none';
  const output = opts.output || 'json';
  if (!(dataFormat in RAW_DATA_FORMATS)) {
    throw new TypeError(`queryRaw: unknown dataFormat '${opts.dataFormat}'`);
  }
  if (!RAW_ENTAIL_VALUES.has(entail)) {
    throw new TypeError(
      `queryRaw: entail must be one of ${[...RAW_ENTAIL_VALUES].join(', ')}`);
  }
  if (!RAW_OUTPUT_FORMATS.has(output)) {
    throw new TypeError(
      `queryRaw: output must be one of ${[...RAW_OUTPUT_FORMATS].join(', ')}`);
  }
  const eng = await l4.loadL4();
  let r;
  try {
    r = eng.call('queryRaw', [
      dataString, queryString,
      JSON.stringify({ dataFormat: RAW_DATA_FORMATS[dataFormat], entail, output }),
    ]);
  } catch (cause) {
    const msg = String((cause && cause.message) || cause);
    const err = new Error('SPARQL query failed: ' + msg);
    err.exitCode = 1;
    err.stderr = msg;
    err.stdout = '';
    throw err;
  }
  return output === 'json' ? JSON.parse(r.text) : r.text;
}

const api = buildApi({
  engineName: 'l4',
  loadEntry: loadLeanEntry,
  runCli: async () => ({ exitCode: 1, stdout: '', stderr: NOT_SUPPORTED }),
});

module.exports = {
  parse: api.parse,
  query: api.query,
  queryHdt: api.queryHdt,
  queryRaw,
  registerExtensionFunction: api.registerExtensionFunction,
  unregisterExtensionFunction: api.unregisterExtensionFunction,
  clearExtensionFunctions: api.clearExtensionFunctions,
  registerServiceEndpoint: api.registerServiceEndpoint,
  clearServiceEndpoints: api.clearServiceEndpoints,
  update: api.update,
  serialize: api.serialize,
  canonicalize: api.canonicalize,
  graphs: api.graphs,
  canonicalHash: api.canonicalHash,
  owlClosure: api.owlClosure,
  coreRdfsClosure: api.coreRdfsClosure,
  coreRdfsCheck: api.coreRdfsCheck,
  rhoDfClosure: api.rhoDfClosure,
  rhoDfFragmentCheck: api.rhoDfFragmentCheck,
  rdfsPlusClosure: api.rdfsPlusClosure,
  // Lean-only: formal/fstar has no CL/IKL parser, so these are NOT
  // exported from index.js/wasm.js. See the OPS comment above.
  clParse: api.clParse,
  clSerialize: api.clSerialize,
  clAlphaNorm: api.clAlphaNorm,
  clNormalize: api.clNormalize,
  // Served by the Lean engine's dispatch ABI when the resolved wasm
  // carries the ops (see the header note).
  owlIsConsistent: api.owlIsConsistent,
  owlEntails: api.owlEntails,
  // Issue 713 stage 1: the format, transform and reasoning functions.
  tableauMaterialise: api.tableauMaterialise,
  tableauDlInconsistent: api.tableauDlInconsistent,
  rmlMap: api.rmlMap,
  csvwToRdf: api.csvwToRdf,
  jsonldToRdf: api.jsonldToRdf,
  jsonldFromRdf: api.jsonldFromRdf,
  xmlWellformed: api.xmlWellformed,
  xpathEval: api.xpathEval,
  rifEval: api.rifEval,
  xsltTransform: api.xsltTransform,
  mathmlEval: api.mathmlEval,
  xformsRecalc: api.xformsRecalc,
  jsonSchemaValidate: api.jsonSchemaValidate,
  schematronValidate: api.schematronValidate,
  toanSummation: api.toanSummation,
  toanProduct: api.toanProduct,
  toanSimplify: api.toanSimplify,
  toanDiff: api.toanDiff,
  toanSubst: api.toanSubst,
  // Not implemented by this engine — kept on the surface so a caller
  // swapping engines gets the pinned capability error, not
  // `undefined is not a function`.
  shaclValidate: api.shaclValidate,
  shexValidate: api.shexValidate,
  capabilities: api.capabilities,
  openDataset: api.openDataset,
  DatasetHandle: api.DatasetHandle,
  ParseError: api.ParseError,
  Dataset: rdfjs.Dataset,
  dataFactory: rdfjs.dataFactory,
  engine: 'lean4-wasm',
  available: l4.available,
  version: pkg.version,
};

// Stage 2 of https://github.com/danbri/factoidal/issues/713: the typed
// maths and VC/DID functions, served by the Lean dispatch ops listed in
// STAGE2_OPS above, with the signatures and result shapes index.d.ts declares.
Object.assign(module.exports, {
  matrixDeterminant: api.matrixDeterminant,
  matrixScalarProduct: api.matrixScalarProduct,
  matrixVectorProduct: api.matrixVectorProduct,
  matrixOuterProduct: api.matrixOuterProduct,
  sigmoidPoints: api.sigmoidPoints,
  sigmoidFormulaMathml: api.sigmoidFormulaMathml,
  vcSha256Hex: api.vcSha256Hex,
  vcEd25519SecretToPublic: api.vcEd25519SecretToPublic,
  vcEd25519Sign: api.vcEd25519Sign,
  vcEd25519Verify: api.vcEd25519Verify,
  vcEddsaCreateFromCanonical: api.vcEddsaCreateFromCanonical,
  vcEddsaVerifyFromCanonical: api.vcEddsaVerifyFromCanonical,
  vcCheckCredential: api.vcCheckCredential,
  vcCheckCredentialSubject: api.vcCheckCredentialSubject,
  vcCheckNoDataLoss: api.vcCheckNoDataLoss,
  vcCheckRelatedResourceDigests: api.vcCheckRelatedResourceDigests,
  didKeyResolve: api.didKeyResolve,
});
