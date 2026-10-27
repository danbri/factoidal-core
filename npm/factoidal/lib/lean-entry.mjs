// The entry object over a loaded Lean engine handle.
//
// A Lean engine handle is what `loadL4()` of l4-assets/l4factoidal.js
// answers: `call(op, args)`, `callBlob(op, args, bytes)`,
// `callBlobIO(op, args, bytes)` over the dispatch ABI of
// formal/lean4/Wasm/Dispatch.lean. Those methods parse the envelope and
// THROW on {"ok":false,...}. lib/api.mjs wants the other shape: one method
// per op, string arguments, the envelope as a JSON string, errors as
// {"ok":false} envelopes. entryFromEngine() builds that object.
//
// Which ops exist is the engine's own answer: the `ops` reflection op
// lists them, and the entry object has a method for each name in that list
// and for no other. capabilities() in lib/api.mjs probes the methods, so a
// wasm module older than this package reports what it serves.
//
// Four ops need more than strings in and an envelope out, and get their
// own adapters below:
//   - queryHdt and storeOpen read a byte region (the dispatch ABI's blob);
//   - registerExtensionFunction / unregisterExtensionFunction /
//     clearExtensionFunctions install the JavaScript call-out of SPARQL 1.1
//     section 17.6 (the ops extRegister, extUnregister, extClear).
// None of them makes a semantic decision: which IRIs reach the host, what
// an absent answer means, which artifact a query reads, are decided in Lean.


// The two npm entries and the engine each loads (issue 713 stage 4). The
// core engine's `ops` reflection lists what only the full engine serves
// (`fullOnlyOps`, `fullOnlyFormats`); a call to one of those names the
// entry that has it.
import { appTermToJson, termToJson } from '../rdfjs.mjs';
import { errorFromEnvelope } from './errors.mjs';
export const FULL_ENTRY = '@factoidal/core';
// The core profile is built for the hub pages only; the package ships the
// full engine (owner, 2026-10-20).
export const CORE_ENTRY = 'l4factoidal-core.js (the hub build of the core profile)';

/**
 * The message of a refusal by the core engine of something only the full
 * engine serves.
 * @param {string} what the function, op or format refused
 */
export function fullEngineMessage(what) {
  return `${what} is not in the core engine (${CORE_ENTRY}, ` +
    `l4factoidal-core.wasm); import '${FULL_ENTRY}', whose full engine ` +
    '(l4factoidal.wasm) serves it';
}

// The ops whose second argument is a format tag of a document they read.
const DOCUMENT_FORMAT_OPS = new Set(['parseToDatasetJson', 'datasetOpen', 'parseDocument']);
const EXT_PENDING_MARKER = '__FACTOIDAL_EXT_PENDING__';

function okEnvelope(extra) {
  return JSON.stringify({ ok: true, ...(extra || {}) });
}

// An engine refusal arrives as an Error whose `.envelope` is the whole
// {"ok":false,...} document: the engine's message, code, spec section and
// position pass to lib/errors.mjs unchanged. Any other throw (the wasm
// trapped, the loader failed) is code op.failed.
function failEnvelope(err) {
  const env = err && err.envelope;
  if (env && typeof env === 'object' && env.ok === false) return JSON.stringify(env);
  return JSON.stringify({ ok: false, code: 'op.failed', error: String((err && err.message) || err) });
}

/**
 * A JavaScript value tagged with its JavaScript type, {js, v}, for the engine
 * (Wasm/Ops/ExtFns.lean, Wasm/Ops/LiteralValue.lean). This copies the value
 * as text; the engine chooses the datatype and the lexical form
 * (L4Factoidal.XSD.JsValue.jsLiteral, issue 894 item 3, issue 1051 item 1).
 * A number is its Number::toString text ('-0' for negative zero); a Date is
 * the text of getTime() ('NaN' for an invalid Date). Any other value: null.
 * @param {unknown} value
 * @returns {{js: string, v: string|boolean} | null}
 */
export function encodeJsValue(value) {
  switch (typeof value) {
    case 'boolean': return { js: 'boolean', v: value };
    case 'number': return { js: 'number', v: Object.is(value, -0) ? '-0' : String(value) };
    case 'bigint': return { js: 'bigint', v: value.toString() };
    case 'string': return { js: 'string', v: value };
    case 'object':
      if (value instanceof Date) return { js: 'date', v: String(value.getTime()) };
      return null;
    default: return null;
  }
}

// One answer for Wasm/Ops/ExtFns.lean: the JavaScript value tagged with its
// JavaScript type (encodeJsValue), or a term object. '' means "no value" (the
// section 17.6 error).
function encodeExtAnswer(out) {
  if (out === null || out === undefined || out === EXT_PENDING_MARKER) return '';
  const tagged = encodeJsValue(out);
  if (tagged) return JSON.stringify(tagged);
  if (typeof out === 'object') {
    try { return JSON.stringify(appTermToJson(out)); } catch (_error) { return ''; }
  }
  return '';
}

// The Lean module asks its host through ONE global,
// `globalThis.__factoidalExtCall(iri, argsJson)` (Wasm/ExtHost.lean). The
// bridges lib/api.mjs registers are keyed by IRI here.
function installExtensionBridge(eng, entry) {
  const bridges = new Map();
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

/** The byte forms of the manifest ops (Wasm/Ops/StoreHandles.lean). */
const MANIFEST_BYTES_OPS = ['storeManifestInspectBytes', 'storeQueryPlanBytes', 'storeOpenBytes'];

/**
 * Build the entry object lib/api.mjs drives, from a loaded engine handle.
 *
 * @param {{call: Function, callBlob?: Function, callBlobIO?: Function}} eng
 * @returns {Record<string, Function> & {abiVersion: string, engine: object}}
 */
export function entryFromEngine(eng) {
  if (!eng || typeof eng.call !== 'function') {
    throw new TypeError(
      'factoidal: expected a Lean engine handle with a call(op, args) method ' +
      '(the value loadL4() of l4-assets/l4factoidal.js resolves to)');
  }
  const reflection = eng.call('ops', []);
  // `engine` is "core" for l4factoidal-core.wasm and "full" for
  // l4factoidal.wasm; a module older than issue 713 stage 4 has no member and
  // is the full engine.
  const profile = reflection.engine === 'core' ? 'core' : 'full';
  const entry = {
    abiVersion: String(reflection.abiVersion),
    engine: eng,
    profile,
    fullOnlyOps: Array.isArray(reflection.fullOnlyOps) ? reflection.fullOnlyOps.map(String) : [],
    fullOnlyFormats: Array.isArray(reflection.fullOnlyFormats)
      ? reflection.fullOnlyFormats.map((f) => String(f).toLowerCase()) : [],
  };
  const ops = Array.isArray(reflection.ops) ? reflection.ops : [];
  for (const op of ops) {
    if (op === 'ops') continue;
    const formatChecked = DOCUMENT_FORMAT_OPS.has(op) && entry.fullOnlyFormats.length > 0;
    entry[op] = (...args) => {
      if (formatChecked && entry.fullOnlyFormats.includes(String(args[1] ?? '').toLowerCase())) {
        return JSON.stringify({
          ok: false, servedBy: 'full', code: 'op.unknown',
          error: fullEngineMessage(`the format '${args[1]}'`),
        });
      }
      try {
        return JSON.stringify(eng.call(op, args.map(String)));
      } catch (err) {
        return failEnvelope(err);
      }
    };
  }
  if (ops.includes('extRegister')) installExtensionBridge(eng, entry);
  // The byte-region ops. `bytes` is a Uint8Array; it crosses into the wasm
  // heap with no encoding.
  // queryHdt goes through the IO form of the blob entry when the engine has it:
  // that entry reads the system clock once for the query, so NOW() (SPARQL 1.1
  // section 17.4.5.1) is bound. The pure `callBlob` has no clock. An engine
  // without `callBlobIO` serves the op through `callBlob`, as before
  // (https://github.com/danbri/factoidal/issues/743).
  if ((typeof eng.callBlobIO === 'function' || typeof eng.callBlob === 'function') &&
      ops.includes('queryHdt')) {
    entry.queryHdt = (bytes, sparql) => {
      try {
        const args = [String(sparql)];
        return JSON.stringify(typeof eng.callBlobIO === 'function'
          ? eng.callBlobIO('queryHdt', args, bytes).envelope
          : eng.callBlob('queryHdt', args, bytes));
      } catch (err) {
        return failEnvelope(err);
      }
    };
  }
  if (typeof eng.callBlobIO === 'function' && ops.includes('storeOpen')) {
    entry.storeOpen = (manifestHex, artifactsJson, bytes) => {
      try {
        return JSON.stringify(
          eng.callBlobIO('storeOpen', [String(manifestHex), String(artifactsJson)], bytes).envelope);
      } catch (err) {
        return failEnvelope(err);
      }
    };
  }
  const blobIoOps = Array.isArray(reflection.blobIoOps) ? reflection.blobIoOps : [];
  // The byte forms of the manifest ops (https://github.com/danbri/factoidal/issues/1039):
  // the manifest crosses as the byte region, not as hexadecimal inside the
  // JSON arguments, and the engine decodes it once for a plan and the open
  // that follows. An engine without them has only the hexadecimal ops; the
  // methods are then absent and lib/api.mjs uses the hexadecimal ops.
  if (typeof eng.callBlobIO === 'function' &&
      MANIFEST_BYTES_OPS.every((op) => blobIoOps.includes(op))) {
    entry.storeManifestInspectBytes = (manifestBytes) => {
      try {
        return JSON.stringify(eng.callBlobIO('storeManifestInspectBytes', [], manifestBytes).envelope);
      } catch (err) {
        return failEnvelope(err);
      }
    };
    entry.storeQueryPlanBytes = (manifestBytes, sparql) => {
      try {
        return JSON.stringify(
          eng.callBlobIO('storeQueryPlanBytes', [String(sparql)], manifestBytes).envelope);
      } catch (err) {
        return failEnvelope(err);
      }
    };
    entry.storeOpenBytes = (manifestBytes, artifactsJson, bytes) => {
      try {
        const region = new Uint8Array(manifestBytes.length + bytes.length);
        region.set(manifestBytes, 0);
        region.set(bytes, manifestBytes.length);
        return JSON.stringify(eng.callBlobIO('storeOpenBytes',
          [String(manifestBytes.length), String(artifactsJson)], region).envelope);
      } catch (err) {
        return failEnvelope(err);
      }
    };
  } else {
    for (const op of MANIFEST_BYTES_OPS) delete entry[op];
  }
  // datasetQuadsBin answers a byte region (formal/lean4/L4Factoidal/RDF/QuadsBin.lean):
  // this method answers {envelope, bytes} and throws on a refusal.
  if (typeof eng.callBlobIO === 'function' && blobIoOps.includes('datasetQuadsBin')) {
    entry.datasetQuadsBin = (handle, optsJson) => {
      try {
        return eng.callBlobIO('datasetQuadsBin', [String(handle), String(optsJson ?? '')], new Uint8Array(0));
      } catch (err) {
        if (err && err.envelope) throw errorFromEnvelope(err.envelope);
        throw err;
      }
    };
  } else {
    delete entry.datasetQuadsBin;
  }
  return entry;
}
