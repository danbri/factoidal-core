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

const XSD = 'http://www.w3.org/2001/XMLSchema#';

// The two npm entries and the engine each loads (issue 713 stage 4). The
// core engine's `ops` reflection lists what only the full engine serves
// (`fullOnlyOps`, `fullOnlyFormats`); a call to one of those names the
// entry that has it.
export const FULL_ENTRY = '@factoidal/core';
export const CORE_ENTRY = '@factoidal/core/core';

/**
 * The message of a refusal by the core engine of something only the full
 * engine serves.
 * @param {string} what the function, op or format refused
 */
export function fullEngineMessage(what) {
  return `${what} is not in the core engine that '${CORE_ENTRY}' loads ` +
    `(l4factoidal-core.wasm); import '${FULL_ENTRY}', whose full engine ` +
    '(l4factoidal.wasm) serves it';
}

// The ops whose second argument is a format tag of a document they read.
const DOCUMENT_FORMAT_OPS = new Set(['parseToDatasetJson', 'datasetOpen', 'parseDocument']);
const EXT_PENDING_MARKER = '__FACTOIDAL_EXT_PENDING__';

function okEnvelope(extra) {
  return JSON.stringify({ ok: true, ...(extra || {}) });
}

// An engine refusal arrives as an Error whose `.envelope` is the whole
// {"ok":false,...} document (the loader keeps it, so a parse failure's
// line, column, offset and format reach lib/api.mjs's ParseError). The
// message stays the loader's own, "l4factoidal: <error>".
function failEnvelope(err) {
  const env = err && err.envelope;
  if (env && typeof env === 'object' && env.ok === false) {
    return JSON.stringify({ ...env, error: String(err.message) });
  }
  return JSON.stringify({ ok: false, error: String((err && err.message) || err) });
}

// One SPARQL Results JSON term object per answer, the wire form
// Wasm/ExtHost.lean reads; '' means "no value" (the section 17.6 error).
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
          ok: false, servedBy: 'full',
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
  return entry;
}
