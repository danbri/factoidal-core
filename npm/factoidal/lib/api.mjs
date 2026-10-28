// factoidal — the typed public API, over the Lean 4 engine's dispatch ABI.
//
// buildApi(driver) wraps an ENTRY OBJECT: one method per dispatch op of
// the Lean wasm module (formal/lean4/Wasm/Dispatch.lean), each taking
// string arguments and answering one JSON envelope string,
// {"ok":true,...} or {"ok":false,"error":...}. lib/lean-entry.mjs builds
// that object from a loaded engine handle; index.mjs (Node), browser.js
// and api.mjs (an engine the caller loaded) all pass it in here, so the
// three entry points share this one file.
//
// All semantic work happens inside the Lean engine. This layer shapes
// arguments (RDF/JS Datasets to N-Quads text, options to JSON) and
// results (envelopes to Datasets, SPARQL results JSON to Bindings). An
// operation whose op the loaded wasm does not have rejects with an
// Error that names the op (missingOpError below).
//
// ES module (0.9.0): no Node built-ins, so the browser loads this file
// as it is.
//
// The op names and envelopes are those of the F* npm entry
// (bin/npm-entry/entry_jsoo.ml) that served this API before 0.9.0; a
// JSDoc note "entry_jsoo.ml's X" below names that lineage. The Lean op of
// the same name serves X now (formal/lean4/Wasm/Dispatch.lean lists them).

import { dataFactory, termFromSrj, termToJson, quadToJson, _setTextEngine } from '../rdfjs.mjs';
import { Dataset, INTERNAL, checkOptions, makeRegistry, WRITER_TAGS } from './dataset.mjs';
import { version as packageVersion } from './version.mjs';
import { openGeneration, readRegion, manifestKeys, hexOfBytes } from './store.mjs';
import { fullEngineMessage, encodeJsValue } from './lean-entry.mjs';
import { memoryDeltaLogStore } from './delta-log-hosts.mjs';
import { FactoidalError, errorFromEnvelope, envelopeResult } from './errors.mjs';
import { buildNodes } from './nodes.mjs';
import { runWithCipher } from './cipher-host.mjs';

// The format names, regimes and query outputs are the engine's tables (op
// engineTables, formal/lean4/Wasm/Ops/Handles.lean), read once per engine:
// no host copy (https://github.com/danbri/factoidal/issues/894 item 5).

// The parse tag a format name selects, from the engine's table.
// A name outside the table is refused by the engine (op apiCheck,
// code format.unknown).
function parseTagOf(e, tables, fmt, who) {
  const key = String(fmt || 'turtle').toLowerCase();
  const tag = tables.parseFormats[key];
  if (tag === undefined) checkOptions(e, who || 'parse', { format: String(fmt) });
  return tag;
}

// Where a function takes an options object, a bare string names the
// format: serialize(ds, 'turtle') is serialize(ds, { format: 'turtle' }).
// Until 0.8.0 the string was read as an empty options object, so
// serialize(ds, 'turtle') produced N-Quads with no error (found by the
// 0.8.0 release probe). Any other non-object value is a caller error and
// is reported as one, naming the function.
function optionsOf(fn, options) {
  if (options == null) return {};
  if (typeof options === 'string') return { format: options };
  if (typeof options === 'object') return options;
  throw new TypeError(
    `${fn}: options must be an object or a format string, got ${typeof options}`);
}

// The loaded wasm has no op for this operation (a build older than this
// package, or a dispatch table that does not serve it). When the entry is
// the core engine and the op is one only the full engine serves, the error
// names the entry that has it (issue 713 stage 4).
// The engine's own answer to the op is the error (code op.unknown); an entry
// with no engine handle to ask gets the same code.
function missingOpError(what, e, op) {
  const eng = e && e.engine;
  if (eng && typeof eng.call === 'function' && op) {
    try {
      eng.call(op, []);
    } catch (err) {
      if (err && err.envelope && err.envelope.code === 'op.unknown') {
        const out = errorFromEnvelope(err.envelope);
        if (e.profile === 'core' && Array.isArray(e.fullOnlyOps) && e.fullOnlyOps.includes(op)) {
          out.message = `${what}: ${fullEngineMessage(`the op '${op}'`)}`;
        }
        return out;
      }
    }
  }
  return new FactoidalError(
    `${what}: the loaded Lean wasm module has no dispatch op for this ` +
    'operation. The module is older than this package; rebuild it with ' +
    'formal/lean4/Wasm/build-wasm.sh, or point FACTOIDAL_L4_ASSETS at a ' +
    'current build.', { code: 'op.unknown' });
}

// The query form, from the engine's SPARQL parser (op queryForm). A query
// the parser rejects answers 'select'; the query op then reports the parse
// error itself.
function queryFormOf(e, sparql) {
  if (typeof e.queryForm !== 'function') return 'select';
  const r = JSON.parse(e.queryForm(String(sparql)));
  return r.ok ? r.kind : 'select';
}

// Bytes for an op that reads the byte region (queryHdt, storeOpen): a
// Uint8Array, an ArrayBuffer, or a string packed one char per byte.
function bytesToUint8Array(bytesLike, who) {
  if (bytesLike instanceof Uint8Array) return bytesLike;
  if (bytesLike instanceof ArrayBuffer) return new Uint8Array(bytesLike);
  if (typeof bytesLike === 'string') return Uint8Array.from(bytesLike, (c) => c.charCodeAt(0) & 0xff);
  throw new TypeError(
    `${who}: expected a Uint8Array, Buffer, ArrayBuffer, or an already-packed string`);
}

// SRJ bindings -> Array<Map<string, Term>>
// The members of a JSON object are unordered (RFC 8259 section 4), so a
// binding object does not give the column order; `head.vars` (SPARQL 1.1
// Query Results JSON Format section 3.1) does. Each Map iterates in
// `head.vars` order, then any variable `head.vars` does not list.
function bindingsFromSrj(srj) {
  const rows = (srj && srj.results && srj.results.bindings) || [];
  const vars = (srj && srj.head && Array.isArray(srj.head.vars)) ? srj.head.vars : [];
  return rows.map((row) => {
    const map = new Map();
    for (const name of vars) {
      if (Object.prototype.hasOwnProperty.call(row, name)) map.set(name, termFromSrj(row[name]));
    }
    for (const [name, term] of Object.entries(row)) {
      if (!map.has(name)) map.set(name, termFromSrj(term));
    }
    return map;
  });
}

// ---------------------------------------------------------------------
// The envelope unwrapper every engine call routes through. A refusal is a
// FactoidalError (lib/errors.mjs) whose code, spec section and position the
// engine decided (formal/lean4/Wasm/Ops/ErrorModel.lean).
// ---------------------------------------------------------------------

function entryResult(jsonText, _what, text) {
  return envelopeResult(jsonText, text);
}

// entryResult() for an op that read `text`: the position's offset becomes a
// UTF-16 index into `text`.
function parseResult(jsonText, what, text) {
  return entryResult(jsonText, what, text);
}

// The lenient parse's diagnostics (https://github.com/danbri/factoidal/issues/716)
// with each `offset` converted to a UTF-16 index as a FactoidalError's, so
// `text.slice(d.offset)` starts at the error. `line` and `column` are kept as
// the engine reports them. One pass over `text` for all diagnostics: the
// offsets are visited in increasing order, whatever order the list has.
function utf16Diagnostics(text, diagnostics) {
  if (!Array.isArray(diagnostics) || diagnostics.length === 0) return [];
  if (typeof text !== 'string') return diagnostics;
  const order = diagnostics
    .map((d, i) => [d && Number.isInteger(d.offset) && d.offset >= 0 ? d.offset : -1, i])
    .filter(([off]) => off >= 0)
    .sort((a, b) => a[0] - b[0]);
  const units = new Map();
  let k = 0;
  let unitsSoFar = 0;
  let scalars = 0;
  for (const ch of text) {
    while (k < order.length && order[k][0] <= scalars) {
      units.set(order[k][1], unitsSoFar);
      k += 1;
    }
    if (k >= order.length) break;
    unitsSoFar += ch.length;
    scalars += 1;
  }
  for (; k < order.length; k += 1) units.set(order[k][1], unitsSoFar);
  return diagnostics.map((d, i) => (units.has(i) ? { ...d, offset: units.get(i) } : d));
}

// ---------------------------------------------------------------------
// The Lean persisted store (Shardborough generations: IBK3, IBK4, IBK5
// blocks with their index sidecars; skills/shardborough-storage). A
// Store is a store HANDLE inside the engine (op storeOpen,
// Wasm/Ops/StoreHandles.lean): every artifact it read was checked against
// the SHA-256 its manifest commits, once, and every query answers from
// the decoded, indexed blocks the handle retains. The engine refuses a
// query whose plan needs a block the handle does not retain, so an answer
// is never one of a partial generation.
// ---------------------------------------------------------------------
class Store {
  constructor(e, env, gen, fromNQuads, withExtensionRounds) {
    this._e = e;
    this._env = env;
    this._gen = gen;
    this._closed = false;
    this._fromNQuads = fromNQuads;
    this._withExtensionRounds = withExtensionRounds;
  }
  /** The engine's handle id. */
  get handle() { return this._env.handle; }
  /** The generation directory name the store was opened from. */
  get generation() { return this._gen.generation; }
  /** True when the generation was opened through CURRENT. */
  get activated() { return this._gen.activated; }
  /** The generation's identity, as the engine reports it. */
  get identity() { return this._env.identity; }
  /** The manifest layout label, e.g. 'predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0'. */
  get layout() { return this._env.layout; }
  /** The manifest wire version. */
  get wireVersion() { return this._env.wireVersion; }
  /** How many artifacts the handle read and verified. */
  get artifacts() { return this._env.artifacts; }
  /** How many artifact bytes the handle read. */
  get bytes() { return this._env.bytes; }
  /** How many rows the handle retains. */
  get rows() { return this._env.rows; }
  /** True once close() has run; every other method rejects after. */
  get closed() { return this._closed; }

  _assertOpen(who) {
    // The engine answers handle.disposed for a closed store handle.
    if (this._closed) entryResult(this._e.storeHandleClose(this.handle), `Store.${who}`);
  }

  /**
   * One SPARQL 1.1 query against the retained blocks.
   * @param {string} sparql
   * @returns {Promise<Array<Map<string, object>>|boolean|Dataset>}
   */
  async query(sparql) {
    this._assertOpen('query');
    if (typeof sparql !== 'string') throw new TypeError('Store.query: sparql must be a string');
    const run = () => entryResult(this._e.storeHandleQuery(this.handle, sparql), 'Store.query', sparql);
    const r = this._withExtensionRounds ? await this._withExtensionRounds(run) : run();
    if (r.kind === 'ask') return r.boolean;
    if (r.kind === 'construct' || r.kind === 'describe') {
      return this._fromNQuads(r.nquads);
    }
    return bindingsFromSrj(r.srj);
  }

  /** The manifest, decoded by the engine (op storeManifestInspect). */
  async inspect() {
    const r = entryResult(typeof this._e.storeManifestInspectBytes === 'function'
      ? this._e.storeManifestInspectBytes(this._gen.manifest)
      : this._e.storeManifestInspect(hexOfBytes(this._gen.manifest)), 'Store.inspect');
    const { ok: _ok, ...rest } = r;
    return rest;
  }

  /** Release the handle and the blocks it retains. Idempotent. */
  async close() {
    if (this._closed) return;
    this._closed = true;
    entryResult(this._e.storeHandleClose(this.handle), 'Store.close');
  }
}

/**
 * Build the public API around a driver.
 *
 * @param {object} driver
 * @param {() => (object|Promise<object>)} driver.loadEntry
 *        Returns the entry object (lib/lean-entry.mjs, entryFromEngine).
 *        A rejection is reported by every operation that needs it.
 * @param {string} driver.engineName  reported as `engine`.
 * @param {(root: string) => ((path: string) => any)} [driver.storeReaderFor]
 *        Turns a collection root path into a store reader (Node: the file
 *        system). Without it, openStore() takes a reader function only.
 * @param {object} [driver.deltaLogStore]
 *        Where the deltaLog* functions keep their records
 *        (lib/delta-log-hosts.mjs): IndexedDB in the browser entries. The
 *        default keeps them in the memory of this process.
 */
function buildApi(driver) {
  let entryPromise; // memoized; a failed load is retried on the next call

  // The entry object. A failure to load the engine (assets missing, a
  // wasm that does not instantiate) rejects every operation with that
  // failure's own message; there is no other engine to fall back to.
  async function entry() {
    if (!entryPromise) {
      entryPromise = Promise.resolve()
        .then(() => driver.loadEntry())
        .then((e) => {
          if (!e) throw new FactoidalError('factoidal: the engine loader returned no entry object', { code: 'host.io' });
          return e;
        })
        .catch((err) => {
          entryPromise = undefined;
          throw err instanceof FactoidalError ? err
            : new FactoidalError(`factoidal: the engine did not load: ${err && err.message}`,
              { code: 'host.io', cause: err });
        });
    }
    return entryPromise;
  }

  // The options object of a public function, checked by the engine (op
  // apiCheck): unknown keys, format names, regimes, outputs and versions.
  async function checkedOptions(who, options) {
    return checkOptions(await entry(), who, options);
  }


  // ---------------------------------------------------------------
  // SPARQL 1.1 §17.6 extension functions — issue #463.
  // https://github.com/danbri/factoidal/issues/463
  //
  // Comunica-style: the caller registers (possibly async) JS functions
  // keyed by absolute IRI; a query using an unregistered IRI gets the
  // spec-required error (in expression position: the row's value
  // errors — unbound in SELECT/BIND, row dropped in FILTER).
  //
  // The engine's evaluator is synchronous, so async functions are
  // bridged with a bounded re-evaluation trampoline: each engine call
  // reaches extBridge synchronously; a cache miss on an async function
  // records the promise, returns a pending marker (an engine-side
  // error in THAT pass), and after the pass every pending promise is
  // awaited into the cache and the query re-runs. The per-(iri, args)
  // memoisation is also what honours the engine's purity assumption on
  // the extension-function call — within one evaluation every call with
  // the same arguments sees one stable answer.
  //
  // The user function receives an array of SRJ-style term objects
  // ({type:'uri'|'literal'|'bnode', value, datatype?, 'xml:lang'?};
  // {type:'error'} for an errored argument) and returns a term object,
  // a JS primitive (boolean / number / string), a Promise of either,
  // or null/undefined (= error). Thrown errors and rejections map to
  // the §17.6 error too.
  // ---------------------------------------------------------------
  const EXT_PENDING_MARKER = '__FACTOIDAL_EXT_PENDING__';
  const EXT_MAX_ROUNDS = 25;
  const extFunctions = new Map();    // iri -> user fn
  const extInstalled = new Set();    // iris registered into the ABI
  let extCache = new Map();          // key -> normalized result (or null)
  let extPending = [];               // [{key, promise}] for this pass

  function extBridge(iriJs, argsJsonJs) {
    // Called SYNCHRONOUSLY from inside the engine.
    const iri = String(iriJs);
    const argsJson = String(argsJsonJs);
    const key = iri + '\u0000' + argsJson;
    if (extCache.has(key)) return extCache.get(key);
    const fn = extFunctions.get(iri);
    if (!fn) return null;
    let out;
    try {
      out = fn(JSON.parse(argsJson));
    } catch (_e) {
      extCache.set(key, null);
      return null;
    }
    if (out && typeof out.then === 'function') {
      extPending.push({ key, promise: out });
      return EXT_PENDING_MARKER;
    }
    out = out === undefined ? null : out;
    extCache.set(key, out);
    return out;
  }

  async function extEnsureInstalled(what) {
    const e = await entry();
    if (typeof e.registerExtensionFunction !== 'function') {
      throw missingOpError(`${what} (extRegister)`);
    }
    for (const iri of extFunctions.keys()) {
      if (!extInstalled.has(iri)) {
        entryResult(e.registerExtensionFunction(iri, extBridge),
          'registerExtensionFunction');
        extInstalled.add(iri);
      }
    }
    return e;
  }

  /**
   * Register a custom SPARQL extension function (SPARQL 1.1 §17.6).
   * @param {string} iri absolute IRI the function is invoked by
   * @param {(args: object[]) => any} fn sync or async; see the block
   *   comment above for the argument/return contract
   */
  async function registerExtensionFunction(iri, fn) {
    if (typeof iri !== 'string' || !/^[A-Za-z][A-Za-z0-9+.-]*:/.test(iri)) {
      throw new TypeError(
        'registerExtensionFunction: iri must be an absolute IRI string');
    }
    if (typeof fn !== 'function') {
      throw new TypeError('registerExtensionFunction: fn must be a function');
    }
    extFunctions.set(iri, fn);
    await extEnsureInstalled('registerExtensionFunction');
  }

  /** Remove one registered extension function. */
  async function unregisterExtensionFunction(iri) {
    extFunctions.delete(iri);
    const e = await entry();
    if (e && typeof e.unregisterExtensionFunction === 'function'
        && extInstalled.has(iri)) {
      entryResult(e.unregisterExtensionFunction(iri),
        'unregisterExtensionFunction');
      extInstalled.delete(iri);
    }
  }

  /** Remove every registered extension function. */
  async function clearExtensionFunctions() {
    extFunctions.clear();
    const e = await entry();
    if (e && typeof e.clearExtensionFunctions === 'function') {
      entryResult(e.clearExtensionFunctions(), 'clearExtensionFunctions');
    }
    extInstalled.clear();
  }

  /**
   * Bind a SPARQL SERVICE endpoint IRI to a local graph snapshot, so
   * SERVICE <iri> { ... } (and LATERAL { SERVICE ... }) queries
   * resolve against it in-process — the same registry the W3C
   * federated-query suite uses (qt:serviceData). `data` is a Dataset,
   * a raw RDF string (options.format, default turtle), or an array of
   * those. The snapshot is the payload's default graph.
   */
  async function registerServiceEndpoint(iri, data, options) {
    if (typeof iri !== 'string' || !/^[A-Za-z][A-Za-z0-9+.-]*:/.test(iri)) {
      throw new TypeError(
        'registerServiceEndpoint: iri must be an absolute IRI string');
    }
    const e = await entry();
    if (typeof e.registerServiceEndpoint !== 'function') {
      throw missingOpError('registerServiceEndpoint');
    }
    const opts = await checkedOptions('registerServiceEndpoint', optionsOf('registerServiceEndpoint', options));
    const nq = await nquadsOf(data, opts, 'registerServiceEndpoint');
    return entryResult(e.registerServiceEndpoint(iri, nq),
      'registerServiceEndpoint');
  }

  /** Remove every registered SERVICE endpoint snapshot. */
  async function clearServiceEndpoints() {
    const e = await entry();
    if (e && typeof e.clearServiceEndpoints === 'function') {
      entryResult(e.clearServiceEndpoints(), 'clearServiceEndpoints');
    }
  }

  // Run one synchronous engine pass, re-running until no NEW async
  // extension results are pending. With no registered functions this
  // is exactly one pass with zero overhead beyond the length check.
  async function withExtensionRounds(runOnce) {
    extCache = new Map(); // per-evaluation memo (purity contract)
    for (let round = 0; ; round++) {
      extPending = [];
      const result = runOnce();
      if (extPending.length === 0) return result;
      if (round >= EXT_MAX_ROUNDS) {
        throw new FactoidalError(
          'extension functions: async resolution did not converge ' +
          `within ${EXT_MAX_ROUNDS} evaluation rounds`, { code: 'capacity.exceeded' });
      }
      const pend = extPending;
      extPending = [];
      await Promise.all(pend.map(async ({ key, promise }) => {
        try {
          const v = await promise;
          extCache.set(key, v === undefined ? null : v);
        } catch (_e) {
          extCache.set(key, null);
        }
      }));
    }
  }

  // The prefixes a result Dataset inherits from its inputs: the union of
  // every Dataset input's `prefixes`, in input order, the first
  // declaration of a label winning. update() and CONSTRUCT answer a
  // FRESH Dataset built from N-Quads, which carry no prefixes; without
  // this the parse -> update -> serialize round trip would lose the
  // source labels (https://github.com/danbri/factoidal/issues/681).
  function prefixesOfData(data) {
    const items = Array.isArray(data) ? data : [data];
    const out = {};
    for (const item of items) {
      if (item instanceof Dataset && item.prefixes) {
        for (const [label, iri] of Object.entries(item.prefixes)) {
          if (!(label in out)) out[label] = iri;
        }
      }
    }
    return out;
  }

  // A ShEx focus/shape-label argument is a string in N-Triples term syntax
  // ("<http://...>" or "_:label"), which the engine reads with its one
  // term-string reader, or an RDF/JS term (NamedNode/BlankNode); accepting
  // both lets a caller pass a term straight out of a query() binding.
  function shexTermToString(t, who) {
    if (typeof t === 'string') return JSON.stringify(termToJson(t));
    if (t && typeof t.termType === 'string') {
      if (t.termType === 'BlankNode' || t.termType === 'NamedNode') {
        return JSON.stringify(termToJson(t)); // the engine writes the node
      }
      throw new TypeError(`${who}: expected an IRI or blank node term`);
    }
    throw new TypeError(`${who}: expected a string or an RDF/JS term`);
  }

  // ---------------------------------------------------------------
  // Datasets (https://github.com/danbri/factoidal/issues/882 item 1).
  // Every producer answers a Dataset (lib/dataset.mjs): a handle into the
  // engine's dataset store. Every consumer takes a Dataset, or text with
  // an explicit {format}; when the format is omitted the engine infers it
  // (op detectFormat) and the result reports it (Dataset.format,
  // Dataset.formatInferred, or the error message).
  // ---------------------------------------------------------------
  let ctxCache = null;
  const registry = makeRegistry();

  async function ctx() {
    const e = await entry();
    if (ctxCache && ctxCache.e === e) return ctxCache;
    let tablesCache = null;
    const c = {
      e,
      registry,
      tables() {
        if (!tablesCache) {
          requireEntryFn(e, 'engineTables', 'format and regime tables');
          const t = entryResult(e.engineTables(), 'engineTables');
          tablesCache = { ...t.tables, errorCodes: t.errorCodes || [],
            errorModelExemptOps: t.errorModelExemptOps || [] };
          for (const k of Object.keys(WRITER_TAGS)) delete WRITER_TAGS[k];
          Object.assign(WRITER_TAGS, tablesCache.writerFormats);
        }
        return tablesCache;
      },
      missing: (what, op) => missingOpError(what, e, op),
      wrap(r, prefixes, extra) {
        // `warnings` (the reader's language-tag warnings) is not an info
        // member: openText() and the lenient parse() pass the warnings of the
        // caller's text in `extra`, with their offsets in UTF-16 units.
        const { ok: _ok, handle, count, prefixes: own, warnings: _w, ...info } = r;
        return new Dataset(INTERNAL, c, handle, count,
          prefixes !== undefined ? prefixes : own, { ...(extra || {}), info });
      },
      fromNQuads(text, prefixes) {
        requireEntryFn(e, 'datasetOpen', 'Dataset');
        const r = entryResult(e.datasetOpen(text, 'nquads', ''), 'Dataset');
        return c.wrap(r, prefixes || {});
      },
      async queryHandle(ds, sparql, opts) { return queryDatasetHandle(c, ds, sparql, opts); },
      async shacl(ds, shapes, opts) { return shaclOnHandle(c, ds, shapes, opts); },
      async shex(ds, schema, opts) {
        if (!opts || opts.focus == null) {
          throw new TypeError('Dataset.validateShex: options.focus is required');
        }
        return shexOnHandle(c, ds, schema, opts.focus, opts.shape);
      },
      async closure(ds, regime) { return closureOnHandle(c, ds, regime); },
    };
    ctxCache = c;
    installTextEngine(e);
    return c;
  }

  // rdfjs.mjs's N-Quads text functions (nquadsToQuads, quadsToNQuads,
  // termToNQuads, DatasetCore.fromNQuads/toNQuads) call these engine ops.
  function installTextEngine(e) {
    if (typeof e.parseQuadsJson !== 'function') return;
    _setTextEngine({
      parseQuads(text) {
        return parseResult(e.parseQuadsJson(text, 'nquads12', ''), 'nquadsToQuads', text).quads;
      },
      writeQuads(quadsJson) {
        return entryResult(e.quadsToNQuads(JSON.stringify(quadsJson)), 'quadsToNQuads').nquads;
      },
      termTokens(termsJson) {
        return entryResult(e.termsToNTriples(JSON.stringify(termsJson)), 'termToNQuads').tokens;
      },
    });
  }

  // The parse tag of `format`, or the engine's inference when it is omitted.
  function formatTagOf(c, text, format, who) {
    if (format === undefined || format === null || format === '') {
      requireEntryFn(c.e, 'detectFormat', `${who} (format inference)`);
      return { tag: entryResult(c.e.detectFormat(text), who).format, inferred: true };
    }
    return { tag: parseTagOf(c.e, c.tables(), format, who), inferred: false };
  }

  // Open `text` as a Dataset. A parse error names the format and says
  // whether it was inferred.
  function openText(c, text, format, baseIRI, who) {
    const { tag, inferred } = formatTagOf(c, text, format, who);
    requireEntryFn(c.e, 'datasetOpen', who);
    let r;
    try {
      r = parseResult(c.e.datasetOpen(text, tag, baseIRI || ''), who, text);
    } catch (err) {
      if (err instanceof FactoidalError) {
        err.formatInferred = inferred;
        err.format = err.format || tag;
      }
      throw err;
    }
    return c.wrap(r, undefined, {
      format: tag, formatInferred: inferred,
      warnings: utf16Diagnostics(text, r.warnings),
    });
  }

  // The Dataset a consumer reads: `data` itself when it is a Dataset, else
  // a temporary one the caller disposes (`temp` true). An array opens as
  // one dataset: its members' N-Quads, each document in its own blank-node
  // scope.
  function datasetOf(c, data, opts, who) {
    if (data instanceof Dataset) {
      if (data.disposed) data.size; // throws the disposed error
      return { ds: data, temp: false };
    }
    if (typeof data === 'string') {
      return { ds: openText(c, data, opts.format, opts.baseIRI, who), temp: true };
    }
    if (data && typeof data.text === 'string' && !Array.isArray(data)) {
      return { ds: openText(c, data.text, data.format || opts.format, data.baseIRI || opts.baseIRI, who), temp: true };
    }
    if (Array.isArray(data)) {
      let nq = '';
      for (const item of data) {
        const { ds, temp } = datasetOf(c, item, opts, who);
        nq += ds.toNQuads();
        if (temp) ds.dispose();
      }
      return { ds: c.fromNQuads(nq, prefixesOfData(data)), temp: true };
    }
    throw new TypeError(`${who}: expected a Dataset, a string, {text, format}, or an array of those`);
  }

  async function withDataset(data, opts, who, f) {
    const c = await ctx();
    const { ds, temp } = datasetOf(c, data, opts, who);
    try {
      return await f(c, ds);
    } finally {
      if (temp) ds.dispose();
    }
  }

  // The N-Quads text of `data`, for the ops that read text only.
  async function nquadsOf(data, opts, who) {
    return withDataset(data, opts, who, (_c, ds) => ds.toNQuads());
  }

  async function queryDatasetHandle(c, ds, sparql, opts) {
    if (typeof sparql !== 'string') throw new TypeError('query: sparql must be a string');
    // The options were checked by the engine (op apiCheck, as 'query' or
    // 'Dataset.query'): regime, version, output and their combination.
    const entail = opts.entail || 'none';
    const sparql12 = opts.sparql12 === true || String(opts.version || '') === '1.2';
    const e = c.e;
    if (sparql12 && entail !== 'none' && opts.output === undefined) {
      // SPARQL 1.2 under an entailment regime: the engine closes the stored
      // dataset and runs the SPARQL 1.2 evaluator (op datasetQuery12Entail,
      // https://github.com/danbri/factoidal/issues/1109).
      requireEntryFn(e, 'datasetQuery12Entail', 'query {sparql12, entail}');
      const r = await withExtensionRounds(() => entryResult(
        e.datasetQuery12Entail(ds.handle, sparql, entail), 'query', sparql));
      if (r.kind === 'ask') return r.boolean;
      if (r.kind === 'construct' || r.kind === 'describe') return c.fromNQuads(r.nquads, ds.prefixes);
      return bindingsFromSrj(r.srj);
    }
    if (entail !== 'none' || opts.output !== undefined) {
      // queryRaw over the stored dataset: an entailment regime, or a
      // results format (SPARQL 1.1 Query Results JSON, XML, CSV, TSV).
      const output = opts.output || 'json';
      const form = queryFormOf(e, sparql);
      const graphForm = form === 'construct' || form === 'describe';
      requireEntryFn(e, 'datasetQueryRaw', `query {entail/output}`);
      if (opts.output === undefined) {
        // An entailment regime with the default answer shape.
        const r = entryResult(e.datasetQueryRaw(ds.handle, sparql, JSON.stringify({
          entail, output: graphForm ? 'ntriples' : 'json' })), 'query', sparql);
        if (graphForm) return c.fromNQuads(r.text, ds.prefixes);
        const srj = JSON.parse(r.text);
        if (typeof srj.boolean === 'boolean') return srj.boolean;
        return bindingsFromSrj(srj);
      }
      const r = entryResult(e.datasetQueryRaw(ds.handle, sparql,
        JSON.stringify({ entail, output })), 'query', sparql);
      return output === 'json' && !graphForm ? JSON.parse(r.text) : r.text;
    }
    const fn = sparql12 ? e.datasetQuery12 : e.datasetQuery;
    if (typeof fn !== 'function') {
      throw missingOpError(`query (datasetQuery${sparql12 ? '12' : ''})`, e,
        sparql12 ? 'datasetQuery12' : 'datasetQuery');
    }
    const r = await withExtensionRounds(() => entryResult(fn(ds.handle, sparql), 'query', sparql));
    if (r.kind === 'ask') return r.boolean;
    if (r.kind === 'construct' || r.kind === 'describe') {
      return c.fromNQuads(r.nquads, ds.prefixes);
    }
    const rows = bindingsFromSrj(r.srj);
    // The engine's warnings (class dataset-iri-not-found for a FROM or FROM
    // NAMED IRI that names no graph, https://github.com/danbri/factoidal/issues/1032),
    // passed through unchanged as a non-enumerable `warnings` property, so
    // the rows themselves are unchanged.
    if (Array.isArray(r.warnings) && r.warnings.length > 0) {
      Object.defineProperty(rows, 'warnings', { value: r.warnings, enumerable: false });
    }
    return rows;
  }

  async function shaclOnHandle(c, ds, shapes, opts) {
    requireEntryFn(c.e, 'datasetShaclValidate', 'SHACL validation');
    const s = datasetOf(c, shapes, opts, 'shaclValidate(shapes)');
    try {
      const r = entryResult(c.e.datasetShaclValidate(ds.handle, s.ds.handle), 'shaclValidate');
      return { conforms: r.conforms, report: c.fromNQuads(r.reportNquads, {}) };
    } finally {
      if (s.temp) s.ds.dispose();
    }
  }

  async function shexOnHandle(c, ds, schema, focus, shape) {
    requireEntryFn(c.e, 'datasetShexValidate', 'ShEx validation');
    if (typeof schema !== 'string') throw new TypeError('shexValidate: schema must be a string');
    const focusStr = shexTermToString(focus, 'shexValidate(focus)');
    const shapeStr = shape == null ? '' : shexTermToString(shape, 'shexValidate(shape)');
    return entryResult(
      c.e.datasetShexValidate(ds.handle, schema, focusStr, shapeStr), 'shexValidate').verdict;
  }

  async function closureOnHandle(c, ds, regime) {
    const r0 = c.tables().closureAliases[String(regime || '').toLowerCase()];
    if (!r0) checkOptions(c.e, 'Dataset.closure', { regime: String(regime == null ? '' : regime) });
    requireEntryFn(c.e, 'datasetClosure', 'closure');
    const r = entryResult(c.e.datasetClosure(ds.handle, r0), 'closure');
    return c.wrap(r, ds.prefixes);
  }

  // Everything below is async: the engine loads asynchronously, and an
  // extension function may answer with a Promise.

  /**
   * Parse one RDF document into a Dataset. Strict by default: a syntax
   * error rejects with a FactoidalError (`code`, `position`, `spec`; for Turtle,
   * TriG, N-Triples and N-Quads). `{lenient:true}` skips each bad statement
   * of Turtle, TriG, N-Triples and N-Quads and lists one diagnostic per
   * skipped statement in `dataset.diagnostics`
   * (https://github.com/danbri/factoidal/issues/716); `maxErrors: n` stops
   * after n diagnostics. With no `format` the engine infers one
   * (`dataset.format`, `dataset.formatInferred`). `{rdfstar:true}` reads
   * JSON-LD as JSON-LD-star (`@triple`, `@reifies`, `@annotation`), as
   * jsonldToRdf() does; it applies to format 'jsonld' only.
   * @param {string} text
   * @param {{format?: string, baseIRI?: string, lenient?: boolean,
   *   maxErrors?: number, rdfstar?: boolean}} [options]
   * @returns {Promise<Dataset>}
   */
  async function parse(text, options) {
    if (typeof text !== 'string') throw new TypeError('parse: text must be a string');
    const opts = await checkedOptions('parse', optionsOf('parse', options));
    const c = await ctx();
    if (opts.rdfstar) {
      const { tag, inferred } = formatTagOf(c, text, opts.format, 'parse');
      if (tag !== 'jsonld') {
        throw new FactoidalError(
          `parse: rdfstar applies to format 'jsonld' only (format '${tag}'${inferred ? ', inferred' : ''})`,
          { code: 'option.conflict' });
      }
      requireEntryFn(c.e, 'datasetFromJsonLd', 'parse {rdfstar:true} (datasetFromJsonLd)');
      const optionsJson = JSON.stringify({
        ...(opts.baseIRI ? { base: opts.baseIRI } : {}),
        rdfstar: true,
      });
      return c.wrap(entryResult(c.e.datasetFromJsonLd(text, optionsJson), 'parse'), {},
        { format: tag, formatInferred: inferred });
    }
    if (opts.lenient) {
      const { tag, inferred } = formatTagOf(c, text, opts.format, 'parse');
      requireEntryFn(c.e, 'parseDocument', 'parse {lenient:true} (parseDocument)');
      const r = parseResult(
        c.e.parseDocument(text, tag, opts.baseIRI || '', JSON.stringify(
          Number.isInteger(opts.maxErrors) && opts.maxErrors >= 0
            ? { lenient: true, maxErrors: opts.maxErrors }
            : { lenient: true })),
        'parse', text);
      const opened = entryResult(c.e.datasetOpen(r.nquads, 'nquads', ''), 'parse');
      return c.wrap(opened, r.prefixes, {
        diagnostics: utf16Diagnostics(text, r.diagnostics),
        warnings: utf16Diagnostics(text, r.warnings),
        format: tag, formatInferred: inferred,
      });
    }
    return openText(c, text, opts.format, opts.baseIRI, 'parse');
  }

  /**
   * Open `data` as a Dataset: the same as parse() for text; for a Dataset,
   * a clone; for an array, one Dataset of all its members.
   * @param {Dataset|string|Array|{text, format}} data
   * @param {{format?: string, baseIRI?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function openDataset(data, options) {
    const opts = await checkedOptions('openDataset', optionsOf('openDataset', options));
    const c = await ctx();
    if (data instanceof Dataset) return data.clone();
    return datasetOf(c, data, opts, 'openDataset').ds;
  }

  /**
   * Run a SPARQL 1.1 (or 1.2) query.
   * @param {Dataset|string|Array} data
   * @param {string} sparql
   * @param {{format?: string, baseIRI?: string,
   *   entail?: 'none'|'RDFS'|'OWL-RL'|'x-rdfscore'|'x-rdfsplus',
   *   sparql12?: boolean, version?: '1.1'|'1.2',
   *   output?: 'json'|'xml'|'csv'|'tsv'|'table'|'ntriples'}} [options]
   * @returns {Promise<Array<Map<string, object>>|boolean|Dataset|string|object>}
   *   SELECT -> Bindings[], ASK -> boolean, CONSTRUCT/DESCRIBE -> Dataset;
   *   with `output`, the results document (text; 'json' parsed).
   */
  async function query(data, sparql, options) {
    if (typeof sparql !== 'string') throw new TypeError('query: sparql must be a string');
    const opts = await checkedOptions('query', optionsOf('query', options));
    return withDataset(data, opts, 'query', (c, ds) => queryDatasetHandle(c, ds, sparql, opts));
  }

  /**
   * Run a SPARQL 1.1 query against a read-only HDT file's raw bytes.
   * SELECT and ASK only; default graph only.
   * @param {Uint8Array|ArrayBuffer|Buffer|string} hdtBytes
   * @param {string} sparql
   * @returns {Promise<Array<Map<string, object>>|boolean>}
   */
  async function queryHdt(hdtBytes, sparql) {
    if (typeof sparql !== 'string') {
      throw new TypeError('queryHdt: sparql must be a string');
    }
    const e = await entry();
    requireEntryFn(e, 'queryHdt', 'queryHdt');
    const r = entryResult(e.queryHdt(bytesToUint8Array(hdtBytes, 'queryHdt'), sparql), 'queryHdt');
    if (r.kind === 'ask') return r.boolean;
    if (r.kind === 'construct' || r.kind === 'describe') return (await ctx()).fromNQuads(r.nquads, {});
    return bindingsFromSrj(r.srj);
  }

  /**
   * Apply a SPARQL 1.1 Update and answer a NEW Dataset; a Dataset argument
   * is not changed (use `dataset.update()` to change one in place).
   * @param {Dataset|string|Array} data
   * @param {string} updateText
   * @param {{format?: string, baseIRI?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function update(data, updateText, options) {
    if (typeof updateText !== 'string') throw new TypeError('update: updateText must be a string');
    const opts = await checkedOptions('update', optionsOf('update', options));
    const c = await ctx();
    const { ds, temp } = datasetOf(c, data, opts, 'update');
    const out = temp ? ds : ds.clone();
    try {
      return await out.update(updateText);
    } catch (err) {
      out.dispose();
      throw err;
    }
  }

  /**
   * Write a dataset in a concrete syntax.
   * @param {Dataset|string|Array} data
   * @param {{format?: string, version?: '1.1'|'1.2', prefixes?: object,
   *   literalShorthand?: boolean, useNativeTypes?: boolean,
   *   useRdfType?: boolean, rdfDirection?: string, rdfstar?: boolean,
   *   inputFormat?: string, baseIRI?: string}} [options]
   *   format: nquads (default), ntriples, turtle, trig, rdfxml, jsonld,
   *   rdfc. inputFormat and baseIRI read text `data`.
   * @returns {Promise<string>}
   */
  async function serialize(data, options) {
    const opts = await checkedOptions('serialize', optionsOf('serialize', options));
    const { inputFormat, baseIRI, ...writeOpts } = opts;
    return withDataset(data, { format: inputFormat, baseIRI }, 'serialize',
      (_c, ds) => ds.serialize(writeOpts));
  }

  /**
   * RDFC-1.0 canonical N-Quads.
   * @param {Dataset|string|Array} data
   * @param {{format?: string, baseIRI?: string}} [options]
   * @returns {Promise<string>}
   */
  async function canonicalize(data, options) {
    const opts = await checkedOptions('canonicalize', optionsOf('canonicalize', options));
    return withDataset(data, opts, 'canonicalize', (_c, ds) => ds.toString('rdfc'));
  }

  /**
   * The named graphs of a Dataset, each as a Dataset (default graph
   * excluded, first-seen order).
   * @param {Dataset} dataset
   * @returns {Array<[name: NamedNode|BlankNode, graph: Dataset]>}
   */
  function graphs(dataset) {
    if (!(dataset instanceof Dataset)) throw new TypeError('graphs: expected a Dataset');
    dataset.size; // throws the disposed error
    const c = dataset._ctx;
    requireEntryFn(c.e, 'datasetGraphNames', 'graphs');
    const names = entryResult(c.e.datasetGraphNames(dataset.handle), 'graphs').graphs;
    return names.map((g) => {
      const term = termFromSrj(g);
      return [term, dataset.match(null, null, null, term)];
    });
  }

  /**
   * The RDFC-1.0 canonical hash of a dataset: the SHA-256, as 64 lowercase
   * hexadecimal digits, of the canonical N-Quads document that canonicalize()
   * answers (RDF Dataset Canonicalization 1.0, section 4.4 note 2), graph
   * names included. Op datasetCanonicalHash computes the canonical form and
   * the digest in Lean. Since 0.20.0; 0.17.0 to 0.19.x dropped every graph
   * name first, so datasets that differ only in their graph names got the
   * same hash. To hash a graph whatever its name, use
   * canonicalHash(asDefaultGraph(g)).
   * @param {Dataset} dataset
   * @returns {Promise<string>}
   */
  async function canonicalHash(dataset) {
    if (!(dataset instanceof Dataset)) {
      throw new TypeError('canonicalHash: expected a Dataset');
    }
    dataset.size; // throws the disposed error
    const c = dataset._ctx;
    requireEntryFn(c.e, 'datasetCanonicalHash', 'canonicalHash');
    return entryResult(c.e.datasetCanonicalHash(dataset.handle), 'canonicalHash').hash;
  }

  /**
   * A new Dataset that holds the triples of every graph of `dataset`, all in
   * the default graph (op datasetGraphAsDefault with the union of the
   * graphs). With one entry of graphs(), it is that graph without its name.
   * @param {Dataset} dataset
   * @returns {Dataset}
   */
  function asDefaultGraph(dataset) {
    if (!(dataset instanceof Dataset)) {
      throw new TypeError('asDefaultGraph: expected a Dataset');
    }
    dataset.size; // throws the disposed error
    const c = dataset._ctx;
    requireEntryFn(c.e, 'datasetGraphAsDefault', 'asDefaultGraph');
    return c.wrap(entryResult(c.e.datasetGraphAsDefault(dataset.handle,
      JSON.stringify({ type: 'union' })), 'asDefaultGraph'), {});
  }

  /**
   * Whether two datasets are isomorphic (RDF 1.1 Concepts 3.6 and 4; blank
   * nodes inside RDF 1.2 triple terms included): the engine's
   * Dataset.isomorphicOutcome (op datasetIsomorphic). Rejects when the
   * blank-node search budget is exceeded.
   * @param {Dataset|string|Array} a
   * @param {Dataset|string|Array} b
   * @param {{format?: string, baseIRI?: string}} [options] read text arguments
   * @returns {Promise<boolean>}
   */
  async function isomorphic(a, b, options) {
    const opts = await checkedOptions('isomorphic', optionsOf('isomorphic', options));
    return withDataset(a, opts, 'isomorphic', (c, da) =>
      withDataset(b, opts, 'isomorphic', (_c, db) => {
        requireEntryFn(c.e, 'datasetIsomorphic', 'isomorphic');
        return entryResult(c.e.datasetIsomorphic(da.handle, db.handle), 'isomorphic').isomorphic;
      }));
  }

  /**
   * The RDF merge of two datasets (RDF 1.1 Semantics section 5.2): a new
   * Dataset that holds the quads of both, with the blank nodes of each input
   * kept apart, so `_:b` in `a` and `_:b` in `b` are two blank nodes. The
   * engine computes it (op datasetMerge, formal/lean4/Wasm/Ops/GraphNodes.lean,
   * theorem mergeDatasets_isMerge); the prefixes are those of `a`, then those
   * of `b` whose label `a` does not declare. A text argument is read as by
   * parse() (`options.format`, `options.baseIRI`), in its own blank-node
   * scope. Since 0.21.0 (https://github.com/danbri/factoidal/issues/1130).
   * @param {Dataset|string|Array} a
   * @param {Dataset|string|Array} b
   * @param {{format?: string, baseIRI?: string}} [options] read text arguments
   * @returns {Promise<Dataset>}
   */
  async function datasetMerge(a, b, options) {
    // An engine built before the op refuses with op.unknown before the
    // options are read (its option table has no row for this function).
    requireEntryFn((await ctx()).e, 'datasetMerge', 'datasetMerge');
    const opts = await checkedOptions('datasetMerge', optionsOf('datasetMerge', options));
    return withDataset(a, opts, 'datasetMerge', (c, da) =>
      withDataset(b, opts, 'datasetMerge', (_c, db) =>
        c.wrap(entryResult(c.e.datasetMerge(da.handle, db.handle), 'datasetMerge'))));
  }

  /**
   * A Dataset holding RDF/JS quads (op datasetFromQuadsJson). Each term is
   * sent as its components; the engine reads no text.
   * @param {Iterable<object>} quads
   * @returns {Promise<Dataset>}
   */
  async function fromQuads(quads) {
    const c = await ctx();
    requireEntryFn(c.e, 'datasetFromQuadsJson', 'fromQuads');
    const arr = [];
    for (const q of quads) arr.push(quadToJson(q));
    return c.wrap(entryResult(c.e.datasetFromQuadsJson(JSON.stringify(arr)), 'fromQuads'), {});
  }

  /** Load the engine; afterwards the N-Quads text functions of `@factoidal/core/rdfjs` work. */
  async function ready() {
    await ctx();
  }

  // The synchronous term functions (sameValue, syntaxFor, splitIri, ...) call
  // the loaded engine: `await ready()`, or any other call, loads it first.
  function loadedCtx(who, op = who) {
    if (!ctxCache) {
      throw new FactoidalError(
        `${who}: the engine is not loaded yet. Await any @factoidal/core call first ` +
        '(for example `await ready()`).', { code: 'op.unknown' });
    }
    requireEntryFn(ctxCache.e, op, who);
    return ctxCache;
  }

  /**
   * SPARQL 1.1 `=` on two RDF terms (sections 17.3 and 17.4.1.7), decided by
   * the engine (L4Factoidal.SPARQL.sameValue;
   * https://github.com/danbri/factoidal/issues/1052).
   * @param {object|string} a an RDF/JS term or an N-Triples term string
   * @param {object|string} b
   * @returns {boolean|null} true: the same value; false: different values;
   *   null: incomparable (the operator's type error)
   */
  function sameValue(a, b) {
    const c = loadedCtx('sameValue');
    const r = entryResult(c.e.sameValue(JSON.stringify(termToJson(a)),
      JSON.stringify(termToJson(b))), 'sameValue');
    return r.sameValue === 'true' ? true : (r.sameValue === 'false' ? false : null);
  }

  const iriText = (iri) => (typeof iri === 'string' ? iri : (iri && iri.value) || '');

  /**
   * The syntax of a document by its file name (or IRI path) and its media
   * type, from the engine's table of W3C registrations
   * (L4Factoidal.RDF.syntaxOfNames; https://github.com/danbri/factoidal/issues/1053).
   * The media type wins when it is given; an unknown media type does not fall
   * back to the name.
   * @param {string|{fileName?: string, mediaType?: string}} what a file name or IRI,
   *   or both names
   * @returns {string|null} a syntax name of formats(), or null
   */
  function syntaxFor(what) {
    const c = loadedCtx('syntaxFor');
    const o = (typeof what === 'string') ? { fileName: what } : (what || {});
    const r = entryResult(c.e.syntaxFor(String(o.fileName ?? ''), String(o.mediaType ?? '')), 'syntaxFor');
    return r.syntax ?? null;
  }

  /**
   * An IRI as a namespace and a local name: the local name is the longest
   * suffix that is an XML NCName, '' when there is none
   * (L4Factoidal.RDF.splitIriXml; https://github.com/danbri/factoidal/issues/1051 item 4).
   * @param {string|{value: string}} iri
   * @returns {{namespace: string, localName: string}}
   */
  function splitIri(iri) {
    const c = loadedCtx('splitIri');
    const r = entryResult(c.e.splitIri(iriText(iri)), 'splitIri');
    return { namespace: r.namespace, localName: r.localName };
  }

  /** Is the text an XML NCName (Namespaces in XML 1.0, production [4])? */
  function isNCName(text) {
    const c = loadedCtx('isNCName');
    return entryResult(c.e.isNCName(String(text)), 'isNCName').ncName === true;
  }

  /**
   * The engine's vocabulary table: prefix, namespace and term local names of
   * rdf, rdfs, xsd and owl, and the namespaces of foaf, dcterms, dc and schema
   * (L4Factoidal.RDF.vocabularyTable; https://github.com/danbri/factoidal/issues/1051 item 5).
   * @returns {Array<{prefix: string, namespace: string, terms: string[]}>}
   */
  function vocabularies() {
    const c = loadedCtx('vocabularies');
    return entryResult(c.e.vocabularies(), 'vocabularies').vocabularies;
  }

  /** The container membership property rdf:_n, n >= 1, as a NamedNode. */
  function memberIri(n) {
    const c = loadedCtx('memberIri');
    return dataFactory.namedNode(entryResult(c.e.memberIri(String(n)), 'memberIri').iri);
  }

  /** The n of rdf:_n, or null for any other IRI. */
  function memberOrdinal(iri) {
    const c = loadedCtx('memberOrdinal');
    return entryResult(c.e.memberOrdinal(iriText(iri)), 'memberOrdinal').ordinal ?? null;
  }

  /** The engine's name tables (formats, regimes, query outputs, pack syntaxes). */
  async function engineTables() {
    return (await ctx()).tables();
  }

  // A wasm module older than this package can lack an op: `e[fnName]` is
  // then undefined. Fail with missingOpError(), which names the op.
  function requireEntryFn(e, fnName, what) {
    if (typeof e[fnName] !== 'function') throw missingOpError(what, e, fnName);
  }

  /**
   * SHACL validation over the default graph of each argument.
   * @param {Dataset|string|Array} data
   * @param {Dataset|string|Array} shapes
   * @param {{format?: string, baseIRI?: string}} [options] read text arguments
   * @returns {Promise<{conforms: boolean, report: Dataset}>}
   */
  async function shaclValidate(data, shapes, options) {
    const opts = await checkedOptions('shaclValidate', optionsOf('shaclValidate', options));
    return withDataset(data, opts, 'shaclValidate(data)', (c, ds) => shaclOnHandle(c, ds, shapes, opts));
  }

  /**
   * ShEx validation of one focus node against one shape (or the schema's
   * start), over the default graph of `data`. The schema text is ShExJ when
   * its first non-blank character is '{', ShExC otherwise.
   * @param {Dataset|string|Array} data
   * @param {string} schema
   * @param {string|{termType,value}} focus
   * @param {string|{termType,value}|null} [shape]
   * @param {{format?: string, baseIRI?: string}} [options]
   * @returns {Promise<boolean>}
   */
  async function shexValidate(data, schema, focus, shape, options) {
    const opts = await checkedOptions('shexValidate', optionsOf('shexValidate', options));
    if (typeof schema !== 'string') throw new TypeError('shexValidate: schema must be a string');
    return withDataset(data, opts, 'shexValidate(data)', (c, ds) => shexOnHandle(c, ds, schema, focus, shape));
  }

  /**
   * Closure of the default graph, as a new Dataset.
   * @param {Dataset|string|Array} data
   * @param {'rdfs'|'owl-rl'|'rho-df'|'rdfs-plus'} regime
   * @param {{format?: string, baseIRI?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function closure(data, regime, options) {
    const opts = await checkedOptions('closure', optionsOf('closure', options));
    return withDataset(data, opts, 'closure', (c, ds) => closureOnHandle(c, ds, regime));
  }

  /**
   * SPARQL 1.2 RL (SPARQL-RL) infer: apply a rule set to the default graph
   * of `data` and answer the inference graph (the triples the rules derive,
   * the rule set's DATA blocks included, that are not in `data`) as a new
   * Dataset. The rule set is SPARQL-RL text (https://w3c.github.io/data-shapes/sparql12-rl/).
   * A rule set that is not well-formed, not stratifiable, or has IMPORTS is
   * refused. Engine op: datasetSparqlRlInfer.
   * @param {Dataset|string|Array} data
   * @param {string} rules
   * @param {{format?: string, baseIRI?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function sparqlRlInfer(data, rules, options) {
    const opts = await checkedOptions('sparqlRlInfer', optionsOf('sparqlRlInfer', options));
    if (typeof rules !== 'string') throw new TypeError('sparqlRlInfer: rules must be a string');
    return withDataset(data, opts, 'sparqlRlInfer(data)', (c, ds) => {
      requireEntryFn(c.e, 'datasetSparqlRlInfer', 'sparqlRlInfer');
      const r = entryResult(c.e.datasetSparqlRlInfer(ds.handle, rules), 'sparqlRlInfer');
      return c.wrap(r, ds.prefixes);
    });
  }

  /**
   * RDFS or OWL 2 RL closure of the default graph, as a new Dataset.
   * @param {Dataset|string|Array} data
   * @param {'RDFS'|'OWL-RL'} mode
   * @param {{format?: string, baseIRI?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function owlClosure(data, mode, options) {
    const m = String(mode || '').toLowerCase();
    // The engine checks the mode against its regime table (op apiCheck).
    await checkedOptions('owlClosure', { mode: String(mode == null ? '' : mode) });
    return closure(data, m, options);
  }

  /**
   * The core-RDFS (rho-df: subPropertyOf, subClassOf, type, domain, range;
   * Munoz, Perez and Gutierrez 2009) closure, as a new Dataset.
   * @param {Dataset|string|Array} data
   * @param {{format?: string, baseIRI?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function coreRdfsClosure(data, options) {
    return closure(data, 'rho-df', options);
  }
  /** Literature-name alias for coreRdfsClosure. */
  const rhoDfClosure = coreRdfsClosure;

  /**
   * Is `data` in the core-RDFS fragment the certified closure covers?
   * @param {Dataset|string|Array} data
   * @param {{format?: string, baseIRI?: string}} [options]
   * @returns {Promise<{ok: boolean, fragment: boolean}>}
   */
  async function coreRdfsCheck(data, options) {
    const opts = await checkedOptions('coreRdfsCheck', optionsOf('coreRdfsCheck', options));
    const nq = await nquadsOf(data, opts, 'coreRdfsCheck(data)');
    const e = await entry();
    requireEntryFn(e, 'rhoDfFragmentCheck', 'core-RDFS fragment check');
    return entryResult(e.rhoDfFragmentCheck(nq), 'coreRdfsCheck');
  }
  /** Literature-name alias for coreRdfsCheck. */
  const rhoDfFragmentCheck = coreRdfsCheck;

  /**
   * Is `description` (a graph whose blank nodes are shared variables)
   * RDFS-entailed by `sources`? Returns the evidence bundle when it is
   * (https://github.com/danbri/factoidal/issues/1002). Op explainGraph, full
   * engine only. `entailed: false` also relies on the named assumption in
   * `assumptions`. Text inputs are Turtle unless `format` says otherwise.
   * @param {Dataset|string|Array} sources
   * @param {Dataset|string|Array} description default graph only
   * @param {{profile?: 'rdfs', format?: string, baseIRI?: string,
   *   sourcesFormat?: string, descriptionFormat?: string}} [options]
   * @returns {Promise<{profile: string, entailed: boolean, bundle: object|null,
   *   assumptions: string[], rejection: object|null, entailedMeans: string}>}
   */
  async function explain(sources, description, options) {
    const o = optionsOf('explain', options);
    if (o.profile !== undefined && o.profile !== 'rdfs') {
      throw new TypeError(`explain: unsupported profile '${o.profile}' (only 'rdfs')`);
    }
    const { profile: _profile, sourcesFormat, descriptionFormat, ...rest } = o;
    // The engine's option table has no entry for explain; the options here are read-only hints.
    const opts = rest;
    const fmt = opts.format || 'turtle';
    const srcNq = await nquadsOf(sources, { ...opts, format: sourcesFormat || fmt }, 'explain(sources)');
    const descNq = await nquadsOf(description, { ...opts, format: descriptionFormat || fmt }, 'explain(description)');
    const e = await entry();
    requireEntryFn(e, 'explainGraph', 'explain');
    const { ok: _ok, ...out } = entryResult(e.explainGraph(srcNq, descNq), 'explain');
    return out;
  }

  /**
   * RDFS-Plus closure (RDFS with owl:sameAs, inverseOf, Symmetric,
   * Transitive, Functional and InverseFunctional properties,
   * equivalentClass and equivalentProperty), as a new Dataset.
   * @param {Dataset|string|Array} data
   * @param {{format?: string, baseIRI?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function rdfsPlusClosure(data, options) {
    return closure(data, 'rdfs-plus', options);
  }

  /**
   * OWL tableau materialisation over the default graph.
   * @param {Dataset|string|Array} data
   * @param {{format?: string, baseIRI?: string}} [options]
   * @returns {Promise<{dataset: Dataset, addedCount: number, budgetHit?: boolean}>}
   */
  async function tableauMaterialise(data, options) {
    const opts = await checkedOptions('tableauMaterialise', optionsOf('tableauMaterialise', options));
    const nq = await nquadsOf(data, opts, 'tableauMaterialise(data)');
    const c = await ctx();
    requireEntryFn(c.e, 'tableauMaterialise', 'OWL tableau materialisation');
    const r = entryResult(c.e.tableauMaterialise(nq), 'tableauMaterialise');
    return {
      dataset: c.fromNQuads(r.nquads, {}),
      addedCount: r.addedCount,
      ...(r.budgetHit !== undefined ? { budgetHit: r.budgetHit } : {}),
    };
  }

  /**
   * OWL DL inconsistency verdict (RL closure, one class-expression pass,
   * RL closure, clash decision); `rlAlone` is the plain OWL-RL verdict.
   * @param {Dataset|string|Array} data
   * @param {{format?: string, baseIRI?: string}} [options]
   * @returns {Promise<{inconsistent: boolean, rlAlone: boolean}>}
   */
  async function tableauDlInconsistent(data, options) {
    const opts = await checkedOptions('tableauDlInconsistent', optionsOf('tableauDlInconsistent', options));
    const nq = await nquadsOf(data, opts, 'tableauDlInconsistent(data)');
    const e = await entry();
    requireEntryFn(e, 'tableauDlInconsistent', 'OWL tableau DL inconsistency check');
    const r = entryResult(e.tableauDlInconsistent(nq), 'tableauDlInconsistent');
    return { inconsistent: r.inconsistent, rlAlone: r.rlAlone };
  }

  /**
   * Checked atomic OWL consistency of the default graph: false is a checked
   * contradiction; null means unsupported syntax or no accepted refutation.
   * No model producer exists. fuel does not change the fixed checker bound.
   * @param {Dataset|string|Array} data
   * @param {{format?: string, baseIRI?: string, fuel?: number|string}} [options]
   * @returns {Promise<{consistent: boolean|null, reason?: string}>}
   */
  async function owlIsConsistent(data, options) {
    const opts = await checkedOptions('owlIsConsistent', optionsOf('owlIsConsistent', options));
    const nq = await nquadsOf(data, opts, 'owlIsConsistent(data)');
    const e = await entry();
    requireEntryFn(e, 'owlIsConsistent', 'OWL DL consistency check');
    const optsJson = JSON.stringify(opts.fuel != null ? { fuel: String(opts.fuel) } : {});
    const r = entryResult(e.owlIsConsistent(nq, optsJson), 'owlIsConsistent');
    return r.reason === undefined
      ? { consistent: r.consistent }
      : { consistent: r.consistent, reason: r.reason };
  }

  /**
   * Does `premise` entail `conclusion`? `entailed` is true, false, or null
   * (a refutation goal ran out of budget; `reason` names the cap).
   * @param {Dataset|string|Array} premise
   * @param {Dataset|string|Array} conclusion
   * @param {{format?: string, baseIRI?: string, fuel?: number|string}} [options]
   * @returns {Promise<{entailed: boolean|null, via: 'closure'|'refutation', reason?: string}>}
   */
  async function owlEntails(premise, conclusion, options) {
    const opts = await checkedOptions('owlEntails', optionsOf('owlEntails', options));
    const premiseNq = await nquadsOf(premise, opts, 'owlEntails(premise)');
    const conclusionNq = await nquadsOf(conclusion, opts, 'owlEntails(conclusion)');
    const e = await entry();
    requireEntryFn(e, 'owlEntails', 'OWL entailment check');
    const optsJson = JSON.stringify(opts.fuel != null ? { fuel: String(opts.fuel) } : {});
    const r = entryResult(e.owlEntails(premiseNq, conclusionNq, optsJson), 'owlEntails');
    return r.reason === undefined
      ? { entailed: r.entailed, via: r.via }
      : { entailed: r.entailed, via: r.via, reason: r.reason };
  }

  /**
   * Evaluate an RML mapping graph over one logical source's raw text.
   * Every triples map reads the same `sourceData`.
   * @param {Dataset|string|Array} mapping the mapping graph
   * @param {string} sourceData raw JSON or CSV text
   * @param {'json'|'csv'} sourceKind
   * @param {{format?: string, baseIRI?: string}} [options] read `mapping` text
   * @returns {Promise<Dataset>}
   */
  async function rmlMap(mapping, sourceData, sourceKind, options) {
    if (typeof sourceData !== 'string') throw new TypeError('rmlMap: sourceData must be a string');
    const kind = String(sourceKind || '').toLowerCase();
    await checkedOptions('rmlMap', { sourceKind: kind });
    const opts = await checkedOptions('rmlMap', optionsOf('rmlMap', options));
    return withDataset(mapping, opts, 'rmlMap(mapping)', (c, ds) => {
      requireEntryFn(c.e, 'datasetFromRml', 'RML mapping evaluation');
      return c.wrap(entryResult(c.e.datasetFromRml(ds.handle, sourceData, kind), 'rmlMap'), {});
    });
  }

  /**
   * CSVW csv2rdf (https://www.w3.org/TR/csv2rdf/): tabular data plus an
   * optional metadata document to a Dataset. Every table of a group reads
   * the same `csvText`; a `tableSchema` URL is not fetched.
   * @param {string} csvText
   * @param {string} [metadataJson] '' or omitted: the header row describes the table
   * @param {{mode?: 'standard'|'minimal', base?: string, url?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function csvwToRdf(csvText, metadataJson, options) {
    if (typeof csvText !== 'string') throw new TypeError('csvwToRdf: csvText must be a string');
    const meta = metadataJson == null ? '' : metadataJson;
    if (typeof meta !== 'string') throw new TypeError('csvwToRdf: metadataJson must be a string');
    const opts = await checkedOptions('csvwToRdf', options);
    const c = await ctx();
    requireEntryFn(c.e, 'datasetFromCsvw', 'CSVW csv2rdf conversion');
    const optionsJson = JSON.stringify({
      ...(opts.mode ? { mode: String(opts.mode).toLowerCase() } : {}),
      ...(opts.base ? { base: opts.base } : {}),
      ...(opts.url ? { url: opts.url } : {}),
    });
    return c.wrap(entryResult(c.e.datasetFromCsvw(csvText, meta, optionsJson), 'csvwToRdf'), {});
  }

  /**
   * JSON-LD 1.1 to RDF with the JSON-LD options parse() has no room for.
   * A remote `@context` is not fetched.
   * @param {string} jsonldText
   * @param {{base?: string, rdfDirection?: string, expandContext?: string,
   *   processingMode?: string, rdfstar?: boolean}} [options]
   *   rdfstar: JSON-LD-star (`@triple`, `@reifies`, `@annotation` as RDF 1.2
   *   triple terms and reifiers).
   * @returns {Promise<Dataset>}
   */
  async function jsonldToRdf(jsonldText, options) {
    if (typeof jsonldText !== 'string') throw new TypeError('jsonldToRdf: jsonldText must be a string');
    const opts = await checkedOptions('jsonldToRdf', options);
    const c = await ctx();
    requireEntryFn(c.e, 'datasetFromJsonLd', 'jsonldToRdf');
    const optionsJson = JSON.stringify({
      ...(opts.base ? { base: opts.base } : {}),
      ...(opts.rdfDirection ? { rdfDirection: opts.rdfDirection } : {}),
      ...(opts.expandContext ? { expandContext: opts.expandContext } : {}),
      ...(opts.processingMode ? { processingMode: opts.processingMode } : {}),
      ...(opts.rdfstar ? { rdfstar: true } : {}),
    });
    return c.wrap(entryResult(c.e.datasetFromJsonLd(jsonldText, optionsJson), 'jsonldToRdf'), {},
      { format: 'jsonld', formatInferred: false });
  }

  /**
   * RIF Core forward-chaining saturation of the default graph, as a new
   * Dataset (input and derived triples).
   * @param {Dataset|string|Array} data
   * @param {string} rifRulesXml
   * @param {{format?: string, baseIRI?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function rifEval(data, rifRulesXml, options) {
    if (typeof rifRulesXml !== 'string') throw new TypeError('rifEval: rifRulesXml must be a string');
    const opts = await checkedOptions('rifEval', optionsOf('rifEval', options));
    return withDataset(data, opts, 'rifEval(data)', (c, ds) => {
      requireEntryFn(c.e, 'datasetRifEval', 'RIF Core evaluation');
      return c.wrap(entryResult(c.e.datasetRifEval(rifRulesXml, ds.handle), 'rifEval'), ds.prefixes);
    });
  }

  /**
   * Expanded JSON-LD of a dataset (JSON-LD 1.1 API section 8), parsed.
   * The text form is `serialize(data, {format: 'jsonld'})`.
   * @param {Dataset|string|Array} data
   * @param {{useNativeTypes?: boolean, useRdfType?: boolean,
   *   rdfDirection?: string, rdfstar?: boolean, format?: string,
   *   baseIRI?: string}} [options]
   * @returns {Promise<any>}
   */
  async function jsonldFromRdf(data, options) {
    const opts = await checkedOptions('jsonldFromRdf', optionsOf('jsonldFromRdf', options));
    const { format, baseIRI, ...w } = opts;
    return withDataset(data, { format, baseIRI }, 'jsonldFromRdf(data)',
      (_c, ds) => JSON.parse(ds.toString({ format: 'jsonld', ...w })));
  }

  /**
   * The syntaxes the engine reads and writes (op datasetFormats).
   * @returns {Promise<Array<{name: string, read11: boolean, read12: boolean,
   *   write11: boolean, write12: boolean, engine: 'core'|'full'}>>}
   */
  async function formats() {
    const e = await entry();
    requireEntryFn(e, 'datasetFormats', 'formats');
    return entryResult(e.datasetFormats(), 'formats').formats;
  }

  /**
   * did:key resolution (entry_jsoo.ml's didKeyResolve export -> the
   * verified DID_Key.did_key_document). Resolves a did:key:z6Mk...
   * (Ed25519) to its DID Document, returned as a Dataset.
   * @param {string} didString a did:key URI
   * @returns {Promise<Dataset>} the DID Document as RDF
   */
  async function didKeyResolve(didString) {
    if (typeof didString !== 'string') {
      throw new TypeError('didKeyResolve: didString must be a string');
    }
    const e = await entry();
    requireEntryFn(e, 'didKeyResolve', 'did:key resolution');
    const r = entryResult(e.didKeyResolve(didString), 'didKeyResolve');
    return (await ctx()).fromNQuads(r.nquads, {});
  }

  /**
   * Test whether an XML document is well-formed (entry_jsoo.ml's
   * xmlWellformed export -> Parser_XML.parse_xml_document, the
   * accept/reject signal bin/xml-runner drives against W3C xmlconf).
   * A DOCTYPE with an internal subset is read (XML 1.0 section 2.8);
   * an external DTD is not fetched.
   * @param {string} xmlText
   * @returns {Promise<boolean>}
   */
  async function xmlWellformed(xmlText) {
    if (typeof xmlText !== 'string') {
      throw new TypeError('xmlWellformed: xmlText must be a string');
    }
    const e = await entry();
    requireEntryFn(e, 'xmlWellformed', 'XML well-formedness');
    const r = entryResult(e.xmlWellformed(xmlText), 'xmlWellformed');
    return !!r.wellformed;
  }

  /**
   * Evaluate an XPath 1.0 expression over an XML document (entry_jsoo.ml's
   * xpathEval export -> XPath_Eval.eval_xpath_from_root). Returns the
   * result envelope: `resultType` ('nodeset'|'string'|'number'|'boolean')
   * plus, for a node-set, `count`/`stringValue`/`nodes`, else a scalar
   * `value`.
   * @param {string} xmlText
   * @param {string} xpathExpr
   * @returns {Promise<object>}
   */
  async function xpathEval(xmlText, xpathExpr) {
    if (typeof xmlText !== 'string' || typeof xpathExpr !== 'string') {
      throw new TypeError('xpathEval: xmlText and xpathExpr must be strings');
    }
    const e = await entry();
    requireEntryFn(e, 'xpathEval', 'XPath evaluation');
    return entryResult(e.xpathEval(xmlText, xpathExpr), 'xpathEval');
  }

  /**
   * Parse Common Logic Interchange Format text (ISO/IEC 24707:2018),
   * with the IKL `that`-operator extension (entry_jsoo.ml's clParse
   * export -> L4Factoidal's CL/Clif.lean reader). Reads CLIF into a CL
   * syntax tree and reports its shape; it never produces RDF -- the
   * IKL-to-RDF projection that used to accompany it is deleted
   * (danbri/factoidal#626). Lean 4 only: formal/fstar has no CL/IKL parser, so this
   * function is absent from index.js/wasm.js -- see capabilities() /
   * factoidal/select's capability table.
   * @param {string} clifText
   * @returns {Promise<{ok: boolean, sentences: number, pureCL: boolean,
   *   normalized: string}>} `pureCL` is a DIALECT flag, not a validity
   *   or quality signal: true while the text stays inside ISO/IEC
   *   24707 Common Logic, false once it uses IKL's `that` operator.
   *   Both values are returned only for text that parsed; a CLIF text
   *   that fails to parse rejects instead (e.g. a bare `(that S)` used
   *   as a proposition rather than a term -- see the GUIDE).
   */
  async function clParse(clifText) {
    if (typeof clifText !== 'string') {
      throw new TypeError('clParse: clifText must be a string');
    }
    const e = await entry();
    requireEntryFn(e, 'clParse', 'Common Logic / IKL parse');
    return entryResult(e.clParse(clifText), 'clParse');
  }

  /**
   * Read Common Logic Interchange Format text and write it back out in
   * the canonical spacing of the CLIF writer (entry_jsoo.ml's
   * clSerialize export -> L4Factoidal's CL/Clif.lean reader/writer
   * pair). Lean 4 only: formal/fstar has no CL/IKL parser, so this
   * function is absent from index.js/wasm.js -- see capabilities() /
   * factoidal/select's capability table.
   *
   * `roundTripProved` is always `false`. The round-trip lemma
   * `clif_roundTrip` (`CL/ClifAdequacy.lean`) is an OPEN lemma: the
   * fragment boundary `marksLexable` is MEASURED, not proved. The
   * field is in the envelope, unmodified, so a caller does not have to
   * go and find that out.
   * @param {string} clifText
   * @returns {Promise<{ok: boolean, clif: string, sentences: number,
   *   roundTripProved: false}>}
   */
  async function clSerialize(clifText) {
    if (typeof clifText !== 'string') {
      throw new TypeError('clSerialize: clifText must be a string');
    }
    const e = await entry();
    requireEntryFn(e, 'clSerialize', 'Common Logic / IKL serialize');
    return entryResult(e.clSerialize(clifText), 'clSerialize');
  }

  /**
   * Alpha-normalise Common Logic Interchange Format text: the canonical
   * representative of each sentence's bound-variable-renaming
   * equivalence class (entry_jsoo.ml's clAlphaNorm export ->
   * L4Factoidal's `CL/Alpha.lean`, `Sentence.alphaNorm`). Bound names
   * become `v1`, `v2`, ... in traversal order, so two sentences that
   * differ only in bound-variable names produce byte-identical output
   * -- IKL GUIDE Appendix B condition (1): renaming a bound variable
   * does not change the proposition expressed. Lean 4 only: formal/fstar
   * has no CL/IKL parser, so this function is absent from
   * index.js/wasm.js -- see capabilities() / factoidal/select's
   * capability table.
   * @param {string} clifText
   * @returns {Promise<{ok: boolean, clif: string, sentences: number}>}
   */
  async function clAlphaNorm(clifText) {
    if (typeof clifText !== 'string') {
      throw new TypeError('clAlphaNorm: clifText must be a string');
    }
    const e = await entry();
    requireEntryFn(e, 'clAlphaNorm', 'Common Logic / IKL alpha-normalise');
    return entryResult(e.clAlphaNorm(clifText), 'clAlphaNorm');
  }

  /**
   * Hayes's satisfiability-preserving reduction of IKL to Common Logic
   * (entry_jsoo.ml's clNormalize export -> L4Factoidal's
   * `CL/Normalize.lean`, `normalizeText`; danbri/factoidal#625), over a
   * whole text: one head text and one shared tail, with the
   * proposition-name counter running across the text. Lean 4 only:
   * formal/fstar has no CL/IKL parser, so this function is absent from
   * index.js/wasm.js -- see capabilities() / factoidal/select's
   * capability table.
   *
   * Two limits, both real, both in the answer, neither hidden:
   *  - `preserves: "satisfiability"` -- the reduction preserves
   *    satisfiability, NOT equivalence. It suits entailment and
   *    consistency testing; it is not a transformation to apply to
   *    data you intend to keep.
   *  - `noIntrusion` IS the proof hypothesis `CL.noIntrSs [] []`
   *    decides, not a paraphrase of it. The transformation runs either
   *    way; when `noIntrusion` is `false`, the output is still
   *    produced, but `tails_satisfiable` / `normalize_preserves` do
   *    not cover that case.
   * @param {string} clifText
   * @returns {Promise<{ok: boolean, head: string[], tail: string[],
   *   clif: string, sentences: number, thatCount: number,
   *   noIntrusion: boolean, preserves: 'satisfiability',
   *   provedUnder: string}>}
   */
  async function clNormalize(clifText) {
    if (typeof clifText !== 'string') {
      throw new TypeError('clNormalize: clifText must be a string');
    }
    const e = await entry();
    requireEntryFn(e, 'clNormalize', 'Common Logic / IKL normalize');
    return entryResult(e.clNormalize(clifText), 'clNormalize');
  }

  // clFiniteSat (entry_jsoo.ml's clFiniteSat -> L4Factoidal's
  // CL/FiniteSatTheorems.lean) is DEFERRED, not excluded, from this
  // typed layer (owner decision, 2026-08-26): it takes a caller-supplied
  // finite-interpretation JSON encoding (see Wasm/Ops/CL.lean's header
  // for the wire format) that has no user yet, and a typed wrapper here
  // would freeze that shape before anyone knows whether it is right. It
  // stays reachable through the raw dispatch ABI (`l4.call('clFiniteSat',
  // [interpJson, clifText])` / factoidal/select's `call('clFiniteSat',
  // ...)`), which needs no shape commitment on this layer.

  // -----------------------------------------------------------------
  // VC Data Integrity crypto (eddsa-rdfc-2022), ops of
  // Wasm/Ops/Vc.lean. Ed25519 is the HACL* C code compiled into the wasm
  // module (L4Factoidal/Crypto/Ed25519.lean's @[extern] binding);
  // SHA-256 is the Lean hash. There is no separate crypto module and no
  // initialisation step.
  // -----------------------------------------------------------------

  async function vcEntry(fnName, what) {
    const e = await entry();
    requireEntryFn(e, fnName, what);
    return e;
  }

  /**
   * SHA-256 of a message string's bytes, as a lowercase hex digest
   * (entry_jsoo.ml's vcSha256Hex -> VC_DataIntegrity.hash_sha256_hex,
   * the Lean SHA-256).
   * @param {string} message the message whose bytes are hashed
   * @returns {Promise<string>} 64-char hex digest
   */
  async function vcSha256Hex(message) {
    if (typeof message !== 'string') {
      throw new TypeError('vcSha256Hex: message must be a string');
    }
    const e = await vcEntry('vcSha256Hex', 'VC SHA-256');
    return entryResult(e.vcSha256Hex(message), 'vcSha256Hex').sha256;
  }

  /**
   * Derive the Ed25519 public key from a 32-byte secret key
   * (entry_jsoo.ml's vcEd25519SecretToPublic -> HACL* Ed25519).
   * @param {string} secretKeyHex 32-byte secret key, hex
   * @returns {Promise<string>} 32-byte public key, hex
   */
  async function vcEd25519SecretToPublic(secretKeyHex) {
    if (typeof secretKeyHex !== 'string') {
      throw new TypeError('vcEd25519SecretToPublic: secretKeyHex must be a string');
    }
    const e = await vcEntry('vcEd25519SecretToPublic', 'VC Ed25519 key derivation');
    return entryResult(
      e.vcEd25519SecretToPublic(secretKeyHex), 'vcEd25519SecretToPublic').publicKeyHex;
  }

  /**
   * Ed25519 signature over a hex-encoded message (entry_jsoo.ml's
   * vcEd25519Sign -> HACL* Ed25519).
   * @param {string} secretKeyHex 32-byte secret key, hex
   * @param {string} messageHex the message to sign, hex
   * @returns {Promise<string>} 64-byte signature, hex
   */
  async function vcEd25519Sign(secretKeyHex, messageHex) {
    if (typeof secretKeyHex !== 'string' || typeof messageHex !== 'string') {
      throw new TypeError('vcEd25519Sign: secretKeyHex and messageHex must be strings');
    }
    const e = await vcEntry('vcEd25519Sign', 'VC Ed25519 sign');
    return entryResult(e.vcEd25519Sign(secretKeyHex, messageHex), 'vcEd25519Sign').signatureHex;
  }

  /**
   * Ed25519 verification (entry_jsoo.ml's vcEd25519Verify -> HACL*
   * Ed25519). A wrong key, tampered signature, altered message, or a
   * malformed-length input all return false — never an
   * exception-hidden true.
   * @param {string} publicKeyHex 32-byte public key, hex
   * @param {string} messageHex the message, hex
   * @param {string} signatureHex the 64-byte signature, hex
   * @returns {Promise<boolean>}
   */
  async function vcEd25519Verify(publicKeyHex, messageHex, signatureHex) {
    if (typeof publicKeyHex !== 'string' || typeof messageHex !== 'string' ||
        typeof signatureHex !== 'string') {
      throw new TypeError(
        'vcEd25519Verify: publicKeyHex, messageHex and signatureHex must be strings');
    }
    const e = await vcEntry('vcEd25519Verify', 'VC Ed25519 verify');
    return !!entryResult(
      e.vcEd25519Verify(publicKeyHex, messageHex, signatureHex), 'vcEd25519Verify').valid;
  }

  // -----------------------------------------------------------------
  // XML Encryption 1.1 and JWE (https://github.com/danbri/factoidal/issues/1084,
  // https://github.com/danbri/factoidal/issues/1085). Every decision is in
  // Lean (formal/lean4/Wasm/Ops/XmlEnc.lean, Wasm/Ops/Jwe.lean); RSA, P-256
  // and X25519 run in the wasm (HACL*). AES runs in this host's WebCrypto:
  // runWithCipher (lib/cipher-host.mjs) answers each request the engine
  // makes and calls the op again. This code converts bytes to base64 and
  // draws random bytes; it reads no document and chooses nothing.
  // -----------------------------------------------------------------

  // The most random octets any of these ops reads (Jwe.randomBytesNeeded is
  // at most 112; xmlEncrypt reads at most 76).
  const CIPHER_RANDOM_BYTES = 112;

  function bytesToBase64(bytes) {
    let bin = '';
    for (let i = 0; i < bytes.length; i += 0x8000) {
      bin += String.fromCharCode.apply(null, bytes.subarray(i, i + 0x8000));
    }
    return btoa(bin);
  }

  function base64ToBytes(text) {
    const bin = atob(text);
    const out = new Uint8Array(bin.length);
    for (let i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
    return out;
  }

  function randomBase64(n) {
    const b = new Uint8Array(n);
    globalThis.crypto.getRandomValues(b);
    return bytesToBase64(b);
  }

  // One op that may ask for AES: the engine's envelope after every request
  // is answered; a refusal throws a FactoidalError.
  async function cipherOp(fnName, what, args) {
    const e = await entry();
    requireEntryFn(e, fnName, what);
    const res = await runWithCipher((a) => JSON.parse(e[fnName](JSON.stringify(a))), args);
    return entryResult(JSON.stringify(res), fnName);
  }

  function checkKeys(fnName, keys) {
    if (!Array.isArray(keys) || !keys.every((k) => k !== null && typeof k === 'object')) {
      throw new TypeError(`${fnName}: keys must be an array of JWK objects`);
    }
  }

  /**
   * Decrypt every xenc:EncryptedData of an XML document (XML Encryption 1.1).
   * Allowlist and key forms: API.md "XML Encryption and JWE".
   * @param {string} document the XML document
   * @param {{keys: object[], allowCbc?: boolean}} options private JWKs
   *   (`kid` is the ds:KeyName); `allowCbc` admits aes128-cbc and aes256-cbc
   * @returns {Promise<{document: string, canonical: string}>}
   */
  async function xmlDecrypt(document, options) {
    if (typeof document !== 'string') throw new TypeError('xmlDecrypt: document must be a string');
    const o = options || {};
    checkKeys('xmlDecrypt', o.keys);
    const r = await cipherOp('xmlDecrypt', 'XML decryption',
      { document, keys: o.keys, allowCbc: o.allowCbc === true });
    return { document: r.document, canonical: r.canonical };
  }

  /**
   * Encrypt the document element (or, with `content`, its content) of an XML
   * document for one recipient (XML Encryption 1.1, AES-GCM content).
   * @param {string} document the XML document
   * @param {{recipient: object, algorithm?: 'aes128-gcm'|'aes256-gcm',
   *   keyTransport?: 'rsa-oaep-mgf1p'|'rsa-oaep-sha256', keyWrap?: 'kw-aes128'|'kw-aes256',
   *   content?: boolean, saml?: boolean}} options `recipient` is a public JWK
   *   (RSA, EC P-256, OKP X25519) or an `oct` key; `saml` wraps the result in
   *   saml:EncryptedAssertion
   * @returns {Promise<{document: string, canonical: string}>}
   */
  async function xmlEncrypt(document, options) {
    if (typeof document !== 'string') throw new TypeError('xmlEncrypt: document must be a string');
    const o = options || {};
    if (o.recipient === null || typeof o.recipient !== 'object') {
      throw new TypeError('xmlEncrypt: options.recipient must be a JWK object');
    }
    const args = { document, recipient: o.recipient, random: randomBase64(CIPHER_RANDOM_BYTES) };
    for (const k of ['algorithm', 'keyTransport', 'keyWrap']) if (o[k] !== undefined) args[k] = o[k];
    if (o.content === true) args.content = true;
    if (o.saml === true) args.saml = true;
    const r = await cipherOp('xmlEncrypt', 'XML encryption', args);
    return { document: r.document, canonical: r.canonical };
  }

  /**
   * Decrypt a JWE in the Compact Serialization (RFC 7516).
   * @param {string} token the compact JWE
   * @param {{jwk: object}} options the recipient's private JWK
   * @returns {Promise<{header: object, plaintext: Uint8Array}>}
   */
  async function jweDecrypt(token, options) {
    if (typeof token !== 'string') throw new TypeError('jweDecrypt: token must be a string');
    const o = options || {};
    if (o.jwk === null || typeof o.jwk !== 'object') throw new TypeError('jweDecrypt: options.jwk must be a JWK object');
    const r = await cipherOp('jweDecrypt', 'JWE decryption', { token, jwk: o.jwk });
    return { header: r.header, plaintext: base64ToBytes(r.plaintext) };
  }

  /**
   * Encrypt to a JWE in the Compact Serialization (RFC 7516).
   * @param {Uint8Array|string} plaintext bytes, or text written as UTF-8
   * @param {{alg: string, enc: string, jwk: object, header?: object}} options
   *   the recipient's public JWK (or the `oct` key for A128KW, A256KW, dir);
   *   `header`: more protected header members
   * @returns {Promise<string>} the compact JWE
   */
  async function jweEncrypt(plaintext, options) {
    let bytes;
    if (typeof plaintext === 'string') bytes = new TextEncoder().encode(plaintext);
    else if (plaintext instanceof Uint8Array) bytes = plaintext;
    else throw new TypeError('jweEncrypt: plaintext must be a Uint8Array or a string');
    const o = options || {};
    if (typeof o.alg !== 'string' || typeof o.enc !== 'string') {
      throw new TypeError('jweEncrypt: options.alg and options.enc must be strings');
    }
    if (o.jwk === null || typeof o.jwk !== 'object') throw new TypeError('jweEncrypt: options.jwk must be a JWK object');
    const args = { alg: o.alg, enc: o.enc, jwk: o.jwk, plaintext: bytesToBase64(bytes),
      random: randomBase64(CIPHER_RANDOM_BYTES) };
    if (o.header !== undefined) args.header = o.header;
    return (await cipherOp('jweEncrypt', 'JWE encryption', args)).token;
  }

  /**
   * Create an eddsa-rdfc-2022 Data Integrity proofValue over an
   * already-canonicalized document + proof config (entry_jsoo.ml's
   * vcEddsaCreateFromCanonical -> VC_DataIntegrity.eddsa_rdfc_2022_
   * create_from_canonical). The two canonical inputs are RDFC-1.0
   * canonical N-Quads (see canonicalize()).
   * @param {string} secretKeyHex 32-byte secret key, hex
   * @param {string} canonicalDocument canonical N-Quads of the document
   * @param {string} canonicalConfig canonical N-Quads of the proof config
   * @returns {Promise<string>} the multibase-z (base58btc) proofValue
   */
  async function vcEddsaCreateFromCanonical(secretKeyHex, canonicalDocument, canonicalConfig) {
    if (typeof secretKeyHex !== 'string' || typeof canonicalDocument !== 'string' ||
        typeof canonicalConfig !== 'string') {
      throw new TypeError(
        'vcEddsaCreateFromCanonical: secretKeyHex, canonicalDocument and canonicalConfig must be strings');
    }
    const e = await vcEntry('vcEddsaCreateFromCanonical', 'VC eddsa-rdfc-2022 proof creation');
    return entryResult(
      e.vcEddsaCreateFromCanonical(secretKeyHex, canonicalDocument, canonicalConfig),
      'vcEddsaCreateFromCanonical').proofValue;
  }

  /**
   * Verify an eddsa-rdfc-2022 proofValue against canonical inputs
   * (entry_jsoo.ml's vcEddsaVerifyFromCanonical ->
   * VC_DataIntegrity.eddsa_rdfc_2022_verify_from_canonical). Wrong
   * key, tampered document/config, or tampered proofValue all return
   * false.
   * @param {string} publicKeyHex 32-byte public key, hex
   * @param {string} canonicalDocument canonical N-Quads of the document
   * @param {string} canonicalConfig canonical N-Quads of the proof config
   * @param {string} proofValue the multibase-z proofValue to check
   * @returns {Promise<boolean>}
   */
  async function vcEddsaVerifyFromCanonical(publicKeyHex, canonicalDocument, canonicalConfig, proofValue) {
    if (typeof publicKeyHex !== 'string' || typeof canonicalDocument !== 'string' ||
        typeof canonicalConfig !== 'string' || typeof proofValue !== 'string') {
      throw new TypeError(
        'vcEddsaVerifyFromCanonical: publicKeyHex, canonicalDocument, canonicalConfig and proofValue must be strings');
    }
    const e = await vcEntry('vcEddsaVerifyFromCanonical', 'VC eddsa-rdfc-2022 proof verification');
    return !!entryResult(
      e.vcEddsaVerifyFromCanonical(publicKeyHex, canonicalDocument, canonicalConfig, proofValue),
      'vcEddsaVerifyFromCanonical').verified;
  }

  /**
   * VC Data Model 2.0 structural conformance check (entry_jsoo.ml's
   * vcCheckCredential -> VC_Credential.vc_check_from_string, 117 pass,
   * 0 fail on the offline vc_stage1 fixture suite). Pure structural
   * validation, no crypto. `v2ctxJson` is the vendored VCDM v2 base context
   * document's raw JSON text (third_party/contexts/credentials-v2.jsonld,
   * `@context` value included — the engine parses the whole document
   * and only reads its own @context field) and `credentialJson` is the
   * raw JSON text of the VC/VP document under test.
   * @param {string} v2ctxJson vendored credentials-v2.jsonld text
   * @param {string} credentialJson the VC/VP document's raw JSON text
   * @returns {Promise<{valid: boolean, reason?: string}>}
   */
  async function vcCheckCredential(v2ctxJson, credentialJson) {
    if (typeof v2ctxJson !== 'string' || typeof credentialJson !== 'string') {
      throw new TypeError('vcCheckCredential: v2ctxJson and credentialJson must be strings');
    }
    const e = await entry();
    requireEntryFn(e, 'vcCheckCredential', 'VC Data Model 2.0 structural check');
    const r = entryResult(e.vcCheckCredential(v2ctxJson, credentialJson), 'vcCheckCredential');
    return r.valid ? { valid: true } : { valid: false, reason: r.reason };
  }

  /**
   * credentialSubject presence/shape check, VERSION-AGNOSTIC (Track A1,
   * docs/designissues/2026-07-11-vc-canivc-eecc-plan.md) —
   * entry_jsoo.ml's vcCheckCredentialSubject ->
   * VC_Credential.vc_check_credential_subject_from_string. Unlike
   * vcCheckCredential above, this does NOT require the VCDM 2.0 base
   * @context to be first (or present at all) — it only checks that a
   * credential-shaped document (type includes "VerifiableCredential")
   * has a present, non-empty credentialSubject. Used for documents
   * under a non-VCDM-2.0 @context (e.g. the vc-di-eddsa Data Integrity
   * conformance suite's legacy VC 1.1 fixtures) where the full
   * vcCheckCredential's @context sentinel would (correctly) reject the
   * document for an unrelated reason.
   * @param {string} credentialJson the VC/VP document's raw JSON text
   * @returns {Promise<{valid: boolean, reason?: string}>}
   */
  async function vcCheckCredentialSubject(credentialJson) {
    if (typeof credentialJson !== 'string') {
      throw new TypeError('vcCheckCredentialSubject: credentialJson must be a string');
    }
    const e = await entry();
    requireEntryFn(e, 'vcCheckCredentialSubject', 'credentialSubject presence check');
    const r = entryResult(e.vcCheckCredentialSubject(credentialJson), 'vcCheckCredentialSubject');
    return r.valid ? { valid: true } : { valid: false, reason: r.reason };
  }

  /**
   * DATA_LOSS_DETECTION_ERROR check (Track A1, same plan doc) —
   * entry_jsoo.ml's vcCheckNoDataLoss ->
   * VC_Credential.vc_check_no_data_loss_from_string. Rejects a
   * credential-shaped document whose `type`/`@type` entries or
   * `credentialSubject` property keys include one that a lenient
   * JSON-LD processor would silently drop (VC Data Integrity spec,
   * "Securing Data Losslessly"). `credentialJson` MUST already have
   * any remote @context IRI the caller recognizes inlined to the real
   * context object — this engine build has no remote-context loader
   * registered, so a still-remote IRI string in "@context" makes
   * context processing fail with an error; the check is not skipped.
   * @param {string} credentialJson the VC/VP document's raw JSON text,
   *   @context already inlined
   * @returns {Promise<{valid: boolean, reason?: string}>}
   */
  async function vcCheckNoDataLoss(credentialJson) {
    if (typeof credentialJson !== 'string') {
      throw new TypeError('vcCheckNoDataLoss: credentialJson must be a string');
    }
    const e = await entry();
    requireEntryFn(e, 'vcCheckNoDataLoss', 'DATA_LOSS_DETECTION_ERROR check');
    const r = entryResult(e.vcCheckNoDataLoss(credentialJson), 'vcCheckNoDataLoss');
    return r.valid ? { valid: true } : { valid: false, reason: r.reason };
  }

  /**
   * relatedResource digest verification (VCDM 2.0 §5.3, vc20-api Track
   * A4) — entry_jsoo.ml's vcCheckRelatedResourceDigests ->
   * VC_Credential.vc_check_related_resource_digests_from_string. The
   * engine does no I/O, so the caller supplies a known-resource digest
   * registry: a JSON array of {"id": <resource URL>, "digestsHex":
   * [<lowercase hex>, ...]} entries computed from the caller's VENDORED
   * copies of each resource's content bytes. A relatedResource entry
   * whose id is in the registry and whose declared digestSRI/
   * digestMultibase matches none of that id's digests is rejected (the
   * spec's digest-mismatch error); an id absent from the registry, or a
   * digest algorithm the registry contract doesn't cover (anything
   * outside sha256/sha384), is unverifiable offline and passes. All
   * decode/match semantics are L4Factoidal/VC/Credential.lean's.
   * @param {string} registryJson the digest registry's raw JSON text
   * @param {string} credentialJson the VC/VP document's raw JSON text
   * @returns {Promise<{valid: boolean, reason?: string}>}
   */
  async function vcCheckRelatedResourceDigests(registryJson, credentialJson) {
    if (typeof registryJson !== 'string' || typeof credentialJson !== 'string') {
      throw new TypeError('vcCheckRelatedResourceDigests: registryJson and credentialJson must be strings');
    }
    const e = await entry();
    requireEntryFn(e, 'vcCheckRelatedResourceDigests', 'relatedResource digest check');
    const r = entryResult(e.vcCheckRelatedResourceDigests(registryJson, credentialJson), 'vcCheckRelatedResourceDigests');
    return r.valid ? { valid: true } : { valid: false, reason: r.reason };
  }

  // -----------------------------------------------------------------
  // Typed "engine" functions (#74 npm FP surface). Each is a pure,
  // string/JSON-in, JSON-out wrapper over one dispatch op. No logic
  // lives on the JS side; these bind the op to a typed Promise.
  // -----------------------------------------------------------------

  /**
   * XSLT 1.0 transform (entry_jsoo.ml's xsltTransform export ->
   * XSLT.Transform.transform). Applies `stylesheetXml` to `sourceXml`
   * and returns the serialized result tree.
   * @param {string} stylesheetXml an XSLT stylesheet document
   * @param {string} sourceXml the source XML document
   * @returns {Promise<string>} the transform output (serialized XML/text)
   */
  async function xsltTransform(stylesheetXml, sourceXml) {
    if (typeof stylesheetXml !== 'string' || typeof sourceXml !== 'string') {
      throw new TypeError('xsltTransform: stylesheetXml and sourceXml must be strings');
    }
    const e = await entry();
    requireEntryFn(e, 'xsltTransform', 'XSLT transform');
    const r = entryResult(e.xsltTransform(stylesheetXml, sourceXml), 'xsltTransform');
    return r.output;
  }

  /**
   * Evaluate a Content MathML document (entry_jsoo.ml's mathmlEval
   * export -> MathML.Content.eval_doc_env). `bindings` maps
   * ci-variable names to value strings; pass {} for a closed
   * expression. Returns the exact numeric/boolean value or an
   * `undef` reason (division-by-zero, type error, ...).
   * @param {string} contentMathmlXml
   * @param {Record<string,string>} [bindings]
   * @returns {Promise<{kind:'rat',num:number,den:number}|{kind:'bool',value:boolean}|{kind:'undef',reason:string}>}
   */
  async function mathmlEval(contentMathmlXml, bindings) {
    if (typeof contentMathmlXml !== 'string') {
      throw new TypeError('mathmlEval: contentMathmlXml must be a string');
    }
    const b = bindings || {};
    if (typeof b !== 'object') {
      throw new TypeError('mathmlEval: bindings must be an object');
    }
    const e = await entry();
    requireEntryFn(e, 'mathmlEval', 'MathML evaluation');
    const r = entryResult(
      e.mathmlEval(contentMathmlXml, JSON.stringify(b)), 'mathmlEval');
    return r.value;
  }

  /**
   * XForms recalculate (entry_jsoo.ml's xformsRecalc export ->
   * XForms.Bind.recalculate). Applies the model binds (calculate,
   * constraint, relevant, required, readonly, type MIPs) to the
   * instance and returns the recomputed instance plus a validity
   * report per bound node.
   * @param {string} instanceXml the XForms instance document
   * @param {Array<{id?:string,target:string,calculate?:string,constraint?:string,relevant?:string,required?:string,readonly?:string,type?:string}>} binds
   * @returns {Promise<{instance:string,validity:Array<object>}>}
   */
  async function xformsRecalc(instanceXml, binds) {
    if (typeof instanceXml !== 'string') {
      throw new TypeError('xformsRecalc: instanceXml must be a string');
    }
    if (!Array.isArray(binds)) {
      throw new TypeError('xformsRecalc: binds must be an array');
    }
    const e = await entry();
    requireEntryFn(e, 'xformsRecalc', 'XForms recalculate');
    const r = entryResult(
      e.xformsRecalc(instanceXml, JSON.stringify(binds)), 'xformsRecalc');
    return { instance: r.instance, validity: r.validity };
  }

  /**
   * JSON Schema (draft-07) validation (entry_jsoo.ml's
   * jsonSchemaValidate export -> JSONSchema.Validate.validate).
   * Returns the verdict — the verified validator gives a definite
   * pass/fail/unsupported, not a per-keyword error list, so `errors`
   * carries a single reason string when not a definite pass.
   * @param {string} schemaJson the schema document (JSON text)
   * @param {string} instanceJson the instance document (JSON text)
   * @returns {Promise<{valid:boolean,result:'pass'|'fail'|'unsupported',errors:string[]}>}
   */
  async function jsonSchemaValidate(schemaJson, instanceJson) {
    if (typeof schemaJson !== 'string' || typeof instanceJson !== 'string') {
      throw new TypeError('jsonSchemaValidate: schemaJson and instanceJson must be strings');
    }
    const e = await entry();
    requireEntryFn(e, 'jsonSchemaValidate', 'JSON Schema validation');
    const r = entryResult(
      e.jsonSchemaValidate(schemaJson, instanceJson), 'jsonSchemaValidate');
    return { valid: !!r.valid, result: r.result, errors: r.errors || [] };
  }

  /**
   * Schematron validation (entry_jsoo.ml's schematronValidate export
   * -> Schematron.Validate.validate). Returns every finding (failed
   * assert, fired report, indeterminate) in pattern-then-document
   * order.
   * @param {string} schematronXml the Schematron schema document
   * @param {string} instanceXml the instance document to check
   * @returns {Promise<{findings:Array<{type:string,context:string,test:string,message:string,path:string,reason?:string}>}>}
   */
  async function schematronValidate(schematronXml, instanceXml) {
    if (typeof schematronXml !== 'string' || typeof instanceXml !== 'string') {
      throw new TypeError('schematronValidate: schematronXml and instanceXml must be strings');
    }
    const e = await entry();
    requireEntryFn(e, 'schematronValidate', 'Schematron validation');
    const r = entryResult(
      e.schematronValidate(schematronXml, instanceXml), 'schematronValidate');
    return { findings: r.findings };
  }

  // TOAN — a small exact-CAS surface over Math.Expr (E_Int/E_Rat/E_Bool/
  // E_Sym/E_App). Callers pass an expression as the JSON codec
  //   {int:n} | {rat:[n,d]} | {bool:b} | {sym:name} | {app:name,args:[...]}
  // and receive Content MathML for the result (via MathML.Present).
  async function toanCall(fnName, what, ...args) {
    const e = await entry();
    requireEntryFn(e, fnName, what);
    const r = entryResult(e[fnName](...args), fnName);
    return r.mathml;
  }

  /**
   * Symbolic finite summation (entry_jsoo.ml's toanSummation ->
   * Math.Series.summation): sum of `body[idx:=lo..hi]`, simplified,
   * as Content MathML.
   * @param {object} bodyExpr the summand, in the expr JSON codec
   * @param {string} idx the summation index symbol
   * @param {number} lo inclusive lower bound
   * @param {number} hi inclusive upper bound
   * @returns {Promise<string>} Content MathML
   */
  async function toanSummation(bodyExpr, idx, lo, hi) {
    if (typeof idx !== 'string') throw new TypeError('toanSummation: idx must be a string');
    return toanCall('toanSummation', 'TOAN summation',
      JSON.stringify(bodyExpr), idx, String(lo), String(hi));
  }

  /**
   * Symbolic finite product (entry_jsoo.ml's toanProduct ->
   * Math.Series.finite_product). Same shape as {@link toanSummation}.
   * @param {object} bodyExpr the factor, in the expr JSON codec
   * @param {string} idx the product index symbol
   * @param {number} lo inclusive lower bound
   * @param {number} hi inclusive upper bound
   * @returns {Promise<string>} Content MathML
   */
  async function toanProduct(bodyExpr, idx, lo, hi) {
    if (typeof idx !== 'string') throw new TypeError('toanProduct: idx must be a string');
    return toanCall('toanProduct', 'TOAN product',
      JSON.stringify(bodyExpr), idx, String(lo), String(hi));
  }

  /**
   * Canonical simplification (entry_jsoo.ml's toanSimplify ->
   * Math.Simplify.simplify) of an expression, as Content MathML.
   * @param {object} expr in the expr JSON codec
   * @returns {Promise<string>} Content MathML
   */
  async function toanSimplify(expr) {
    return toanCall('toanSimplify', 'TOAN simplify', JSON.stringify(expr));
  }

  /**
   * Symbolic differentiation (entry_jsoo.ml's toanDiff ->
   * Math.Diff.diff) of `expr` w.r.t. `variable`, as Content MathML.
   * @param {object} expr in the expr JSON codec
   * @param {string} variable the differentiation variable
   * @returns {Promise<string>} Content MathML
   */
  async function toanDiff(expr, variable) {
    if (typeof variable !== 'string') throw new TypeError('toanDiff: variable must be a string');
    return toanCall('toanDiff', 'TOAN diff', JSON.stringify(expr), variable);
  }

  /**
   * Substitution (entry_jsoo.ml's toanSubst -> Math.Subst.subst):
   * `expr[variable := value]`, simplified, as Content MathML.
   * @param {object} expr in the expr JSON codec
   * @param {string} variable the symbol to replace
   * @param {object} value the replacement, in the expr JSON codec
   * @returns {Promise<string>} Content MathML
   */
  async function toanSubst(expr, variable, value) {
    if (typeof variable !== 'string') throw new TypeError('toanSubst: variable must be a string');
    return toanCall('toanSubst', 'TOAN subst',
      JSON.stringify(expr), variable, JSON.stringify(value));
  }



  // -----------------------------------------------------------------
  // The Lean persisted store (see the Store class above).
  // -----------------------------------------------------------------

  function storeReader(source, who) {
    if (typeof source === 'function') return source;
    if (typeof source === 'string') {
      if (typeof driver.storeReaderFor !== 'function') {
        throw new TypeError(
          `${who}: a path needs a file system; here, pass a reader function ` +
          '(path) => bytes, for example one over fetch()');
      }
      return driver.storeReaderFor(source);
    }
    throw new TypeError(`${who}: expected a collection root path or a reader function`);
  }

  /**
   * Open a store: read the generation CURRENT names (or `generation`),
   * read the artifacts the engine names, and open a store handle over
   * them (op storeOpen). With no `sparql` and no `keys`, every artifact
   * the manifest declares is read, so every query the generation can
   * answer works. With `sparql`, only the artifacts that query's plan
   * names (op storeQueryPlan) are read. With `keys`, exactly those.
   * @param {string|((path: string) => any)} source a collection root path
   *   (Node), or a reader from a root-relative path to the file's bytes
   * @param {{generation?: string, sparql?: string, keys?: string[]}} [options]
   * @returns {Promise<Store>}
   */
  async function openStore(source, options) {
    const opts = options || {};
    const reader = storeReader(source, 'openStore');
    const e = await entry();
    requireEntryFn(e, 'storeOpen', 'openStore (storeOpen)');
    const gen = await openGeneration(reader, opts.generation);
    // The byte ops when the engine has them (issue 1039): the manifest
    // crosses as bytes and is decoded once for the plan and the open. An
    // older engine gets the hexadecimal ops, as before.
    const bytesOps = typeof e.storeOpenBytes === 'function';
    const manifestHex = bytesOps ? null : hexOfBytes(gen.manifest);
    let keys;
    if (Array.isArray(opts.keys)) {
      keys = opts.keys.map(String);
    } else if (typeof opts.sparql === 'string') {
      const plan = entryResult(bytesOps
        ? e.storeQueryPlanBytes(gen.manifest, opts.sparql)
        : e.storeQueryPlan(manifestHex, opts.sparql), 'openStore(plan)');
      keys = plan.keys.concat(plan.sidecarKeys || [], plan.blobKeys || []);
    } else {
      keys = manifestKeys(entryResult(bytesOps
        ? e.storeManifestInspectBytes(gen.manifest)
        : e.storeManifestInspect(manifestHex), 'openStore(inspect)'));
    }
    const { blob, artifacts } = await readRegion(reader, gen.generation, keys);
    const env = entryResult(bytesOps
      ? e.storeOpenBytes(gen.manifest, JSON.stringify(artifacts), blob)
      : e.storeOpen(manifestHex, JSON.stringify(artifacts), blob), 'openStore');
    const c = await ctx();
    return new Store(e, env, gen, (nq) => c.fromNQuads(nq, {}), withExtensionRounds);
  }

  /**
   * One query against a store: open it with the artifacts the query's
   * plan names, query, close.
   * @param {string|((path: string) => any)} source
   * @param {string} sparql
   * @param {{generation?: string}} [options]
   * @returns {Promise<Array<Map<string, object>>|boolean|Dataset>}
   */
  async function queryStore(source, sparql, options) {
    if (typeof sparql !== 'string') throw new TypeError('queryStore: sparql must be a string');
    const store = await openStore(source, { generation: (options || {}).generation, sparql });
    try {
      return await store.query(sparql);
    } finally {
      await store.close();
    }
  }

  /** The store handles this engine instance holds open (op storeHandleList). */
  async function listStores() {
    const e = await entry();
    requireEntryFn(e, 'storeHandleList', 'listStores');
    const { ok: _ok, ...rest } = entryResult(e.storeHandleList(), 'listStores');
    return rest;
  }

  /**
   * One call, serialised answer (op queryRaw): parse `dataString`, close
   * the default graph under `entail`, run the query, and write the answer
   * in `output`: 'json' (default; parsed SPARQL results JSON), or 'csv',
   * 'tsv', 'xml', 'table', 'ntriples' (text). A CONSTRUCT or DESCRIBE
   * answer is a graph: 'ntriples' or 'table' only.
   * @param {string} dataString
   * @param {string} queryString
   * @param {{dataFormat?: string, entail?: string, output?: string}} [options]
   * @returns {Promise<object|string>}
   */
  async function queryRaw(dataString, queryString, options) {
    if (typeof dataString !== 'string') {
      throw new TypeError('queryRaw: dataString must be a string');
    }
    if (typeof queryString !== 'string') {
      throw new TypeError('queryRaw: queryString must be a string');
    }
    const opts = await checkedOptions('queryRaw', options);
    const dataFormat = String(opts.dataFormat || 'turtle').toLowerCase();
    const entail = opts.entail || 'none';
    const output = opts.output || 'json';
    const tables = (await ctx()).tables();
    const e = await entry();
    requireEntryFn(e, 'queryRaw', 'queryRaw');
    const r = entryResult(e.queryRaw(dataString, queryString,
      JSON.stringify({ dataFormat: tables.rawDataFormats[dataFormat], entail, output })),
    'queryRaw', queryString);
    return output === 'json' ? JSON.parse(r.text) : r.text;
  }

  // ---------------------------------------------------------------
  // The durable update log of a browser host (hub post 18,
  // https://github.com/danbri/factoidal/issues/728).
  //
  // One record for each committed SPARQL Update request, kept by the host
  // store (driver.deltaLogStore: IndexedDB in the browser entries, the
  // memory of the process by default). The engine makes every decision
  // about the bytes: op deltaLogEncode writes a record (a DLB1 frame with
  // its checksum), op deltaLogMerge decodes the records, stops at the first
  // record that does not verify, and applies the batches before it
  // (formal/lean4/L4Factoidal/Storage/BrowserLog.lean, with the theorems in
  // BrowserLogTheorems.lean). This layer moves text between the two. The
  // names and result shapes are those of the F* browser entry before 0.9.0.
  // ---------------------------------------------------------------
  const DEFAULT_DELTA_DB_NAME = 'factoidal-delta-log';
  const deltaLogStore = driver.deltaLogStore || memoryDeltaLogStore();

  function requireDeltaHandle(handle, who) {
    if (!handle || typeof handle.dbName !== 'string') {
      throw new TypeError(`${who}: handle must be the object deltaLogOpen() returned`);
    }
  }

  /**
   * Open (create when absent) a durable update log. In the browser the log is
   * an IndexedDB database of that name; under Node it lives in the memory of
   * the process.
   * @param {string} [dbName='factoidal-delta-log']
   * @returns {Promise<{dbName: string}>}
   */
  async function deltaLogOpen(dbName) {
    const name = dbName == null || dbName === '' ? DEFAULT_DELTA_DB_NAME : String(dbName);
    await deltaLogStore.open(name);
    return { dbName: name };
  }

  /**
   * Append one SPARQL Update request as one record (op deltaLogEncode).
   * INSERT DATA, DELETE DATA, CLEAR DEFAULT, CLEAR GRAPH, DROP GRAPH and
   * CREATE GRAPH are admitted; any other form rejects and nothing is
   * written. `seq` is the record's position in the log.
   * @param {{dbName: string}} handle
   * @param {string} sparqlUpdate
   * @param {{epoch?: number}} [options]
   * @returns {Promise<{seq: number, opCount: number}>}
   */
  async function deltaLogAppend(handle, sparqlUpdate, options) {
    requireDeltaHandle(handle, 'deltaLogAppend');
    if (typeof sparqlUpdate !== 'string') {
      throw new TypeError('deltaLogAppend: sparqlUpdate must be a string');
    }
    const epoch = (options && options.epoch) || 0;
    if (!Number.isSafeInteger(epoch) || epoch < 0) {
      throw new TypeError('deltaLogAppend: options.epoch must be a natural number');
    }
    const e = await entry();
    requireEntryFn(e, 'deltaLogEncode', 'deltaLogAppend');
    let opCount = 0;
    const { seq } = await deltaLogStore.append(handle.dbName, (nextSeq) => {
      const r = entryResult(e.deltaLogEncode(sparqlUpdate, String(nextSeq), String(epoch)),
        'deltaLogAppend');
      opCount = r.opCount;
      return { hex: r.hex, epoch };
    });
    return { seq, opCount };
  }

  /**
   * The records of the log, in commit order, as hexadecimal text joined by
   * "\n": the text deltaLogMerge() hands to the engine.
   * @param {{dbName: string}} handle
   * @returns {Promise<string>}
   */
  async function deltaLogReadAllHex(handle) {
    requireDeltaHandle(handle, 'deltaLogReadAllHex');
    return (await deltaLogStore.readAll(handle.dbName)).join('\n');
  }

  /**
   * Merge on read (op deltaLogMerge): the base dataset with the log's
   * batches applied in commit order, as N-Quads. A torn final record (an
   * append that did not complete) is not applied; deltaLogInspect() reports
   * it. A damaged record, or a record whose checksum verifies but whose
   * entries the engine cannot decode, makes the merge throw: the records
   * after it would otherwise be lost without a message
   * (https://github.com/danbri/factoidal/issues/843).
   * @param {{dbName: string}} handle
   * @param {string} baseNQuads the dataset before the log, as N-Quads
   * @returns {Promise<string>}
   */
  async function deltaLogMerge(handle, baseNQuads) {
    requireDeltaHandle(handle, 'deltaLogMerge');
    if (typeof baseNQuads !== 'string') {
      throw new TypeError('deltaLogMerge: baseNQuads must be a string');
    }
    const e = await entry();
    requireEntryFn(e, 'deltaLogMerge', 'deltaLogMerge');
    const logHex = await deltaLogReadAllHex(handle);
    return entryResult(e.deltaLogMerge(baseNQuads, logHex), 'deltaLogMerge').nquads;
  }

  /**
   * What the log holds (op deltaLogDecode): the number of batches and
   * entries that verify, whether the log ends with a torn record and its
   * size in bytes, and {seq, epoch, entries} for each batch. Throws for a
   * damaged record or a record whose entries the engine cannot decode
   * (https://github.com/danbri/factoidal/issues/843).
   * @param {{dbName: string}} handle
   * @returns {Promise<{batches: number, entries: number, torn: boolean,
   *   tornBytes: number, logBytes: number,
   *   records: Array<{seq: number, epoch: number, entries: number}>}>}
   */
  async function deltaLogInspect(handle) {
    requireDeltaHandle(handle, 'deltaLogInspect');
    const e = await entry();
    requireEntryFn(e, 'deltaLogDecode', 'deltaLogInspect');
    const { ok: _ok, ...rest } = entryResult(
      e.deltaLogDecode(await deltaLogReadAllHex(handle)), 'deltaLogInspect');
    return rest;
  }

  /**
   * Remove the log and its records.
   * @param {{dbName: string}} handle
   * @returns {Promise<void>}
   */
  async function deltaLogDestroy(handle) {
    requireDeltaHandle(handle, 'deltaLogDestroy');
    await deltaLogStore.destroy(handle.dbName);
  }

  /**
   * TEST ONLY: cut the last 4 bytes (8 hex digits) of the last record, as a
   * write torn by a crash would leave it. IndexedDB transactions are atomic,
   * so a page has no other way to make one. False when the log is empty.
   * @param {{dbName: string}} handle
   * @returns {Promise<boolean>}
   */
  async function _deltaLogCorruptLastForTest(handle) {
    requireDeltaHandle(handle, '_deltaLogCorruptLastForTest');
    return deltaLogStore.corruptLast(handle.dbName);
  }

  /**
   * Feature probe, for tests and downstream capability checks.
   * @returns {Promise<{entry: boolean, construct: boolean,
   *   update: boolean, canonicalize: boolean, graphs: boolean,
   *   canonicalHash: boolean, shacl: boolean, shex: boolean,
   *   owlClosure: boolean, explain: boolean, stages: boolean, rml: boolean, csvw: boolean, jsonld: boolean,
   *   rif: boolean}>}
   */
  let capsCache = null;
  async function capabilities() {
    if (capsCache) return capsCache;
    capsCache = capabilitiesUncached();
    return capsCache;
  }

  async function capabilitiesUncached() {
    const e = await entry();
    const has = (name) => typeof e[name] === 'function';
    return {
      entry: true, construct: true, update: true, canonicalize: true,
      graphs: true, canonicalHash: true,
      // Per-op probes: a wasm module older than this package reports the
      // ops it actually has.
      shacl: has('shaclValidate'),
      shex: has('shexValidate'),
      sparqlRl: has('datasetSparqlRlInfer'),
      owlClosure: has('owlClosure'),
      explain: has('explainGraph'),
      stages: has('stageList'),
      pipelineCheck: has('pipelineCheck'),
      pipelineCheckNodes: has('pipelineCheckNodes'),
      graphCheck: has('graphCheckNodes'),
      datasetMerge: has('datasetMerge'),
      entailment: has('queryRaw'),
      tableau: has('tableauMaterialise') && has('tableauDlInconsistent'),
      rml: has('rmlMap'),
      csvw: has('csvwToRdf'),
      jsonld: has('jsonldToRdf'),
      jsonldFromRdf: has('jsonldFromRdf'),
      didKey: has('didKeyResolve'),
      xml: has('xmlWellformed'),
      xpath: has('xpathEval'),
      rif: has('rifEval'),
      xslt: has('xsltTransform'),
      mathml: has('mathmlEval'),
      xforms: has('xformsRecalc'),
      jsonSchema: has('jsonSchemaValidate'),
      schematron: has('schematronValidate'),
      toan: has('toanSummation'),
      hdt: has('queryHdt'),
      // VC Data Integrity: Ed25519 is HACL* compiled into the wasm module,
      // SHA-256 is the Lean hash; no separate crypto module or init step.
      vcCrypto: has('vcEd25519Verify') && has('vcEddsaVerifyFromCanonical'),
      profile: e.profile || 'full',
      abiVersion: e.abiVersion,
      datasetHandles: has('datasetOpen') && has('datasetQuery') &&
        has('datasetUpdate') && has('datasetSerialize') && has('datasetClose'),
      datasetInEngine: has('datasetClone') && has('datasetClosure') && has('datasetQueryRaw'),
      sparql12: has('queryDataset12') && has('datasetQuery12'),
      parseDiagnostics: has('parseDocument'),
      turtlePrefixes: has('serializeTurtleWith'),
      store: has('storeOpen') && has('storeHandleQuery'),
      deltaLog: has('deltaLogEncode') && has('deltaLogDecode') && has('deltaLogMerge'),
      literalValues: has('literalValue') && has('literalFromValue'),
    };
  }

  // ---------------------------------------------------------------
  // Literal values (https://github.com/danbri/factoidal/issues/1051 items 1-3).
  // The ops literalValue and literalFromValue (formal/lean4/Wasm/Ops/
  // LiteralValue.lean, over L4Factoidal.RDF.LiteralValue) make every
  // decision: the XSD lexical-to-value mapping, validity, the canonical form,
  // the datatype of a JavaScript value. These functions are SYNCHRONOUS, so a
  // library-style API can call them in a getter; the engine must be loaded
  // first (await ready(), or any other call).
  // ---------------------------------------------------------------
  function loadedEntry(who) {
    if (!ctxCache) {
      throw new FactoidalError(
        `${who}: the engine is not loaded yet. Await any @factoidal/core call ` +
        'first (for example `await ready()`); after that this function is synchronous.',
        { code: 'op.unknown' });
    }
    return ctxCache.e;
  }

  function literalAnswer(term, who) {
    if (!term || typeof term !== 'object' || term.termType !== 'Literal') {
      throw new TypeError(`${who}: expected an RDF/JS Literal term`);
    }
    const e = loadedEntry(who);
    requireEntryFn(e, 'literalValue', who);
    return entryResult(e.literalValue(JSON.stringify(termToJson(term))), who);
  }

  // NaN and the infinities have no JSON number; the engine names them in
  // `special`, and this copies the matching JavaScript number in.
  const SPECIAL_NUMBERS = { NaN: NaN, INF: Infinity, '-INF': -Infinity };
  function valueOut(v) {
    if (v && typeof v.special === 'string' && v.special in SPECIAL_NUMBERS) {
      return { ...v, number: SPECIAL_NUMBERS[v.special] };
    }
    // A JSON text -0 may reach this layer as 0; negativeZero is the engine's
    // statement of the sign.
    if (v && v.negativeZero === true) return { ...v, number: -0 };
    return v;
  }

  /**
   * The value of a literal: {datatype, recognized, valid, value?, canonical?}.
   * `recognized` false: the engine has no lexical space for the datatype, and
   * `valid` is null. `value` and `canonical` are present for a valid literal
   * of a datatype with a value model (the shapes are in API.md).
   */
  function literalValue(term) {
    const r = literalAnswer(term, 'literalValue');
    const out = { datatype: r.datatype, recognized: r.recognized,
      valid: r.recognized ? r.valid : null };
    if (r.value !== undefined) out.value = valueOut(r.value);
    if (r.canonical !== undefined) out.canonical = r.canonical;
    return out;
  }

  /** true or false: the lexical form is in the datatype's lexical space;
   * null: the engine has no lexical space for the datatype. */
  function isValidLiteral(term) {
    const r = literalAnswer(term, 'isValidLiteral');
    return r.recognized ? r.valid : null;
  }

  /** The literal with the canonical lexical form of its value (XSD 1.1 Part 2
   * section 2.3.1), the same datatype and language; null when the literal is
   * not valid or the engine has no canonical mapping for its datatype. */
  function canonicalLiteral(term) {
    const r = literalAnswer(term, 'canonicalLiteral');
    if (r.canonical === undefined) return null;
    if (term.language) return dataFactory.literal(r.canonical, term.direction
      ? { language: term.language, direction: term.direction } : term.language);
    return dataFactory.literal(r.canonical, dataFactory.namedNode(r.datatype));
  }

  /**
   * The literal of a JavaScript value. The engine chooses the datatype (table
   * in API.md) unless `options.datatype` names one (an IRI, a NamedNode, or
   * an XSD built-in local name such as 'int'); the value must then be in that
   * datatype's value space, else a FactoidalError with code literal.value.
   */
  function literalFromValue(value, options) {
    const who = 'literalFromValue';
    const tagged = encodeJsValue(value);
    if (!tagged) {
      throw new TypeError(`${who}: expected a boolean, number, bigint, string or Date`);
    }
    const dt = options && options.datatype;
    const hint = dt === undefined || dt === null ? ''
      : (typeof dt === 'string' ? dt : (dt && typeof dt.value === 'string' ? dt.value : null));
    if (hint === null) throw new TypeError(`${who}: options.datatype must be a string or a NamedNode`);
    const e = loadedEntry(who);
    requireEntryFn(e, 'literalFromValue', who);
    const r = entryResult(e.literalFromValue(JSON.stringify(tagged), hint), who);
    return dataFactory.literal(r.value, dataFactory.namedNode(r.datatype));
  }

  // The node-composition API (lib/nodes.mjs, issue 1002 step 2).
  const nodeApi = buildNodes({
    entry, entryResult, requireEntryFn, Dataset,
    parse, closure, shaclValidate, query, serialize, canonicalize, canonicalHash, explain, csvwToRdf,
    datasetMerge,
  });

  return {
    parse,
    query,
    queryHdt,
    update,
    openDataset,
    closure,
    formats,
    registerExtensionFunction,
    unregisterExtensionFunction,
    clearExtensionFunctions,
    registerServiceEndpoint,
    clearServiceEndpoints,
    serialize,
    canonicalize,
    graphs,
    canonicalHash,
    asDefaultGraph,
    shaclValidate,
    shexValidate,
    sparqlRlInfer,
    owlClosure,
    coreRdfsClosure,
    coreRdfsCheck,
    explain,
    stages: nodeApi.stages,
    node: nodeApi.node,
    pipe: nodeApi.pipe,
    graph: nodeApi.graph,
    run: nodeApi.run,
    rdfsPlusClosure,
    rhoDfClosure,
    rhoDfFragmentCheck,
    tableauMaterialise,
    tableauDlInconsistent,
    owlIsConsistent,
    owlEntails,
    rmlMap,
    csvwToRdf,
    jsonldToRdf,
    jsonldFromRdf,
    didKeyResolve,
    xmlWellformed,
    xpathEval,
    clParse,
    clSerialize,
    clAlphaNorm,
    clNormalize,
    rifEval,
    xsltTransform,
    mathmlEval,
    xformsRecalc,
    jsonSchemaValidate,
    schematronValidate,
    toanSummation,
    toanProduct,
    toanSimplify,
    toanDiff,
    toanSubst,
    vcSha256Hex,
    vcEd25519SecretToPublic,
    vcEd25519Sign,
    vcEd25519Verify,
    xmlDecrypt,
    xmlEncrypt,
    jweDecrypt,
    jweEncrypt,
    vcEddsaCreateFromCanonical,
    vcEddsaVerifyFromCanonical,
    vcCheckCredential,
    vcCheckCredentialSubject,
    vcCheckNoDataLoss,
    vcCheckRelatedResourceDigests,
    capabilities,
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
    queryRaw,
    isomorphic,
    datasetMerge,
    fromQuads,
    literalValue,
    isValidLiteral,
    canonicalLiteral,
    literalFromValue,
    ready,
    engineTables,
    sameValue,
    syntaxFor,
    splitIri,
    isNCName,
    vocabularies,
    memberIri,
    memberOrdinal,
    Dataset,
    Store,
    FactoidalError,
    dataFactory,
    // Metadata (issue #682): the same two fields on every driver's
    // typed surface, so a caller can log/report which package version
    // and which engine (js/wasm/entry/l4) answered a call without a
    // separate require('../package.json').
    version: packageVersion,
    engine: driver.engineName,
  };
}

export {
  buildApi, bindingsFromSrj, entryResult, parseResult,
  missingOpError, FactoidalError, Store,
};
