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

import { Dataset, dataFactory, termFromSrj } from '../rdfjs.mjs';
import { version as packageVersion } from './version.mjs';
import { openGeneration, readRegion, manifestKeys, hexOfBytes } from './store.mjs';

const DATA_FORMAT_EXT = {
  turtle:    'ttl',
  ttl:       'ttl',
  ntriples:  'nt',
  nt:        'nt',
  nquads:    'nq',
  nq:        'nq',
  trig:      'trig',
  rdfxml:    'rdf',
  'rdf-xml': 'rdf',
  rdf:       'rdf',
  jsonld:    'jsonld',
  'json-ld': 'jsonld',
  // RDF 1.2 opt-in: these select the engine's RDF 1.2 parsers (triple
  // terms <<( s p o )>>, ~ reifiers, {| |} annotations, VERSION,
  // directional literals "x"@lang--dir; Wasm/Ops/Parse.lean's
  // `Mode.rdf12`); the plain names above stay RDF 1.1.
  turtle12:   'ttl12',
  ttl12:      'ttl12',
  ntriples12: 'nt12',
  nt12:       'nt12',
  nquads12:   'nq12',
  nq12:       'nq12',
  trig12:     'trig12',
};

// Canonical format tag for the engine's parse ops (parseToDatasetJson,
// datasetOpen); the *12 tags select the RDF 1.2 mode.
const DATA_FORMAT_TAG = {
  ttl: 'turtle', nt: 'ntriples', nq: 'nquads', trig: 'trig', rdf: 'rdfxml',
  jsonld: 'jsonld',
  ttl12: 'turtle12', nt12: 'ntriples12', nq12: 'nquads12', trig12: 'trig12',
};

const ENTAIL_VALUES = new Set(['none', 'RDFS', 'OWL-RL', 'x-rdfscore', 'x-rdfsplus']);

// queryRaw's options (op queryRaw, Wasm/Ops/QueryExtras.lean).
const RAW_OUTPUT_FORMATS = new Set(['json', 'csv', 'tsv', 'xml', 'table', 'ntriples']);
const RAW_DATA_FORMATS = {
  turtle: 'turtle', ttl: 'turtle', ntriples: 'ntriples', nt: 'ntriples',
  nquads: 'nquads', nq: 'nquads', trig: 'trig', rdfxml: 'rdfxml',
  'rdf-xml': 'rdfxml', rdf: 'rdfxml',
};

function extForFormat(fmt) {
  const key = String(fmt || 'turtle').toLowerCase();
  if (!(key in DATA_FORMAT_EXT)) {
    throw new TypeError(
      `Unknown format '${fmt}'. Expected one of: ` +
      Object.keys(DATA_FORMAT_EXT).join(', ')
    );
  }
  return DATA_FORMAT_EXT[key];
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
// package, or a dispatch table that does not serve it).
function missingOpError(what) {
  return new Error(
    `${what}: the loaded Lean wasm module has no dispatch op for this ` +
    'operation. The module is older than this package; rebuild it with ' +
    'formal/lean4/Wasm/build-wasm.sh, or point FACTOIDAL_L4_ASSETS at a ' +
    'current build.');
}

// Detect the query form for result-shape dispatch. IRIs and comments
// are blanked first so '#' inside a PREFIX IRI cannot hide the verb.
// The engine's SPARQL parser remains the authority — this only picks
// the output shape.
function sniffQueryForm(sparql) {
  const cleaned = String(sparql)
    .replace(/<[^>]*>/g, ' ')
    .replace(/#[^\n]*/g, ' ');
  const m = cleaned.match(/\b(select|ask|construct|describe)\b/i);
  return m ? m[1].toLowerCase() : 'select';
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
function bindingsFromSrj(srj) {
  const rows = (srj && srj.results && srj.results.bindings) || [];
  return rows.map((row) => {
    const map = new Map();
    for (const [name, term] of Object.entries(row)) {
      map.set(name, termFromSrj(term));
    }
    return map;
  });
}

// ---------------------------------------------------------------------
// Strict parsing (issue #344) -- ParseError, and the shared envelope
// unwrapper every engine call routes through.
// ---------------------------------------------------------------------

/**
 * A parse failure that carries a position: `line`/`column`/`offset`
 * when the failing engine call reported one (a parseToDatasetJson or
 * datasetOpen error over Turtle, TriG, N-Triples or N-Quads), else
 * `undefined`. RDF/XML and JSON-LD failures, and any non-parse engine
 * error, stay plain Error -- entryResult() below decides which one to
 * throw.
 *
 * Units: `line` and `column` are 1-based; `column` counts Unicode scalar
 * values, as the engine reports it. `offset` is a UTF-16 code-unit index
 * into the input JavaScript string, so `text.slice(err.offset)` starts
 * at the error. The engine counts Unicode scalar values;
 * utf16OffsetOf() below converts.
 */
class ParseError extends Error {
  constructor(message, info) {
    super(message);
    this.name = 'ParseError';
    const i = info || {};
    this.line = i.line;
    this.column = i.column;
    this.offset = i.offset;
    this.format = i.format;
    if (typeof Error.captureStackTrace === 'function') {
      Error.captureStackTrace(this, ParseError);
    }
  }
}

// Unwrap one dispatch-op JSON envelope ({"ok":true,...} |
// {"ok":false,"error":...}). A `line` or `offset` member on the error
// envelope means the failing call was a parse (Turtle/TriG/N-Triples/
// N-Quads carry a position; RDF/XML and JSON-LD carry a message only)
// -- throw ParseError so a caller can branch on position without
// string-matching the message. Every other failure stays a plain
// Error, as before. Pure (no per-driver state), so every buildApi()
// instance and DatasetHandle share this one function.
function entryResult(jsonText, what) {
  const r = JSON.parse(jsonText);
  if (!r.ok) {
    if (r.line !== undefined || r.offset !== undefined) {
      throw new ParseError(`${what}: ${r.error}`, {
        line: r.line, column: r.column, offset: r.offset, format: r.format,
      });
    }
    throw new Error(`${what}: ${r.error}`);
  }
  return r;
}

// The Lean engine reports a parse error's `offset` as a count of Unicode
// scalar values from the start of the input. A JavaScript string is
// indexed in UTF-16 code units, where a character outside the Basic
// Multilingual Plane (U+10000 and above) takes two. This converts the
// engine's count into the UTF-16 index of the same position. A count past
// the end of the text gives text.length. Iterating a string with for..of
// yields one element per code point (a lone surrogate is one element, and
// the engine reads it as one replacement character), so both sides count
// the same units.
function utf16OffsetOf(text, scalarOffset) {
  if (typeof text !== 'string' || !Number.isInteger(scalarOffset) || scalarOffset < 0) {
    return scalarOffset;
  }
  let units = 0;
  let scalars = 0;
  for (const ch of text) {
    if (scalars >= scalarOffset) break;
    units += ch.length;
    scalars += 1;
  }
  return units;
}

// entryResult() for an op that parsed `text`: a positioned ParseError gets
// its offset converted to a UTF-16 index into `text`.
function parseResult(jsonText, what, text) {
  try {
    return entryResult(jsonText, what);
  } catch (err) {
    if (err instanceof ParseError && typeof err.offset === 'number') {
      err.offset = utf16OffsetOf(text, err.offset);
    }
    throw err;
  }
}

// ---------------------------------------------------------------------
// Dataset handles (issue #680) -- parse once via openDataset(), then
// query()/update()/serialize() many times against the engine's own
// cached, indexed copy instead of re-parsing N-Quads text and
// rebuilding the SPARQL index on every call (mirrors
// formal/lean4/Wasm/Ops/Handles.lean's op names/envelopes on the Lean
// side, the op names and envelopes).
//
// Module-level (like ParseError above), not defined inside buildApi():
// every method here needs only `entryResult`/`bindingsFromSrj`/
// `Dataset`/`pendingError`, which are all free of per-driver state.
// The two exceptions -- `freshBnodePrefix` (so toDataset()'s blank
// nodes don't collide with another parse from the same api instance)
// and `withExtensionRounds` (the same async-extension-function
// trampoline query()/update() use, since a handle's engine object `e`
// is the SAME entry object those register against) -- are per-driver
// closures, so openDataset() passes them in at construction time.
// ---------------------------------------------------------------------
class DatasetHandle {
  constructor(e, handle, size, prefixes, freshBnodePrefix, withExtensionRounds) {
    this._e = e;
    this._handle = handle;
    this._size = size;
    this._prefixes = Object.freeze({ ...(prefixes || {}) });
    this._closed = false;
    this._freshBnodePrefix = freshBnodePrefix;
    this._withExtensionRounds = withExtensionRounds;
  }
  /** The opaque engine handle id (e.g. "h1"). */
  get handle() { return this._handle; }
  /** Quad count as of the last open()/update(). */
  get size() { return this._size; }
  /** Prefixes recorded at open (or carried over from a Dataset argument). */
  get prefixes() { return this._prefixes; }
  /** True once close() has run -- every other method rejects after. */
  get closed() { return this._closed; }

  _assertOpen(who) {
    if (this._closed) {
      throw new Error(`DatasetHandle.${who}: handle '${this._handle}' is closed`);
    }
  }

  /**
   * Run a SPARQL 1.1 query against the stored dataset (no re-parse, no
   * backend rebuild).
   * @param {string} sparql
   * @param {{sparql12?: boolean, version?: string}} [options]
   * @returns {Promise<Array<Map<string, object>>|boolean|Dataset>}
   */
  async query(sparql, options) {
    this._assertOpen('query');
    if (typeof sparql !== 'string') {
      throw new TypeError('DatasetHandle.query: sparql must be a string');
    }
    const opts = options || {};
    const sparql12 = opts.sparql12 === true || String(opts.version || '') === '1.2';
    const fn = sparql12 ? this._e.datasetQuery12 : this._e.datasetQuery;
    if (typeof fn !== 'function') {
      throw missingOpError(`DatasetHandle.query (datasetQuery${sparql12 ? '12' : ''})`);
    }
    const run = () => entryResult(fn(this._handle, sparql), 'query');
    const r = this._withExtensionRounds ? await this._withExtensionRounds(run) : run();
    if (r.kind === 'ask') return r.boolean;
    if (r.kind === 'construct' || r.kind === 'describe') {
      return Dataset.fromNQuads(r.nquads, { blankNodePrefix: this._freshBnodePrefix(), prefixes: { ...this._prefixes } });
    }
    return bindingsFromSrj(r.srj);
  }

  /**
   * Apply a SPARQL 1.1 Update to the stored dataset IN PLACE (the
   * stored dataset is replaced and its backend rebuilt).
   * @param {string} updateText
   * @returns {Promise<DatasetHandle>} this handle, refreshed.
   */
  async update(updateText) {
    this._assertOpen('update');
    if (typeof updateText !== 'string') {
      throw new TypeError('DatasetHandle.update: updateText must be a string');
    }
    if (typeof this._e.datasetUpdate !== 'function') {
      throw missingOpError('DatasetHandle.update');
    }
    const r = entryResult(this._e.datasetUpdate(this._handle, updateText), 'update');
    this._size = r.count;
    return this;
  }

  /**
   * Serialize the stored dataset. 'turtle' uses the handle's own
   * recorded prefixes (from openDataset(), or from a Dataset
   * argument's `.prefixes`) automatically; pass `prefixes` to add to
   * them or `literalShorthand:false` to turn off the bare-literal
   * shorthand -- either forces the prefix/shorthand-aware ABI call.
   * @param {{format?: 'nquads'|'turtle'|'ttl', prefixes?: object,
   *   literalShorthand?: boolean}} [options]
   * @returns {Promise<string>}
   */
  async serialize(options) {
    this._assertOpen('serialize');
    const opts = optionsOf('DatasetHandle.serialize', options);
    const rawOut = String(opts.format || 'nquads').toLowerCase();
    const outFormat = rawOut === 'ttl' ? 'turtle' : rawOut;
    if (outFormat !== 'nquads' && outFormat !== 'turtle') {
      throw new TypeError("DatasetHandle.serialize: format must be 'nquads' or 'turtle'");
    }
    if (outFormat === 'turtle') {
      const mergedPrefixes = { ...this._prefixes, ...(opts.prefixes || {}) };
      const needsWith = Object.keys(mergedPrefixes).length > 0 ||
        opts.literalShorthand !== undefined;
      if (needsWith) {
        if (typeof this._e.datasetSerializeWith !== 'function') {
          throw missingOpError('DatasetHandle.serialize (prefixes/literalShorthand)');
        }
        const optionsJson = JSON.stringify({
          prefixes: mergedPrefixes,
          ...(opts.literalShorthand !== undefined ? { literalShorthand: !!opts.literalShorthand } : {}),
        });
        return entryResult(
          this._e.datasetSerializeWith(this._handle, 'turtle', optionsJson), 'serialize').turtle;
      }
    }
    if (typeof this._e.datasetSerialize !== 'function') throw missingOpError('DatasetHandle.serialize');
    const r = entryResult(this._e.datasetSerialize(this._handle, outFormat), 'serialize');
    return outFormat === 'turtle' ? r.turtle : r.nquads;
  }

  /** Materialize the stored dataset as a heap Dataset. */
  async toDataset() {
    const nq = await this.serialize({ format: 'nquads' });
    return Dataset.fromNQuads(nq, {
      blankNodePrefix: this._freshBnodePrefix(),
      prefixes: this._prefixes,
    });
  }

  /** RDFC-1.0 canonical N-Quads of the stored dataset. */
  async canonicalize() {
    this._assertOpen('canonicalize');
    const nq = await this.serialize({ format: 'nquads' });
    if (typeof this._e.canonicalizeToNQuads !== 'function') {
      throw missingOpError('DatasetHandle.canonicalize');
    }
    return entryResult(this._e.canonicalizeToNQuads(nq), 'canonicalize').nquads;
  }

  /** Release the handle. Idempotent; every other method rejects after. */
  async close() {
    if (this._closed) return;
    this._closed = true;
    if (typeof this._e.datasetClose !== 'function') return;
    entryResult(this._e.datasetClose(this._handle), 'close');
  }
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
  constructor(e, env, gen, manifestHex, freshBnodePrefix, withExtensionRounds) {
    this._e = e;
    this._env = env;
    this._gen = gen;
    this._manifestHex = manifestHex;
    this._closed = false;
    this._freshBnodePrefix = freshBnodePrefix;
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
    if (this._closed) throw new Error(`Store.${who}: store handle '${this.handle}' is closed`);
  }

  /**
   * One SPARQL 1.1 query against the retained blocks.
   * @param {string} sparql
   * @returns {Promise<Array<Map<string, object>>|boolean|Dataset>}
   */
  async query(sparql) {
    this._assertOpen('query');
    if (typeof sparql !== 'string') throw new TypeError('Store.query: sparql must be a string');
    const run = () => entryResult(this._e.storeHandleQuery(this.handle, sparql), 'Store.query');
    const r = this._withExtensionRounds ? await this._withExtensionRounds(run) : run();
    if (r.kind === 'ask') return r.boolean;
    if (r.kind === 'construct' || r.kind === 'describe') {
      return Dataset.fromNQuads(r.nquads, { blankNodePrefix: this._freshBnodePrefix() });
    }
    return bindingsFromSrj(r.srj);
  }

  /** The manifest, decoded by the engine (op storeManifestInspect). */
  async inspect() {
    const r = entryResult(this._e.storeManifestInspect(this._manifestHex), 'Store.inspect');
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
 */
function buildApi(driver) {
  let parseCounter = 0;
  let entryPromise; // memoized; a failed load is retried on the next call

  // The entry object. A failure to load the engine (assets missing, a
  // wasm that does not instantiate) rejects every operation with that
  // failure's own message; there is no other engine to fall back to.
  async function entry() {
    if (!entryPromise) {
      entryPromise = Promise.resolve()
        .then(() => driver.loadEntry())
        .then((e) => {
          if (!e) throw new Error('factoidal: the engine loader returned no entry object');
          return e;
        })
        .catch((err) => { entryPromise = undefined; throw err; });
    }
    return entryPromise;
  }

  // entryResult() is now module-level (see above ParseError) -- pure,
  // shared by every buildApi() instance and by DatasetHandle.

  function freshBnodePrefix() {
    return `p${parseCounter++}_`;
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
    const docs = toDocs(data, options);
    const nq = docsToEntryNQuads(e, docs, 'registerServiceEndpoint');
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
        throw new Error(
          'extension functions: async resolution did not converge ' +
          `within ${EXT_MAX_ROUNDS} evaluation rounds`);
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

  // Normalize the `data` argument of query/update/serialize/
  // canonicalize into engine inputs. Accepts a Dataset, a raw string
  // (with options.format, default turtle), or an array of those —
  // each element is loaded as its own document so blank-node labels
  // stay document-scoped (the engine's IO entry gives every parsed
  // document its own blank-node scope, Wasm/Dispatch.lean's
  // parseToDatasetJsonScoped).
  function toDocs(data, options) {
    const opts = optionsOf('data', options);
    const items = Array.isArray(data) ? data : [data];
    return items.map((item, i) => {
      if (item instanceof Dataset) {
        return { ext: 'nq', content: item.toNQuads() };
      }
      if (typeof item === 'string') {
        return { ext: extForFormat(opts.format), content: item };
      }
      if (item && typeof item.text === 'string') {
        return { ext: extForFormat(item.format || opts.format), content: item.text };
      }
      throw new TypeError(
        `data[${i}]: expected a Dataset, a string, or {text, format}`);
    });
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

  // Normalize toDocs() output into one concatenated N-Quads string: each
  // non-N-Quads document goes through parseToDatasetJson (its own
  // blank-node scope), N-Quads text is passed on as it is. Every
  // operation that takes `data` hands the engine this string. A parse
  // failure rejects with a ParseError whose offset indexes that
  // document's own text.
  function docsToEntryNQuads(e, docs, what) {
    let nq = '';
    for (const d of docs) {
      if (d.ext === 'nq') { nq += d.content; continue; }
      const r = parseResult(
        e.parseToDatasetJson(d.content, DATA_FORMAT_TAG[d.ext], ''),
        `${what}(parse)`, d.content);
      nq += r.nquads;
    }
    return nq;
  }

  // A ShEx focus/shape-label argument is either a raw string (an IRI,
  // or "_:label" for a blank node -- the entry ABI's own convention)
  // or an RDF/JS term (NamedNode/BlankNode); accepting both lets a
  // caller pass a term straight out of a query() binding.
  function shexTermToString(t, who) {
    if (typeof t === 'string') return t;
    if (t && typeof t.termType === 'string') {
      if (t.termType === 'BlankNode') return `_:${t.value}`;
      if (t.termType === 'NamedNode') return t.value;
      throw new TypeError(`${who}: expected an IRI or blank node term`);
    }
    throw new TypeError(`${who}: expected a string or an RDF/JS term`);
  }

  // Everything below is async: the engine loads asynchronously, and an
  // extension function may answer with a Promise.

  /**
   * Parse one RDF document into a Dataset. Strict by default (issue
   * #344): a syntax error, an undeclared prefix, or an unresolvable
   * relative IRI (no baseIRI in effect) rejects with a ParseError
   * (`line`/`column`/`offset` present for Turtle/TriG/N-Triples/
   * N-Quads; RDF/XML and JSON-LD failures carry a message only).
   * `{lenient:true}` needs the engine op parseDocument, which the Lean
   * engine does not have yet (https://github.com/danbri/factoidal/issues/716);
   * it rejects naming the op.
   * @param {string} text
   * @param {{format?: string, baseIRI?: string, lenient?: boolean}} [options]
   * @returns {Promise<Dataset>}
   */
  async function parse(text, options) {
    if (typeof text !== 'string') {
      throw new TypeError('parse: text must be a string');
    }
    const opts = optionsOf('parse', options);
    const ext = extForFormat(opts.format);
    const baseIRI = opts.baseIRI || '';
    const bnodePrefix = freshBnodePrefix();

    const e = await entry();
    if (opts.lenient) {
      if (typeof e.parseDocument !== 'function') {
        throw missingOpError('parse {lenient:true} (parseDocument)');
      }
      const r = parseResult(
        e.parseDocument(text, DATA_FORMAT_TAG[ext], baseIRI, JSON.stringify({ lenient: true })),
        'parse', text);
      return Dataset.fromNQuads(r.nquads, {
        blankNodePrefix: bnodePrefix,
        prefixes: r.prefixes,
        diagnostics: r.diagnostics,
      });
    }
    const r = parseResult(
      e.parseToDatasetJson(text, DATA_FORMAT_TAG[ext], baseIRI), 'parse', text);
    return Dataset.fromNQuads(r.nquads, {
      blankNodePrefix: bnodePrefix,
      prefixes: r.prefixes,
    });
  }

  /**
   * Run a SPARQL 1.1 query.
   * @param {Dataset|string|Array} data
   * @param {string} sparql
   * @param {{format?: string, entail?: 'none'|'RDFS'|'OWL-RL'|'x-rdfscore'|'x-rdfsplus',
   *   sparql12?: boolean, version?: string}} [options]
   * @returns {Promise<Array<Map<string, object>>|boolean|Dataset>}
   *   SELECT -> Bindings[] (Map of variable name -> RDF/JS Term),
   *   ASK -> boolean, CONSTRUCT and DESCRIBE -> Dataset.
   */
  async function query(data, sparql, options) {
    if (typeof sparql !== 'string') {
      throw new TypeError('query: sparql must be a string');
    }
    const opts = optionsOf('query', options);
    const entail = opts.entail || 'none';
    // x-ikl-* is NOT IMPLEMENTED. It is not withheld by policy.
    //
    // CORRECTION 2026-08-26: this comment previously cited the owner's
    // direction-B ruling (danbri/factoidal#618) as the reason. That
    // ruling was about the IKL-to-RDF projection, not this regime
    // family, and citing it here misstated a decision the owner did
    // not make. The family is the OWNER'S design
    // (danbri/factoidal#581); its Lean dispatch was deleted on
    // 2026-08-26 as collateral of the projection purge
    // (danbri/factoidal#626), not as its target. The semantics
    // survived -- Unified/ClBridge.lean's asserted_merge_sound is the
    // regime's soundness statement -- so restoring it is a dispatch
    // branch, not a redesign. Checked explicitly (not just left out of
    // ENTAIL_VALUES below) so a future ENTAIL_VALUES edit can't
    // reopen this without deliberately removing this check too; see
    // test/select.test.js's regression test.
    if (/^x-ikl/i.test(entail)) {
      throw new TypeError(
        `query: entail '${entail}' is not implemented. The x-ikl-* ` +
        "entailment regimes are the owner's design " +
        "(danbri/factoidal#581); the Lean engine's dispatch for them " +
        'was deleted on 2026-08-26 as collateral of the IKL-to-RDF ' +
        'projection purge (danbri/factoidal#626). This is not a ' +
        'policy exclusion.');
    }
    if (!ENTAIL_VALUES.has(entail)) {
      throw new TypeError(
        `query: entail must be one of ${[...ENTAIL_VALUES].join(', ')}`);
    }

    if (data instanceof DatasetHandle) {
      if (entail !== 'none') {
        throw new TypeError(
          "query: entail must be 'none' when data is a DatasetHandle " +
          '(a handle carries no entailment-closure step)');
      }
      return data.query(sparql, opts);
    }

    const form = sniffQueryForm(sparql);
    const docs = toDocs(data, opts);
    const e = await entry();
    const nq = docsToEntryNQuads(e, docs, 'query');
    // SPARQL 1.2 opt-in: {sparql12:true} or {version:'1.2'} routes to the
    // op queryDataset12 (the Lean SPARQL parser's 1.2 mode: triple-term
    // patterns, reified triples, annotations, TRIPLE/isTRIPLE/SUBJECT/
    // PREDICATE/OBJECT). The default stays SPARQL 1.1.
    const sparql12 = opts.sparql12 === true || String(opts.version || '') === '1.2';

    if (entail !== 'none') {
      // An entailment regime: the engine closes the DEFAULT graph under the
      // regime, then evaluates the query (one op, queryRaw, in
      // Wasm/Ops/QueryExtras.lean). Extension functions and SERVICE
      // registrations are not in scope on this path.
      if (sparql12) {
        throw new TypeError(
          "query: entail and SPARQL 1.2 cannot be combined; the entailment path reads SPARQL 1.1");
      }
      requireEntryFn(e, 'queryRaw', `query {entail:'${entail}'}`);
      const graphForm = form === 'construct' || form === 'describe';
      const r = entryResult(e.queryRaw(nq, sparql, JSON.stringify({
        dataFormat: 'nquads', entail, output: graphForm ? 'ntriples' : 'json',
      })), 'query');
      if (graphForm) {
        return Dataset.fromNQuads(r.text, {
          blankNodePrefix: freshBnodePrefix(),
          prefixes: prefixesOfData(data),
        });
      }
      const srj = JSON.parse(r.text);
      if (typeof srj.boolean === 'boolean') return srj.boolean;
      return bindingsFromSrj(srj);
    }

    if (sparql12 && typeof e.queryDataset12 !== 'function') {
      throw missingOpError('query {sparql12:true} (queryDataset12)');
    }
    const r = await withExtensionRounds(() => entryResult(
      (sparql12 ? e.queryDataset12 : e.queryDataset)(nq, sparql), 'query'));
    if (r.kind === 'ask') return r.boolean;
    if (r.kind === 'construct' || r.kind === 'describe') {
      return Dataset.fromNQuads(r.nquads, {
        blankNodePrefix: freshBnodePrefix(),
        prefixes: prefixesOfData(data),
      });
    }
    return bindingsFromSrj(r.srj);
  }

  /**
   * Run a SPARQL 1.1 query against a read-only HDT (Header-Dictionary-
   * Triples) file's raw bytes. The bytes travel to the engine as the
   * dispatch ABI's byte region (op queryHdt, Wasm/Ops/QueryExtras.lean),
   * with no text encoding. Default graph only (an HDT file holds one
   * graph); SELECT and ASK only.
   * @param {Uint8Array|ArrayBuffer|Buffer|string} hdtBytes whole .hdt
   *   file contents (a string is read as one char per byte)
   * @param {string} sparql a SELECT or ASK query
   * @returns {Promise<Array<Map<string, object>>|boolean>}
   */
  async function queryHdt(hdtBytes, sparql) {
    if (typeof sparql !== 'string') {
      throw new TypeError('queryHdt: sparql must be a string');
    }
    const form = sniffQueryForm(sparql);
    if (form === 'construct' || form === 'describe') {
      throw new TypeError(
        `queryHdt: ${form.toUpperCase()} is not supported over an HDT file (SELECT/ASK only)`);
    }
    const e = await entry();
    requireEntryFn(e, 'queryHdt', 'queryHdt');
    const r = entryResult(e.queryHdt(bytesToUint8Array(hdtBytes, 'queryHdt'), sparql), 'queryHdt');
    if (r.kind === 'ask') return r.boolean;
    return bindingsFromSrj(r.srj);
  }

  /**
   * Apply a SPARQL 1.1 Update to a dataset, returning the new Dataset.
   * @param {Dataset|string|Array} data
   * @param {string} updateText
   * @param {{format?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function update(data, updateText, options) {
    if (typeof updateText !== 'string') {
      throw new TypeError('update: updateText must be a string');
    }
    if (data instanceof DatasetHandle) {
      throw new TypeError(
        'update: data is a DatasetHandle; call handle.update() directly ' +
        '-- update() always returns a FRESH Dataset, but a handle\'s own ' +
        'update() mutates the handle in place and returns the handle.');
    }
    const e = await entry();
    const opts = optionsOf('update', options);
    const nq = docsToEntryNQuads(e, toDocs(data, opts), 'update');
    const sparql12 = opts.sparql12 === true || String(opts.version || '') === '1.2';
    if (sparql12 && typeof e.updateDataset12 !== 'function') {
      throw missingOpError('update {sparql12:true} (updateDataset12)');
    }
    const r = entryResult(
      (sparql12 ? e.updateDataset12 : e.updateDataset)(nq, updateText), 'update');
    return Dataset.fromNQuads(r.nquads, {
      blankNodePrefix: freshBnodePrefix(),
      prefixes: prefixesOfData(data),
    });
  }

  /**
   * Open a dataset handle (issue #680): parse `data` once, then run
   * many query()/update()/serialize() calls against the engine's own
   * cached, indexed copy -- no re-parse, no SPARQL-index rebuild per
   * call (see the tests/perf/npm_handle_vs_stateless.mjs numbers for
   * the measured difference).
   * @param {Dataset|string|Array|{text,format}} data a Dataset (opened
   *   as N-Quads, keeping the Dataset's own `.prefixes` on the handle
   *   for Turtle output), a string (`options.format`/`baseIRI` apply),
   *   or an array of those (each non-N-Quads document normalizes
   *   through parseToDatasetJson first, then the whole array opens as
   *   one N-Quads document -- no per-document prefixes survive that
   *   merge).
   * @param {{format?: string, baseIRI?: string}} [options]
   * @returns {Promise<DatasetHandle>}
   */
  async function openDataset(data, options) {
    const e = await entry();
    requireEntryFn(e, 'datasetOpen', 'openDataset');
    const opts = optionsOf('openDataset', options);

    if (data instanceof Dataset) {
      const r = entryResult(e.datasetOpen(data.toNQuads(), 'nquads', ''), 'openDataset');
      return new DatasetHandle(e, r.handle, r.count, data.prefixes, freshBnodePrefix, withExtensionRounds);
    }
    if (typeof data === 'string') {
      const ext = extForFormat(opts.format);
      const baseIRI = opts.baseIRI || '';
      const r = parseResult(
        e.datasetOpen(data, DATA_FORMAT_TAG[ext], baseIRI), 'openDataset', data);
      return new DatasetHandle(e, r.handle, r.count, r.prefixes, freshBnodePrefix, withExtensionRounds);
    }
    const docs = toDocs(data, opts);
    const nq = docsToEntryNQuads(e, docs, 'openDataset');
    const r = entryResult(e.datasetOpen(nq, 'nquads', ''), 'openDataset');
    return new DatasetHandle(e, r.handle, r.count, {}, freshBnodePrefix, withExtensionRounds);
  }

  /**
   * Serialize a dataset (engine-produced bytes, sorted N-Quads order).
   * @param {Dataset|string|Array|DatasetHandle} data a DatasetHandle
   *   routes to `data.serialize(options)`.
   *   'nquads' and 'ntriples' answer the engine's N-Quads text in sorted
   *   line order; 'ntriples' refuses data with a named graph.
   * @param {{format?: 'nquads'|'ntriples'|'turtle', inputFormat?: string,
   *   prefixes?: object, literalShorthand?: boolean}} [options]
   *   `prefixes`/`literalShorthand` apply to 'turtle' only.
   * @returns {Promise<string>}
   *   'turtle' (prefix-compacted, subject-grouped; the ops
   *   serializeTurtle/serializeTurtleWith, Syntax/TurtleSerialize.lean)
   *   flattens every named graph into the default graph
   *   (Turtle has no named-graph notion); use 'nquads' when graph
   *   names must survive. `prefixes` is used, and unused caller
   *   namespaces are dropped, when given or when `data` is a Dataset
   *   with non-empty `.prefixes` (that Dataset's own prefixes are used
   *   automatically); `literalShorthand` (default true) controls
   *   whether xsd:integer/decimal/double/boolean literals with a
   *   Turtle-grammar-matching lexical form print bare.
   */
  async function serialize(data, options) {
    const opts = optionsOf('serialize', options);
    if (data instanceof DatasetHandle) {
      return data.serialize(opts);
    }
    const rawOut = String(opts.format || 'nquads').toLowerCase();
    const outFormat = rawOut === 'ttl' ? 'turtle' : rawOut;
    if (outFormat !== 'nquads' && outFormat !== 'ntriples' && outFormat !== 'turtle') {
      throw new TypeError(
        "serialize: format must be 'nquads', 'ntriples', or 'turtle'");
    }
    const docs = toDocs(data, { format: opts.inputFormat });

    const e = await entry();
    if (outFormat === 'turtle') {
      const nq = docsToEntryNQuads(e, docs, 'serialize(turtle)');
      const dataPrefixes = (data instanceof Dataset) ? data.prefixes : null;
      const hasOptions = opts.prefixes !== undefined || opts.literalShorthand !== undefined;
      const useWith = hasOptions || (dataPrefixes && Object.keys(dataPrefixes).length > 0);
      if (useWith) {
        requireEntryFn(e, 'serializeTurtleWith', 'Turtle serialization (prefixes/literalShorthand)');
        const mergedPrefixes = { ...(dataPrefixes || {}), ...(opts.prefixes || {}) };
        const optionsJson = JSON.stringify({
          prefixes: mergedPrefixes,
          ...(opts.literalShorthand !== undefined ? { literalShorthand: !!opts.literalShorthand } : {}),
        });
        return entryResult(e.serializeTurtleWith(nq, optionsJson), 'serialize').turtle;
      }
      requireEntryFn(e, 'serializeTurtle', 'Turtle serialization');
      return entryResult(e.serializeTurtle(nq), 'serialize').turtle;
    }

    // N-Quads, sorted (the engine's canonical N-Quads line order).
    // 'ntriples' is the same text when every quad is in the default
    // graph; N-Triples has no graph term, so data with a named graph is
    // refused for that format rather than flattened.
    const nq = docs.every((d) => d.ext === 'nq')
      ? docs.map((d) => d.content).join('')
      : docsToEntryNQuads(e, docs, `serialize(${outFormat})`);
    const out = entryResult(e.serializeNQuads(nq), 'serialize').nquads;
    if (outFormat === 'ntriples') {
      for (const q of Dataset.fromNQuads(out)) {
        if (q.graph.termType !== 'DefaultGraph') {
          throw new TypeError(
            "serialize: format 'ntriples' holds one graph and the data has a " +
            "named graph; use format 'nquads'");
        }
      }
    }
    return out;
  }

  /**
   * RDFC-1.0 canonicalization: canonical blank-node labels + sorted
   * canonical N-Quads.
   * @param {Dataset|string|Array} data
   * @param {{format?: string}} [options]
   * @returns {Promise<string>}
   */
  async function canonicalize(data, options) {
    if (data instanceof DatasetHandle) {
      return data.canonicalize();
    }
    const docs = toDocs(data, optionsOf('canonicalize', options));
    const e = await entry();
    const nq = docsToEntryNQuads(e, docs, 'canonicalize');
    return entryResult(e.canonicalizeToNQuads(nq), 'canonicalize').nquads;
  }

  /**
   * Enumerate the named graphs of an already-parsed Dataset.
   *
   * Graphs-api design (docs/designissues/2026-07-05-graphs-api-design.md
   * section 1.3): DatasetCore.match(null,null,null,graphNode) already
   * gives per-graph read access, but match() alone cannot answer "what
   * graph names exist" -- this is exactly that enumeration, and only
   * that: it walks quads already produced by the engine's parser, so
   * it needs no engine round-trip (no new RDF/SPARQL semantics, rule
   * #11 stays satisfied trivially).
   *
   * @param {Dataset} dataset
   * @returns {Array<[iri: string, graph: Dataset]>}
   *   default graph excluded, first-seen order.
   */
  function graphs(dataset) {
    if (!(dataset instanceof Dataset)) {
      throw new TypeError('graphs: expected a Dataset');
    }
    const seen = new Map(); // iri -> graph term (first occurrence)
    for (const q of dataset) {
      const g = q.graph;
      if (!g || g.termType === 'DefaultGraph') continue;
      if (!seen.has(g.value)) seen.set(g.value, g);
    }
    const out = [];
    for (const [iri, gTerm] of seen) {
      out.push([iri, dataset.match(null, null, null, gTerm)]);
    }
    return out;
  }

  /**
   * RDFC-1.0 canonical hash of a single graph -- the graph-scoped
   * sibling of canonicalize(), gated via capabilities() the same way
   * (docs/designissues/2026-07-05-graphs-api-design.md section 1.3).
   * Accepts a whole dataset or (more usually) one entry of graphs()'s
   * output; either way, every quad's graph component is dropped before
   * canonicalizing, matching RDF.Canonical.fst's
   * canonicalize_named_graph, which projects the named graph into
   * `{ ds_default = g; ds_named = [] }` before reusing
   * canonicalize_to_nquads unmodified.
   *
   * @param {Dataset} datasetOrGraph
   * @returns {Promise<string>} canonical N-Quads text for that graph alone.
   */
  async function canonicalHash(datasetOrGraph) {
    if (!(datasetOrGraph instanceof Dataset)) {
      throw new TypeError(
        'canonicalHash: expected a Dataset (e.g. one entry of graphs())');
    }
    const asDefaultGraph = new Dataset(
      datasetOrGraph.toArray().map(
        (q) => dataFactory.quad(q.subject, q.predicate, q.object)));
    return canonicalize(asDefaultGraph.toNQuads(), { format: 'nquads' });
  }

  // A wasm module older than this package can lack an op: `e[fnName]` is
  // then undefined, which would otherwise surface as "e.x is not a
  // function". Fail with missingOpError(), which names the op.
  function requireEntryFn(e, fnName, what) {
    if (typeof e[fnName] !== 'function') throw missingOpError(what);
  }

  /**
   * SHACL validation (op shaclValidate, Wasm/Ops/Validate.lean): SHACL
   * Core, SHACL-SPARQL constraints and SHACL 1.2 node expressions, over
   * the default graph of each argument. A shapes graph with a feature
   * the validator does not read (the SPARQL-based target of SHACL-AF)
   * and a validation failure (SHACL 5.3.2) reject.
   * @param {Dataset|string|Array} data
   * @param {Dataset|string|Array} shapes
   * @param {{format?: string}} [options] applies to both data and shapes
   * @returns {Promise<{conforms: boolean, report: Dataset}>}
   *   report is the validation report graph (one sh:ValidationReport
   *   with sh:conforms, and one sh:result per validation result).
   */
  async function shaclValidate(data, shapes, options) {
    const e = await entry();
    requireEntryFn(e, 'shaclValidate', 'SHACL validation');
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'shaclValidate(data)');
    const shapesNq = docsToEntryNQuads(e, toDocs(shapes, options), 'shaclValidate(shapes)');
    const r = entryResult(e.shaclValidate(dataNq, shapesNq), 'shaclValidate');
    return {
      conforms: r.conforms,
      report: Dataset.fromNQuads(r.reportNquads, {
        blankNodePrefix: freshBnodePrefix(),
      }),
    };
  }

  /**
   * ShEx (Shape Expressions) validation of one focus node against one
   * shape (op shexValidate, Wasm/Ops/Validate.lean), over the default
   * graph of `data`.
   * @param {Dataset|string|Array} data
   * @param {string} schemaJson the schema, as text -- either ShExJ (a
   *   JSON Schema document) or ShExC (the compact human-readable
   *   syntax; L4Factoidal/ShEx/Compact.lean). Dispatch rule: the schema
   *   text's first non-whitespace character decides the format -- '{'
   *   means ShExJ, anything else is parsed as ShExC. No separate flag
   *   or file-extension hint is needed; a schema whose ShExC text
   *   happens to start with whitespace then '{' would misdetect, but no
   *   valid ShExC document starts that way (ShExC always opens with a
   *   directive keyword, a shape label, or START).
   * @param {string|{termType,value}} focus an IRI, "_:label", or an
   *   RDF/JS NamedNode/BlankNode term
   * @param {string|{termType,value}|null} [shape] a shape label (same
   *   shapes as focus); omit/null to validate against the schema's own `start`
   * @param {{format?: string}} [options]
   * @returns {Promise<boolean>} the verdict. (The type allows null for
   *   an engine that defers a schema; the Lean validator decides every
   *   schema it reads.)
   */
  async function shexValidate(data, schemaJson, focus, shape, options) {
    const e = await entry();
    requireEntryFn(e, 'shexValidate', 'ShEx validation');
    if (typeof schemaJson !== 'string') {
      throw new TypeError('shexValidate: schemaJson must be a string');
    }
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'shexValidate(data)');
    const focusStr = shexTermToString(focus, 'shexValidate(focus)');
    const shapeStr = shape == null ? '' : shexTermToString(shape, 'shexValidate(shape)');
    const r = entryResult(
      e.shexValidate(dataNq, schemaJson, focusStr, shapeStr), 'shexValidate');
    return r.verdict;
  }

  const OWL_CLOSURE_MODES = { rdfs: 'RDFS', 'owl-rl': 'OWL-RL', owlrl: 'OWL-RL', owl_rl: 'OWL-RL' };

  function normalizeClosureMode(mode) {
    const canonical = OWL_CLOSURE_MODES[String(mode || '').toLowerCase()];
    if (!canonical) {
      throw new TypeError(
        `owlClosure: mode must be 'RDFS' or 'OWL-RL' (got '${mode}')`);
    }
    return canonical;
  }

  /**
   * RDFS or OWL-RL entailment closure, materialized as a new Dataset
   * (input triples + derived triples). Only the default graph is
   * closed over.
   * @param {Dataset|string|Array} data
   * @param {'RDFS'|'OWL-RL'} mode
   * @param {{format?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function owlClosure(data, mode, options) {
    const e = await entry();
    requireEntryFn(e, 'owlClosure', 'OWL/RDFS closure');
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'owlClosure(data)');
    const r = entryResult(
      e.owlClosure(dataNq, normalizeClosureMode(mode)), 'owlClosure');
    return Dataset.fromNQuads(r.nquads, { blankNodePrefix: freshBnodePrefix() });
  }

  /**
   * The core-RDFS closure (L4Factoidal/RDFS/Closure.lean, `closureFix`):
   * rdfs2/3/5/7/9/11 only.
   * "corerdfs" is this project's API name for the fragment the
   * literature calls ρdf — subPropertyOf/subClassOf/type/domain/range,
   * per Muñoz, Pérez & Gutierrez, "Simple and Efficient Minimal
   * RDFS", J. Web Semantics 7(3), 2009. `rhoDfClosure` remains as an
   * alias so code can be grepped against the theorem registry.
   * Returns the raw certified result, not a Dataset: the N-Triples
   * text is the object the theorems talk about.
   * @param {Dataset|string|Array} data
   * @param {{format?: string}} [options]
   * @returns {Promise<{ok: boolean, ntriples: string}>}
   */
  async function coreRdfsClosure(data, options) {
    const e = await entry();
    requireEntryFn(e, 'rhoDfClosure', 'certified core-RDFS closure');
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'coreRdfsClosure(data)');
    return entryResult(e.rhoDfClosure(dataNq), 'coreRdfsClosure');
  }
  /** Literature-name alias for coreRdfsClosure (ρdf; see above). */
  const rhoDfClosure = coreRdfsClosure;

  /**
   * Decidable core-RDFS fragment check (`is_rho_df_frag`, tied by an
   * F* lemma to the prop the regime theorems quantify over): does the
   * certified path's guarantee apply to this data? Naming: see
   * coreRdfsClosure above. `rhoDfFragmentCheck` remains as an alias.
   * @param {Dataset|string|Array} data
   * @param {{format?: string}} [options]
   * @returns {Promise<{ok: boolean, fragment: boolean}>}
   */
  async function coreRdfsCheck(data, options) {
    const e = await entry();
    requireEntryFn(e, 'rhoDfFragmentCheck', 'core-RDFS fragment check');
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'coreRdfsCheck(data)');
    return entryResult(e.rhoDfFragmentCheck(dataNq), 'coreRdfsCheck');
  }
  /** Literature-name alias for coreRdfsCheck (ρdf; see above). */
  const rhoDfFragmentCheck = coreRdfsCheck;

  /**
   * RDFS-Plus closure (RDF.Entailment.RDFSPlus.fst's
   * `rdfs_plus_closure`): the full RDFS step plus the practical OWL
   * subset -- owl:sameAs (symmetry/transitivity/substitution),
   * owl:inverseOf, Symmetric/Transitive/Functional/
   * InverseFunctionalProperty, equivalentClass/Property. The tier the
   * literature calls RDFS-Plus (Allemang & Hendler, "Semantic Web for
   * the Working Ontologist", 2008) or RDFS++ (AllegroGraph). Claim
   * level, weaker than coreRdfsClosure's and stated exactly: every OWL
   * row runs under a PROVED licensing + truth lemma (per-rule
   * certificates in the theorem registry); no chain-level completeness
   * is claimed -- owl:sameAs equality breaks the Herbrand argument the
   * corerdfs completeness theorem uses.
   * @param {Dataset|string|Array} data
   * @param {{format?: string}} [options]
   * @returns {Promise<{ok: boolean, ntriples: string, rounds: number}>}
   */
  async function rdfsPlusClosure(data, options) {
    const e = await entry();
    requireEntryFn(e, 'rdfsPlusClosure', 'RDFS-Plus closure');
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'rdfsPlusClosure(data)');
    return entryResult(e.rdfsPlusClosure(dataNq), 'rdfsPlusClosure');
  }

  /**
   * OWL tableau materialisation (formal/fstar/Tableau.fst's
   * `tableau_materialise`): add `i rdf:type <ClassExpression>` for
   * every individual the model-construction reasoner can prove is a
   * member of an OWL class expression (someValuesFrom / hasValue /
   * unionOf / intersectionOf, and the named class an equivalentClass
   * restriction defines). This is the same F* function the SPARQL 1.1
   * entailment-regime suite runs under the DL regime. Needs the
   * Default graph only (same scope cut as owlClosure).
   * @param {Dataset|string|Array} data
   * @param {{format?: string}} [options]
   * @returns {Promise<{dataset: Dataset, addedCount: number, budgetHit?: boolean}>}
   *   dataset is input + tableau-derived triples; addedCount is how many
   *   the tableau added; budgetHit (Lean engine only) is true when the
   *   materialisation work budget ran out.
   */
  async function tableauMaterialise(data, options) {
    const e = await entry();
    requireEntryFn(e, 'tableauMaterialise', 'OWL tableau materialisation');
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'tableauMaterialise(data)');
    const r = entryResult(e.tableauMaterialise(dataNq), 'tableauMaterialise');
    return {
      dataset: Dataset.fromNQuads(r.nquads, { blankNodePrefix: freshBnodePrefix() }),
      addedCount: r.addedCount,
      // Only the Lean engine reports it: true when the materialisation
      // work budget ran out, so an absent membership is a cap, not a proof.
      ...(r.budgetHit !== undefined ? { budgetHit: r.budgetHit } : {}),
    };
  }

  /**
   * OWL DL inconsistency verdict: OWL RL closure, one class-expression
   * materialisation pass, OWL RL closure again, then the clash decision
   * (Wasm/Ops/Reasoning.lean). `rlAlone` is the plain OWL-RL verdict on the same
   * input, so a caller can see the DL>=RL cases the tableau adds: a
   * disjointness clash reached only after the tableau materialises a
   * restriction membership the Datalog closure never derives. Default
   * graph only.
   * @param {Dataset|string|Array} data
   * @param {{format?: string}} [options]
   * @returns {Promise<{inconsistent: boolean, rlAlone: boolean}>}
   */
  async function tableauDlInconsistent(data, options) {
    const e = await entry();
    requireEntryFn(e, 'tableauDlInconsistent', 'OWL tableau DL inconsistency check');
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'tableauDlInconsistent(data)');
    const r = entryResult(e.tableauDlInconsistent(dataNq), 'tableauDlInconsistent');
    return { inconsistent: r.inconsistent, rlAlone: r.rlAlone };
  }

  /**
   * OWL DL consistency verdict via the clash-detecting tableau
   * (L4Factoidal/OWL/Refute.lean, `tableauConsistent`) over the OWL RL
   * closure. Default graph only (same scope cut as
   * tableauDlInconsistent).
   *
   * Three-valued: `consistent` is `false` (a clash on every
   * tableau branch), `true` (a model was constructed with no clash), or
   * `null` -- the refuter ran out of budget before deciding, with
   * `reason` naming the fuel cap. `null` is never collapsed to `false`.
   *
   * @param {Dataset|string|Array} data the ontology + ABox graph
   * @param {{format?: string, fuel?: number|string}} [options] format
   *   parses `data` (default 'turtle'); fuel overrides the refutation
   *   budget (default 20000).
   * @returns {Promise<{consistent: boolean|null, reason?: string}>}
   */
  async function owlIsConsistent(data, options) {
    const e = await entry();
    requireEntryFn(e, 'owlIsConsistent', 'OWL DL consistency check');
    const opts = options || {};
    const dataNq = docsToEntryNQuads(e, toDocs(data, opts), 'owlIsConsistent(data)');
    const optsJson = JSON.stringify(opts.fuel != null ? { fuel: String(opts.fuel) } : {});
    const r = entryResult(e.owlIsConsistent(dataNq, optsJson), 'owlIsConsistent');
    return r.reason === undefined
      ? { consistent: r.consistent }
      : { consistent: r.consistent, reason: r.reason };
  }

  /**
   * OWL entailment check: does `premise` entail `conclusion`? Two
   * paths (Wasm/Ops/Reason.lean): `via: "closure"` when every conclusion
   * triple is in the OWL-RL closure of the premise; `via: "refutation"`
   * when the negated conclusion (L4Factoidal/OWL/NegationGoals.lean) is
   * refuted on every goal by the clash-detecting tableau. Default graph
   * only.
   *
   * Three-valued: `entailed` is `true`, `false`, or `null` (a refutation
   * goal exhausted its fuel budget -- indeterminate, never a silent
   * `false`; `reason` names the cap).
   *
   * @param {Dataset|string|Array} premise
   * @param {Dataset|string|Array} conclusion
   * @param {{format?: string, fuel?: number|string}} [options] format
   *   parses both graphs (default 'turtle'); fuel overrides the
   *   refutation budget (default 20000).
   * @returns {Promise<{entailed: boolean|null, via: 'closure'|'refutation', reason?: string}>}
   */
  async function owlEntails(premise, conclusion, options) {
    const e = await entry();
    requireEntryFn(e, 'owlEntails', 'OWL entailment check');
    const opts = options || {};
    const premiseNq = docsToEntryNQuads(e, toDocs(premise, opts), 'owlEntails(premise)');
    const conclusionNq = docsToEntryNQuads(e, toDocs(conclusion, opts), 'owlEntails(conclusion)');
    const optsJson = JSON.stringify(opts.fuel != null ? { fuel: String(opts.fuel) } : {});
    const r = entryResult(e.owlEntails(premiseNq, conclusionNq, optsJson), 'owlEntails');
    return r.reason === undefined
      ? { entailed: r.entailed, via: r.via }
      : { entailed: r.entailed, via: r.via, reason: r.reason };
  }

  /**
   * Evaluate an RML mapping graph against one logical source's raw
   * data, returning the generated triples as a Dataset. Every triples
   * map in `mapping` reads the SAME `sourceData`, so a join across two
   * different logical sources is not reachable through this one-source
   * function. The iteration format is the mapping's
   * `rml:referenceFormulation` (RML Core); `sourceKind` is checked.
   * @param {Dataset|string|Array} mapping the RML mapping graph (Turtle by default)
   * @param {string} sourceData raw JSON or CSV text (not RDF)
   * @param {'json'|'csv'} sourceKind
   * @param {{format?: string}} [options] applies to `mapping`
   * @returns {Promise<Dataset>}
   */
  async function rmlMap(mapping, sourceData, sourceKind, options) {
    const e = await entry();
    requireEntryFn(e, 'rmlMap', 'RML mapping evaluation');
    if (typeof sourceData !== 'string') {
      throw new TypeError('rmlMap: sourceData must be a string');
    }
    const kind = String(sourceKind || '').toLowerCase();
    if (kind !== 'json' && kind !== 'csv') {
      throw new TypeError("rmlMap: sourceKind must be 'json' or 'csv'");
    }
    const mappingNq = docsToEntryNQuads(e, toDocs(mapping, options), 'rmlMap(mapping)');
    const r = entryResult(e.rmlMap(mappingNq, sourceData, kind), 'rmlMap');
    return Dataset.fromNQuads(r.nquads, { blankNodePrefix: freshBnodePrefix() });
  }

  /**
   * CSVW csv2rdf conversion (w3.org/TR/csv2rdf): convert tabular data
   * plus an optional CSVW metadata document into a Dataset (op
   * csvwToRdf, L4Factoidal/CSVW). Every table in a multi-table `tables`
   * group reads the SAME `csvText`; a `tableSchema` given as a URL is not
   * fetched.
   * @param {string} csvText raw RFC 4180 tabular data (not RDF)
   * @param {string} [metadataJson] CSVW metadata document (JSON text);
   *   '' / omitted infers the schema from the CSV's own header row
   * @param {{mode?: 'standard'|'minimal', base?: string, url?: string}}
   *   [options] mode defaults to 'standard' (full csvw:TableGroup/
   *   Table/Row wrapper); base is the resolution base IRI (default
   *   'file:///'); url is the tabular file's own URL used when the
   *   metadata carries none (default 'table.csv') -- cell predicates
   *   default to `<tableUrl>#<colName>`, so url shapes every emitted
   *   predicate IRI.
   * @returns {Promise<Dataset>}
   */
  async function csvwToRdf(csvText, metadataJson, options) {
    if (typeof csvText !== 'string') {
      throw new TypeError('csvwToRdf: csvText must be a string');
    }
    const meta = metadataJson == null ? '' : metadataJson;
    if (typeof meta !== 'string') {
      throw new TypeError('csvwToRdf: metadataJson must be a string');
    }
    const e = await entry();
    requireEntryFn(e, 'csvwToRdf', 'CSVW csv2rdf conversion');
    const opts = options || {};
    const optionsJson = JSON.stringify({
      ...(opts.mode ? { mode: String(opts.mode).toLowerCase() } : {}),
      ...(opts.base ? { base: opts.base } : {}),
      ...(opts.url ? { url: opts.url } : {}),
    });
    const r = entryResult(e.csvwToRdf(csvText, meta, optionsJson), 'csvwToRdf');
    return Dataset.fromNQuads(r.nquads, { blankNodePrefix: freshBnodePrefix() });
  }

  /**
   * Parse a JSON-LD document into a Dataset, with JSON-LD-specific
   * options `parse()` has no room for (plain `parse(text,
   * {format:'jsonld'})` also works; this exists for callers that need
   * rdfDirection/expandContext/processingMode). A remote `@context` is
   * not fetched (no network access through the engine).
   * @param {string} jsonldText
   * @param {{base?: string, rdfDirection?: string, expandContext?: string,
   *   processingMode?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function jsonldToRdf(jsonldText, options) {
    if (typeof jsonldText !== 'string') {
      throw new TypeError('jsonldToRdf: jsonldText must be a string');
    }
    const e = await entry();
    requireEntryFn(e, 'jsonldToRdf', 'jsonldToRdf');
    const opts = options || {};
    const optionsJson = JSON.stringify({
      ...(opts.base ? { base: opts.base } : {}),
      ...(opts.rdfDirection ? { rdfDirection: opts.rdfDirection } : {}),
      ...(opts.expandContext ? { expandContext: opts.expandContext } : {}),
      ...(opts.processingMode ? { processingMode: opts.processingMode } : {}),
    });
    const r = entryResult(e.jsonldToRdf(jsonldText, optionsJson), 'jsonldToRdf');
    return Dataset.fromNQuads(r.nquads, { blankNodePrefix: freshBnodePrefix() });
  }

  /**
   * RIF Core forward-chaining saturation, materialized as a new
   * Dataset (input triples + derived triples, default graph only --
   * RIF Core has no named-graph notion).
   * @param {Dataset|string|Array} data the premise graph
   * @param {string} rifRulesXml a RIF Core XML rule document
   * @param {{format?: string}} [options] applies to `data`
   * @returns {Promise<Dataset>}
   */
  async function rifEval(data, rifRulesXml, options) {
    const e = await entry();
    requireEntryFn(e, 'rifEval', 'RIF Core evaluation');
    if (typeof rifRulesXml !== 'string') {
      throw new TypeError('rifEval: rifRulesXml must be a string');
    }
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'rifEval(data)');
    const r = entryResult(e.rifEval(rifRulesXml, dataNq), 'rifEval');
    return Dataset.fromNQuads(r.saturatedNquads, {
      blankNodePrefix: freshBnodePrefix(),
    });
  }

  /**
   * Serialize an RDF dataset as an expanded-form JSON-LD document --
   * the reverse of jsonldToRdf (entry_jsoo.ml's jsonldFromRdf export ->
   * the verified JSONLD.FromRdf.from_rdf). Returns the parsed JSON-LD
   * value (an array of node objects).
   * @param {Dataset|string|Array} data
   * @param {{useNativeTypes?:boolean,useRdfType?:boolean,format?:string}} [options]
   * @returns {Promise<any>} the JSON-LD document (JCS-canonical, parsed)
   */
  async function jsonldFromRdf(data, options) {
    const e = await entry();
    requireEntryFn(e, 'jsonldFromRdf', 'jsonldFromRdf');
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'jsonldFromRdf(data)');
    const opts = options || {};
    const optionsJson = JSON.stringify({
      ...(opts.useNativeTypes ? { useNativeTypes: true } : {}),
      ...(opts.useRdfType ? { useRdfType: true } : {}),
    });
    const r = entryResult(e.jsonldFromRdf(dataNq, optionsJson), 'jsonldFromRdf');
    return JSON.parse(r.jsonld);
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
    return Dataset.fromNQuads(r.nquads, { blankNodePrefix: freshBnodePrefix() });
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

  // Matrix / vector algebra over exact rationals (Math.Matrix). A
  // matrix is a JSON array of rows; a vector a JSON array of cells;
  // a cell is an integer or a [num,den] pair. Results render via
  // Math.Matrix.mres_to_string ("undef" carries a `reason`).
  async function matrixCall(fnName, what, ...jsonArgs) {
    const e = await entry();
    requireEntryFn(e, fnName, what);
    const r = entryResult(e[fnName](...jsonArgs.map((a) => JSON.stringify(a))), fnName);
    return { result: r.result, reason: r.reason || '' };
  }

  /**
   * Determinant of a square matrix (entry_jsoo.ml's matrixDeterminant
   * -> Math.Matrix.dyn_determinant), exact.
   * @param {Array<Array<number|[number,number]>>} matrix
   * @returns {Promise<{result:string,reason:string}>}
   */
  async function matrixDeterminant(matrix) {
    if (!Array.isArray(matrix)) throw new TypeError('matrixDeterminant: matrix must be an array of rows');
    return matrixCall('matrixDeterminant', 'matrix determinant', matrix);
  }

  /**
   * Dot / scalar product of two vectors (entry_jsoo.ml's
   * matrixScalarProduct -> Math.Matrix.dyn_scalarproduct).
   * @param {Array<number|[number,number]>} a
   * @param {Array<number|[number,number]>} b
   * @returns {Promise<{result:string,reason:string}>}
   */
  async function matrixScalarProduct(a, b) {
    if (!Array.isArray(a) || !Array.isArray(b)) throw new TypeError('matrixScalarProduct: a and b must be arrays');
    return matrixCall('matrixScalarProduct', 'vector scalar product', a, b);
  }

  /**
   * Cross product of two 3-vectors (entry_jsoo.ml's
   * matrixVectorProduct -> Math.Matrix.dyn_vectorproduct).
   * @param {Array<number|[number,number]>} a
   * @param {Array<number|[number,number]>} b
   * @returns {Promise<{result:string,reason:string}>}
   */
  async function matrixVectorProduct(a, b) {
    if (!Array.isArray(a) || !Array.isArray(b)) throw new TypeError('matrixVectorProduct: a and b must be arrays');
    return matrixCall('matrixVectorProduct', 'vector cross product', a, b);
  }

  /**
   * Outer product of two vectors (entry_jsoo.ml's matrixOuterProduct
   * -> Math.Matrix.dyn_outerproduct).
   * @param {Array<number|[number,number]>} a
   * @param {Array<number|[number,number]>} b
   * @returns {Promise<{result:string,reason:string}>}
   */
  async function matrixOuterProduct(a, b) {
    if (!Array.isArray(a) || !Array.isArray(b)) throw new TypeError('matrixOuterProduct: a and b must be arrays');
    return matrixCall('matrixOuterProduct', 'vector outer product', a, b);
  }

  // A `scaled` value as entry_jsoo.ml's scaledJson envelope decodes it:
  // {mantissa,scale,decimal} strings straight off the wire.
  function scaledFromJson(s) {
    return { mantissa: s.mantissa, scale: s.scale, decimal: s.decimal };
  }

  /**
   * n+1 evenly spaced samples of the logistic sigmoid
   * L / (1 + exp(-k*(x - x0))) over [xmin, xmax] (entry_jsoo.ml's
   * sigmoidPoints -> Math.Sigmoid.sigmoid_points). All arithmetic --
   * argument reduction, the truncated Taylor series, repeated
   * squaring, and the x samples themselves -- runs as exact rational
   * arithmetic inside Math.Sigmoid.fst; see that module's header for
   * the documented error bound on the returned (rounded) values. This
   * wrapper only marshals JSON; it never computes exp itself.
   * @param {{k:number|string,x0:number|string,l:number|string,
   *   xmin:number|string,xmax:number|string,n:number|string}} params
   * @returns {Promise<Array<{x:{mantissa:string,scale:string,decimal:string},
   *   y:{mantissa:string,scale:string,decimal:string}}>>}
   */
  async function sigmoidPoints(params) {
    if (!params || typeof params !== 'object') {
      throw new TypeError('sigmoidPoints: params must be an object');
    }
    const e = await entry();
    requireEntryFn(e, 'sigmoidPoints', 'sigmoid points');
    const wire = {
      k: String(params.k), x0: String(params.x0), l: String(params.l),
      xmin: String(params.xmin), xmax: String(params.xmax), n: String(params.n),
    };
    const r = entryResult(e.sigmoidPoints(JSON.stringify(wire)), 'sigmoid points');
    return r.points.map((p) => ({ x: scaledFromJson(p.x), y: scaledFromJson(p.y) }));
  }

  /**
   * Presentation MathML for the sigmoid formula L / (1 + exp(-k*(x - x0))),
   * engine-serialized (entry_jsoo.ml's sigmoidFormulaMathml ->
   * MathML.Present.to_presentation_mathml applied to a fixed
   * Math.Expr.expr) -- never hand-written MathML.
   * @returns {Promise<string>} a `<math>...</math>` Presentation MathML document
   */
  async function sigmoidFormulaMathml() {
    const e = await entry();
    requireEntryFn(e, 'sigmoidFormulaMathml', 'sigmoid formula MathML');
    const r = entryResult(e.sigmoidFormulaMathml(), 'sigmoid formula MathML');
    return r.mathml;
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
    const manifestHex = hexOfBytes(gen.manifest);
    let keys;
    if (Array.isArray(opts.keys)) {
      keys = opts.keys.map(String);
    } else if (typeof opts.sparql === 'string') {
      const plan = entryResult(e.storeQueryPlan(manifestHex, opts.sparql), 'openStore(plan)');
      keys = plan.keys.concat(plan.sidecarKeys || [], plan.blobKeys || []);
    } else {
      keys = manifestKeys(entryResult(e.storeManifestInspect(manifestHex), 'openStore(inspect)'));
    }
    const { blob, artifacts } = await readRegion(reader, gen.generation, keys);
    const env = entryResult(e.storeOpen(manifestHex, JSON.stringify(artifacts), blob), 'openStore');
    return new Store(e, env, gen, manifestHex, freshBnodePrefix, withExtensionRounds);
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
    const opts = options || {};
    const dataFormat = String(opts.dataFormat || 'turtle').toLowerCase();
    const entail = opts.entail || 'none';
    const output = opts.output || 'json';
    if (!(dataFormat in RAW_DATA_FORMATS)) {
      throw new TypeError(`queryRaw: unknown dataFormat '${opts.dataFormat}'`);
    }
    if (!ENTAIL_VALUES.has(entail)) {
      throw new TypeError(`queryRaw: entail must be one of ${[...ENTAIL_VALUES].join(', ')}`);
    }
    if (!RAW_OUTPUT_FORMATS.has(output)) {
      throw new TypeError(`queryRaw: output must be one of ${[...RAW_OUTPUT_FORMATS].join(', ')}`);
    }
    const e = await entry();
    requireEntryFn(e, 'queryRaw', 'queryRaw');
    const r = JSON.parse(e.queryRaw(dataString, queryString,
      JSON.stringify({ dataFormat: RAW_DATA_FORMATS[dataFormat], entail, output })));
    if (!r.ok) {
      const err = new Error('SPARQL query failed: ' + r.error);
      err.stderr = String(r.error);
      throw err;
    }
    return output === 'json' ? JSON.parse(r.text) : r.text;
  }

  /**
   * Feature probe, for tests and downstream capability checks.
   * @returns {Promise<{entry: boolean, construct: boolean,
   *   update: boolean, canonicalize: boolean, graphs: boolean,
   *   canonicalHash: boolean, shacl: boolean, shex: boolean,
   *   owlClosure: boolean, rml: boolean, csvw: boolean, jsonld: boolean,
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
      owlClosure: has('owlClosure'),
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
      matrix: has('matrixDeterminant'),
      sigmoid: has('sigmoidPoints') && has('sigmoidFormulaMathml'),
      hdt: has('queryHdt'),
      // VC Data Integrity: Ed25519 is HACL* compiled into the wasm module,
      // SHA-256 is the Lean hash; no separate crypto module or init step.
      vcCrypto: has('vcEd25519Verify') && has('vcEddsaVerifyFromCanonical'),
      profile: e.profile || 'full',
      abiVersion: e.abiVersion,
      datasetHandles: has('datasetOpen') && has('datasetQuery') &&
        has('datasetUpdate') && has('datasetSerialize') && has('datasetClose'),
      sparql12: has('queryDataset12') && has('datasetQuery12'),
      parseDiagnostics: has('parseDocument'),
      turtlePrefixes: has('serializeTurtleWith'),
      store: has('storeOpen') && has('storeHandleQuery'),
    };
  }

  return {
    parse,
    query,
    queryHdt,
    update,
    openDataset,
    registerExtensionFunction,
    unregisterExtensionFunction,
    clearExtensionFunctions,
    registerServiceEndpoint,
    clearServiceEndpoints,
    serialize,
    canonicalize,
    graphs,
    canonicalHash,
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
    matrixDeterminant,
    matrixScalarProduct,
    matrixVectorProduct,
    matrixOuterProduct,
    sigmoidPoints,
    sigmoidFormulaMathml,
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
    capabilities,
    openStore,
    queryStore,
    listStores,
    queryRaw,
    Dataset,
    DatasetHandle,
    Store,
    ParseError,
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
  buildApi, sniffQueryForm, bindingsFromSrj, entryResult, parseResult,
  utf16OffsetOf, missingOpError, ParseError, DatasetHandle, Store,
};
