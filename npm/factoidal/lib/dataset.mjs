// factoidal — Dataset: an RDF dataset held inside the Lean engine.
//
// https://github.com/danbri/factoidal/issues/882 item 1. A Dataset is a
// handle into the engine's dataset store (formal/lean4/Wasm/Ops/Handles.lean
// and Wasm/Ops/DatasetFull.lean). The parsed, indexed dataset stays in the
// wasm memory; a query, an update, a validation, a closure or a
// serialisation sends the handle id and the query text, not the data. An op
// that makes a dataset (parse, CSVW, RML, JSON-LD, closures, RIF) answers a
// new handle, so a pipeline of steps moves no N-Quads text between them.
//
// This file only marshals: every decision about RDF is the engine's.
//
// Lifetime: dispose() (or `using ds = ...`, Symbol.dispose) releases the
// engine copy. A Dataset that is garbage collected without dispose() is
// released by a FinalizationRegistry callback. Every method of a disposed
// Dataset throws a TypeError that names the method.

import { dataFactory, quadFromJson, quadToJson, termToJson, termFromSrj, Literal, NamedNode } from '../rdfjs.mjs';

const INTERNAL = Symbol('factoidal.Dataset.internal');

// Writer names (lower case) -> the engine's writer tag: the engine's table
// (op engineTables, `writerFormats`), read once per engine. JSON-LD is served
// by the op datasetToJsonLd; the SPARQL results formats are query outputs.
// `WRITER_TAGS` stays exported for callers that read it; it is filled from
// the engine on the first Dataset.
const WRITER_TAGS = {};

const VERSIONS = { '1.1': '11', '1.2': '12' };

/** Throw a TypeError when `options` has a key outside `allowed`. */
function checkOptions(who, options, allowed) {
  if (options == null) return {};
  if (typeof options !== 'object' || Array.isArray(options)) {
    throw new TypeError(`${who}: options must be an object, got ${Array.isArray(options) ? 'array' : typeof options}`);
  }
  for (const key of Object.keys(options)) {
    if (!allowed.includes(key)) {
      throw new TypeError(
        `${who}: unknown option '${key}'. Known options: ${allowed.join(', ') || '(none)'}`);
    }
  }
  return options;
}

function envelope(jsonText, what) {
  const r = JSON.parse(jsonText);
  if (!r.ok) throw new Error(`${what}: ${r.error}`);
  return r;
}

const SERIALIZE_OPTIONS = ['format', 'version', 'prefixes', 'literalShorthand',
  'useNativeTypes', 'useRdfType', 'rdfDirection'];

// The quads of the compact answer of datasetQuadsJson: each distinct term is
// built once and shared (TermJson.compactCertified).
function quadsFromCompact(terms, ixs) {
  const ts = terms.map(termFromSrj);
  const dg = dataFactory.defaultGraph();
  return ixs.map((ix) => dataFactory.quad(ts[ix[0]], ts[ix[1]], ts[ix[2]],
    ix.length > 3 ? ts[ix[3]] : dg));
}

// The region of op datasetQuadsBin, read as the engine wrote it
// (formal/lean4/L4Factoidal/RDF/QuadsBin.lean: `binSpec` is the layout,
// `decodeBin` the reader this function follows, `decodeBin_quadsBin` the
// theorem that the region reads back as exactly the quads). Every number is a
// u32 little-endian; each term is in the term codec of DLOG version 2, which
// names the term kind, the datatype IRI, the language tag and the base
// direction explicitly, so this function copies fields and decides nothing.
const UTF8 = new TextDecoder('utf-8', { fatal: true });
const DIRECTION = ['', 'ltr', 'rtl'];

function quadsFromRegion(bytes, out) {
  const v = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  if (bytes.length < 12 || v.getUint32(0, true) !== 0x31425146) {
    throw new Error('iterate: the engine answered no datasetQuadsBin region');
  }
  const nTerms = v.getUint32(4, true);
  const nQuads = v.getUint32(8, true);
  let p = 12;
  // UTF-8 bytes to a string; a short run of bytes below 0x80 (one UTF-16
  // unit each) is copied without a TextDecoder call.
  const str = () => {
    const n = v.getUint32(p, true);
    const a = p + 4;
    p = a + n;
    if (n <= 64) {
      let i = a;
      while (i < p && bytes[i] < 0x80) i++;
      if (i === p) return String.fromCharCode.apply(null, bytes.subarray(a, p));
    }
    return UTF8.decode(bytes.subarray(a, p));
  };
  const datatypes = new Map();
  const term = () => {
    switch (bytes[p++]) {
      case 0: return new NamedNode(str());
      case 1: return dataFactory.blankNode(str());
      case 2: {
        const lexical = str();
        const dt = str();
        let datatype = datatypes.get(dt);
        if (datatype === undefined) { datatype = new NamedNode(dt); datatypes.set(dt, datatype); }
        const flag = bytes[p++];
        const language = flag === 0 ? '' : str();
        const direction = flag === 2 ? DIRECTION[bytes[p++]] : '';
        return new Literal(lexical, language, datatype, direction);
      }
      case 3: {
        const s = term();
        const pr = term();
        return dataFactory.quad(s, pr, term());
      }
      default: throw new Error('iterate: a term tag outside the DLOG version 2 codec');
    }
  };
  const ts = new Array(nTerms);
  for (let i = 0; i < nTerms; i++) ts[i] = term();
  const dg = dataFactory.defaultGraph();
  for (let i = 0; i < nQuads; i++, p += 16) {
    const g = v.getUint32(p + 12, true);
    out.push(dataFactory.quad(ts[v.getUint32(p, true)], ts[v.getUint32(p + 4, true)],
      ts[v.getUint32(p + 8, true)], g === 0 ? dg : ts[g - 1]));
  }
  return nQuads;
}

// Quads of the first datasetQuadsBin call while iterating: an iteration that
// stops early reads this many; the rest come in one more call.
const FIRST_PAGE = 4096;

class Dataset {
  /** @private Datasets come from parse(), csvwToRdf() and the other producers. */
  constructor(token, ctx, handle, size, prefixes, extra) {
    if (token !== INTERNAL) {
      throw new TypeError(
        'Dataset: use parse(), openDataset() or another producer; the constructor is internal');
    }
    this._ctx = ctx;
    this._handle = handle;
    this._size = size;
    this._prefixes = Object.freeze({ ...(prefixes || {}) });
    const x = extra || {};
    this._diagnostics = Object.freeze((x.diagnostics || []).slice());
    this._format = x.format;
    this._formatInferred = !!x.formatInferred;
    this._info = Object.freeze({ ...(x.info || {}) });
    this._disposed = false;
    this._nquads = null;   // cached N-Quads text, dropped on update
    this._quads = null;    // cached quad array, dropped on update
    if (ctx.registry) ctx.registry.register(this, { e: ctx.e, handle }, this);
  }

  /** The engine's handle id (opaque, e.g. "h7"). */
  get handle() { return this._handle; }
  /** Number of quads. */
  get size() { this._open('size'); return this._size; }
  /** Prefixes the source document declared (label -> namespace IRI). */
  get prefixes() { return this._prefixes; }
  /** Diagnostics of a lenient parse ({lenient:true}); else empty. */
  get diagnostics() { return this._diagnostics; }
  /** The syntax the data was read from, when it was read from text. */
  get format() { return this._format; }
  /** True when `format` was inferred because the caller gave none. */
  get formatInferred() { return this._formatInferred; }
  /** True after dispose(). */
  get disposed() { return this._disposed; }
  /**
   * What the producing op reported beside the data: `rounds` for the rho-df
   * and RDFS-Plus closures; `inputCount`, `derivedCount`, `fuel` for rifEval.
   */
  get info() { return this._info; }

  _open(who) {
    if (this._disposed) {
      throw new TypeError(`Dataset.${who}: the Dataset was disposed (handle '${this._handle}')`);
    }
  }

  _changed(size) {
    this._size = size;
    this._nquads = null;
    this._quads = null;
  }

  /**
   * SPARQL 1.1 (or 1.2) query.
   * @param {string} sparql
   * @param {{sparql12?: boolean, version?: '1.1'|'1.2', entail?: string,
   *   output?: 'json'|'xml'|'csv'|'tsv'|'table'|'ntriples'}} [options]
   *   With `output` (or an `entail` regime other than 'none') the answer
   *   is text (`output` 'json': the parsed results JSON object).
   * @returns {Promise<Array<Map<string, object>>|boolean|Dataset|string|object>}
   */
  async query(sparql, options) {
    this._open('query');
    return this._ctx.queryHandle(this, sparql,
      checkOptions('Dataset.query', options, ['sparql12', 'version', 'entail', 'output']));
  }

  /**
   * SPARQL 1.1 Update, applied to this Dataset in place.
   * @param {string} updateText
   * @param {{}} [options] none today
   * @returns {Promise<Dataset>} this Dataset
   */
  async update(updateText, options) {
    this._open('update');
    checkOptions('Dataset.update', options, []);
    if (typeof updateText !== 'string') {
      throw new TypeError('Dataset.update: updateText must be a string');
    }
    const r = envelope(this._ctx.e.datasetUpdate(this._handle, updateText), 'update');
    this._changed(r.count);
    return this;
  }

  /**
   * SHACL validation with this Dataset as the data graph.
   * @param {Dataset|string} shapes a Dataset or text
   * @param {{format?: string, baseIRI?: string}} [options] read `shapes` text
   * @returns {Promise<{conforms: boolean, report: Dataset}>}
   */
  async validateShacl(shapes, options) {
    this._open('validateShacl');
    return this._ctx.shacl(this, shapes,
      checkOptions('Dataset.validateShacl', options, ['format', 'baseIRI']));
  }

  /**
   * ShEx validation of one focus node with this Dataset as the data graph.
   * @param {string} schema ShExC or ShExJ text
   * @param {{focus: string|object, shape?: string|object}} options
   * @returns {Promise<boolean>}
   */
  async validateShex(schema, options) {
    this._open('validateShex');
    return this._ctx.shex(this, schema,
      checkOptions('Dataset.validateShex', options, ['focus', 'shape']));
  }

  /**
   * Closure of the default graph under a regime, as a new Dataset.
   * @param {'rdfs'|'owl-rl'|'rho-df'|'rdfs-plus'} regime
   * @returns {Promise<Dataset>}
   */
  async closure(regime) {
    this._open('closure');
    return this._ctx.closure(this, regime);
  }

  /** RDFC-1.0 canonical N-Quads. @returns {Promise<string>} */
  async canonicalize() {
    this._open('canonicalize');
    return this.toString('rdfc');
  }

  /**
   * The dataset as a document.
   * @param {{format?: string, version?: '1.1'|'1.2', prefixes?: object,
   *   literalShorthand?: boolean, useNativeTypes?: boolean,
   *   useRdfType?: boolean, rdfDirection?: string}} [options]
   *   format: nquads (default), ntriples, turtle, trig, rdfxml, jsonld,
   *   rdfc (RDFC-1.0 canonical N-Quads).
   * @returns {Promise<string>}
   */
  async serialize(options) {
    this._open('serialize');
    if (typeof options === 'string') return this._write({ format: options });
    return this._write(checkOptions('Dataset.serialize', options, SERIALIZE_OPTIONS));
  }

  /**
   * Synchronous serialize(): `toString('turtle')` or `toString({format})`.
   * @param {string|object} [formatOrOptions]
   * @returns {string}
   */
  toString(formatOrOptions) {
    this._open('toString');
    const opts = typeof formatOrOptions === 'string'
      ? { format: formatOrOptions }
      : checkOptions('Dataset.toString', formatOrOptions, SERIALIZE_OPTIONS);
    return this._write(opts);
  }

  _write(opts) {
    const e = this._ctx.e;
    const name = String(opts.format || 'nquads').toLowerCase();
    const writerTags = this._ctx.tables().writerFormats;
    const tag = writerTags[name];
    if (!tag) {
      throw new TypeError(
        `Dataset.serialize: unknown format '${opts.format}'. Known formats: ` +
        [...new Set(Object.values(writerTags))].join(', '));
    }
    let suffix = '';
    if (opts.version !== undefined) {
      suffix = VERSIONS[String(opts.version)];
      if (!suffix) throw new TypeError("Dataset.serialize: version must be '1.1' or '1.2'");
    }
    if (tag !== 'turtle' && (opts.prefixes !== undefined || opts.literalShorthand !== undefined)) {
      throw new TypeError("Dataset.serialize: 'prefixes' and 'literalShorthand' apply to format 'turtle' only");
    }
    const jsonldKeys = ['useNativeTypes', 'useRdfType', 'rdfDirection'];
    if (tag !== 'jsonld' && jsonldKeys.some((k) => opts[k] !== undefined)) {
      throw new TypeError(`Dataset.serialize: ${jsonldKeys.join(', ')} apply to format 'jsonld' only`);
    }
    if (tag === 'jsonld') {
      if (typeof e.datasetToJsonLd !== 'function') throw this._ctx.missing('serialize {format:jsonld}', 'datasetToJsonLd');
      const r = envelope(e.datasetToJsonLd(this._handle, JSON.stringify({
        ...(opts.useNativeTypes ? { useNativeTypes: true } : {}),
        ...(opts.useRdfType ? { useRdfType: true } : {}),
        ...(opts.rdfDirection ? { rdfDirection: String(opts.rdfDirection) } : {}),
        ...(suffix ? { version: String(opts.version) } : {}),
      })), 'serialize');
      return r.jsonld;
    }
    if (tag === 'nquads' && !suffix && this._nquads !== null) return this._nquads;
    const fullTag = tag + suffix;
    let r;
    if (tag === 'turtle' && (opts.prefixes !== undefined || opts.literalShorthand !== undefined ||
        Object.keys(this._prefixes).length > 0)) {
      r = envelope(e.datasetSerializeWith(this._handle, fullTag, JSON.stringify({
        prefixes: { ...this._prefixes, ...(opts.prefixes || {}) },
        ...(opts.literalShorthand !== undefined ? { literalShorthand: !!opts.literalShorthand } : {}),
      })), 'serialize');
    } else {
      r = envelope(e.datasetSerialize(this._handle, fullTag), 'serialize');
    }
    const text = r.text !== undefined ? r.text : (tag === 'turtle' ? r.turtle : r.nquads);
    if (tag === 'nquads' && !suffix) this._nquads = text;
    return text;
  }

  /** N-Quads text (sorted, the engine's canonical line order). */
  toNQuads() {
    this._open('toNQuads');
    return this._write({ format: 'nquads' });
  }

  /** A new Dataset with the same quads; updates of one leave the other unchanged. */
  clone() {
    this._open('clone');
    const r = envelope(this._ctx.e.datasetClone(this._handle), 'clone');
    return this._ctx.wrap(r, this._prefixes);
  }

  /**
   * RDF/JS quads, built from the engine's term objects (op datasetQuadsJson),
   * in the line order of toNQuads(). No N-Quads text is read here.
   * @returns {Iterator<object>}
   */
  *[Symbol.iterator]() {
    this._open('iterate');
    if (this._quads) { yield* this._quads; return; }
    const e = this._ctx.e;
    if (typeof e.datasetQuadsBin !== 'function') { yield* this._allQuads(); return; }
    // The engine's region (op datasetQuadsBin) in two calls, a first page and
    // the rest; the whole list is cached when the rest is read.
    const acc = [];
    const first = e.datasetQuadsBin(this._handle, `{"offset":0,"limit":${FIRST_PAGE}}`);
    quadsFromRegion(first.bytes, acc);
    for (let i = 0; i < acc.length; i++) yield acc[i];
    if (acc.length < first.envelope.total) {
      const rest = e.datasetQuadsBin(this._handle, `{"offset":${acc.length}}`);
      const from = acc.length;
      quadsFromRegion(rest.bytes, acc);
      for (let i = from; i < acc.length; i++) yield acc[i];
    }
    if (!this._quads) this._quads = Object.freeze(acc);
  }

  // Every quad, read once and cached.
  _allQuads() {
    if (!this._quads) {
      const e = this._ctx.e;
      if (typeof e.datasetQuadsBin === 'function') {
        const acc = [];
        quadsFromRegion(e.datasetQuadsBin(this._handle, '').bytes, acc);
        this._quads = Object.freeze(acc);
      } else {
        const r = envelope(e.datasetQuadsJson(this._handle, '{"compact":true}'), 'iterate');
        this._quads = Object.freeze(r.ixs ? quadsFromCompact(r.terms, r.ixs) : r.quads.map((q) => quadFromJson(q)));
      }
    }
    return this._quads;
  }

  /** Every quad as an array. */
  toArray() {
    this._open('toArray');
    return this._allQuads().slice();
  }

  // A quad pattern for the ops datasetMatch and datasetMatchCount: four
  // engine term objects, null for an unbound position, {type:'default'} for
  // the default graph.
  _pattern(subject, predicate, object, graph) {
    return JSON.stringify([termToJson(subject), termToJson(predicate), termToJson(object),
      termToJson(graph)]);
  }

  /** RDF/JS DatasetCore.has: one indexed lookup in the engine. */
  has(quad) {
    this._open('has');
    const r = envelope(this._ctx.e.datasetMatchCount(this._handle,
      this._pattern(quad.subject, quad.predicate, quad.object, quad.graph || { termType: 'DefaultGraph' })), 'has');
    return r.count > 0;
  }

  /**
   * RDF/JS DatasetCore.match: the matching quads as a new Dataset, found
   * through the engine's indexes. `null`/`undefined` matches any term.
   */
  match(subject, predicate, object, graph) {
    this._open('match');
    const r = envelope(this._ctx.e.datasetMatch(this._handle,
      this._pattern(subject, predicate, object, graph)), 'match');
    return this._ctx.wrap(r, this._prefixes);
  }

  /**
   * RDF/JS DatasetCore.add: add one quad (set semantics). A blank node is
   * the node of that label in this Dataset. Each call changes the engine
   * copy and costs time in the dataset size; for many quads use update()
   * or parse().
   */
  add(quad) {
    this._open('add');
    const r = envelope(this._ctx.e.datasetAddQuadsJson(this._handle,
      JSON.stringify([quadToJson(quad)])), 'add');
    this._changed(r.count);
    return this;
  }

  /** RDF/JS DatasetCore.delete: remove one quad. */
  delete(quad) {
    this._open('delete');
    const r = envelope(this._ctx.e.datasetDeleteQuadsJson(this._handle,
      JSON.stringify([quadToJson(quad)])), 'delete');
    this._changed(r.count);
    return this;
  }

  /** Release the engine copy. Idempotent. */
  dispose() {
    if (this._disposed) return;
    this._disposed = true;
    this._nquads = null;
    this._quads = null;
    if (this._ctx.registry) this._ctx.registry.unregister(this);
    try { this._ctx.e.datasetClose(this._handle); } catch (_err) { /* engine gone */ }
  }

  /** `using ds = await parse(...)` disposes at the end of the block. */
  [Symbol.dispose]() { this.dispose(); }
}

/**
 * A FinalizationRegistry that closes the engine handle of a Dataset that is
 * collected without dispose(). Null where the platform has none.
 */
function makeRegistry() {
  if (typeof FinalizationRegistry !== 'function') return null;
  return new FinalizationRegistry(({ e, handle }) => {
    try { e.datasetClose(handle); } catch (_err) { /* engine gone */ }
  });
}

export { Dataset, INTERNAL, checkOptions, makeRegistry, WRITER_TAGS, termFromSrj };
