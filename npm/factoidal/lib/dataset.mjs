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

import { nquadsLineToQuad, quadToNQuads, termFromSrj } from '../rdfjs.mjs';

const INTERNAL = Symbol('factoidal.Dataset.internal');

// Writer names (lower case) -> the engine's writer tag. JSON-LD is served
// by the op datasetToJsonLd; the SPARQL results formats are query outputs.
const WRITER_TAGS = {
  nquads: 'nquads', nq: 'nquads', 'n-quads': 'nquads',
  ntriples: 'ntriples', nt: 'ntriples', 'n-triples': 'ntriples',
  turtle: 'turtle', ttl: 'turtle',
  trig: 'trig',
  rdfxml: 'rdfxml', 'rdf-xml': 'rdfxml', rdf: 'rdfxml',
  jsonld: 'jsonld', 'json-ld': 'jsonld',
  rdfc: 'rdfc', canonical: 'rdfc', 'rdfc-1.0': 'rdfc',
};

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
    const tag = WRITER_TAGS[name];
    if (!tag) {
      throw new TypeError(
        `Dataset.serialize: unknown format '${opts.format}'. Known formats: ` +
        [...new Set(Object.values(WRITER_TAGS))].join(', '));
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
   * RDF/JS quads, read from the engine's N-Quads text one line at a time.
   * @returns {Iterator<object>}
   */
  *[Symbol.iterator]() {
    this._open('iterate');
    if (this._quads) { yield* this._quads; return; }
    const text = this.toNQuads();
    let start = 0;
    let lineNo = 0;
    while (start < text.length) {
      let end = text.indexOf('\n', start);
      if (end < 0) end = text.length;
      lineNo += 1;
      const line = text.slice(start, end);
      start = end + 1;
      const q = nquadsLineToQuad(line, lineNo);
      if (q) yield q;
    }
  }

  /** Every quad as an array. */
  toArray() {
    this._open('toArray');
    if (!this._quads) this._quads = Object.freeze([...this]);
    return this._quads.slice();
  }

  /** RDF/JS DatasetCore.has. */
  has(quad) {
    this._open('has');
    const line = quadToNQuads(quad);
    return this.toArray().some((q) => quadToNQuads(q) === line);
  }

  /**
   * RDF/JS DatasetCore.match: the quads that match, as a new Dataset.
   * `null`/`undefined` matches any term.
   */
  match(subject, predicate, object, graph) {
    this._open('match');
    const keep = this.toArray().filter((q) =>
      (!subject || subject.equals(q.subject)) &&
      (!predicate || predicate.equals(q.predicate)) &&
      (!object || object.equals(q.object)) &&
      (!graph || graph.equals(q.graph)));
    return this._ctx.fromNQuads(keep.map(quadToNQuads).join(''), this._prefixes);
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
