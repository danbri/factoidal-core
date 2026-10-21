// factoidal — RDF/JS data model + N-Quads token converters.
//
// Implements the RDF/JS Data Model specification
// (https://rdf.js.org/data-model-spec/): DataFactory producing
// NamedNode / BlankNode / Literal / Variable / DefaultGraph / Quad
// terms with spec-compliant `termType` / `value` / `language` /
// `datatype` and `.equals()`. Self-contained — no runtime deps.
//
// Also: the field copy between RDF/JS terms and the engine's term objects
// (Lean L4Factoidal.RDF.TermJson), and N-Quads text in and out through
// engine ops. This file reads and writes no RDF syntax itself: no escaping,
// no tokenising (https://github.com/danbri/factoidal/issues/894). The text
// functions need the engine, which lib/api.mjs installs when it loads.
//
// ES module (0.9.0): the same file serves Node (index.mjs, and rdfjs.js for
// require()) and the browser (browser.js), with no build step.

// RDF/JS Data Model defaults of DataFactory.literal.
const XSD_STRING = 'http://www.w3.org/2001/XMLSchema#string'; // purity-lint: allow RDF/JS DataFactory default
const RDF_LANGSTRING =
  'http://www.w3.org/1999/02/22-rdf-syntax-ns#langString'; // purity-lint: allow RDF/JS DataFactory default

// ---------------------------------------------------------------------
// Terms
// ---------------------------------------------------------------------

class NamedNode {
  constructor(iri) {
    this.termType = 'NamedNode';
    this.value = iri;
    Object.freeze(this);
  }
  equals(other) {
    return !!other && other.termType === 'NamedNode' &&
      other.value === this.value;
  }
}

class BlankNode {
  constructor(label) {
    this.termType = 'BlankNode';
    this.value = label;
    Object.freeze(this);
  }
  equals(other) {
    return !!other && other.termType === 'BlankNode' &&
      other.value === this.value;
  }
}

class Literal {
  constructor(value, language, datatype, direction) {
    this.termType = 'Literal';
    this.value = value;
    this.language = language || '';
    // RDF/JS Data Model DataFactory.literal: no datatype argument means
    // xsd:string, a language means rdf:langString.
    this.datatype = datatype ||
      new NamedNode(language ? RDF_LANGSTRING : XSD_STRING); // purity-lint: allow RDF/JS DataFactory default
    this.direction = direction || '';
    Object.freeze(this);
  }
  equals(other) {
    return !!other && other.termType === 'Literal' &&
      other.value === this.value &&
      other.language === this.language &&
      (other.direction || '') === this.direction &&
      !!other.datatype && other.datatype.value === this.datatype.value;
  }
}

class Variable {
  constructor(name) {
    this.termType = 'Variable';
    this.value = name;
    Object.freeze(this);
  }
  equals(other) {
    return !!other && other.termType === 'Variable' &&
      other.value === this.value;
  }
}

class DefaultGraph {
  constructor() {
    this.termType = 'DefaultGraph';
    this.value = '';
    Object.freeze(this);
  }
  equals(other) {
    return !!other && other.termType === 'DefaultGraph';
  }
}

const DEFAULT_GRAPH = new DefaultGraph();

class Quad {
  constructor(subject, predicate, object, graph) {
    // Per spec, a Quad is itself a Term with termType 'Quad', value ''.
    this.termType = 'Quad';
    this.value = '';
    this.subject = subject;
    this.predicate = predicate;
    this.object = object;
    this.graph = graph || DEFAULT_GRAPH;
    Object.freeze(this);
  }
  equals(other) {
    return !!other &&
      (other.termType === 'Quad' || other.termType === undefined) &&
      this.subject.equals(other.subject) &&
      this.predicate.equals(other.predicate) &&
      this.object.equals(other.object) &&
      this.graph.equals(other.graph);
  }
}

// ---------------------------------------------------------------------
// DataFactory
// ---------------------------------------------------------------------

let blankNodeCounter = 0;

const dataFactory = {
  namedNode(value) {
    return new NamedNode(String(value));
  },
  blankNode(label) {
    return new BlankNode(
      label !== undefined && label !== null
        ? String(label)
        : 'fjs_b' + (blankNodeCounter++)
    );
  },
  literal(value, languageOrDatatype) {
    const v = String(value);
    if (languageOrDatatype === undefined || languageOrDatatype === null) {
      return new Literal(v, '', null);
    }
    if (typeof languageOrDatatype === 'string') {
      return new Literal(v, languageOrDatatype, null);
    }
    // RDF/JS Data Model 1.1: {language, direction} for a directional
    // language-tagged string.
    if (typeof languageOrDatatype.language === 'string' && languageOrDatatype.termType === undefined) {
      return new Literal(v, languageOrDatatype.language, null, languageOrDatatype.direction || '');
    }
    // A NamedNode datatype.
    if (languageOrDatatype.termType === 'NamedNode') {
      if (languageOrDatatype.value === RDF_LANGSTRING) {
        // langString without a language tag is not constructible; treat
        // as plain string per the most defensive reading of the spec.
        return new Literal(v, '', null);
      }
      return new Literal(v, '', new NamedNode(languageOrDatatype.value));
    }
    throw new TypeError(
      'literal: second argument must be a language string or a NamedNode'
    );
  },
  variable(name) {
    return new Variable(String(name));
  },
  defaultGraph() {
    return DEFAULT_GRAPH;
  },
  quad(subject, predicate, object, graph) {
    return new Quad(subject, predicate, object, graph);
  },
  fromTerm(original) {
    if (!original || typeof original.termType !== 'string') {
      throw new TypeError('fromTerm: not a term');
    }
    switch (original.termType) {
      case 'NamedNode':    return new NamedNode(original.value);
      case 'BlankNode':    return new BlankNode(original.value);
      case 'Variable':     return new Variable(original.value);
      case 'DefaultGraph': return DEFAULT_GRAPH;
      case 'Literal':
        return new Literal(
          original.value,
          original.language || '',
          original.datatype ? new NamedNode(original.datatype.value) : null,
          original.direction || ''
        );
      case 'Quad':         return dataFactory.fromQuad(original);
      default:
        throw new TypeError(`fromTerm: unknown termType '${original.termType}'`);
    }
  },
  fromQuad(original) {
    if (!original || !original.subject) {
      throw new TypeError('fromQuad: not a quad');
    }
    return new Quad(
      dataFactory.fromTerm(original.subject),
      dataFactory.fromTerm(original.predicate),
      dataFactory.fromTerm(original.object),
      original.graph ? dataFactory.fromTerm(original.graph) : DEFAULT_GRAPH
    );
  },
};

// ---------------------------------------------------------------------
// SPARQL Results JSON term -> RDF/JS term
// ---------------------------------------------------------------------

/**
 * Convert a SPARQL 1.1 Results JSON term object
 * ({type:'uri'|'bnode'|'literal'|'typed-literal', value, 'xml:lang',
 * datatype}) into an RDF/JS term.
 */
function termFromSrj(t) {
  return termFromSrjWith(t, dataFactory);
}

function termFromSrjWith(t, f) {
  if (!t || typeof t.type !== 'string') {
    throw new TypeError('termFromSrj: not a results-JSON term');
  }
  switch (t.type) {
    case 'uri':
      return f.namedNode(t.value);
    case 'bnode':
      return f.blankNode(t.value);
    case 'literal':
    case 'typed-literal': {
      const lang = t['xml:lang'];
      if (lang) {
        if (t['its:dir'] && f === dataFactory) {
          return new Literal(t.value, lang,
            t.datatype ? new NamedNode(t.datatype) : null, t['its:dir']);
        }
        return f.literal(t.value, lang);
      }
      if (t.datatype) return f.literal(t.value, f.namedNode(t.datatype));
      return f.literal(t.value);
    }
    case 'triple': {
      // RDF 1.2 triple term:
      // {"type":"triple","value":{"subject":T,"predicate":T,"object":T}}
      // -> an RDF/JS Quad term. The object may itself be a triple term.
      const v = t.value || {};
      return f.quad(termFromSrjWith(v.subject, f), termFromSrjWith(v.predicate, f),
        termFromSrjWith(v.object, f));
    }
    default:
      throw new TypeError(`termFromSrj: unknown term type '${t.type}'`);
  }
}

// ---------------------------------------------------------------------
// RDF/JS term <-> engine term object (Lean `L4Factoidal.RDF.TermJson`).
//
// These functions copy fields; they read and write no RDF syntax. Every
// N-Quads parse and write below is an engine op
// (https://github.com/danbri/factoidal/issues/894 items 1 and 2).
// ---------------------------------------------------------------------

/** The engine term object of an RDF/JS term (`TermJson.encodeTerm`'s shape). */
function termToJson(term) {
  if (term === null || term === undefined) return null;
  // A term given as text is one RDF 1.2 N-Triples term (`<IRI>`, `_:label`,
  // a literal, `<<( s p o )>>`). The engine reads it
  // (L4Factoidal.RDF.TermJson.readTermString); this file copies the text.
  if (typeof term === 'string') return { type: 'nt', value: term };
  switch (term.termType) {
    case 'NamedNode': return { type: 'uri', value: term.value };
    case 'BlankNode': return { type: 'bnode', value: term.value };
    case 'Literal': {
      const o = { type: 'literal', value: term.value };
      if (term.datatype) o.datatype = term.datatype.value;
      if (term.language) o['xml:lang'] = term.language;
      if (term.direction) o['its:dir'] = term.direction;
      return o;
    }
    case 'Quad':
      return { type: 'triple', value: {
        subject: termToJson(term.subject), predicate: termToJson(term.predicate),
        object: termToJson(term.object) } };
    case 'DefaultGraph': return { type: 'default' };
    default:
      throw new TypeError(`termToJson: cannot send termType '${term.termType}' to the engine`);
  }
}

/**
 * The engine term object of a term an application supplies, for example an
 * extension function's answer: an RDF/JS term (duck-typed on termType), an
 * engine term object ({type, value, ...}), or a plain object
 * {value, datatype} or {value, language, direction?}. The components are
 * copied as given; the engine checks them (TermJson.decodeCheckedTerm) and
 * keeps the lexical form and the datatype IRI unchanged.
 */
function appTermToJson(out) {
  if (typeof out.termType === 'string') return termToJson(out);
  if (typeof out.type === 'string') return out;
  const o = { type: 'literal', value: out.value };
  if (out.datatype !== undefined && out.datatype !== null) {
    o.datatype = typeof out.datatype === 'string' ? out.datatype : out.datatype.value;
  }
  if (out.language !== undefined && out.language !== null && out.language !== '') o['xml:lang'] = out.language;
  if (out.direction !== undefined && out.direction !== null && out.direction !== '') o['its:dir'] = out.direction;
  return o;
}

/** The engine quad array of an RDF/JS quad: [s, p, o] or [s, p, o, g]. */
function quadToJson(quad) {
  const out = [termToJson(quad.subject), termToJson(quad.predicate), termToJson(quad.object)];
  if (quad.graph && quad.graph.termType !== 'DefaultGraph') out.push(termToJson(quad.graph));
  return out;
}

/** The RDF/JS quad of an engine quad array. */
function quadFromJson(arr, factory) {
  const f = factory || dataFactory;
  return f.quad(termFromSrjWith(arr[0], f), termFromSrjWith(arr[1], f),
    termFromSrjWith(arr[2], f), arr.length > 3 ? termFromSrjWith(arr[3], f) : f.defaultGraph());
}

// The engine the text functions below call. lib/api.mjs installs it when it
// loads the engine; until then they throw.
let textEngine = null;

/** @private lib/api.mjs: install the engine ops the text functions call. */
function _setTextEngine(engine) { textEngine = engine; }

function needEngine(who) {
  if (!textEngine) {
    throw new Error(
      `${who}: N-Quads text is read and written by the engine, which is not ` +
      'loaded yet. Await any @factoidal/core call first (for example ' +
      '`await ready()`), or use parse() and Dataset.toString().');
  }
  return textEngine;
}

/** One RDF/JS term as its canonical N-Quads token (the engine writes it). */
function termToNQuads(term) {
  if (term && term.termType === 'DefaultGraph') return '';
  return needEngine('termToNQuads').termTokens([termToJson(term)])[0];
}

/** One RDF/JS quad as its canonical N-Quads line (with trailing newline). */
function quadToNQuads(quad) {
  return needEngine('quadToNQuads').writeQuads([quadToJson(quad)]);
}

/** An iterable of RDF/JS quads as an N-Quads document, one line per quad. */
function quadsToNQuads(quads) {
  const arr = [];
  for (const q of quads) arr.push(quadToJson(q));
  return needEngine('quadsToNQuads').writeQuads(arr);
}

/**
 * Parse an N-Quads document (RDF 1.2 grammar) into RDF/JS quads; the engine
 * parses it and rejects any line the grammar rejects.
 * The quads come in the engine's order: the default graph, then each named
 * graph in the order of its first quad.
 * options.blankNodePrefix: prepended to every blank-node label (keeps the
 * labels of separate documents apart); options.factory: an RDF/JS
 * DataFactory.
 */
function nquadsToQuads(text, options) {
  const opts = options || {};
  const factory = opts.factory || dataFactory;
  const f = opts.blankNodePrefix
    ? { ...factory, blankNode: (label) => factory.blankNode(opts.blankNodePrefix + label) }
    : factory;
  const quads = needEngine('nquadsToQuads').parseQuads(String(text));
  return quads.map((q) => quadFromJson(q, f));
}

/** One N-Quads statement as an RDF/JS quad; null for a blank or comment line. */
function nquadsLineToQuad(line, _lineNo, factory) {
  const qs = nquadsToQuads(line, { factory });
  return qs.length ? qs[0] : null;
}

// ---------------------------------------------------------------------
// Dataset — a minimal RDF/JS DatasetCore over an in-memory quad array.
// ---------------------------------------------------------------------

// A string that two terms share exactly when equals() holds between them
// (the fields each equals() above compares). JSON arrays are
// self-delimiting, so the key of a quad, four term keys in a row, is
// injective too. The Dataset keeps the keys of its quads in a Set: add()
// and has() are then one lookup each. Until 2026-10-10 both scanned the
// quad array, so building a Dataset of n quads cost n^2/2 equals() calls:
// 12,000 quads took 3.1 s in parse() (issue 713 stage 5).
function termKey(t) {
  if (!t) return 'null';
  switch (t.termType) {
    case 'Literal':
      return JSON.stringify(['Literal', t.value, t.language, t.datatype ? t.datatype.value : null,
        t.direction || '']);
    case 'DefaultGraph':
      return '["DefaultGraph"]';
    case 'Quad':
      return '["Quad",' + termKey(t.subject) + ',' + termKey(t.predicate) + ',' +
        termKey(t.object) + ',' + termKey(t.graph) + ']';
    default:
      return JSON.stringify([t.termType, t.value]);
  }
}

function quadKey(q) {
  return termKey(q.subject) + termKey(q.predicate) + termKey(q.object) +
    termKey(q.graph || DEFAULT_GRAPH);
}

/**
 * An in-memory RDF/JS DatasetCore over a quad array. The package's Dataset
 * (lib/dataset.mjs) keeps its data in the engine; this class is for callers
 * that build quads in JavaScript, for example to hand to fn.js.
 */
class DatasetCore {
  constructor(quads, options) {
    this._quads = [];
    // The quadKey() of every quad in _quads, for set semantics in O(1).
    this._keys = new Set();
    if (quads) for (const q of quads) this.add(q);
    const opts = options || {};
    // Own, non-enumerable properties (issue #680/#681): a frozen
    // snapshot of the prefixes/diagnostics the engine reported at
    // parse time, so JSON.stringify()/toArray() (and any caller
    // enumerating own enumerable keys) see only the quads, exactly as
    // before this landed.
    Object.defineProperty(this, 'prefixes', {
      value: Object.freeze({ ...(opts.prefixes || {}) }),
      enumerable: false, writable: false, configurable: false,
    });
    Object.defineProperty(this, 'diagnostics', {
      value: Object.freeze((opts.diagnostics || []).slice()),
      enumerable: false, writable: false, configurable: false,
    });
  }
  get size() {
    return this._quads.length;
  }
  add(quad) {
    const key = quadKey(quad);
    if (!this._keys.has(key)) {
      this._keys.add(key);
      this._quads.push(quad);
    }
    return this;
  }
  delete(quad) {
    if (this._keys.delete(quadKey(quad))) {
      const ix = this._quads.findIndex((q) => q.equals(quad));
      if (ix >= 0) this._quads.splice(ix, 1);
    }
    return this;
  }
  has(quad) {
    return this._keys.has(quadKey(quad));
  }
  match(subject, predicate, object, graph) {
    const out = new DatasetCore();
    for (const q of this._quads) {
      if (subject   && !subject.equals(q.subject))     continue;
      if (predicate && !predicate.equals(q.predicate)) continue;
      if (object    && !object.equals(q.object))       continue;
      if (graph     && !graph.equals(q.graph))         continue;
      out._quads.push(q);
      out._keys.add(quadKey(q));
    }
    return out;
  }
  [Symbol.iterator]() {
    return this._quads[Symbol.iterator]();
  }
  toArray() {
    return this._quads.slice();
  }
  /** N-Quads text, written by the engine. */
  toNQuads() {
    return quadsToNQuads(this._quads);
  }
  toString() {
    return this.toNQuads();
  }
  static fromNQuads(text, options) {
    return new DatasetCore(nquadsToQuads(text, options), options);
  }
}

export {
  dataFactory,
  NamedNode,
  BlankNode,
  Literal,
  Variable,
  DefaultGraph,
  Quad,
  DatasetCore,
  termFromSrj,
  termToJson,
  appTermToJson,
  quadToJson,
  quadFromJson,
  quadKey,
  termKey,
  _setTextEngine,
  nquadsLineToQuad,
  termToNQuads,
  quadToNQuads,
  quadsToNQuads,
  nquadsToQuads,
  XSD_STRING,
  RDF_LANGSTRING,
}
