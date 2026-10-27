// TypeScript declarations for @factoidal/core 0.9: one engine, the Lean 4
// library L4Factoidal compiled to WebAssembly (formal/lean4). Every
// function below is a dispatch op of that module (Wasm/Dispatch.lean)
// behind a typed wrapper (lib/api.mjs). The same declarations describe
// browser.js (browser.d.ts re-exports them).
//
// Self-contained: the RDF/JS interfaces below are structurally
// compatible with @rdfjs/types (same names and shapes) but declared
// here so the package has zero dependencies.

// ---------------------------------------------------------------------
// RDF/JS data model (https://rdf.js.org/data-model-spec/)
// ---------------------------------------------------------------------

export interface NamedNode<Iri extends string = string> {
  termType: 'NamedNode';
  value: Iri;
  equals(other: Term | null | undefined): boolean;
}

export interface BlankNode {
  termType: 'BlankNode';
  value: string;
  equals(other: Term | null | undefined): boolean;
}

export interface Literal {
  termType: 'Literal';
  value: string;
  /** Language tag ('' when none). */
  language: string;
  /** Datatype IRI term (xsd:string for plain literals). */
  datatype: NamedNode;
  equals(other: Term | null | undefined): boolean;
}

export interface Variable {
  termType: 'Variable';
  value: string;
  equals(other: Term | null | undefined): boolean;
}

export interface DefaultGraph {
  termType: 'DefaultGraph';
  value: '';
  equals(other: Term | null | undefined): boolean;
}

export interface Quad {
  termType: 'Quad';
  value: '';
  subject: Quad_Subject;
  predicate: Quad_Predicate;
  object: Quad_Object;
  graph: Quad_Graph;
  equals(other: Quad | null | undefined): boolean;
}

export type Quad_Subject = NamedNode | BlankNode | Variable;
export type Quad_Predicate = NamedNode | Variable;
export type Quad_Object = NamedNode | BlankNode | Literal | Variable;
export type Quad_Graph = DefaultGraph | NamedNode | BlankNode | Variable;

export type Term =
  | NamedNode | BlankNode | Literal | Variable | DefaultGraph | Quad;

export interface DataFactory {
  namedNode<Iri extends string = string>(value: Iri): NamedNode<Iri>;
  blankNode(label?: string): BlankNode;
  literal(value: string, languageOrDatatype?: string | NamedNode): Literal;
  variable(name: string): Variable;
  defaultGraph(): DefaultGraph;
  quad(
    subject: Quad_Subject,
    predicate: Quad_Predicate,
    object: Quad_Object,
    graph?: Quad_Graph
  ): Quad;
  fromTerm(original: Term): Term;
  fromQuad(original: Quad): Quad;
}

/** The package's RDF/JS DataFactory. */
export const dataFactory: DataFactory;

/**
 * The stable error codes. The engine decides the code of every refusal
 * (formal/lean4/Wasm/Ops/ErrorModel.lean); `engineTables().errorCodes` lists
 * each with its specification section and summary, and the README table
 * "Errors" is generated from that list. `host.io` is a failure of
 * the host (file system, IndexedDB), not of the engine.
 */
export type FactoidalErrorCode =
  | 'parse.syntax'
  | 'parse.rdf12-required'
  | 'term.invalid-iri'
  | 'term.invalid-langtag'
  | 'term.invalid'
  | 'query.syntax'
  | 'query.failed'
  | 'update.syntax'
  | 'update.failed'
  | 'format.unknown'
  | 'serialize.unsupported-rdf12'
  | 'serialize.failed'
  | 'canon.unsupported-rdf12'
  | 'canon.failed'
  | 'owl.unsupported-rdf12'
  | 'reason.failed'
  | 'regime.refused'
  | 'validate.failed'
  | 'xml.failed'
  | 'crypto.failed'
  | 'store.failed'
  | 'registry.failed'
  | 'handle.unknown'
  | 'handle.disposed'
  | 'option.unknown'
  | 'option.invalid-value'
  | 'option.conflict'
  | 'capacity.exceeded'
  | 'call.arity'
  | 'call.arguments'
  | 'op.unknown'
  | 'op.failed'
  | 'host.io';

/** Where in the input a FactoidalError happened. */
export interface FactoidalErrorPosition {
  /** 1-based line. */
  line: number;
  /** 1-based column, counted in Unicode scalar values. */
  column: number;
  /**
   * A UTF-16 code-unit index into the input JavaScript string:
   * `text.slice(err.position.offset)` starts at the error.
   */
  offset: number;
  /** The same position as a count of UTF-8 bytes from the start of the input. */
  byteOffset: number;
}

/**
 * The one error class of the package. Every function rejects (or throws)
 * with it; a `TypeError` is thrown only when an argument has the wrong
 * JavaScript type. The engine decides `code`, `spec` and `position`.
 */
export class FactoidalError extends Error {
  constructor(message: string, info?: {
    code?: FactoidalErrorCode; position?: FactoidalErrorPosition | null;
    spec?: string | null; cause?: unknown; format?: string; formatInferred?: boolean;
  });
  readonly name: 'FactoidalError';
  /** The stable machine code. */
  readonly code: FactoidalErrorCode;
  /** Where the input defines a position (a parse, a query, an update), else null. */
  readonly position: FactoidalErrorPosition | null;
  /** The URL of the specification section that defines the condition, else null. */
  readonly spec: string | null;
  /** The underlying error, when there is one (host.io). */
  readonly cause?: unknown;
  /** For a parse failure of text: the syntax it was read as. */
  readonly format?: string;
  /** For a parse failure of text: true when the syntax was inferred. */
  readonly formatInferred?: boolean;
}

/** One recoverable-parse diagnostic from a `{lenient:true}` parse() call. */
export interface ParseDiagnostic {
  message: string;
  /**
   * The position of the error as a UTF-16 code-unit index into the input
   * JavaScript string, as FactoidalError.position.offset: `text.slice(d.offset)` starts
   * at the error.
   */
  offset: number;
  /** 1-based; a line ends at each LINE FEED (CR LF is one line end). */
  line: number;
  /** 1-based, counted in Unicode scalar values from the start of the line. */
  column: number;
  /**
   * The stable error class (https://github.com/danbri/factoidal/issues/716):
   * 'undefined-prefix', 'relative-iri', 'bad-iri', 'bad-escape',
   * 'unterminated-string', 'bad-literal', 'bad-blank-node',
   * 'bad-prefixed-name', 'bad-directive', 'bad-graph-name', 'rdf12-syntax',
   * 'unclosed-group', 'nesting-limit', 'unexpected-token', 'internal' or
   * 'too-many-errors'. A warning (`Dataset.warnings`) has the class
   * 'ill-formed-language-tag'.
   */
  class: string;
}

/** Every options key of Dataset.serialize(), serialize() and toString(). */
export interface WriteOptions {
  /**
   * 'nquads' (default; sorted line order), 'ntriples' (refused when the
   * dataset has a named graph), 'turtle', 'trig', 'rdfxml', 'jsonld'
   * (expanded JSON-LD 1.1), 'rdfc' (RDFC-1.0 canonical N-Quads). Turtle and
   * RDF/XML write the named graphs as one graph. `formats()` lists what
   * each writer supports.
   */
  format?: WriteFormat;
  /** '1.1' refuses a dataset with an RDF 1.2 term; '1.2' (default) writes it. */
  version?: '1.1' | '1.2';
  /** 'turtle' only: prefix label -> namespace IRI, merged over `dataset.prefixes`. */
  prefixes?: Record<string, string>;
  /** 'turtle' only. Default true: integers, decimals, doubles and booleans print bare. */
  literalShorthand?: boolean;
  /** 'jsonld' only (JSON-LD 1.1 API section 8). */
  useNativeTypes?: boolean;
  /** 'jsonld' only. */
  useRdfType?: boolean;
  /** 'jsonld' only. */
  rdfDirection?: string;
  /** 'jsonld' only: write RDF 1.2 triple terms as JSON-LD-star (`@triple`,
   *  `@reifies`, `@annotation`). Without it a triple term is refused. */
  rdfstar?: boolean;
}

export type WriteFormat =
  | 'nquads' | 'nq' | 'ntriples' | 'nt' | 'turtle' | 'ttl' | 'trig'
  | 'rdfxml' | 'rdf-xml' | 'rdf' | 'jsonld' | 'json-ld' | 'rdfc' | 'canonical';

/** Results formats of query() with `output`. */
export type ResultsFormat = 'json' | 'xml' | 'csv' | 'tsv' | 'table' | 'ntriples';

/** One row of formats(). */
export interface FormatCapability {
  name: string;
  read11: boolean;
  read12: boolean;
  write11: boolean;
  write12: boolean;
  /** 'core' when both engines serve it; 'full' when only the full engine does. */
  engine: 'core' | 'full';
}

/**
 * An RDF dataset held inside the engine (https://github.com/danbri/factoidal/issues/882).
 * Every producer (parse, csvwToRdf, rmlMap, jsonldToRdf, the closures,
 * rifEval, CONSTRUCT) answers one; every consumer accepts one. The data
 * stays in the wasm memory: a method sends the handle id, not the data.
 * Release it with dispose() or `using`; a Dataset collected without
 * dispose() is released by a FinalizationRegistry. A method of a disposed
 * Dataset throws a TypeError.
 */
export class Dataset implements Iterable<Quad> {
  private constructor();
  /** The engine's handle id (opaque). */
  readonly handle: string;
  /** Number of quads. */
  readonly size: number;
  /** Prefixes the source document declared (label -> namespace IRI). */
  readonly prefixes: Record<string, string>;
  /** Diagnostics of a `{lenient:true}` parse; else empty. */
  readonly diagnostics: ParseDiagnostic[];
  /**
   * Warnings of the parse of text: one per language tag that is not
   * well-formed under BCP 47 section 2.2.9 (class 'ill-formed-language-tag',
   * the position of the tag's first character). The reader keeps the triple
   * and the writers write the tag unchanged. Empty otherwise.
   */
  readonly warnings: ParseDiagnostic[];
  /** The parse format tag, when the data was read from text. */
  readonly format: string | undefined;
  /** True when `format` was inferred because the caller gave none. */
  readonly formatInferred: boolean;
  /** True after dispose(). */
  readonly disposed: boolean;
  /** Members the producing op reported: `rounds` (rho-df, RDFS-Plus closures); `inputCount`, `derivedCount`, `fuel` (rifEval). */
  readonly info: Record<string, unknown>;
  query(sparql: string, options?: DatasetQueryOptions): Promise<Bindings[] | boolean | Dataset | string | object>;
  /** SPARQL 1.1 Update in place; answers this Dataset. */
  update(updateText: string, options?: Record<string, never>): Promise<this>;
  validateShacl(shapes: DataInput, options?: { format?: DataFormat; baseIRI?: string }): Promise<ShaclValidateResult>;
  validateShex(schema: string, options: { focus: string | NamedNode | BlankNode; shape?: string | NamedNode | BlankNode | null }): Promise<boolean>;
  closure(regime: ClosureRegime): Promise<Dataset>;
  canonicalize(): Promise<string>;
  serialize(options?: WriteOptions): Promise<string>;
  toString(formatOrOptions?: WriteFormat | WriteOptions): string;
  toNQuads(): string;
  clone(): Dataset;
  /**
   * RDF/JS DatasetCore (https://rdf.js.org/dataset-spec/); match and has use
   * the engine indexes. `{match: 'value'}`: a literal object matches every
   * object literal that is the same term or has the same value (sameValue());
   * the other positions match by term.
   */
  has(quad: Quad, options?: MatchOptions): boolean;
  add(quad: Quad): this;
  /** With `{match: 'value'}`: remove every quad of the same subject, predicate
   *  and graph whose object has the same value as the quad's literal object. */
  delete(quad: Quad, options?: MatchOptions): this;
  match(subject?: Term | null, predicate?: Term | null, object?: Term | null, graph?: Term | null,
    options?: MatchOptions): Dataset;
  toArray(): Quad[];
  [Symbol.iterator](): Iterator<Quad>;
  dispose(): void;
  [Symbol.dispose](): void;
}


export type ClosureRegime = 'rdfs' | 'owl-rl' | 'rho-df' | 'rdfs-plus';

export interface DatasetQueryOptions {
  sparql12?: boolean;
  version?: '1.1' | '1.2';
  /** Close the default graph under a regime before the query. */
  entail?: EntailRegime;
  /** Answer the results document in this format (text; 'json' parsed). */
  output?: ResultsFormat;
}

// ---------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------

/** RDF serialization format tags accepted for input text. */
export type DataFormat =
  | 'turtle' | 'ttl'
  | 'ntriples' | 'nt'
  | 'nquads' | 'nq'
  | 'trig'
  | 'rdfxml' | 'rdf-xml' | 'rdf'
  | 'jsonld' | 'json-ld'
  // RDF 1.2 parsers (triple terms, reifiers, annotations, VERSION,
  // directional language tags). The names above parse RDF 1.1 and reject
  // RDF 1.2 syntax with "requires RDF 1.2 mode".
  | 'turtle12' | 'ttl12'
  | 'ntriples12' | 'nt12'
  | 'nquads12' | 'nq12'
  | 'trig12';

/** Entailment regime applied to the data before evaluation. */
/**
 * Entailment regime for query(): the W3C-named regimes plus two
 * experimental certified regimes (RDF.Entailment.RegimeDispatch.fst) —
 * 'x-rdfscore': BGP answers over the theorem-backed corerdfs (ρdf)
 * closure, sound and complete on fragment data;
 * 'x-rdfsplus': RDFS plus the practical OWL subset, every rule under
 * proved licensing + truth lemmas. See docs/theorem-registry.md.
 */
export type EntailRegime = 'none' | 'RDFS' | 'OWL-RL' | 'x-rdfscore' | 'x-rdfsplus';

/**
 * One SELECT solution: a Map from variable name (no leading '?') to
 * the bound RDF/JS term. Unbound variables are absent from the Map. The
 * Map iterates in the order of the SELECT clause (the `head.vars` of the
 * SPARQL 1.1 Query Results JSON Format, section 3.1).
 */
export type Bindings = Map<string, Term>;

/**
 * Input data: a Dataset, a document string, or several of either. Text
 * is read in `options.format`; with no format the engine infers one and
 * the error (or `dataset.format`) reports it.
 */
export type DataInput =
  | Dataset
  | string
  | { text: string; format?: DataFormat; baseIRI?: string }
  | Array<Dataset | string | { text: string; format?: DataFormat; baseIRI?: string }>;

/** Same as DataInput (kept for 0.9 type imports). */
export type QueryInput = DataInput;

export interface ParseOptions {
  /** Omitted: inferred by the engine (op detectFormat), reported in `dataset.format`. */
  format?: DataFormat;
  /** Base IRI for resolving relative IRIs (Turtle/TriG/RDF-XML). */
  baseIRI?: string;
  /**
   * Recover instead of rejecting on the first syntax error
   * (https://github.com/danbri/factoidal/issues/716, engine op
   * `parseDocument`): Turtle, TriG, N-Triples and N-Quads skip each bad
   * statement and keep every good one; `dataset.diagnostics` has one
   * entry per skipped statement. RDF/XML and JSON-LD parse strictly. A
   * document with no error gives the strict result and no diagnostics.
   * Default: false (strict; a syntax error, an undeclared prefix, or an
   * unresolvable relative IRI rejects the whole parse with a FactoidalError).
   */
  lenient?: boolean;
  /**
   * With `lenient`: stop after this many diagnostics; the parse then ends
   * with one diagnostic of class 'too-many-errors'. Default: no limit.
   */
  maxErrors?: number;
}

export interface QueryOptions extends DatasetQueryOptions {
  /** Format tag for string data inputs; omitted: inferred. */
  format?: DataFormat;
  baseIRI?: string;
}

/**
 * Parse one RDF document into a Dataset. The returned Dataset's quad
 * order is sorted (canonical N-Quads order), not document order;
 * anonymous blank-node labels (`_anonN`) DO reflect document order.
 * See README.md's "Blank nodes, labels and statement order". Strict
 * by default (issue #344): a syntax error rejects with a FactoidalError
 * (`line`/`column`/`offset` for Turtle/TriG/N-Triples/N-Quads; a
 * message only for RDF/XML and JSON-LD). `options.lenient` recovers
 * instead; see ParseOptions.
 */
export function parse(text: string, options?: ParseOptions | DataFormat): Promise<Dataset>;

/**
 * Run a SPARQL 1.1 query (or 1.2, with `sparql12`).
 * SELECT resolves to Bindings[]; ASK resolves to a boolean;
 * CONSTRUCT and DESCRIBE resolve to a Dataset (DESCRIBE answers the
 * Concise Bounded Description of each resource named). A `SERVICE <iri>`
 * whose IRI no registerServiceEndpoint() call named answers no
 * solutions even without SILENT
 * (https://github.com/danbri/factoidal/issues/717). `data` may be a Dataset
 * from openDataset(), in which case this routes to `data.query()` and
 * `options.entail` must be 'none' or omitted (a handle carries no
 * entailment-closure step).
 */
export function query(
  data: QueryInput,
  sparql: string,
  options?: QueryOptions | DataFormat
): Promise<Bindings[] | boolean | Dataset | string | object>;

/**
 * Run a SPARQL 1.1 query against a read-only HDT (Header-Dictionary-
 * Triples) file's raw bytes (op queryHdt; the bytes cross into the
 * engine with no encoding). Default graph only, SELECT/ASK only.
 * @param hdtBytes whole .hdt file contents
 */
export function queryHdt(
  hdtBytes: Uint8Array | ArrayBuffer | string,
  sparql: string
): Promise<Bindings[] | boolean>;

/**
 * An argument or return value of a custom extension function, in the
 * SRJ term shape: {type:'uri'|'literal'|'bnode', value, datatype?,
 * 'xml:lang'?}. An errored argument arrives as {type:'error'}.
 */
export interface ExtensionTerm {
  type: 'uri' | 'literal' | 'bnode' | 'error';
  value?: string;
  datatype?: string;
  'xml:lang'?: string;
}

/**
 * Register a custom SPARQL extension function (SPARQL 1.1 §17.6,
 * issue #463; Comunica-style). `fn` may be sync or async; it receives
 * the evaluated arguments as ExtensionTerm[] and returns an
 * ExtensionTerm, a JS primitive (boolean | number | string), a
 * Promise of either, or null/undefined (= the §17.6 error). A query
 * calling an IRI with no registered function gets the same error:
 * unbound in SELECT/BIND position, row dropped in FILTER position.
 */
export function registerExtensionFunction(
  iri: string,
  fn: (args: ExtensionTerm[]) =>
    ExtensionTerm | boolean | number | string | null | undefined |
    Promise<ExtensionTerm | boolean | number | string | null | undefined>
): Promise<void>;

/** Remove one registered extension function. */
export function unregisterExtensionFunction(iri: string): Promise<void>;

/** Remove every registered extension function. */
export function clearExtensionFunctions(): Promise<void>;

/**
 * Bind a SPARQL SERVICE endpoint IRI to a local graph snapshot, so
 * SERVICE <iri> { ... } (and LATERAL { SERVICE ... }) queries resolve
 * against it in-process — the same registry the W3C federated-query
 * suite uses (qt:serviceData). The snapshot is the payload's default
 * graph.
 */
export function registerServiceEndpoint(
  iri: string,
  data: DataInput,
  options?: { format?: DataFormat; baseIRI?: string }
): Promise<{ ok: true; count: number }>;

/** Remove every registered SERVICE endpoint snapshot. */
export function clearServiceEndpoints(): Promise<void>;

/** Apply a SPARQL 1.1 Update and answer a NEW Dataset; a Dataset argument is unchanged. */
export function update(
  data: DataInput,
  updateText: string,
  options?: { format?: DataFormat; baseIRI?: string } | DataFormat
): Promise<Dataset>;

/** Open `data` as a Dataset (a Dataset argument is cloned). */
export function openDataset(
  data: DataInput,
  options?: { format?: DataFormat; baseIRI?: string } | DataFormat
): Promise<Dataset>;

/** Closure of the default graph under `regime`, as a new Dataset. */
export function closure(
  data: DataInput,
  regime: ClosureRegime,
  options?: { format?: DataFormat; baseIRI?: string }
): Promise<Dataset>;

/** The syntaxes the engine reads and writes, from the engine (op datasetFormats). */
export function formats(): Promise<FormatCapability[]>;

export interface SerializeOptions extends WriteOptions {
  /** Format of string `data`; omitted: inferred. */
  inputFormat?: DataFormat;
  baseIRI?: string;
}

/** Write a dataset in a concrete syntax (see WriteOptions). */
export function serialize(
  data: DataInput,
  options?: SerializeOptions | WriteFormat
): Promise<string>;

/**
 * RDFC-1.0 dataset canonicalization: canonical blank-node labels plus
 * sorted canonical N-Quads. Two isomorphic inputs canonicalize to the
 * same string. `data` may be a Dataset, in which case this
 * routes to `data.canonicalize()` (options are ignored for a handle).
 */
export function canonicalize(
  data: DataInput,
  options?: { format?: DataFormat; baseIRI?: string } | DataFormat
): Promise<string>;

/**
 * Enumerate the named graphs of an already-parsed Dataset (default
 * graph excluded), in first-seen order. Pure enumeration over
 * `dataset`'s own quads -- no engine round-trip, always available.
 * `graph` is the same Dataset filtered to that one graph name (what
 * `dataset.match(null, null, null, graphTerm)` would return).
 */
export function graphs(dataset: Dataset): Array<[name: NamedNode | BlankNode, graph: Dataset]>;

/**
 * The RDFC-1.0 canonical hash of a single graph: the SHA-256 of its
 * canonical N-Quads document, as 64 lowercase hexadecimal digits (RDF
 * Dataset Canonicalization 1.0, section 4.4 note 2). The engine computes
 * the canonical form and the digest. Every quad's graph component is
 * dropped first, so isomorphic graphs (including under blank-node
 * relabeling) give the same hash whatever graph name they were extracted
 * from. Typically called with one entry of graphs()'s output. For the
 * canonical text, use canonicalize(). Rejects when the input holds an
 * RDF 1.2 triple term or the section 4.4 call budget is exceeded.
 */
export function canonicalHash(datasetOrGraph: Dataset): Promise<string>;

/**
 * Whether two datasets are isomorphic (RDF 1.1 Concepts 3.6 and 4; blank
 * nodes inside RDF 1.2 triple terms included). The engine decides
 * (op datasetIsomorphic); rejects when its blank-node search budget is
 * exceeded.
 */
export function isomorphic(a: DataInput, b: DataInput, options?: { format?: string; baseIRI?: string }): Promise<boolean>;

/** A Dataset holding RDF/JS quads; each term is sent to the engine as its components. */
export function fromQuads(quads: Iterable<Quad>): Promise<Dataset>;

/** Load the engine. Afterwards the N-Quads text functions of `@factoidal/core/rdfjs` work. */
export function ready(): Promise<void>;

/** The engine's name tables: format names, entailment regimes, query outputs, pack syntaxes. */
export function engineTables(): Promise<Record<string, unknown>>;

/**
 * How Dataset.has, match and delete compare the object position
 * (https://github.com/danbri/factoidal/issues/1052). 'term' (the default):
 * RDF term equality. 'value': a literal object matches by value (sameValue()).
 */
export interface MatchOptions {
  match?: 'term' | 'value';
}

/**
 * SPARQL 1.1 `=` on two RDF terms (sections 17.3 and 17.4.1.7), decided by the
 * engine: `true` the same value (`"01"^^xsd:integer` and `"1.0"^^xsd:decimal`),
 * `false` different values, `null` incomparable (the operator's type error:
 * two different literals of an unknown datatype, an ill-typed literal and
 * another literal, `xsd:integer` and `xsd:boolean`). `"NaN"^^xsd:double` is
 * not the same value as itself. A term is an RDF/JS term or an N-Triples term
 * string. Synchronous: the engine must be loaded (`await ready()`).
 */
export function sameValue(a: Term | string, b: Term | string): boolean | null;

/** A SHACL validation-report term (see shaclValidate). */
export interface ShaclValidateResult {
  conforms: boolean;
  /** The validation report graph: one sh:ValidationReport with
   *  sh:conforms, and one sh:result per validation result. */
  report: Dataset;
}

/**
 * SHACL validation (SHACL Core, SHACL-SPARQL constraints, SHACL 1.2 node
 * expressions) of the data graph's default graph. A shapes graph that
 * uses the SPARQL-based target of SHACL-AF, and a validation failure in
 * the sense of SHACL 5.3.2, reject.
 * @param data the data graph
 * @param shapes the shapes graph
 */
export function shaclValidate(
  data: DataInput,
  shapes: DataInput,
  options?: { format?: DataFormat; baseIRI?: string }
): Promise<ShaclValidateResult>;

/**
 * ShEx (Shape Expressions) validation of one focus node against one
 * shape, over the default graph of `data`. The Lean validator decides
 * every schema it reads, so the answer is a boolean (the type keeps
 * `null`, which an engine that defers a schema would answer). An
 * `IMPORT` in the schema is not followed.
 * @param schemaJson the schema as text: ShExJ when its first
 *   non-whitespace character is '{', ShExC otherwise
 * @param focus an IRI, "_:label", or an RDF/JS NamedNode/BlankNode term
 * @param shape a shape label (same shapes as focus); omit/null for the
 *   schema's own `start`
 */
export function shexValidate(
  data: DataInput,
  schemaJson: string,
  focus: string | NamedNode | BlankNode,
  shape?: string | NamedNode | BlankNode | null,
  options?: { format?: DataFormat; baseIRI?: string }
): Promise<boolean | null>;

/**
 * RDFS or OWL-RL entailment closure, materialized as a new Dataset
 * (input triples + derived triples). Default graph only.
 */
export function owlClosure(
  data: DataInput,
  mode: 'RDFS' | 'OWL-RL',
  options?: { format?: DataFormat; baseIRI?: string }
): Promise<Dataset>;

/**
 * The CERTIFIED six-rule core-RDFS closure
 * (formal/fstar/RDF.Entailment.RDFS.RhoDFClosure.fst's
 * `rho_df_closure`): rdfs2/3/5/7/9/11 only, with the machine-checked
 * decides-iff — on fragment inputs the result's simple query answers
 * are exactly the entailed consequences (see
 * docs/theorem-registry.md). Returns the closure as a new Dataset.
 * "corerdfs" is this project's API name for the fragment the
 * literature calls ρdf (subPropertyOf/subClassOf/type/domain/range —
 * Muñoz, Pérez & Gutierrez, "Simple and Efficient Minimal RDFS",
 * J. Web Semantics 7(3), 2009).
 */
export function coreRdfsClosure(
  data: DataInput,
  options?: { format?: DataFormat; baseIRI?: string }
): Promise<Dataset>;

/**
 * Decidable core-RDFS fragment check (L4Factoidal/RDFS, `isRhoDfFrag`):
 * is the data in the core-RDFS fragment coreRdfsClosure is defined for?
 */
export function coreRdfsCheck(
  data: DataInput,
  options?: { format?: DataFormat; baseIRI?: string }
): Promise<{ ok: boolean; fragment: boolean }>;

/** The evidence bundle and verdict of explain(). */
export interface ExplainResult {
  profile: 'rdfs';
  /** true: the checker accepted `bundle`; the sources RDFS-entail the description. */
  entailed: boolean;
  bundle: null | {
    sources: string;
    description: string;
    mapping: Array<{ bnode: string; term: string }>;
    steps: Array<{ rule: string; conclusion: string; premises: number[] }>;
    support: number[];
  };
  /** Named assumptions that `entailed: false` relies on. */
  assumptions: string[];
  rejection:
    | null
    | { kind: 'noMatch'; index: number; triple: string }
    | { kind: 'noJointMapping' }
    | { kind: 'checkerRefused'; reason: string };
  entailedMeans: string;
}

/**
 * Is `description` (blank nodes shared across its triples) RDFS-entailed by
 * `sources`? Full engine only; the description is default-graph only. Text
 * inputs are Turtle unless `format` says otherwise.
 * https://github.com/danbri/factoidal/issues/1002
 */
export function explain(
  sources: DataInput,
  description: DataInput,
  options?: {
    profile?: 'rdfs';
    format?: DataFormat;
    baseIRI?: string;
    sourcesFormat?: DataFormat;
    descriptionFormat?: DataFormat;
  }
): Promise<ExplainResult>;

/**
 * One registered stage, as the engine's op stageList reads it from the Lean
 * registry (L4Factoidal.Dataflow.registry).
 * https://github.com/danbri/factoidal/issues/1002
 */
export interface StageInfo {
  /** The stage declaration relative to L4Factoidal.Dataflow (or L4Factoidal); the area when there is none. */
  name: string;
  /** The full Lean declaration name, or null (status tested or missing). */
  declaration: string | null;
  area: string;
  dir: string;
  /** The interface type of the declaration (Stage, RdfReader, SoundReasoner, ...), or null. */
  kind: string | null;
  wireIn: string;
  wireOut: string;
  status: 'proved' | 'tested' | 'assumed' | 'missing';
  /** The contract declaration (full Lean name), or null. */
  contract: string | null;
  theorems: string[];
  /** The named assumptions of the stage (full Lean names). */
  assumptions: string[];
  tests: string[];
  note: string;
  /** false exactly when status is 'missing': such a stage does not run. */
  runnable: boolean;
  /**
   * true when this package has a function that runs the stage as a node AND
   * the engine reports the stage runnable (an older engine that reports a
   * stage 'missing' leaves it unbound).
   */
  bound: boolean;
}

/**
 * The status of a node: the registry status, or 'unproved' when the stage is
 * 'proved' and one of the node's settings is outside its proved domain (op
 * pipelineCheckNodes, Lean Dataflow/NodeSettings.lean).
 */
export type NodeStatus = StageInfo['status'] | 'unproved';

/** A setting outside the proved domain of its stage, with the reason. */
export interface OutsideSetting {
  readonly setting: string;
  readonly reason: string;
}

/** One evidence record: the node that ran and what it produced. */
export interface EvidenceRecord {
  stage: string;
  status: NodeStatus;
  contract: string | null;
  assumptions: string[];
  /** true iff `status` is 'proved'. */
  checked: boolean;
  /** true on a step that ran under run()'s `unchecked` opt-in and is not checked. */
  unchecked?: true;
  /** With `unchecked`: the status and named assumptions, or 'no contract' for a missing stage. */
  reason?: string;
  /** The node's own output beside the graph: the explain result, the SHACL report, the written text, ... */
  artefact: unknown;
  /**
   * The node's settings in canonical form (keys sorted at every depth; the
   * defaults of absent settings that narrow the contract, e.g. `lenient:
   * false`, `entail: 'none'`; a Dataset value as `{nquadsSha256}`). Present
   * when the engine has the op pipelineCheckNodes.
   */
  settings?: Record<string, unknown>;
  /** `sha256:` and the hex SHA-256 of the canonical settings text. */
  settingsDigest?: string;
  /** With status 'unproved': the registry status ('proved'). */
  registryStatus?: StageInfo['status'];
  /** With status 'unproved': the settings outside the proved domain. */
  outside?: OutsideSetting[];
}

/** The value on a wire. */
export interface Wire<G = unknown> {
  graph: G;
  evidence: EvidenceRecord[];
}

/** A node: a registered stage with its parameters. */
export interface FactoidalNode {
  readonly stage: string;
  readonly kind: string | null;
  /** The engine's status of this node with its settings (see NodeStatus). */
  readonly status: NodeStatus;
  /** The registry status of the stage. */
  readonly registryStatus: StageInfo['status'];
  readonly contract: string | null;
  readonly assumptions: readonly string[];
  readonly wireIn: string;
  /**
   * The output wire with these settings: for shippedEvaluator, 'Table' for
   * SELECT, 'Answer' for ASK, 'Dataset' for CONSTRUCT and DESCRIBE (Lean
   * formWire, evalContract_wire). With an older engine, the registry wire.
   */
  readonly wireOut: string;
  readonly runnable: boolean;
  readonly bound: boolean;
  /** The settings as given (passed to the package function that runs the stage). */
  readonly params: Readonly<Record<string, unknown>>;
  /** The settings as sent to the engine: JSON values, a Dataset as {$nquads}. */
  readonly settingsWire: Readonly<Record<string, unknown>>;
  /** The engine's canonical settings, or null with an older engine. */
  readonly settings: Readonly<Record<string, unknown>> | null;
  readonly settingsDigest: string | null;
  readonly outside: readonly OutsideSetting[];
  /** Values the engine read from the settings: `form` of a query, `mode` ('1.1' | '1.2') of a reader. */
  readonly derived: Readonly<Record<string, string>> | null;
}

/** The engine's check of a list of stages (op pipelineCheck, Lean pipelineReport). */
export interface PipelineCheck {
  /** Each stage's output wire is the next stage's input wire or converts to it (Lean wellTyped_iff). */
  readonly wellTyped: boolean;
  readonly wireIn: string | null;
  readonly wireOut: string | null;
  /** The first stage `at` whose output does not feed stage `at + 1`. */
  readonly mismatch: { readonly at: number; readonly out: string; readonly in: string } | null;
  /** Where an output reaches the next input by a named conversion (Dataflow/Wire.lean). */
  readonly conversions: readonly { readonly at: number; readonly from: string; readonly to: string }[];
  /** The union of the stages' named assumptions: the premises of Pipeline.guarantee_sound. */
  readonly assumptions: readonly string[];
  readonly contract: { readonly theorem: string; readonly stages: readonly (string | null)[] };
  readonly stages: readonly {
    readonly name: string; readonly status: NodeStatus; readonly checked: boolean;
    readonly contract: string | null; readonly assumptions: readonly string[];
    readonly wireIn: string; readonly wireOut: string;
    /** The fields below come from the op pipelineCheckNodes only. */
    readonly registryStatus?: StageInfo['status'];
    readonly settings?: Record<string, unknown>;
    readonly settingsDigest?: string;
    /** The role of each setting: 'parameter' | 'selects-wire' | 'inert' | 'narrows' | 'unlisted'. */
    readonly roles?: Readonly<Record<string, string>>;
    readonly outside?: readonly OutsideSetting[];
    readonly derived?: Readonly<Record<string, string>>;
  }[];
}

/**
 * A pipeline: nodes in order. `check` is the engine's op pipelineCheck;
 * `assumptions` and `wellTyped` are its fields. With an engine that has no
 * such op, `check` and `wellTyped` are null and `assumptions` is the union
 * of the nodes' assumptions.
 */
export interface Pipeline {
  readonly nodes: readonly FactoidalNode[];
  readonly assumptions: readonly string[];
  readonly wellTyped: boolean | null;
  readonly check: PipelineCheck | null;
}

/** The result of run(): the last graph, one record per node, the assumption union. */
export interface RunResult<G = unknown> extends Wire<G> {
  /** The assumptions of the records on the input wire, then the engine's union for the pipeline (op pipelineCheck). */
  assumptions: string[];
  /** true iff every evidence record is checked (status 'proved') and the pipeline is well typed. */
  proved: boolean;
  /** The engine's type check of the pipeline; null when the engine has no op pipelineCheck. */
  wellTyped: boolean | null;
  /** The stage names of the records that are not checked. */
  uncheckedSteps: string[];
}

/** Options of run(). */
export interface RunOptions {
  /**
   * Let stages that are not 'proved' run, and 'missing' stages too when the
   * package has a runner for them. Each such step's record says so, and the
   * result's `proved` is false. A stage with no runner still rejects (op.unknown).
   */
  unchecked?: boolean;
}

/** The engine's stage list (op stageList, full engine). */
export function stages(): Promise<StageInfo[]>;

/**
 * A node for the registered stage `name`. `params` are passed to the
 * package function that runs it: reader options; `{shapes}` for
 * shaclValidator; `{query}` for shippedEvaluator; `{description}` for
 * rdfsExplainGraphStage. An unknown name rejects with a FactoidalError.
 */
export function node(name: string, params?: Record<string, unknown>): Promise<FactoidalNode>;

/** Compose nodes and pipelines left to right. */
export function pipe(...nodes: Array<FactoidalNode | Pipeline>): Pipeline;

/**
 * Run a node or pipeline on `input` (a Wire, or the graph: text for a
 * reader, else a Dataset or data input). Rejects before any node runs when
 * a node's stage has status 'missing' (unless `options.unchecked`) or has
 * no package function, or when the engine's check finds the pipeline not
 * well typed (unless `options.unchecked`; then `proved` is false).
 */
export function run(pipeline: FactoidalNode | Pipeline, input: unknown, options?: RunOptions): Promise<RunResult>;

/** Literature-name alias for coreRdfsClosure (ρdf). */
export function rhoDfClosure(
  data: DataInput,
  options?: { format?: DataFormat; baseIRI?: string }
): Promise<Dataset>;

/** Literature-name alias for coreRdfsCheck (ρdf). */
export function rhoDfFragmentCheck(
  data: DataInput,
  options?: { format?: DataFormat; baseIRI?: string }
): Promise<{ ok: boolean; fragment: boolean }>;

/**
 * RDFS-Plus closure (RDF.Entailment.RDFSPlus.fst's `rdfs_plus_closure`):
 * RDFS plus the practical OWL subset — owl:sameAs, owl:inverseOf,
 * Symmetric/Transitive/Functional/InverseFunctionalProperty,
 * equivalentClass/Property ("RDFS-Plus", Allemang & Hendler 2008;
 * "RDFS++", AllegroGraph). Every OWL row carries proved licensing +
 * truth lemmas; no chain-level completeness claim (theorem registry).
 */
export function rdfsPlusClosure(
  data: DataInput,
  options?: { format?: DataFormat; baseIRI?: string }
): Promise<Dataset>;

/**
 * OWL tableau materialisation (L4Factoidal/OWL/Materialise.lean,
 * `materialiseWithBudget`): add `i rdf:type <ClassExpression>` for every
 * individual the model-construction reasoner proves is a member of an
 * OWL class expression (someValuesFrom / hasValue / unionOf /
 * intersectionOf, and the named class an equivalentClass restriction
 * defines). Default graph only.
 * `dataset` is input + tableau-derived triples; `addedCount` is how
 * many triples the tableau added; `budgetHit` is true when the work
 * budget ran out, so an absent membership is then a cap, not a proof.
 */
export function tableauMaterialise(
  data: DataInput,
  options?: { format?: DataFormat; baseIRI?: string }
): Promise<{ dataset: Dataset; addedCount: number; budgetHit?: boolean }>;

/**
 * OWL DL inconsistency verdict: OWL RL closure, one class-expression
 * materialisation pass, OWL RL closure again, then the clash decision.
 * `rlAlone` is the plain OWL-RL verdict on the same input, so a caller
 * can see the cases the tableau adds. Default graph only.
 */
export function tableauDlInconsistent(
  data: DataInput,
  options?: { format?: DataFormat; baseIRI?: string }
): Promise<{ inconsistent: boolean; rlAlone: boolean }>;

/**
 * Checked consistency for the original default graph in a restricted
 * OWL fragment (named subclass/class assertions, Thing/Nothing,
 * owl:someValuesFrom restrictions as a superclass or a class assertion,
 * owl:TransitiveProperty, sameAs/differentFrom, declarations, annotations
 * and annotated axioms).
 * true requires a checked finite model and has no `reason`; false requires
 * an accepted refutation certificate; null means unsupported-syntax,
 * budget-out or incomplete-search. Named graphs do not contribute axioms.
 * RDF 1.2 terms are refused. Other restrictions, object/data property
 * axioms, imports and equivalentClass are unsupported. `fuel` bounds the
 * model search and the certificate checker (default 20000 rounds).
 * This is not complete OWL DL support.
 */
export function owlIsConsistent(
  data: DataInput,
  options?: { format?: DataFormat; fuel?: number | string }
): Promise<{ consistent: boolean | null; reason?: string }>;

/**
 * OWL entailment check: does `premise` entail `conclusion`? Two paths: `via: "closure"` (the conclusion is in the OWL-RL
 * closure of the premise) or `via: "refutation"` (the negated
 * conclusion is refuted on every goal). Default graph only. The current
 * implementation returns `true` for those positive results and `null`
 * when it cannot establish entailment. `reason` distinguishes budget-out,
 * incomplete-search, unsupported-conclusion and unsupported-punning.
 * `false` (via `refutation`, reason `countermodel: ...`) requires a checked
 * finite model of the premise in which the conclusion fails; both graphs
 * must be in the fragment that `owlIsConsistent` reads.
 * The punning refusal is limited; full OWL DL recognition and universal
 * Direct Semantics soundness are not established by this API.
 */
export function owlEntails(
  premise: DataInput,
  conclusion: DataInput,
  options?: { format?: DataFormat; fuel?: number | string }
): Promise<{ entailed: boolean | null; via: 'closure' | 'refutation'; reason?: string }>;

/**
 * Evaluate an RML mapping graph against one logical source's raw data,
 * returning the generated triples as a Dataset. Every triples map in `mapping` reads the SAME
 * `sourceData` -- joins across two different logical sources are out
 * of scope for this entry point.
 * @param mapping the RML mapping graph (Turtle by default)
 * @param sourceData raw JSON or CSV text (not RDF)
 */
export function rmlMap(
  mapping: DataInput,
  sourceData: string,
  sourceKind: 'json' | 'csv',
  options?: { format?: DataFormat; baseIRI?: string }
): Promise<Dataset>;

export interface CsvwOptions {
  /** 'standard' (default): full csvw:TableGroup/Table/Row wrapper;
   *  'minimal': bare cell triples only. */
  mode?: 'standard' | 'minimal';
  /** Base IRI for resolving the metadata's `url` and templates
   *  (default 'file:///'). */
  base?: string;
  /** The tabular file's own URL, used when the metadata carries none
   *  (default 'table.csv'); cell predicates default to
   *  `<tableUrl>#<colName>`. */
  url?: string;
}

/**
 * CSVW csv2rdf conversion (w3.org/TR/csv2rdf): convert raw tabular
 * data plus an optional CSVW metadata document (JSON text -- '' or
 * omitted infers the schema from the CSV's own header row) into a
 * Dataset. Every table in a
 * multi-table `tables` group reads the SAME `csvText`.
 */
export function csvwToRdf(
  csvText: string,
  metadataJson?: string,
  options?: CsvwOptions
): Promise<Dataset>;

export interface JsonLdOptions {
  base?: string;
  rdfDirection?: string;
  expandContext?: string;
  processingMode?: string;
  /** JSON-LD-star: read `@triple`, `@reifies`, `@annotation` as RDF 1.2
   *  triple terms and reifiers. */
  rdfstar?: boolean;
}

/**
 * Parse a JSON-LD document into a Dataset, with JSON-LD-specific
 * options `parse()` has no room for (plain `parse(text,
 * {format:'jsonld'})` also works for the common case). A remote
 * `@context` is not fetched.
 */
export function jsonldToRdf(
  jsonldText: string,
  options?: JsonLdOptions
): Promise<Dataset>;

export interface JsonLdFromRdfOptions {
  useNativeTypes?: boolean;
  useRdfType?: boolean;
  /** JSON-LD-star: write RDF 1.2 triple terms (`@triple`, `@reifies`,
   *  `@annotation`). Without it a triple term is refused. */
  rdfstar?: boolean;
  format?: DataFormat;
}

/**
 * Serialize an RDF dataset as an expanded-form JSON-LD document -- the
 * reverse of jsonldToRdf (the verified JSONLD.FromRdf.from_rdf).
 * Returns the parsed JSON-LD value (an array of node objects).
 */
export function jsonldFromRdf(
  data: DataInput,
  options?: JsonLdFromRdfOptions
): Promise<any>;

/**
 * did:key resolution: resolve a `did:key:z6Mk...` (Ed25519) to its DID
 * Document, returned as a Dataset (the verified DID_Key.did_key_document).
 *
 */
export function didKeyResolve(didString: string): Promise<Dataset>;

/**
 * Test whether an XML document is well-formed (XML 1.0). A DOCTYPE with
 * an internal subset is read (XML 1.0 section 2.8); an external DTD is
 * not fetched.
 */
export function xmlWellformed(xmlText: string): Promise<boolean>;

/** The value shape returned by {@link xpathEval}. */
export interface XPathResult {
  resultType: 'nodeset' | 'string' | 'number' | 'boolean';
  count?: number;
  stringValue?: string;
  /** `kind` includes 'root' and 'namespace' as well as 'element',
   *  'attribute', 'text', 'comment' and 'processing-instruction'. */
  nodes?: Array<{ kind: string; name: string; value: string }>;
  value?: string | number | boolean;
}

/**
 * Evaluate an XPath 1.0 expression over an XML document (the full
 * XPath 1.0 function library). A number result is its XPath string form
 * when it is not finite ('Infinity', 'NaN').
 */
export function xpathEval(
  xmlText: string,
  xpathExpr: string
): Promise<XPathResult>;

/**
 * RIF Core forward-chaining saturation, materialized as a new Dataset
 * (input triples + derived triples, default graph only).
 * @param data the premise graph
 * @param rifRulesXml a RIF Core XML rule document
 */
export function rifEval(
  data: DataInput,
  rifRulesXml: string,
  options?: { format?: DataFormat; baseIRI?: string }
): Promise<Dataset>;

// ---------------------------------------------------------------------
// The persisted store: Shardborough generations (IBK3, IBK4 and IBK5
// blocks with their index sidecars) that `factoidal pack` or the native
// l4block-shard-pack wrote. skills/shardborough-storage describes the
// format. A Store is a store handle inside the engine: every artifact it
// read was checked against the SHA-256 its manifest commits, once, and
// every query answers from the decoded, indexed blocks it retains.
// ---------------------------------------------------------------------

/**
 * Reads one file of a store: `path` is relative to the collection root
 * ('CURRENT', 'gen-1/manifest.sbm2', 'gen-1/predicate-0.ibk3', ...). In a
 * browser, a reader over fetch():
 * `(p) => fetch(base + p).then((r) => r.arrayBuffer())`.
 */
export type StoreReader =
  (path: string) => Uint8Array | ArrayBuffer | Promise<Uint8Array | ArrayBuffer>;

export interface OpenStoreOptions {
  /** Open this generation directory instead of the one CURRENT names. */
  generation?: string;
  /** Read only the artifacts this query's plan names. */
  sparql?: string;
  /** Read exactly these artifact keys. */
  keys?: string[];
}

/** An open store handle (op storeOpen). */
export class Store {
  readonly handle: string;
  readonly generation: string;
  /** True when the generation was opened through CURRENT. */
  readonly activated: boolean;
  readonly identity: string;
  /** The manifest layout label, e.g. 'predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0'. */
  readonly layout: string;
  readonly wireVersion: number;
  /** Artifacts read and verified. */
  readonly artifacts: number;
  /** Artifact bytes read. */
  readonly bytes: number;
  /** Rows the handle retains. */
  readonly rows: number;
  readonly closed: boolean;
  /** One SPARQL 1.1 query against the retained blocks. The engine refuses
   *  a query whose plan needs a block the handle did not read. */
  query(sparql: string): Promise<Bindings[] | boolean | Dataset>;
  /** The manifest, decoded by the engine (op storeManifestInspect). */
  inspect(): Promise<Record<string, unknown>>;
  /** Release the handle. Idempotent. */
  close(): Promise<void>;
}

/**
 * Open a store. `source` is a collection root path (Node; the directory
 * holding CURRENT) or a StoreReader (any runtime). With no options every
 * artifact the manifest declares is read. Large collections need a
 * deeper call stack than Node's default: see
 * `@factoidal/core/store-worker` (README "The persisted store").
 */
export function openStore(source: string | StoreReader, options?: OpenStoreOptions): Promise<Store>;

/** A synchronous reader of the files of one SBM11 generation directory (or
 * collection root): the engine names every file and checks every answer. */
export interface Sbm11Reader {
  readAt(file: string, offset: number, length: number): Uint8Array | null;
  size(file: string): number | null;
}

/** The answer of one SBM11 query. */
export interface Sbm11Answer {
  /** `path=ids` or `path=reference reason="..." ...` */
  path: string;
  rows: number;
  /** `srj` (SELECT, ASK) or `ntriples` (CONSTRUCT, DESCRIBE) */
  format: 'srj' | 'ntriples';
  /** the bytes `l4sbm11 query` writes, as text */
  readonly result: string;
  /** the same answer as UTF-8 bytes */
  readonly bytes: Uint8Array;
  bytesRead: number;
  reads: number;
  /** the parsed SPARQL JSON for SELECT and ASK */
  readonly json: any;
}

/** An open SBM11 generation. */
export interface Sbm11Store {
  handle: string;
  /** the generation CURRENT names, or "" when the source is a generation */
  generation: string;
  terms: number;
  query(sparql: string, options?: { base?: string; sparql12?: boolean; reference?: boolean }): Sbm11Answer;
  /** the resources the reader read, when its reader records them (lwsSbm11Reader) */
  readonly evidence: Sbm11ReadEvidence[] | undefined;
  close(): void;
}

/** Open an SBM11 generation (https://github.com/danbri/factoidal/issues/1009).
 * Node: `source` is a directory unless a reader is given or registered. */
export function openSbm11(source: string, options?: { reader?: Sbm11Reader }): Promise<Sbm11Store>;

/** Serve `source` with `reader`; `null` removes it. */
export function registerSbm11Source(source: string, reader: Sbm11Reader | null): void;

/** Pack an RDF document into the files of one SBM11 generation, in memory
 * (wasm op `sbm11PackFiles`, https://github.com/danbri/factoidal/issues/1009
 * stage 2): file name to bytes, the files `l4sbm11-pack` writes for the same
 * quads, without `CURRENT`. Rejects with `code: 'SBM11_NO_PACK_OP'` on a wasm
 * module that has no such op. */
export function packSbm11(text: string | Uint8Array,
  options: { syntax: 'turtle' | 'trig' | 'nquads' | 'ntriples' | 'rdfxml' | 'jsonld' | string; base?: string }
): Promise<Map<string, Uint8Array>>;

/** A reader over files held in memory (for example the result of `packSbm11`). */
export function mapReader(files: Map<string, Uint8Array> | Record<string, Uint8Array>): Sbm11Reader;

/** One LWS resource an SBM11 reader read (https://github.com/danbri/factoidal/issues/1010). */
export interface Sbm11ReadEvidence {
  resource: string;
  etag: string;
  lastModified: string | null;
  /** HTTP requests made for this resource */
  requests: number;
  /** answers that were 206 Partial Content */
  partial: number;
  /** content bytes received */
  bytes: number;
}

/** A synchronous HTTP GET: `(url, headers) -> answer`. */
export type Sbm11Transport = (url: string, headers: Record<string, string>) =>
  { status: number; header(name: string): string | null; bytes: Uint8Array };

/** A reader of the SBM11 files held as LWS resources under the container
 * `url` (one resource per file, CURRENT a resource too), by HTTP Range GETs
 * when the server answers 206, else by whole GETs kept in memory. Node: the
 * default transport is a fetch in a worker thread; close() stops it. */
export function lwsSbm11Reader(url: string, opts?: {
  auth?: string; headers?: Record<string, string>; transport?: Sbm11Transport; timeoutMs?: number
}): Sbm11Reader & { evidence(): Sbm11ReadEvidence[]; errors(): string[]; close(): void };

/** One query against a store: open with the query's plan, query, close. */
export function queryStore(
  source: string | StoreReader,
  sparql: string,
  options?: { generation?: string }
): Promise<Bindings[] | boolean | Dataset>;

/** The store handles this engine instance holds open, with the residency caps (op storeHandleList). */
export function listStores(): Promise<Record<string, unknown>>;

/**
 * A durable update log (hub post 18): the object deltaLogOpen() returns.
 * In the browser the log is an IndexedDB database named `dbName`; under
 * Node it lives in the memory of the process.
 */
export interface DeltaLogHandle {
  dbName: string;
}

/** What deltaLogInspect() reports (op deltaLogDecode). */
export interface DeltaLogInspection {
  /** Batches (records) that verify, from the start of the log. */
  batches: number;
  /** Entries in those batches. */
  entries: number;
  /** The log ends with a torn final record: an append that did not complete. */
  torn: boolean;
  /** Bytes of that torn record (0 when the log is not torn). */
  tornBytes: number;
  /** Bytes of the whole log. */
  logBytes: number;
  records: Array<{ seq: number; epoch: number; entries: number }>;
}

/** Open (create when absent) a durable update log. Default name 'factoidal-delta-log'. */
export function deltaLogOpen(dbName?: string): Promise<DeltaLogHandle>;

/**
 * Append one SPARQL Update request as one record (op deltaLogEncode).
 * INSERT DATA, DELETE DATA, CLEAR DEFAULT, CLEAR GRAPH, DROP GRAPH and
 * CREATE GRAPH are admitted; any other form rejects and nothing is written.
 */
export function deltaLogAppend(
  handle: DeltaLogHandle,
  sparqlUpdate: string,
  options?: { epoch?: number }
): Promise<{ seq: number; opCount: number }>;

/** The records of the log, in commit order, as hexadecimal text joined by "\n". */
export function deltaLogReadAllHex(handle: DeltaLogHandle): Promise<string>;

/**
 * Merge on read (op deltaLogMerge): `baseNQuads` with the batches of the log
 * applied in commit order, as N-Quads. A torn final record (an append that
 * did not complete) is not applied. A damaged record, or a record whose
 * entries the engine cannot decode, makes the merge reject: the records after
 * it would otherwise be lost (https://github.com/danbri/factoidal/issues/843).
 */
export function deltaLogMerge(handle: DeltaLogHandle, baseNQuads: string): Promise<string>;

/**
 * What the log holds, record by record (op deltaLogDecode). Rejects for a
 * damaged record or a record whose entries the engine cannot decode.
 */
export function deltaLogInspect(handle: DeltaLogHandle): Promise<DeltaLogInspection>;

/** Remove the log and its records. */
export function deltaLogDestroy(handle: DeltaLogHandle): Promise<void>;

/** TEST ONLY: cut the last 4 bytes of the last record, as a torn write would. False when the log is empty. */
export function _deltaLogCorruptLastForTest(handle: DeltaLogHandle): Promise<boolean>;



// ---------------------------------------------------------------------
// Common Logic (ISO/IEC 24707:2018) and IKL
// ---------------------------------------------------------------------

// Reads Common Logic Interchange Format
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

// Reads CLIF text and writes it
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

// Alpha-normalises CLIF text: the
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

// Hayes's reduction of IKL to
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
// through the raw dispatch ABI (`(await loadEngine()).call('clFiniteSat',
// [interpJson, clifText])`), which needs no typed shape commitment here.

// ---------------------------------------------------------------------
// Typed engine functions (#74 npm FP surface). Each is a pure,
// value-in / value-out wrapper over one engine op.
// ---------------------------------------------------------------------

/**
 * XSLT 1.0 transform (XSLT.Transform.transform): apply `stylesheetXml`
 * to `sourceXml`, returning the serialized result tree.
 */
export function xsltTransform(
  stylesheetXml: string,
  sourceXml: string
): Promise<string>;

/** The exact value a Content MathML expression evaluates to. */
export type MathValue =
  | { kind: 'rat'; num: number; den: number }
  | { kind: 'bool'; value: boolean }
  | { kind: 'undef'; reason: string };

/**
 * Evaluate a Content MathML document (MathML.Content.eval_doc_env).
 * `bindings` maps ci-variable names to value strings; pass {} (or
 * omit) for a closed expression.
 */
export function mathmlEval(
  contentMathmlXml: string,
  bindings?: Record<string, string>
): Promise<MathValue>;

/** One XForms model bind (a subset of the §7 MIPs). */
export interface XFormsBind {
  id?: string;
  target: string;
  calculate?: string;
  constraint?: string;
  relevant?: string;
  required?: string;
  readonly?: string;
  type?:
    | 'string' | 'boolean' | 'integer'
    | 'decimal' | 'float' | 'double';
}

/** Per-node validity from an XForms recalculate. */
export interface XFormsNodeValidity {
  target: string;
  value: string;
  typeValid: boolean;
  constraint: boolean;
  relevant: boolean;
  required: boolean;
  readonly: boolean;
  valid: boolean;
}

/**
 * XForms recalculate (XForms.Bind.recalculate): apply the model binds
 * to `instanceXml`, returning the recomputed instance and a validity
 * report per bound node.
 */
export function xformsRecalc(
  instanceXml: string,
  binds: XFormsBind[]
): Promise<{ instance: string; validity: XFormsNodeValidity[] }>;

/**
 * JSON Schema (draft-07) validation (JSONSchema.Validate.validate).
 * The verified validator gives a definite pass/fail/unsupported verdict
 * rather than a per-keyword error list; `errors` carries a single
 * reason string when the result is not a definite pass.
 */
export function jsonSchemaValidate(
  schemaJson: string,
  instanceJson: string
): Promise<{
  valid: boolean;
  result: 'pass' | 'fail' | 'unsupported';
  errors: string[];
}>;

/** One Schematron finding. */
export interface SchematronFinding {
  type: 'assert-fail' | 'report-hit' | 'indeterminate';
  context: string;
  test: string;
  message: string;
  path: string;
  reason?: string;
}

/**
 * Schematron validation (Schematron.Validate.validate): every finding
 * (failed assert, fired report, indeterminate) in pattern-then-document
 * order.
 */
export function schematronValidate(
  schematronXml: string,
  instanceXml: string
): Promise<{ findings: SchematronFinding[] }>;

/**
 * An exact-arithmetic expression in the TOAN JSON codec, mirroring
 * Math.Expr.expr (E_Int/E_Rat/E_Bool/E_Sym/E_App).
 */
export type ToanExpr =
  | { int: number }
  | { rat: [number, number] }
  | { bool: boolean }
  | { sym: string }
  | { app: string; args: ToanExpr[] };

/** Finite summation of `bodyExpr[idx:=lo..hi]`, as Content MathML. */
export function toanSummation(
  bodyExpr: ToanExpr,
  idx: string,
  lo: number,
  hi: number
): Promise<string>;

/** Finite product of `bodyExpr[idx:=lo..hi]`, as Content MathML. */
export function toanProduct(
  bodyExpr: ToanExpr,
  idx: string,
  lo: number,
  hi: number
): Promise<string>;

/** Canonical simplification of `expr`, as Content MathML. */
export function toanSimplify(expr: ToanExpr): Promise<string>;

/** Derivative of `expr` w.r.t. `variable`, as Content MathML. */
export function toanDiff(expr: ToanExpr, variable: string): Promise<string>;

/** `expr[variable := value]` simplified, as Content MathML. */
export function toanSubst(
  expr: ToanExpr,
  variable: string,
  value: ToanExpr
): Promise<string>;



// ---------------------------------------------------------------------
// VC Data Integrity crypto (eddsa-rdfc-2022), the ops of
// formal/lean4/Wasm/Ops/Vc.lean. Ed25519 is HACL*'s C code compiled into
// the wasm module; SHA-256 is the Lean hash. No initialisation step.
// ---------------------------------------------------------------------

/**
 * SHA-256 of a message string's bytes, as a lowercase hex digest
 * (the Lean SHA-256).
 */
export function vcSha256Hex(message: string): Promise<string>;

/** Derive the Ed25519 public key (hex) from a 32-byte secret key (hex). */
export function vcEd25519SecretToPublic(secretKeyHex: string): Promise<string>;

/** Ed25519 signature (hex) over a hex-encoded message. */
export function vcEd25519Sign(
  secretKeyHex: string,
  messageHex: string
): Promise<string>;

/**
 * Ed25519 verification. Wrong key, tampered signature, altered
 * message, or a malformed-length input all resolve to false — never an
 * exception-hidden true.
 */
export function vcEd25519Verify(
  publicKeyHex: string,
  messageHex: string,
  signatureHex: string
): Promise<boolean>;

/**
 * Create an eddsa-rdfc-2022 Data Integrity proofValue (multibase-z,
 * base58btc) over already-canonicalized inputs — RDFC-1.0 canonical
 * N-Quads of the document and of the proof config (see canonicalize()).
 */
export function vcEddsaCreateFromCanonical(
  secretKeyHex: string,
  canonicalDocument: string,
  canonicalConfig: string
): Promise<string>;

/**
 * Verify an eddsa-rdfc-2022 proofValue against canonical inputs. Wrong
 * key, tampered document/config, or tampered proofValue all resolve to
 * false.
 */
export function vcEddsaVerifyFromCanonical(
  publicKeyHex: string,
  canonicalDocument: string,
  canonicalConfig: string,
  proofValue: string
): Promise<boolean>;

/**
 * VC Data Model 2.0 structural conformance check (VC.Credential.fst's
 * vc_check_from_string, ported to L4Factoidal/VC/Credential.lean — 117 pass, 0 fail on the offline
 * vc_stage1 fixture suite). Pure structural validation, no crypto.
 * `v2ctxJson` is the vendored VCDM v2 base context document's raw JSON
 * text (third_party/contexts/credentials-v2.jsonld); `credentialJson`
 * is the raw JSON text of the VC/VP document under test.
 */
export function vcCheckCredential(
  v2ctxJson: string,
  credentialJson: string
): Promise<{ valid: boolean; reason?: string }>;

/**
 * credentialSubject presence/shape check, VERSION-AGNOSTIC (Track A1,
 * docs/designissues/2026-07-11-vc-canivc-eecc-plan.md) —
 * VC.Credential.fst's vc_check_credential_subject_from_string. Unlike
 * vcCheckCredential, does not require the VCDM 2.0 base @context to be
 * present/first.
 */
export function vcCheckCredentialSubject(
  credentialJson: string
): Promise<{ valid: boolean; reason?: string }>;

/**
 * DATA_LOSS_DETECTION_ERROR check (Track A1, same plan doc) —
 * VC.Credential.fst's vc_check_no_data_loss_from_string. `credentialJson`
 * must already have any remote @context IRI inlined to the real context
 * object.
 */
export function vcCheckNoDataLoss(
  credentialJson: string
): Promise<{ valid: boolean; reason?: string }>;

/**
 * relatedResource digest verification (VCDM 2.0 §5.3) —
 * VC.Credential.fst's vc_check_related_resource_digests_from_string.
 * `registryJson` is a JSON array of {"id", "digestsHex"} entries computed
 * from vendored copies of each known resource's content bytes.
 */
export function vcCheckRelatedResourceDigests(
  registryJson: string,
  credentialJson: string
): Promise<{ valid: boolean; reason?: string }>;

/**
 * Feature probe: which ops the loaded wasm module serves. A module older
 * than this package can lack some; an operation whose op is missing
 * rejects naming it.
 */
export function capabilities(): Promise<{
  entry: boolean;
  construct: boolean;
  update: boolean;
  canonicalize: boolean;
  graphs: boolean;
  canonicalHash: boolean;
  shacl: boolean;
  shex: boolean;
  owlClosure: boolean;
  explain: boolean;
  stages: boolean;
  /** The op pipelineCheck: pipe() and run() use the engine's type check and assumption union. */
  pipelineCheck: boolean;
  /** The op pipelineCheckNodes: node settings in evidence, and the evaluator's output wire from the query form. */
  pipelineCheckNodes: boolean;
  tableau: boolean;
  rml: boolean;
  csvw: boolean;
  jsonld: boolean;
  jsonldFromRdf: boolean;
  didKey: boolean;
  xml: boolean;
  xpath: boolean;
  rif: boolean;
  xslt: boolean;
  mathml: boolean;
  xforms: boolean;
  jsonSchema: boolean;
  schematron: boolean;
  toan: boolean;
  /** The VC Data Integrity crypto ops are present. */
  vcCrypto: boolean;
  /** query()'s `entail` regimes (op queryRaw) are served. */
  entailment: boolean;
  /** queryHdt() (op queryHdt) is served. */
  hdt: boolean;
  /** query()'s `sparql12` and Dataset.query's (queryDataset12, datasetQuery12). */
  sparql12: boolean;
  /** openStore() and the Store methods (storeOpen, storeHandleQuery). */
  store: boolean;
  /** The deltaLog* functions (deltaLogEncode, deltaLogDecode, deltaLogMerge). */
  deltaLog: boolean;
  /** 'full': the whole library is in the wasm module. */
  profile: 'full' | string;
  /** The dispatch ABI version string of the loaded wasm module. */
  abiVersion: string;
  /** openDataset()/Dataset (datasetOpen/Query/Update/Serialize/Close) are present. */
  datasetHandles: boolean;
  /** parse()'s `{lenient:true}` (parseDocument) is present. */
  parseDiagnostics: boolean;
  /** serialize()'s `{prefixes, literalShorthand}` (serializeTurtleWith) is present. */
  turtlePrefixes: boolean;
}>;

// ---------------------------------------------------------------------
// One call, serialised answer (op queryRaw)
// ---------------------------------------------------------------------

/** SPARQL Results JSON term (https://www.w3.org/TR/sparql11-results-json/). */
export interface SrjTerm {
  type: 'uri' | 'bnode' | 'literal' | 'typed-literal';
  value: string;
  'xml:lang'?: string;
  datatype?: string;
}

export interface SparqlResultsJson {
  head: { vars?: string[]; link?: string[] };
  results?: { bindings: Array<Record<string, SrjTerm>> };
  boolean?: boolean;
}

export type OutputFormat =
  | 'json' | 'csv' | 'tsv' | 'xml' | 'table' | 'ntriples';

/**
 * One call, serialised answer: parse `dataString`, close the default
 * graph under `entail`, run the query. Resolves to parsed SPARQL Results
 * JSON when output is 'json' (default), the text otherwise. 'csv', 'tsv'
 * and 'xml' are the W3C SPARQL results formats (CSV and TSV have no ASK
 * encoding, so an ASK with those rejects); 'table' and 'ntriples' are
 * display formats. A CONSTRUCT or DESCRIBE answer is a graph and takes
 * 'ntriples' or 'table' only.
 */
export function queryRaw(
  dataString: string,
  queryString: string,
  options?: {
    dataFormat?: DataFormat;
    entail?: EntailRegime;
    output?: OutputFormat;
  }
): Promise<SparqlResultsJson | string>;

/** Package version string, e.g. '0.9.0'. */
export const version: string;

/** The engine: 'lean4-wasm'. */
export const engine: string;

/**
 * The loaded Lean engine handle, for the dispatch ops this package does
 * not wrap: `call(op, args)` answers the parsed envelope and throws on
 * {"ok":false}; `call('ops', [])` lists the op names. Node: index.mjs;
 * browser: browser.js.
 */
export function loadEngine(): Promise<{
  version(): string;
  call(op: string, args: string[]): any;
  callBlob(op: string, args: string[], bytes: Uint8Array | ArrayBuffer): any;
  callBlobIO(op: string, args: string[], bytes?: Uint8Array | ArrayBuffer): { envelope: any; bytes: Uint8Array };
}>;

declare const _default: {
  parse: typeof parse;
  query: typeof query;
  queryHdt: typeof queryHdt;
  update: typeof update;
  openDataset: typeof openDataset;
  closure: typeof closure;
  formats: typeof formats;
  serialize: typeof serialize;
  canonicalize: typeof canonicalize;
  graphs: typeof graphs;
  canonicalHash: typeof canonicalHash;
  isomorphic: typeof isomorphic;
  fromQuads: typeof fromQuads;
  ready: typeof ready;
  engineTables: typeof engineTables;
  sameValue: typeof sameValue;
  shaclValidate: typeof shaclValidate;
  shexValidate: typeof shexValidate;
  owlClosure: typeof owlClosure;
  tableauMaterialise: typeof tableauMaterialise;
  tableauDlInconsistent: typeof tableauDlInconsistent;
  owlIsConsistent: typeof owlIsConsistent;
  owlEntails: typeof owlEntails;
  rmlMap: typeof rmlMap;
  csvwToRdf: typeof csvwToRdf;
  jsonldToRdf: typeof jsonldToRdf;
  jsonldFromRdf: typeof jsonldFromRdf;
  didKeyResolve: typeof didKeyResolve;
  xmlWellformed: typeof xmlWellformed;
  xpathEval: typeof xpathEval;
  rifEval: typeof rifEval;
  clParse: typeof clParse;
  clSerialize: typeof clSerialize;
  clAlphaNorm: typeof clAlphaNorm;
  clNormalize: typeof clNormalize;
  openStore: typeof openStore;
  queryStore: typeof queryStore;
  listStores: typeof listStores;
  deltaLogOpen: typeof deltaLogOpen;
  deltaLogAppend: typeof deltaLogAppend;
  deltaLogReadAllHex: typeof deltaLogReadAllHex;
  deltaLogMerge: typeof deltaLogMerge;
  deltaLogInspect: typeof deltaLogInspect;
  deltaLogDestroy: typeof deltaLogDestroy;
  _deltaLogCorruptLastForTest: typeof _deltaLogCorruptLastForTest;
  xsltTransform: typeof xsltTransform;
  mathmlEval: typeof mathmlEval;
  xformsRecalc: typeof xformsRecalc;
  jsonSchemaValidate: typeof jsonSchemaValidate;
  schematronValidate: typeof schematronValidate;
  toanSummation: typeof toanSummation;
  toanProduct: typeof toanProduct;
  toanSimplify: typeof toanSimplify;
  toanDiff: typeof toanDiff;
  toanSubst: typeof toanSubst;
  vcSha256Hex: typeof vcSha256Hex;
  vcEd25519SecretToPublic: typeof vcEd25519SecretToPublic;
  vcEd25519Sign: typeof vcEd25519Sign;
  vcEd25519Verify: typeof vcEd25519Verify;
  vcEddsaCreateFromCanonical: typeof vcEddsaCreateFromCanonical;
  vcEddsaVerifyFromCanonical: typeof vcEddsaVerifyFromCanonical;
  vcCheckCredential: typeof vcCheckCredential;
  vcCheckCredentialSubject: typeof vcCheckCredentialSubject;
  vcCheckNoDataLoss: typeof vcCheckNoDataLoss;
  vcCheckRelatedResourceDigests: typeof vcCheckRelatedResourceDigests;
  capabilities: typeof capabilities;
  Dataset: typeof Dataset;
  Store: typeof Store;
  FactoidalError: typeof FactoidalError;
  dataFactory: DataFactory;
  queryRaw: typeof queryRaw;
  version: string;
  engine: string;
};
export default _default;

// Added in 0.10.0 (lib/pure.mjs).
export function aeadSeal(a: { key: Uint8Array; nonce: Uint8Array; plaintext?: Uint8Array; aad?: Uint8Array }): Promise<Uint8Array>;
export function aeadOpen(a: { key: Uint8Array; nonce: Uint8Array; ciphertext: Uint8Array; aad?: Uint8Array }): Promise<Uint8Array>;
export function hpkeSeal(a: { skE: Uint8Array; pkR: Uint8Array; plaintext?: Uint8Array; info?: Uint8Array; aad?: Uint8Array }): Promise<{ message: Uint8Array; enc: Uint8Array; ciphertext: Uint8Array }>;
export function hpkeOpen(a: { skR: Uint8Array; message: Uint8Array; info?: Uint8Array; aad?: Uint8Array }): Promise<Uint8Array>;
export function proofCheck(bundleJson: string): Promise<Record<string, unknown>>;
export function proofInspect(bundleJson: string): Promise<Record<string, unknown>>;
export function canonicalizeNQuads(nquads: string): Promise<string>;
export function normalizeNQuads(nquads: string): Promise<string>;
export function serveStore(root: string, options?: { port?: number; host?: string; queryPath?: string; gspPath?: string; tdb2?: boolean }): Promise<{ url: string; port: number; close(): Promise<void> }>;

/** Pack a small built-in store (Node only) under dir or a temporary directory; returns the collection root. */
export function sampleStorePath(dir?: string): string;
/** What the sample store holds. */
export const sampleStoreFacts: Readonly<{ triples: number; source: string; layout: string }>;
