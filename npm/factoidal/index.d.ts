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
 * A parse failure that carries a position (issue #344): `line`/
 * `column`/`offset` are set when the failing engine call reported one
 * (Turtle, TriG, N-Triples, N-Quads); `undefined` for an RDF/XML or
 * JSON-LD failure, or any non-parse engine error, which stay a plain
 * `Error`. `name` is `'ParseError'`.
 */
export class ParseError extends Error {
  readonly name: 'ParseError';
  /** 1-based line of the error. */
  readonly line?: number;
  /** 1-based column of the error, counted in Unicode scalar values. */
  readonly column?: number;
  /**
   * The position of the error as a UTF-16 code-unit index into the input
   * JavaScript string: `text.slice(err.offset)` starts at the error. A
   * character outside the Basic Multilingual Plane (U+10000 and above)
   * counts 2, as in every JavaScript string index. (The engine reports a
   * count of Unicode scalar values; the wrapper converts.)
   */
  readonly offset?: number;
  readonly format?: string;
}

/** One recoverable-parse diagnostic from a `{lenient:true}` parse() call. */
export interface ParseDiagnostic {
  message: string;
  offset: number;
  line: number;
  column: number;
}

/**
 * An in-memory RDF/JS DatasetCore
 * (https://rdf.js.org/dataset-spec/#datasetcore-interface) that also
 * round-trips to the engine's N-Quads interchange text.
 */
export class Dataset implements Iterable<Quad> {
  constructor(
    quads?: Iterable<Quad>,
    options?: { prefixes?: Record<string, string>; diagnostics?: ParseDiagnostic[] }
  );
  readonly size: number;
  /**
   * Prefixes the engine reported at parse time (declaration order, no
   * colons), or `{}` for a Dataset with none recorded. A frozen, own,
   * non-enumerable property -- absent from `JSON.stringify()`/
   * `Object.keys()`, and from `toArray()`'s quads.
   */
  readonly prefixes: Record<string, string>;
  /**
   * Recoverable-parse diagnostics from a `{lenient:true}` parse() call,
   * or `[]` for a strict parse (or one with no errors). Same
   * non-enumerable-property treatment as `prefixes`.
   */
  readonly diagnostics: ParseDiagnostic[];
  add(quad: Quad): this;
  delete(quad: Quad): this;
  has(quad: Quad): boolean;
  match(
    subject?: Term | null,
    predicate?: Term | null,
    object?: Term | null,
    graph?: Term | null
  ): Dataset;
  [Symbol.iterator](): Iterator<Quad>;
  toArray(): Quad[];
  /** N-Quads serialization of the quads (the engine interchange form). */
  toNQuads(): string;
  toString(): string;
  static fromNQuads(
    text: string,
    options?: {
      blankNodePrefix?: string;
      factory?: DataFactory;
      prefixes?: Record<string, string>;
      diagnostics?: ParseDiagnostic[];
    }
  ): Dataset;
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
  | 'jsonld' | 'json-ld';

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

/** Input data: a Dataset, a document string, or several of either. */
export type DataInput =
  | Dataset
  | string
  | { text: string; format?: DataFormat }
  | Array<Dataset | string | { text: string; format?: DataFormat }>;

/** Anything query()/serialize()/canonicalize() accept: DataInput, or an already-open DatasetHandle. */
export type QueryInput = DataInput | DatasetHandle;

export interface ParseOptions {
  /** Default: 'turtle'. */
  format?: DataFormat;
  /** Base IRI for resolving relative IRIs (Turtle/TriG/RDF-XML). */
  baseIRI?: string;
  /**
   * Recover instead of rejecting on the first syntax error (issue
   * #344): the returned Dataset holds whatever the parser recovered,
   * and `dataset.diagnostics` lists what was skipped. Needs the engine
   * op `parseDocument`, which the Lean engine does not have yet
   * (https://github.com/danbri/factoidal/issues/716): the call rejects
   * naming the op. Default: false (strict; a syntax error,
   * an undeclared prefix, or an unresolvable relative IRI rejects the
   * whole parse with a ParseError).
   */
  lenient?: boolean;
}

export interface QueryOptions {
  /** Format tag for string data inputs. Default: 'turtle'. */
  format?: DataFormat;
  /**
   * Default: 'none'. Any other regime closes the DEFAULT graph under it
   * before the query (op queryRaw); extension functions and SERVICE
   * registrations are not in scope on that path.
   */
  entail?: EntailRegime;
  /**
   * Read the query with the SPARQL 1.2 grammar (triple-term patterns
   * `<<( s p o )>>`, reified triples, annotations, TRIPLE / isTRIPLE /
   * SUBJECT / PREDICATE / OBJECT). Same as `version: '1.2'`.
   */
  sparql12?: boolean;
  version?: '1.1' | '1.2';
}

/**
 * Parse one RDF document into a Dataset. The returned Dataset's quad
 * order is sorted (canonical N-Quads order), not document order;
 * anonymous blank-node labels (`_anonN`) DO reflect document order.
 * See README.md's "Blank nodes, labels and statement order". Strict
 * by default (issue #344): a syntax error rejects with a ParseError
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
 * (https://github.com/danbri/factoidal/issues/717). `data` may be a DatasetHandle
 * from openDataset(), in which case this routes to `data.query()` and
 * `options.entail` must be 'none' or omitted (a handle carries no
 * entailment-closure step).
 */
export function query(
  data: QueryInput,
  sparql: string,
  options?: QueryOptions | DataFormat
): Promise<Bindings[] | boolean | Dataset>;

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
  options?: { format?: DataFormat }
): Promise<{ ok: true; count: number }>;

/** Remove every registered SERVICE endpoint snapshot. */
export function clearServiceEndpoints(): Promise<void>;

/**
 * Apply a SPARQL 1.1 Update, returning the updated Dataset. `data`
 * must NOT be a DatasetHandle -- update() always returns a FRESH
 * Dataset, whereas a handle's own `handle.update()` mutates the
 * handle in place and returns it; passing a handle here rejects with
 * a TypeError naming `handle.update()`.
 *
 */
export function update(
  data: DataInput,
  updateText: string,
  options?: { format?: DataFormat } | DataFormat
): Promise<Dataset>;

/**
 * Open a dataset handle (issue #680): parse `data` once, then run
 * many query()/update()/serialize() calls against the engine's own
 * cached, indexed copy -- no re-parse, no SPARQL-index rebuild per
 * call.
 * @param data a Dataset (opened as N-Quads, keeping the Dataset's own
 *   `.prefixes` on the handle for Turtle output), a string
 *   (`options.format`/`baseIRI` apply), or an array of those (each
 *   non-N-Quads document normalizes through the strict parser first,
 *   then the whole array opens as one N-Quads document -- no
 *   per-document prefixes survive that merge).
 */
export function openDataset(
  data: DataInput,
  options?: { format?: DataFormat; baseIRI?: string } | DataFormat
): Promise<DatasetHandle>;

/**
 * A dataset kept open and indexed in the engine (issue #680), from
 * openDataset(). Every method rejects once `closed` is true.
 */
export class DatasetHandle {
  /** The opaque engine handle id (e.g. "h1"). */
  readonly handle: string;
  /** Quad count as of the last open()/update(). */
  readonly size: number;
  /** Prefixes recorded at open (or carried over from a Dataset argument). */
  readonly prefixes: Record<string, string>;
  /** True once close() has run. */
  readonly closed: boolean;
  /** Run a SPARQL 1.1 query against the stored dataset. */
  query(
    sparql: string,
    options?: { sparql12?: boolean; version?: string }
  ): Promise<Bindings[] | boolean | Dataset>;
  /** Apply a SPARQL 1.1 Update in place. Returns this handle, refreshed. */
  update(updateText: string): Promise<DatasetHandle>;
  /**
   * Serialize the stored dataset. 'turtle' uses the handle's own
   * recorded prefixes automatically; pass `prefixes` to add to them,
   * or `literalShorthand:false` to turn off the bare-literal
   * shorthand.
   */
  serialize(options?: {
    format?: 'nquads' | 'turtle' | 'ttl';
    prefixes?: Record<string, string>;
    literalShorthand?: boolean;
  } | 'nquads' | 'turtle' | 'ttl'): Promise<string>;
  /** Materialize the stored dataset as a heap Dataset. */
  toDataset(): Promise<Dataset>;
  /** RDFC-1.0 canonical N-Quads of the stored dataset. */
  canonicalize(): Promise<string>;
  /** Release the handle. Idempotent; every other method rejects after. */
  close(): Promise<void>;
}

export interface SerializeOptions {
  /**
   * Output format. Default: 'nquads'. A bare string in place of the
   * options object names the format: serialize(ds, 'turtle'). 'nquads'
   * is the engine's N-Quads text, lines in sorted order (not document
   * order); 'ntriples' is the same text and refuses data with a named
   * graph. 'turtle' (prefix-compacted, subject-grouped) flattens every
   * named graph into the default graph — use 'nquads' when graph names
   * must survive.
   */
  format?: 'nquads' | 'ntriples' | 'turtle' | 'ttl';
  /** Format tag for string data inputs. Default: 'turtle'. */
  inputFormat?: DataFormat;
  /**
   * 'turtle' only (issue #681): caller prefix pairs win, in the
   * caller's order; unused caller namespaces are not emitted; auto
   * `nsN:` labels skip caller labels. Used automatically, merged with
   * any pairs given here, when `data` is a Dataset with non-empty
   * `.prefixes`.
   */
  prefixes?: Record<string, string>;
  /**
   * 'turtle' only. Default: true. Whether xsd:integer/decimal/double/
   * boolean literals with a Turtle-grammar-matching lexical form print
   * bare (`22`) instead of typed (`"22"^^xsd:integer`).
   */
  literalShorthand?: boolean;
}

/**
 * Serialize a dataset (engine-produced, sorted N-Quads order). `data`
 * may be a DatasetHandle, in which case this routes to
 * `data.serialize(options)`.
 */
export function serialize(
  data: QueryInput,
  options?: SerializeOptions | NonNullable<SerializeOptions['format']>
): Promise<string>;

/**
 * RDFC-1.0 dataset canonicalization: canonical blank-node labels plus
 * sorted canonical N-Quads. Two isomorphic inputs canonicalize to the
 * same string. `data` may be a DatasetHandle, in which case this
 * routes to `data.canonicalize()` (options are ignored for a handle).
 */
export function canonicalize(
  data: QueryInput,
  options?: { format?: DataFormat } | DataFormat
): Promise<string>;

/**
 * Enumerate the named graphs of an already-parsed Dataset (default
 * graph excluded), in first-seen order. Pure enumeration over
 * `dataset`'s own quads -- no engine round-trip, always available.
 * `graph` is the same Dataset filtered to that one graph name (what
 * `dataset.match(null, null, null, graphTerm)` would return).
 */
export function graphs(dataset: Dataset): Array<[iri: string, graph: Dataset]>;

/**
 * RDFC-1.0 canonical hash of a single graph -- the graph-scoped
 * sibling of canonicalize(). Every quad's graph component is dropped
 * before canonicalizing, so isomorphic graphs (including under
 * blank-node relabeling) hash to the same string regardless of what
 * graph name they were extracted from. Typically called with one
 * entry of graphs()'s output.
 */
export function canonicalHash(datasetOrGraph: Dataset): Promise<string>;

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
  options?: { format?: DataFormat }
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
  options?: { format?: DataFormat }
): Promise<boolean | null>;

/**
 * RDFS or OWL-RL entailment closure, materialized as a new Dataset
 * (input triples + derived triples). Default graph only.
 */
export function owlClosure(
  data: DataInput,
  mode: 'RDFS' | 'OWL-RL',
  options?: { format?: DataFormat }
): Promise<Dataset>;

/**
 * The CERTIFIED six-rule core-RDFS closure
 * (formal/fstar/RDF.Entailment.RDFS.RhoDFClosure.fst's
 * `rho_df_closure`): rdfs2/3/5/7/9/11 only, with the machine-checked
 * decides-iff — on fragment inputs the result's simple query answers
 * are exactly the entailed consequences (see
 * docs/theorem-registry.md). Returns N-Triples text plus status.
 * "corerdfs" is this project's API name for the fragment the
 * literature calls ρdf (subPropertyOf/subClassOf/type/domain/range —
 * Muñoz, Pérez & Gutierrez, "Simple and Efficient Minimal RDFS",
 * J. Web Semantics 7(3), 2009).
 */
export function coreRdfsClosure(
  data: DataInput,
  options?: { format?: DataFormat }
): Promise<{ ok: boolean; ntriples: string }>;

/**
 * Decidable core-RDFS fragment check (L4Factoidal/RDFS, `isRhoDfFrag`):
 * is the data in the core-RDFS fragment coreRdfsClosure is defined for?
 */
export function coreRdfsCheck(
  data: DataInput,
  options?: { format?: DataFormat }
): Promise<{ ok: boolean; fragment: boolean }>;

/** Literature-name alias for coreRdfsClosure (ρdf). */
export function rhoDfClosure(
  data: DataInput,
  options?: { format?: DataFormat }
): Promise<{ ok: boolean; ntriples: string }>;

/** Literature-name alias for coreRdfsCheck (ρdf). */
export function rhoDfFragmentCheck(
  data: DataInput,
  options?: { format?: DataFormat }
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
  options?: { format?: DataFormat }
): Promise<{ ok: boolean; ntriples: string; rounds: number }>;

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
  options?: { format?: DataFormat }
): Promise<{ dataset: Dataset; addedCount: number; budgetHit?: boolean }>;

/**
 * OWL DL inconsistency verdict: OWL RL closure, one class-expression
 * materialisation pass, OWL RL closure again, then the clash decision.
 * `rlAlone` is the plain OWL-RL verdict on the same input, so a caller
 * can see the cases the tableau adds. Default graph only.
 */
export function tableauDlInconsistent(
  data: DataInput,
  options?: { format?: DataFormat }
): Promise<{ inconsistent: boolean; rlAlone: boolean }>;

/**
 * OWL DL consistency verdict via the clash-detecting tableau
 * (L4Factoidal/OWL/Refute.lean) over the OWL RL closure.
 * Default graph only. `consistent` is three-valued: `false` (a clash on
 * every branch), `true` (a model built), or `null` -- a budget-out, with
 * `reason` naming the fuel cap (never a silent false).
 */
export function owlIsConsistent(
  data: DataInput,
  options?: { format?: DataFormat; fuel?: number | string }
): Promise<{ consistent: boolean | null; reason?: string }>;

/**
 * OWL entailment check: does `premise` entail `conclusion`? Two paths: `via: "closure"` (the conclusion is in the OWL-RL
 * closure of the premise) or `via: "refutation"` (the negated
 * conclusion is refuted on every goal). Default graph only. `entailed` is `true`, `false`, or `null`
 * (a refutation budget-out, with `reason` naming the cap).
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
  options?: { format?: DataFormat }
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
  options?: { format?: DataFormat }
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

/** One query against a store: open with the query's plan, query, close. */
export function queryStore(
  source: string | StoreReader,
  sparql: string,
  options?: { generation?: string }
): Promise<Bindings[] | boolean | Dataset>;

/** The store handles this engine instance holds open, with the residency caps (op storeHandleList). */
export function listStores(): Promise<Record<string, unknown>>;

/** The collection root of the sample store this package carries (Node only). */
export function sampleStorePath(): string;

/** What the sample store holds, as recorded when it was packed. */
export const sampleStoreFacts: Readonly<{
  triples: number;
  blocks: number;
  layout: string;
  wireVersion: number;
  source: string;
  licence: string;
  licenceUrl: string;
  publisher: string;
}>;

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

/** A matrix/vector cell: an integer or an exact [num, den] rational. */
export type MatrixCell = number | [number, number];

/** The rendered result of a matrix/vector operation. */
export interface MatrixResult {
  /** Math.Matrix.mres_to_string of the result ("undef" on failure). */
  result: string;
  /** The diagnostic reason when the result is undefined, else "". */
  reason: string;
}

/** Exact determinant of a square matrix (Math.Matrix.dyn_determinant). */
export function matrixDeterminant(
  matrix: MatrixCell[][]
): Promise<MatrixResult>;

/** Dot product of two vectors (Math.Matrix.dyn_scalarproduct). */
export function matrixScalarProduct(
  a: MatrixCell[],
  b: MatrixCell[]
): Promise<MatrixResult>;

/** Cross product of two 3-vectors (Math.Matrix.dyn_vectorproduct). */
export function matrixVectorProduct(
  a: MatrixCell[],
  b: MatrixCell[]
): Promise<MatrixResult>;

/** Outer product of two vectors (Math.Matrix.dyn_outerproduct). */
export function matrixOuterProduct(
  a: MatrixCell[],
  b: MatrixCell[]
): Promise<MatrixResult>;

/**
 * A fixed-precision decimal (Math.Sigmoid.scaled: mantissa / 10^scale),
 * the same (mantissa, scale) convention SPARQL11.Algebra.parse_to_scaled
 * uses for xsd:decimal literals. `decimal` is the same pair formatted
 * back to a string by SPARQL11_Algebra.format_scaled_value.
 */
export interface ScaledValue {
  mantissa: string;
  scale: string;
  decimal: string;
}

/** Parameters for {@link sigmoidPoints}: decimal-literal strings/numbers. */
export interface SigmoidParams {
  k: number | string;
  x0: number | string;
  l: number | string;
  xmin: number | string;
  xmax: number | string;
  n: number | string;
}

/**
 * n+1 evenly spaced samples of the logistic sigmoid
 * L / (1 + exp(-k*(x - x0))) over [xmin, xmax] (Math.Sigmoid.
 * sigmoid_points). All arithmetic -- argument reduction, the
 * truncated Taylor series, repeated squaring, and the x samples
 * themselves -- runs as exact rational arithmetic inside
 * Math.Sigmoid.fst; see that module's header for the documented error
 * bound on the returned (rounded) values.
 */
export function sigmoidPoints(
  params: SigmoidParams
): Promise<Array<{ x: ScaledValue; y: ScaledValue }>>;

/**
 * Presentation MathML for the sigmoid formula L / (1 + exp(-k*(x - x0))),
 * engine-serialized (MathML.Present.to_presentation_mathml applied to a
 * fixed Math.Expr.expr) -- never hand-written MathML.
 */
export function sigmoidFormulaMathml(): Promise<string>;

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
  matrix: boolean;
  /** The sigmoid (Math.Sigmoid) ABI exports are present. */
  sigmoid: boolean;
  /** The VC Data Integrity crypto ops are present. */
  vcCrypto: boolean;
  /** query()'s `entail` regimes (op queryRaw) are served. */
  entailment: boolean;
  /** queryHdt() (op queryHdt) is served. */
  hdt: boolean;
  /** query()'s `sparql12` and DatasetHandle.query's (queryDataset12, datasetQuery12). */
  sparql12: boolean;
  /** openStore() and the Store methods (storeOpen, storeHandleQuery). */
  store: boolean;
  /** 'full': the whole library is in the wasm module. */
  profile: 'full' | string;
  /** The dispatch ABI version string of the loaded wasm module. */
  abiVersion: string;
  /** openDataset()/DatasetHandle (datasetOpen/Query/Update/Serialize/Close) are present. */
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
  serialize: typeof serialize;
  canonicalize: typeof canonicalize;
  graphs: typeof graphs;
  canonicalHash: typeof canonicalHash;
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
  matrixDeterminant: typeof matrixDeterminant;
  matrixScalarProduct: typeof matrixScalarProduct;
  matrixVectorProduct: typeof matrixVectorProduct;
  matrixOuterProduct: typeof matrixOuterProduct;
  sigmoidPoints: typeof sigmoidPoints;
  sigmoidFormulaMathml: typeof sigmoidFormulaMathml;
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
  DatasetHandle: typeof DatasetHandle;
  Store: typeof Store;
  ParseError: typeof ParseError;
  dataFactory: DataFactory;
  queryRaw: typeof queryRaw;
  version: string;
  engine: string;
};
export default _default;
