/-
L4Factoidal.RDF.Sink — the serialiser layer: RDF quads to a document in any
concrete syntax.

Owner, 2026-10-14, verbatim: "SMB11 should store rdf graphs regardless of
source formats - this is why we have reflected w3c rdf core concepts into
Lean. I don't see any reason for the format to be made so explicit for
internal data manipulation- file formats are for exchange and publishing".
Tracking: https://github.com/danbri/factoidal/issues/837.

`L4Factoidal/RDF/Source.lean` turns a document into quads. This module is its
other half: the one place that turns quads into a document. A store gives its
quads (the abstract syntax of RDF 1.1 and RDF 1.2 Concepts, `L4Factoidal.RDF`) to
a `Writer` and does not know in which concrete syntax they are written. A module
under `L4Factoidal/Storage/` imports this module and no `L4Factoidal.Syntax`
module (`tests/sbm11/run.sh` part (n) checks it). A tool at the edge chooses a
format by name (`RdfFormat`, `formatOfLabel`, `formatOfExtension`) and gives it to
`Writer.init`.

## Two meanings of "write a document"

* The batch meaning, `serializeDataset`: a `Dataset` in memory becomes the text.
  The writers are the library's whole-graph serialisers (`Dataset.toNQuads`,
  `Graph.toNTriples`, the pretty-printer `turtleOfGraphAuto` that derives
  prefixes from the whole graph, `graphToRdfXml`, `FromRdf.fromRdf`).
  `Harness/SourceConvert.lean` (`l4source-convert`) uses it.
* The stream meaning, `Writer`: the quads arrive one at a time, in the order the
  caller chooses, and each call returns the text that quad completes. `l4sbm11
  export` uses it, with the quads of the SPO permutation of a generation, so that
  the writer holds one statement and not the dataset.

## What streams

| format | writer | memory |
|---|---|---|
| N-Quads, N-Triples | one line for each quad | one quad |
| Turtle | `bodyPush`: one statement for each subject, `;` between predicates, `,` between objects | one subject, one predicate, one triple |
| TriG | the Turtle statements inside blocks; a new block when the graph of the quad changes | the same, and the open graph name |
| RDF/XML | `rdfxml`: one `rdf:Description` for each subject, written when the next subject starts (`RdfXmlWrite.rxPush`); the namespace table comes from the caller (`Options.rdfxmlNamespaces`) | one subject's triples |
| JSON-LD | `jsonld`: a flattened document, one node object for each subject and graph, written when the next subject starts (`JsonLdStream`) | one subject's quads |
| RDF/XML without a namespace table, JSON-LD without `Extra.jsonldStream` | `whole`: the quads are kept and the document is written at the end | the dataset |

RDF/XML (https://github.com/danbri/factoidal/issues/846). The start tag of
`rdf:RDF` declares the namespaces of all the predicates, so the writer needs them
before the first triple: the caller gives the table (`Options.rdfxmlNamespaces`;
`l4sbm11 export` reads the predicates of the store first, and `streamQuads` takes
them from its list). When each subject's triples arrive one after the other (the
SPO order of a store), the text is the text of the whole-graph writer
`graphToRdfXmlWith` with the same table (`runList_rdfxml_eq`,
`RdfXmlWrite.streamRdfXml_eq`); with the table of the graph's own predicates that is
`graphToRdfXml`.

JSON-LD (https://github.com/danbri/factoidal/issues/847). The whole-dataset
writer (`fromRdf`, JSON-LD 1.1 API section 8.5) sorts the node objects by `@id` and
turns `rdf:first`/`rdf:rest` chains of blank nodes that are referenced once into
`@list`: both need the whole dataset. The stream writes a flattened document in
expanded form: a JSON array with, for each run of one subject's quads, one node
object for the default graph (`{"@id": s, ...}`) and one graph object for each
named graph (`{"@id": g, "@graph": [{"@id": s, ...}]}`), in the order of the
quads, and `{"@id": g, "@graph": []}` for a named graph with no triple. The node
object of a subject is the one `fromRdf` builds from the subject's triples
(`rdf:type` to `@type`). JSON-LD node map generation (JSON-LD 1.1 API section 7.2)
merges node objects with the same `@id` and the graphs with the same name, so the
document is the same dataset; a list is written as its `rdf:first` and `rdf:rest`
triples. `runList_jsonld_eq` proves that the stream writes the elements of all
the runs, in order, separated by commas, in one array. That a JSON-LD reader reads
the document back to the same quads is checked (`SinkJsonLd.lean`,
`tests/sbm11/export_roundtrip.sh`), not proved:
https://github.com/danbri/factoidal/issues/943.

The streaming Turtle and TriG writers write every IRI in full (`<...>`), `a` for
`rdf:type`, and numbers and booleans in their short form, unless the caller gives
a prefix table (`Options.prefixes`, a namespace and a label with its colon, as
`PrefixTable` has them): deriving the prefixes needs the IRIs of the whole graph.
The writer holds the table as an `Abbreviator` (`L4Factoidal/Syntax/TurtleSerialize.lean`),
built once when the writer starts: a scan for a small table and an index for a large one,
so a table of n prefixes costs a hash lookup for each distinct length of a namespace and
not n comparisons for each IRI (`bodyPushBy_ofTable` proves the writer's text equal to the
scan's; https://github.com/danbri/factoidal/issues/865).

## The order of the quads

N-Quads and N-Triples do not depend on the order. Turtle and TriG write a
subject's triples as one statement when they arrive one after the other, and
write a second statement for the same subject when they do not, which is also a
correct document. The SPO permutation of a store gives every triple of a subject
in one run, and the quads of one `(s, p, o)` of different graphs in one run. TriG
starts a new block when the graph of the next quad is not the open one. A graph
that the SPO order interleaves with others therefore gets several blocks. TriG
accepts several blocks for one graph name: the graph is the union of the blocks
of that name. The W3C RDF 1.1 TriG tests `alternating_iri_graphs` and
`alternating_bnode_graphs` alternate the blocks of two graphs, and the Lean TriG
readers pass them.

## Named graphs with no triple

RDF 1.1 Concepts section 4: a named graph is a graph name and an RDF graph, and
the RDF graph can be empty. A quad cannot state a graph with no triple, so a
caller states it with `Writer.declare` (2026-10-15,
https://github.com/danbri/factoidal/issues/855). TriG writes a block with no
triple (`GRAPH <g> {` and `}`, also for a blank node name), and JSON-LD a node
object with an empty `@graph` (the dataset of a whole writer has the graph).
N-Quads has no statement without a triple, and N-Triples, Turtle and RDF/XML
have no graph name: `Writer.statesEmptyGraph` is `false` for them, and the
caller says what the document leaves out. `streamDataset` writes a whole
`Dataset` this way: its quads, then each named graph with no triple.

## Syntaxes with no graph name

N-Triples, Turtle and RDF/XML have no place for the name of a graph. A quad in a
named graph is an error, unless the caller chooses (`GraphChoice`): the default
graph only, the union of all the graphs, or one graph. In the union a triple that
repeats the one before it is written once (with the SPO order that is every
repeat).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.Source
import L4Factoidal.Syntax.NTriples
import L4Factoidal.Syntax.NQuads
import L4Factoidal.Syntax.TurtleSerialize
import L4Factoidal.Syntax.RdfXmlWrite
import L4Factoidal.RDF.Runs
import L4Factoidal.RDF.WriterLabels
import Std.Data.HashMap

namespace L4Factoidal.RDF.Sink

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-- The RDF version a document is written as: `.rdf11` or `.rdf12` (triple terms
    and directional language strings). The same type as the `Source` side. -/
abbrev RdfVersion := Source.RdfVersion

/-! ## What a format does -/

/-- The formats whose stream writer keeps the quads of one subject until the next
    subject starts (RDF/XML and JSON-LD); the others keep at most one statement. -/
def writesBySubject : RdfFormat → Bool
  | .rdfxml | .jsonld => true
  | .nt | .turtle | .nquads | .trig => false

/-! ## Parameters of a writer -/

/-- Which quads a syntax with no graph name (N-Triples, Turtle, RDF/XML) writes. -/
inductive GraphChoice where
  /-- A quad in a named graph is an error. -/
  | refuse
  /-- Only the quads of the default graph; the others are skipped. -/
  | defaultOnly
  /-- Every quad, as a triple of one graph. -/
  | union
  /-- Only the quads of the named graph. -/
  | named (g : Subject)
  deriving BEq

structure Options where
  version : RdfVersion := .rdf12
  graphs : GraphChoice := .refuse
  /-- Turtle and TriG: namespace IRIs and labels with their colon, as
      `PrefixTable` has them. The writer declares each of them at the start. -/
  prefixes : PrefixTable := []
  /-- RDF/XML: the namespace table of the predicates the writer will get
      (`RdfXmlWrite.namespacesOf`). With a table the writer streams; without one it
      keeps the triples and writes at the end. -/
  rdfxmlNamespaces : Option (List (String × String)) := none

/-- A serialiser of one whole dataset, for the syntaxes the caller links in.
    JSON-LD lives outside this module so that a build without the JSON-LD library
    does not carry it: `L4Factoidal/RDF/SinkJsonLd.lean` supplies `withJsonLd`. -/
abbrev DatasetWriter := RdfVersion → Dataset → Except String String

/-- The JSON-LD stream writer's two element writers, which the caller links in
    (`L4Factoidal/RDF/SinkJsonLd.lean`, `jsonLdStream`). -/
structure JsonLdStream where
  /-- The JSON texts of the elements for the quads of one subject, in order. -/
  subject : List (Triple × Option Subject) → Except String (List String)
  /-- The JSON text of a named graph with no triple. -/
  emptyGraph : Subject → String

structure Extra where
  jsonld : Option DatasetWriter := none
  jsonldStream : Option JsonLdStream := none

/-! ## The batch meaning -/

/-- Every triple of the dataset as one graph: the default graph, then each named
    graph. -/
def flatten (ds : Dataset) : Graph := ds.default ++ ds.named.flatMap (·.graph)

/-- The TriG text of a dataset: the default graph as N-Triples lines (TriG
    accepts them as they are), then each named graph as `name { ... }`. -/
def datasetToTrig (v : RdfVersion) (ds : Dataset) : Except String String := do
  let mut out ← Graph.toNTriples ds.default v
  for ng in ds.named do
    out := out ++ Subject.toNTriples ng.name ++ " {\n" ++ (← Graph.toNTriples ng.graph v) ++ "}\n"
  return out

/-! ### Blank-node labels and language tags (https://github.com/danbri/factoidal/issues/986)

The N-Triples, N-Quads, Turtle and TriG writers write the dataset
`Dataset.relabelForWrite` (`RDF/WriterLabels.lean`): a blank-node label outside
BLANK_NODE_LABEL [141s] gets a fresh valid label, the same for each of its
occurrences, that no other blank node of the document has. A language tag
outside LANGTAG [144s] (`langTagWritable`; RDF 1.2: subtags of 1 to 8
characters) has no valid rewrite: the writer refuses the dataset with
`langTagError`, which names the tag. `Term.toNTriples` refuses it for the
N-Triples and N-Quads lines; the Turtle and TriG text writers check the dataset
first (`checkLangTags`). -/

/-- The first language tag of the term (in a triple term too) that the writer
of `v` cannot write. -/
def Term.badLangTag? (v : RdfVersion) : Term → Option String
  | .literal wl =>
      match wl.val.langTag with
      | some tag => if langTagWritable v tag then none else some tag
      | none => none
  | .tripleTerm _ _ o => Term.badLangTag? v o
  | _ => none

/-- The first language tag of the graph that the writer of `v` cannot write. -/
def Graph.badLangTag? (v : RdfVersion) (g : Graph) : Option String :=
  g.findSome? fun t => Term.badLangTag? v t.o

/-- The error for the first language tag of the dataset that the writer of `v`
cannot write. -/
def checkLangTags (v : RdfVersion) (ds : Dataset) : Except String Unit :=
  match Graph.badLangTag? v (flatten ds) with
  | some tag => .error (langTagError tag)
  | none => .ok ()

/-- The dataset that the writer of `fmt` writes: relabelled for the syntaxes
of the N-Triples family. -/
def writerInput (fmt : RdfFormat) (ds : Dataset) : Dataset :=
  match fmt with
  | .nt | .nquads | .turtle | .trig => ds.relabelForWrite
  | _ => ds

/-- The text of a whole dataset in syntax `fmt`. The syntaxes with no graph name
    write the triples of all the graphs together (`flatten`). -/
def serializeDataset (extra : Extra) (fmt : RdfFormat) (v : RdfVersion) (ds : Dataset) :
    Except String String :=
  match fmt with
  | .nquads => Dataset.toNQuads ds.relabelForWrite v
  | .nt => Graph.toNTriples (flatten ds.relabelForWrite) v
  | .turtle => do
      checkLangTags v ds
      pure (turtleOfGraphAuto (flatten ds.relabelForWrite))
  | .trig => datasetToTrig v ds.relabelForWrite
  | .rdfxml => RdfXmlWrite.graphToRdfXml (flatten ds)
  | .jsonld =>
      match extra.jsonld with
      | some write => write v ds
      | none => .error "JSON-LD is not available in this build"

/-! ## The lines of N-Triples and N-Quads -/

/-- One N-Triples line, with its line break. -/
def ntriplesLine (v : RdfVersion) (t : Triple) : Except String String :=
  Triple.toNTriples v t

/-- One N-Quads line, with its line break: the graph name is written when there
    is one. -/
def nquadsLine (v : RdfVersion) (t : Triple) (g : Option Subject) : Except String String :=
  match g with
  | none => Triple.toNTriples v t
  | some name => namedLine v name t

/-- One N-Quads line for terms, as a store holds them. Without the line break;
    the term syntax is that of `Term.toNTriples`. `l4sbm11 dump` prints it. -/
def nquadsLineOfTerms (v : RdfVersion) (s p o : Term) (g : Option Term) : Except String String := do
  let ss ← Term.toNTriples v s
  let ps ← Term.toNTriples v p
  let os ← Term.toNTriples v o
  match g with
  | none => pure s!"{ss} {ps} {os} ."
  | some gt => pure s!"{ss} {ps} {os} {← Term.toNTriples v gt} ."

/-! ## The statements of Turtle and TriG -/

/-- Where a Turtle or TriG writer is in the statement it is writing. -/
structure BodyState where
  /-- TriG: the graph of the open block (`some none` is the default graph);
      `none` when no block is open. Turtle never sets it. -/
  graph : Option (Option Subject) := none
  /-- The subject of the open statement. -/
  subj : Option Subject := none
  /-- The predicate of the open predicate-object list. -/
  pred : Option WfIri := none
  /-- The last triple written in this block, to skip an exact repeat. -/
  last : Option Triple := none

/-- The text that ends the open statement. -/
def BodyState.closeStatement (st : BodyState) : String :=
  if st.subj.isSome then " .\n\n" else ""

/-- Write a triple. The triples of one subject follow one another: a new subject
    ends the open statement and starts another; the same subject with a new
    predicate continues it with `;`; the same predicate continues the object
    list with `,`. The statement is the one `walkTriples` writes.

    This is the SPECIFICATION, in terms of the prefix table: each IRI is shortened by a
    scan of the table. The writer runs `bodyPushBy`, which holds the table as an
    `Abbreviator` built once (`bodyPushBy_ofTable`), so a table of n prefixes does not cost n
    comparisons for each IRI (https://github.com/danbri/factoidal/issues/865). -/
def bodyPush (table : PrefixTable) (st : BodyState) (t : Triple) : BodyState × String :=
  let o := tsTermToTurtle table true t.o
  let p := tsPredicateToTurtle table t.p
  match st.subj with
  | none =>
      ({ st with subj := some t.s, pred := some t.p, last := some t },
        tsSubjectToTurtle table t.s ++ " " ++ p ++ " " ++ o)
  | some s =>
      if s == t.s then
        if st.pred == some t.p then
          ({ st with last := some t }, " , " ++ o)
        else
          ({ st with pred := some t.p, last := some t }, " ;\n    " ++ p ++ " " ++ o)
      else
        ({ st with subj := some t.s, pred := some t.p, last := some t },
          " .\n\n" ++ tsSubjectToTurtle table t.s ++ " " ++ p ++ " " ++ o)

/-- TriG: before a quad of graph `g`, end the open block if its graph is another
    one and open the block of `g`. The specification, in terms of the prefix table
    (`trigSwitchBy` is the form the writer runs). -/
def trigSwitch (table : PrefixTable) (st : BodyState) (g : Option Subject) : BodyState × String :=
  if st.graph == some g then (st, "")
  else
    let close := st.closeStatement ++ (if st.graph.isSome then "}\n\n" else "")
    let opening := match g with
      | none => "{\n"
      | some name => "GRAPH " ++ tsSubjectToTurtle table name ++ " {\n"
    ({ graph := some g }, close ++ opening)

/-- `bodyPush` with the IRIs shortened by an `Abbreviator`: the scan for a small
    table, an index for a large one. The abbreviator is data that the writer holds, so
    the index is built once, when the writer starts. -/
def bodyPushBy (ab : Abbreviator) (st : BodyState) (t : Triple) : BodyState × String :=
  let o := tsTermToTurtleBy ab.run true t.o
  let p := tsPredicateToTurtleBy ab.run t.p
  match st.subj with
  | none =>
      ({ st with subj := some t.s, pred := some t.p, last := some t },
        tsSubjectToTurtleBy ab.run t.s ++ " " ++ p ++ " " ++ o)
  | some s =>
      if s == t.s then
        if st.pred == some t.p then
          ({ st with last := some t }, " , " ++ o)
        else
          ({ st with pred := some t.p, last := some t }, " ;\n    " ++ p ++ " " ++ o)
      else
        ({ st with subj := some t.s, pred := some t.p, last := some t },
          " .\n\n" ++ tsSubjectToTurtleBy ab.run t.s ++ " " ++ p ++ " " ++ o)

/-- `trigSwitch` with the graph name shortened by an `Abbreviator`. -/
def trigSwitchBy (ab : Abbreviator) (st : BodyState) (g : Option Subject) : BodyState × String :=
  if st.graph == some g then (st, "")
  else
    let close := st.closeStatement ++ (if st.graph.isSome then "}\n\n" else "")
    let opening := match g with
      | none => "{\n"
      | some name => "GRAPH " ++ tsSubjectToTurtleBy ab.run name ++ " {\n"
    ({ graph := some g }, close ++ opening)

/-- The writer's form is the specification's: for the abbreviator of a table, `bodyPushBy`
    writes the text and the state that `bodyPush` writes. -/
theorem bodyPushBy_ofTable (table : PrefixTable) (st : BodyState) (t : Triple) :
    bodyPushBy (Abbreviator.ofTable table) st t = bodyPush table st t := by
  unfold bodyPushBy bodyPush tsTermToTurtleBy tsPredicateToTurtleBy tsSubjectToTurtleBy
  rw [Abbreviator.run_ofTable]
  have ho : tsTermToTurtleLoop (tsAbbreviateIri table) true t.o "" 0 = tsTermToTurtle table true t.o := by
    have := tsTermToTurtleFast_eq table true t.o
    exact this
  rw [ho]
  rfl

theorem trigSwitchBy_ofTable (table : PrefixTable) (st : BodyState) (g : Option Subject) :
    trigSwitchBy (Abbreviator.ofTable table) st g = trigSwitch table st g := by
  unfold trigSwitchBy trigSwitch tsSubjectToTurtleBy
  rw [Abbreviator.run_ofTable]
  rfl

#print axioms bodyPushBy_ofTable
#print axioms trigSwitchBy_ofTable

/-- The text that ends a Turtle or TriG document. -/
def BodyState.finish (st : BodyState) : String :=
  st.closeStatement ++ (if st.graph.isSome then "}\n" else "")

/-- The `@prefix` lines at the start of a Turtle or TriG document. -/
def prefixHeader (table : PrefixTable) : String :=
  let lines := renderPrefixHeader table
  String.join lines ++ (if lines.isEmpty then "" else "\n")

/-! ## Choosing the quads of a syntax with no graph name -/

/-- Whether the quad of graph `g` is written. -/
def GraphChoice.keeps (c : GraphChoice) (g : Option Subject) : Except String Bool :=
  match c, g with
  | .refuse, none => .ok true
  | .refuse, some name =>
      .error s!"a quad is in the named graph {Subject.toNTriples name}, and this syntax has no graph name: choose the default graph, the union of the graphs or one graph"
  | .defaultOnly, g => .ok g.isNone
  | .union, _ => .ok true
  | .named n, g => .ok (g == some n)

/-! ## The writer -/

/-- How a whole writer writes the dataset it kept. -/
inductive WholeKind where
  | rdfxml
  | custom (write : DatasetWriter)

/-- The quads of one subject, the newest first, and the subject key. -/
abbrev QuadRun := Option (String × List (Triple × Option Subject))

/-- The key of a quad: the key of its subject. -/
def quadKey (q : Triple × Option Subject) : String := RdfXmlWrite.tripleKey q.1

/-- A writer of one document, generic in nothing: every constructor holds its own
    small state. -/
inductive Writer where
  | nquads (v : RdfVersion)
  | ntriples (v : RdfVersion) (graphs : GraphChoice) (last : Option Triple)
  | turtle (ab : Abbreviator) (graphs : GraphChoice) (st : BodyState)
  | trig (ab : Abbreviator) (st : BodyState)
  /-- RDF/XML by subject: the namespace table, the open subject group and the last
      triple written (to skip a repeat in the union of the graphs). -/
  | rdfxml (nss : List (String × String)) (graphs : GraphChoice) (cur : RdfXmlWrite.Open)
      (last : Option Triple)
  /-- JSON-LD by subject: the element writers, the open subject's quads, and whether an
      element has been written (the next one is preceded by a comma). -/
  | jsonld (js : JsonLdStream) (cur : QuadRun) (started : Bool)
  /-- RDF/XML without a namespace table, JSON-LD without a stream writer: the kept
      quads, newest first, how to write them, and the names of the named graphs
      that `declare` stated, newest first. -/
  | whole (kind : WholeKind) (v : RdfVersion) (graphs : GraphChoice) (quadsRev : List (Triple × Option Subject))
      (last : Option Triple) (declaredRev : List Subject)

/-- The text that appends the elements `es` to an array that already has an element
    when `started` is true. -/
def sepText (started : Bool) : List String → String
  | [] => ""
  | e :: es => (if started then "," else "") ++ ",".intercalate (e :: es)

/-- Whether the array has an element after `es` is appended. -/
def sepNext (started : Bool) (es : List String) : Bool := started || !es.isEmpty

/-- A writer at the start of a document, and the text that starts it (the prefix
    declarations of Turtle and TriG, the start tag of RDF/XML, the `[` of JSON-LD).
    The only failure is a format whose writer the caller did not link: JSON-LD
    without `Extra.jsonldStream` or `Extra.jsonld`. -/
def Writer.init (extra : Extra) (fmt : RdfFormat) (opts : Options) : Except String (Writer × String) :=
  match fmt with
  | .nquads => .ok (.nquads opts.version, "")
  | .nt => .ok (.ntriples opts.version opts.graphs none, "")
  | .turtle => .ok (.turtle (Abbreviator.ofTable opts.prefixes) opts.graphs {}, prefixHeader opts.prefixes)
  | .trig => .ok (.trig (Abbreviator.ofTable opts.prefixes) {}, prefixHeader opts.prefixes)
  | .rdfxml =>
      match opts.rdfxmlNamespaces with
      | some nss => .ok (.rdfxml nss opts.graphs none none, RdfXmlWrite.headerOf nss)
      | none => .ok (.whole .rdfxml opts.version opts.graphs [] none [], "")
  | .jsonld =>
      match extra.jsonldStream, extra.jsonld with
      | some js, _ => .ok (.jsonld js none false, "[")
      | none, some write => .ok (.whole (.custom write) opts.version .union [] none [], "")
      | none, none => .error "JSON-LD is not available in this build"

/-- JSON-LD: the elements of the open subject's quads, and the new state of the array. -/
def flushJsonLd (js : JsonLdStream) (cur : QuadRun) (started : Bool) : Except String (Bool × String) :=
  match cur with
  | none => .ok (started, "")
  | some (_, qs) =>
      match js.subject qs.reverse with
      | .error e => .error e
      | .ok es => .ok (sepNext started es, sepText started es)

/-- Give the writer one quad; the text it completes comes back with the new
    writer. -/
def Writer.push : Writer → Triple → Option Subject → Except String (Writer × String)
  | .nquads v, t, g => do
      let line ← nquadsLine v t g
      pure (.nquads v, line)
  | .ntriples v graphs last, t, g => do
      if !(← graphs.keeps g) then pure (.ntriples v graphs last, "")
      else if last == some t then pure (.ntriples v graphs last, "")
      else
        let line ← ntriplesLine v t
        pure (.ntriples v graphs (some t), line)
  | .turtle ab graphs st, t, g => do
      if !(← graphs.keeps g) then pure (.turtle ab graphs st, "")
      else if st.last == some t then pure (.turtle ab graphs st, "")
      else
        let (st', text) := bodyPushBy ab st t
        pure (.turtle ab graphs st', text)
  | .trig ab st, t, g =>
      let (st1, opening) := trigSwitchBy ab st g
      if st1.last == some t then .ok (.trig ab st1, opening)
      else
        let (st2, text) := bodyPushBy ab st1 t
        .ok (.trig ab st2, opening ++ text)
  | .rdfxml nss graphs cur last, t, g =>
      match graphs.keeps g with
      | .error e => .error e
      | .ok false => .ok (.rdfxml nss graphs cur last, "")
      | .ok true =>
          if graphs == .union && last == some t then .ok (.rdfxml nss graphs cur last, "")
          else
            match RdfXmlWrite.rxPush nss cur t with
            | .error e => .error e
            | .ok (c, text) => .ok (.rdfxml nss graphs c (some t), text)
  | .jsonld js cur started, t, g =>
      let k := quadKey (t, g)
      match cur with
      | none => .ok (.jsonld js (some (k, [(t, g)])) started, "")
      | some (k', qs) =>
          if k' == k then .ok (.jsonld js (some (k', (t, g) :: qs)) started, "")
          else
            match js.subject qs.reverse with
            | .error e => .error e
            | .ok es => .ok (.jsonld js (some (k, [(t, g)])) (sepNext started es), sepText started es)
  | .whole kind v graphs quadsRev last declaredRev, t, g => do
      if !(← graphs.keeps g) then pure (.whole kind v graphs quadsRev last declaredRev, "")
      else if last == some t && g.isNone then pure (.whole kind v graphs quadsRev last declaredRev, "")
      else pure (.whole kind v graphs ((t, g) :: quadsRev) (some t) declaredRev, "")

/-- Whether the writer can state a named graph with no triple: TriG and JSON-LD.
    N-Quads has no statement without a triple; N-Triples, Turtle and RDF/XML have
    no graph name. -/
def Writer.statesEmptyGraph : Writer → Bool
  | .trig .. => true
  | .jsonld .. => true
  | .whole (.custom _) .. => true
  | _ => false

/-- State the named graph `name` with no triple (RDF 1.1 Concepts section 4).
    TriG ends the open statement and block and writes a block with no triple.
    JSON-LD writes the open subject's elements and a graph object with an empty
    `@graph`; a whole JSON-LD writer keeps the name, and the dataset it writes at
    the end has the graph. The other writers cannot state it: the writer and no
    text come back (`statesEmptyGraph` is `false`). A name that also has quads is
    stated twice in TriG and JSON-LD, which is the same dataset (a graph is the
    union of its blocks; node map generation merges graph objects of one name). -/
def Writer.declare : Writer → Subject → Except String (Writer × String)
  | .trig ab st, name =>
      let close := st.closeStatement ++ (if st.graph.isSome then "}\n\n" else "")
      .ok (.trig ab {}, close ++ "GRAPH " ++ tsSubjectToTurtleBy ab.run name ++ " {\n}\n\n")
  | .jsonld js cur started, name =>
      match flushJsonLd js cur started with
      | .error e => .error e
      | .ok (st, text) =>
          .ok (.jsonld js none true, text ++ sepText st [js.emptyGraph name])
  | .whole kind v graphs quadsRev last declaredRev, name =>
      .ok (.whole kind v graphs quadsRev last (name :: declaredRev), "")
  | w, _ => .ok (w, "")

/-- The dataset of kept quads given newest first: the default graph, then the
    named graphs in the order their names first appear. -/
def datasetOfQuadsRev (quadsRev : List (Triple × Option Subject)) : Dataset :=
  let quads := quadsRev.reverse
  let step := fun (acc : Array Triple × Array (Subject × Array Triple) × Std.HashMap Subject Nat)
      (q : Triple × Option Subject) =>
    let (dflt, named, index) := acc
    match q.2 with
    | none => (dflt.push q.1, named, index)
    | some name =>
        match index.get? name with
        | some i => (dflt, named.modify i (fun (n, ts) => (n, ts.push q.1)), index)
        | none => (dflt, named.push (name, #[q.1]), index.insert name named.size)
  let (dflt, named, _) := quads.foldl step (#[], #[], {})
  { default := dflt.toList, named := named.toList.map fun (n, ts) => { name := n, graph := ts.toList } }

/-- The dataset with each declared name that is not a graph name of it added as a
    named graph with no triple, in the order of `names`. -/
def withDeclared (ds : Dataset) (names : List Subject) : Dataset :=
  let step := fun (acc : Array NamedGraph × Std.HashSet Subject) (n : Subject) =>
    if acc.2.contains n then acc else (acc.1.push { name := n, graph := [] }, acc.2.insert n)
  let (named, _) := names.foldl step (ds.named.toArray, Std.HashSet.ofList (ds.named.map (·.name)))
  { ds with named := named.toList }

/-- The end of the document: the text that closes the open statement and block,
    or, for a whole writer, the document. -/
def Writer.finish : Writer → Except String String
  | .nquads _ => .ok ""
  | .ntriples .. => .ok ""
  | .turtle _ _ st => .ok st.finish
  | .trig _ st => .ok st.finish
  | .rdfxml nss _ cur _ => RdfXmlWrite.rxFinish nss cur
  | .jsonld js cur started =>
      match flushJsonLd js cur started with
      | .error e => .error e
      | .ok (_, text) => .ok (text ++ "]")
  | .whole kind v _ quadsRev _ declaredRev =>
      let ds := withDeclared (datasetOfQuadsRev quadsRev) declaredRev.reverse
      match kind with
      | .rdfxml => RdfXmlWrite.graphToRdfXml (flatten ds)
      | .custom write => write v ds

/-- Write a list of quads after the text `acc` and finish: the text a caller
    assembles from the pieces. A loop: one call for each quad, no frame kept. -/
def Writer.runList : Writer → String → List (Triple × Option Subject) → Except String String
  | w, acc, [] =>
      match w.finish with
      | .error e => .error e
      | .ok e => .ok (acc ++ e)
  | w, acc, (t, g) :: l =>
      match w.push t g with
      | .error e => .error e
      | .ok (w', text) => w'.runList (acc ++ text) l

/-- Write a list of quads and finish: the text a caller would assemble from the
    pieces. -/
def Writer.writeAll (w : Writer) (header : String) (quads : List (Triple × Option Subject)) :
    Except String String :=
  w.runList header quads

/-- RDF/XML: the namespace table of predicates given in the order they first appear
    (`RdfXmlWrite.namespacesOf`). -/
def rdfxmlTableOfPredicates (ps : List WfIri) : List (String × String) :=
  RdfXmlWrite.namespacesOf ps

/-- RDF/XML: the namespace table of the quads a writer with graph choice `graphs`
    keeps (a quad that `graphs` refuses is skipped here; the writer refuses it). -/
def rdfxmlTableOf (graphs : GraphChoice) (quads : List (Triple × Option Subject)) :
    List (String × String) :=
  RdfXmlWrite.namespacesOf ((quads.filter (fun q => (graphs.keeps q.2).toOption.getD false)).map (·.1.p))

/-- The options with the RDF/XML namespace table of `quads` when the caller gave none. -/
def withTable (fmt : RdfFormat) (opts : Options) (quads : List (Triple × Option Subject)) : Options :=
  match fmt, opts.rdfxmlNamespaces with
  | .rdfxml, none => { opts with rdfxmlNamespaces := some (rdfxmlTableOf opts.graphs quads) }
  | _, _ => opts

/-- The text of the quads in syntax `fmt`, by the stream writer. -/
def streamQuads (extra : Extra) (fmt : RdfFormat) (opts : Options)
    (quads : List (Triple × Option Subject)) : Except String String := do
  let (w, header) ← Writer.init extra fmt (withTable fmt opts quads)
  w.writeAll header quads

/-- The text of a whole dataset by the stream writer: its quads (the default
    graph, then each named graph in list order), then each named graph with no
    triple, stated by `Writer.declare`. -/
def streamDataset (extra : Extra) (fmt : RdfFormat) (opts : Options) (ds0 : Dataset) :
    Except String String := do
  if fmt == .turtle || fmt == .trig then checkLangTags opts.version ds0
  let ds := writerInput fmt ds0
  let quads : List (Triple × Option Subject) :=
    ds.default.map (fun t => (t, none)) ++ ds.named.flatMap (fun ng => ng.graph.map (fun t => (t, some ng.name)))
  let (w0, header) ← Writer.init extra fmt (withTable fmt opts quads)
  let mut w := w0
  let mut out := header
  for (t, g) in quads do
    let (w', text) ← w.push t g
    w := w'
    out := out ++ text
  for ng in ds.named do
    if ng.graph.isEmpty then
      let (w', text) ← w.declare ng.name
      w := w'
      out := out ++ text
  pure (out ++ (← w.finish))

/-! ## What the stream writers write

`runList_rdfxml_eq`: for the triples of the default graph, the RDF/XML writer writes
what `RdfXmlWrite.rxRun` writes, so (`RdfXmlWrite.streamRdfXml_eq`) the text of the
whole-graph writer when each subject's triples are consecutive.

`runList_jsonld_eq`: the JSON-LD writer writes one array of the elements of the
runs of one subject's quads (`Runs.runs quadKey`), in order. -/

/-- The elements of the runs, in order. A specification: one call for each run. -/
def elemsOf (js : JsonLdStream) : List (String × List (Triple × Option Subject)) → Except String (List String)
  | [] => .ok []
  | r :: rs =>
      match js.subject r.2 with
      | .error e => .error e
      | .ok a =>
          match elemsOf js rs with
          | .error e => .error e
          | .ok b => .ok (a ++ b)

theorem sepText_append (started : Bool) (es1 es2 : List String) :
    sepText started (es1 ++ es2) = sepText started es1 ++ sepText (sepNext started es1) es2 := by
  cases es1 with
  | nil => simp [sepText, sepNext]
  | cons e es1 =>
      cases es2 with
      | nil => simp [sepText]
      | cons f es2 =>
          simp only [List.cons_append, sepText, sepNext, List.isEmpty_cons, Bool.not_false,
            Bool.or_true, if_true]
          rw [← List.cons_append, String.intercalate_append_of_ne_nil (by simp) (by simp)]
          simp [String.append_assoc]

/-- The default graph's triples through the RDF/XML writer: `RdfXmlWrite.rxRun`. -/
theorem runList_rdfxml (nss : List (String × String)) :
    ∀ (l : List Triple) (cur : RdfXmlWrite.Open) (last : Option Triple) (acc : String),
      (Writer.rdfxml nss .refuse cur last).runList acc (l.map (·, none)) =
        RdfXmlWrite.rxRun nss cur acc l
  | [], cur, last, acc => by
      simp only [List.map_nil, Writer.runList, Writer.finish, RdfXmlWrite.rxRun]
      cases RdfXmlWrite.rxFinish nss cur <;> rfl
  | t :: l, cur, last, acc => by
      simp only [List.map_cons, Writer.runList, Writer.push, GraphChoice.keeps, RdfXmlWrite.rxRun]
      have hu : ((GraphChoice.refuse == GraphChoice.union) && last == some t) = false := rfl
      simp only [hu, Bool.false_eq_true, if_false]
      cases RdfXmlWrite.rxPush nss cur t with
      | error e => rfl
      | ok r => exact runList_rdfxml nss l r.1 (some t) (acc ++ r.2)

/-- The RDF/XML writer with namespace table `nss`, given the triples of a graph in an
    order where each subject's triples are consecutive (the SPO order of a store),
    writes the text of the whole-graph writer with the same table. -/
theorem runList_rdfxml_eq (nss : List (String × String)) (l : List Triple)
    (h : RdfXmlWrite.Contiguous l) :
    (Writer.rdfxml nss .refuse none none).runList (RdfXmlWrite.headerOf nss) (l.map (·, none)) =
      RdfXmlWrite.graphToRdfXmlWith nss l := by
  rw [runList_rdfxml]
  exact RdfXmlWrite.streamRdfXml_eq nss l h

/-- The JSON-LD writer after the text `acc`, with the open run `cur`: the elements of
    the runs, appended to the array. -/
theorem runList_jsonld (js : JsonLdStream) :
    ∀ (l : List (Triple × Option Subject)) (cur : QuadRun) (started : Bool) (acc : String),
      (Writer.jsonld js cur started).runList acc l =
        match elemsOf js (Runs.runsFrom quadKey cur l) with
        | .error e => .error e
        | .ok es => .ok (acc ++ (sepText started es ++ "]"))
  | [], none, started, acc => by
      simp [Writer.runList, Writer.finish, flushJsonLd, Runs.runsFrom, elemsOf, sepText]
  | [], some (k, qs), started, acc => by
      simp only [Writer.runList, Writer.finish, flushJsonLd, Runs.runsFrom, elemsOf]
      cases js.subject qs.reverse with
      | error e => rfl
      | ok es => simp
  | (t, g) :: l, none, started, acc => by
      have : (Writer.jsonld js none started).runList acc ((t, g) :: l) =
          (Writer.jsonld js (some (quadKey (t, g), [(t, g)])) started).runList acc l := by
        simp [Writer.runList, Writer.push]
      rw [this, runList_jsonld js l]
      simp [Runs.runsFrom]
  | (t, g) :: l, some (k, qs), started, acc => by
      by_cases hk : (k == quadKey (t, g)) = true
      · have : (Writer.jsonld js (some (k, qs)) started).runList acc ((t, g) :: l) =
            (Writer.jsonld js (some (k, (t, g) :: qs)) started).runList acc l := by
          simp [Writer.runList, Writer.push, hk]
        rw [this, runList_jsonld js l]
        simp [Runs.runsFrom, hk]
      · cases hs : js.subject qs.reverse with
        | error e => simp [Writer.runList, Writer.push, hk, hs, Runs.runsFrom, elemsOf]
        | ok es =>
            have : (Writer.jsonld js (some (k, qs)) started).runList acc ((t, g) :: l) =
                (Writer.jsonld js (some (quadKey (t, g), [(t, g)])) (sepNext started es)).runList
                  (acc ++ sepText started es) l := by
              simp [Writer.runList, Writer.push, hk, hs]
            rw [this, runList_jsonld js l]
            simp only [Runs.runsFrom, hk, Bool.false_eq_true, if_false, elemsOf, hs]
            cases elemsOf js (Runs.runsFrom quadKey (some (quadKey (t, g), [(t, g)])) l) with
            | error e => rfl
            | ok b => simp [sepText_append, String.append_assoc]

/-- The JSON-LD writer from the start: `[`, the elements of all the runs of one
    subject's quads separated by commas, and `]`. -/
theorem runList_jsonld_eq (js : JsonLdStream) (l : List (Triple × Option Subject)) :
    (Writer.jsonld js none false).runList "[" l =
      match elemsOf js (Runs.runs quadKey l) with
      | .error e => .error e
      | .ok es => .ok ("[" ++ ",".intercalate es ++ "]") := by
  rw [runList_jsonld]
  unfold Runs.runs
  cases elemsOf js (Runs.runsFrom quadKey none l) with
  | error e => rfl
  | ok es =>
      cases es with
      | nil => simp [sepText]
      | cons e es => simp [sepText, String.append_assoc]

#print axioms sepText_append
#print axioms runList_rdfxml_eq
#print axioms runList_jsonld_eq

/-! ## Build-time checks -/

private def iri! (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

private def sIri (s : String) (h : isIri s := by rfl) : Subject := .iri ⟨s, h⟩

private def intLit (lex : String) : Term :=
  .literal ⟨{ lexicalForm := lex, datatype := xsdInteger, langTag := none, direction := none }, rfl⟩

private def strLit (lex : String) : Term := .literal (Literal.string lex)

private def tr (s : Subject) (p : String) (o : Term) (h : isIri p := by rfl) : Triple :=
  { s := s, p := ⟨p, h⟩, o := o }

private def sA : Subject := sIri "http://e/a"
private def sB : Subject := sIri "http://e/b"
private def gX : Subject := sIri "http://e/gx"
private def gY : Subject := .bnode "gy"

/-- Triples in SPO order of a store: the subject `a` has two predicates, one with
    two objects, and appears in two graphs; a literal needs escaping; a blank
    node is an object. -/
private def quadsSpo : List (Triple × Option Subject) :=
  [ (tr sA "http://e/p" (.iri (iri! "http://e/o1")), none),
    (tr sA "http://e/p" (.iri (iri! "http://e/o2")), none),
    (tr sA "http://e/p" (.iri (iri! "http://e/o2")), some gX),
    (tr sA "http://e/q" (strLit "x \"y\"\n"), some gX),
    (tr sA "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" (.iri (iri! "http://e/C")), some gY),
    (tr sB "http://e/p" (intLit "007"), none),
    (tr sB "http://e/p" (.bnode "n1"), some gY),
    (tr (.bnode "n1") "http://e/q" (strLit "z"), some gY) ]

private def datasetOf (quads : List (Triple × Option Subject)) : Dataset :=
  datasetOfQuadsRev quads.reverse

/-- Two datasets are equal as sets of quads with the same graph names. -/
private def sameQuads (a b : Dataset) : Bool :=
  let qs (d : Dataset) : List (Triple × Option Subject) :=
    d.default.map (fun t => (t, none)) ++ d.named.flatMap fun ng => ng.graph.map fun t => (t, some ng.name)
  let x := qs a
  let y := qs b
  x.all (fun q => y.any (· == q)) && y.all (fun q => x.any (· == q))

/-- The quads, written in `fmt`, read back through the source layer: the same
    quads. -/
private def roundTrips (fmt : RdfFormat) (quads : List (Triple × Option Subject)) : Bool :=
  match streamQuads {} fmt {} quads with
  | .error _ => false
  | .ok text =>
      match Source.parseDocument {} fmt .rdf12 none text with
      | .error _ => false
      | .ok ds => sameQuads ds (datasetOf quads)

#guard roundTrips .nquads quadsSpo
#guard roundTrips .trig quadsSpo
#guard roundTrips .rdfxml (quadsSpo.filter (·.2.isNone))
-- RDF/XML by subject: the default graph of `quadsSpo` (each subject's triples
-- consecutive) gives the text of the whole-graph writer (`runList_rdfxml_eq`).
#guard (streamQuads {} .rdfxml {} (quadsSpo.filter (·.2.isNone))).toOption ==
  (serializeDataset {} .rdfxml .rdf12 (datasetOf (quadsSpo.filter (·.2.isNone)))).toOption
-- The union of the graphs: a triple in two graphs is written once.
#guard match streamQuads {} .rdfxml { graphs := .union } quadsSpo with
       | .ok text => (text.splitOn "rdf:resource=\"http://e/o2\"").length == 2
       | .error _ => false

-- The graph-only syntaxes refuse a quad in a named graph, and write what the caller chooses.
#guard (streamQuads {} .nt {} quadsSpo).toOption.isNone
#guard (streamQuads {} .turtle {} quadsSpo).toOption.isNone
#guard (streamQuads {} .rdfxml {} quadsSpo).toOption.isNone
#guard (streamQuads {} .nt { graphs := .defaultOnly } quadsSpo).toOption.isSome
#guard (streamQuads {} .nt { graphs := .named gX } quadsSpo).toOption.isSome

-- Default graph: the triples read back are those of the default graph.
#guard match streamQuads {} .turtle { graphs := .defaultOnly } quadsSpo with
       | .ok text =>
           match Source.parseDocument {} .turtle .rdf12 none text with
           | .ok ds => ds.default.length == 3 && ds.named.isEmpty
           | .error _ => false
       | .error _ => false

-- Union: the triple (a p o2) is in the default graph and in graph gx, and is written once.
#guard match streamQuads {} .nt { graphs := .union } quadsSpo with
       | .ok text => ((text.splitOn "\n").filter (· != "")).length == 7
       | .error _ => false

-- One graph: the triples of gx.
#guard match streamQuads {} .nt { graphs := .named gX } quadsSpo with
       | .ok text => ((text.splitOn "\n").filter (· != "")).length == 2
       | .error _ => false

-- Turtle: one statement for the subject `a`, with `,` and `;` (default graph only, so
-- that the triples of `a` are one run).
#guard match streamQuads {} .turtle { graphs := .defaultOnly } (quadsSpo.take 2) with
       | .ok text => (text.splitOn "<http://e/a>").length == 2 && (text.splitOn " , ").length == 2
       | .error _ => false

-- N-Quads from the stream writer is the batch writer's text, line for line.
#guard match streamQuads {} .nquads {} quadsSpo, Dataset.toNQuads (datasetOf quadsSpo) .rdf12 with
       | .ok a, .ok b =>
           (a.splitOn "\n").toArray.qsort (· < ·) == (b.splitOn "\n").toArray.qsort (· < ·)
       | _, _ => false

-- A prefix table shortens the IRIs it covers and the document reads back the same.
#guard match streamQuads {} .trig { prefixes := [("http://e/", "e:")] } quadsSpo with
       | .ok text =>
           (text.splitOn "@prefix e: <http://e/> .").length == 2 &&
           (match Source.parseDocument {} .trig .rdf12 none text with
            | .ok ds => sameQuads ds (datasetOf quadsSpo)
            | .error _ => false)
       | .error _ => false

-- Named graphs with no triple: one IRI and one blank node, beside a graph with a triple.
private def dsEmpty : Dataset :=
  { default := [tr sA "http://e/p" (.iri (iri! "http://e/o1"))],
    named := [ { name := gX, graph := [] }, { name := gY, graph := [] },
               { name := sIri "http://e/g1", graph := [tr sB "http://e/p" (intLit "1")] } ] }

/-- The named graphs of a dataset read back are those of `dsEmpty`: `gx` with no
    triple, `g1` with one, and one blank node name with no triple. -/
private def likeDsEmpty (ds : Dataset) : Bool :=
  ds.default.length == 1 && ds.named.length == 3 &&
  ds.named.any (fun ng => ng.name == gX && ng.graph.isEmpty) &&
  ds.named.any (fun ng => ng.name == sIri "http://e/g1" && ng.graph.length == 1) &&
  ds.named.any (fun ng => (match ng.name with | .bnode _ => true | .iri _ => false) && ng.graph.isEmpty)

-- TriG states both graphs with no triple, and the TriG reader reads them back.
#guard match streamDataset {} .trig {} dsEmpty with
       | .ok text =>
           match Source.parseDocument {} .trig .rdf12 none text with
           | .ok ds => likeDsEmpty ds
           | .error _ => false
       | .error _ => false
-- A block with no triple after an open block closes it first.
#guard match Writer.init {} .trig {} with
       | .ok (w, _) =>
           match w.push (tr sA "http://e/p" (strLit "v")) (some gX) with
           | .ok (w1, t1) =>
               match w1.declare gY with
               | .ok (_, t2) => t1 ++ t2 == "GRAPH <http://e/gx> {\n<http://e/a> <http://e/p> \"v\" .\n\n}\n\nGRAPH _:gy {\n}\n\n"
               | .error _ => false
           | .error _ => false
       | .error _ => false
-- N-Quads cannot state them: the two lines of the quads only.
#guard match streamDataset {} .nquads {} dsEmpty with
       | .ok text => ((text.splitOn "\n").filter (· != "")).length == 2
       | .error _ => false
#guard (Writer.nquads .rdf12).statesEmptyGraph == false
#guard (Writer.trig (Abbreviator.ofTable []) {}).statesEmptyGraph == true
-- `withDeclared` adds a name once, and not a name that has a graph.
#guard (withDeclared dsEmpty [gX, sIri "http://e/g2", sIri "http://e/g2"]).named.length == 4

-- JSON-LD without a linked writer is refused at `init`, by name.
#guard (match Writer.init ({} : Extra) .jsonld {} with
        | .error m => m == "JSON-LD is not available in this build"
        | .ok _ => false)

end L4Factoidal.RDF.Sink
