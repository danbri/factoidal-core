/-
L4Factoidal.RDF.SinkJsonLd — the JSON-LD writer of the serialiser layer.

`L4Factoidal/RDF/Sink.lean` writes JSON-LD through a writer the caller links in
(`Sink.Extra.jsonld`), so that a build without the JSON-LD library does not carry
it, as `L4Factoidal/RDF/SourceJsonLd.lean` does for the reader. A tool that writes
JSON-LD (`l4sbm11 export`, `l4source-convert`) imports this module and passes
`Sink.withJsonLd`.

The writer is JSON-LD 1.1 "Serialize RDF as JSON-LD" (JSON-LD 1.1 API section
8.5) through `JSONLD.FromRdf.fromRdf` with its default options, in the canonical
form of RFC 8785 (`jcsDocument`). The document is in expanded form. With the default
options an RDF 1.2 triple term has no JSON-LD form, and the writer says so;
`withJsonLdStar` writes it in the JSON-LD-star form (`@triple`, `@reifies`,
`@annotation`; `docs/designissues/2026-10-26-jsonld-star.md`). JSON-LD has no RDF 1.1 or
RDF 1.2 mode, so the version argument is ignored.

The stream writer (`jsonLdStream`, https://github.com/danbri/factoidal/issues/847)
writes a flattened document in expanded form, one subject at a time: for the quads
of one subject, a node object for the default graph and a graph object
`{"@id": g, "@graph": [node]}` for each named graph, in the order the graphs first
appear among the subject's quads. A node object is the one `fromRdf` builds from
the subject's triples of that graph (`subjectNode`: `rdf:type` to `@type`, the
values of `rdfToObject`), in RFC 8785 form. It does not sort by `@id` and does not
write `@list`: both need the whole dataset. `l4sbm11 export` uses it;
`serializeDataset` (`l4source-convert`) still uses `fromRdf`.

`Sink.runList_jsonld_eq` proves what text the stream writes. That the JSON-LD reader
reads that text back to the same quads is checked, not proved: the `#guard`s below
and `tests/sbm11/export_roundtrip.sh`. Open issue and expected-failure row
(`Harness/ProofObligations.lean`, `jsonLdStream_readBack`):
https://github.com/danbri/factoidal/issues/943.
-/
import L4Factoidal.RDF.Sink
import L4Factoidal.RDF.SourceJsonLd
import L4Factoidal.JSONLD.FromRdf

namespace L4Factoidal.RDF.Sink

open L4Factoidal.RDF

/-- A dataset as expanded-form JSON-LD text, with the fromRdf options `opts`. -/
def jsonLdWriterWith (opts : L4Factoidal.JSONLD.FromRdf.Options) : DatasetWriter := fun _version ds =>
  match L4Factoidal.JSONLD.FromRdf.fromRdf ds opts with
  | some doc => .ok (L4Factoidal.JSONLD.jcsDocument doc)
  | none => .error (if opts.rdfstar then "from_rdf returned none (an rdf:JSON literal that is not valid JSON)"
                    else "from_rdf returned none (an rdf:JSON literal that is not valid JSON, or a triple term)")

/-- A dataset as expanded-form JSON-LD text (default options: a triple term is an
    error). -/
def jsonLdWriter : DatasetWriter := jsonLdWriterWith {}

/-- The node object of subject `s` from its triples in one graph (every triple has
    subject `s`): the node `fromRdf` builds for `s` with the options `opts`, with no
    `@graph`. With `rdfstar`, a triple term is `@triple` and `rdf:reifies` is
    `@reifies`; the stream does not fold annotations (that needs the whole graph). -/
def subjectNodeWith (opts : L4Factoidal.JSONLD.FromRdf.Options) (s : Subject) (ts : List Triple) :
    Except String L4Factoidal.JSON.Json :=
  open L4Factoidal.JSONLD.FromRdf in
  match buildNodemap opts [] ts with
  | none => .error "from_rdf returned none (an rdf:JSON literal that is not valid JSON, or a triple term)"
  | some nm =>
      match findNode nm (subjId s) with
      | some n => .ok (nodeToJson n none)
      | none => .ok (.object [("@id", .string (subjId s))])

/-- `subjectNodeWith` with the default options. -/
def subjectNode (s : Subject) (ts : List Triple) : Except String L4Factoidal.JSON.Json :=
  subjectNodeWith {} s ts

/-- The triples of one subject's quads, by graph, in the order each graph first
    appears. A subject is in few graphs, so the groups are a list. -/
def byGraph (qs : List (Triple × Option Subject)) : List (Option Subject × List Triple) :=
  let step := fun (acc : Array (Option Subject × Array Triple)) (q : Triple × Option Subject) =>
    match acc.findIdx? (fun e => e.1 == q.2) with
    | some i => acc.modify i (fun (g, ts) => (g, ts.push q.1))
    | none => acc.push (q.2, #[q.1])
  (qs.foldl step #[]).toList.map fun (g, ts) => (g, ts.toList)

/-- The elements of one subject's quads, as JSON text, with the fromRdf options
    `opts`. -/
def subjectElemsWith (opts : L4Factoidal.JSONLD.FromRdf.Options) (qs : List (Triple × Option Subject)) :
    Except String (List String) := do
  match qs with
  | [] => pure []
  | (t, _) :: _ =>
      let mut out : Array String := #[]
      for (g, ts) in byGraph qs do
        let node ← subjectNodeWith opts t.s ts
        let elem := match g with
          | none => node
          | some name => .object [("@id", .string (L4Factoidal.JSONLD.FromRdf.subjId name)), ("@graph", .array [node])]
        out := out.push (L4Factoidal.JSONLD.jcsDocument elem)
      pure out.toList

/-- The elements of one subject's quads, as JSON text (default options). -/
def subjectElems (qs : List (Triple × Option Subject)) : Except String (List String) :=
  subjectElemsWith {} qs

/-- The element of a named graph with no triple. -/
def emptyGraphElem (name : Subject) : String :=
  L4Factoidal.JSONLD.jcsDocument
    (.object [("@id", .string (L4Factoidal.JSONLD.FromRdf.subjId name)), ("@graph", .array [])])

/-- The JSON-LD stream writer. -/
def jsonLdStream : JsonLdStream := { subject := subjectElems, emptyGraph := emptyGraphElem }

/-- The writers a native tool links: JSON-LD, whole (`serializeDataset`) and by subject
    (`Writer`). -/
def withJsonLd : Extra := { jsonld := some jsonLdWriter, jsonldStream := some jsonLdStream }

/-- The JSON-LD stream writer with the fromRdf options `opts`. -/
def jsonLdStreamWith (opts : L4Factoidal.JSONLD.FromRdf.Options) : JsonLdStream :=
  { subject := subjectElemsWith opts, emptyGraph := emptyGraphElem }

/-- The JSON-LD writers in JSON-LD-star mode (`rdfstar`): a triple term is written as
    `@triple`, `rdf:reifies` as `@reifies`, and the whole-dataset writer folds a
    blank-node reifier of an asserted triple into `@annotation`. Opt-in: `withJsonLd`
    keeps refusing triple terms. -/
def withJsonLdStar : Extra :=
  { jsonld := some (jsonLdWriterWith { rdfstar := true }),
    jsonldStream := some (jsonLdStreamWith { rdfstar := true }) }

/-! ## Build-time checks -/

private def exDs : Dataset :=
  match Source.parseDocument Source.withJsonLd .jsonld .rdf11 none
      "{\"@id\":\"http://e/a\",\"http://e/p\":[{\"@value\":\"v\"},{\"@id\":\"http://e/b\"}]}" with
  | .ok ds => ds
  | .error _ => Dataset.empty

-- The text written and read back by the JSON-LD reader is the dataset.
#guard exDs.default.length == 2 &&
  (match serializeDataset withJsonLd .jsonld .rdf12 exDs with
   | .ok text =>
       match Source.parseDocument Source.withJsonLd .jsonld .rdf12 none text with
       | .ok ds => ds.default.length == 2 && ds.named.isEmpty
       | .error _ => false
   | .error _ => false)

-- The stream writer gives the batch writer's document when the dataset has one
-- subject, no list and no named graph.
#guard (match Writer.init withJsonLd .jsonld {} with
        | .error _ => false
        | .ok (w, header) =>
            (w.writeAll header (exDs.default.map fun t => (t, none))).toOption ==
              (serializeDataset withJsonLd .jsonld .rdf12 exDs).toOption)

/-- The quads of a dataset, as one dataset with one entry for each graph name: the
    JSON-LD reader gives one entry for each graph object, and the document has
    several graph objects for one name. -/
private def merged (d : Dataset) : Dataset :=
  datasetOfQuadsRev (d.default.map (fun t => (t, none)) ++
    d.named.flatMap (fun (ng : NamedGraph) => ng.graph.map (fun t => (t, some ng.name)))).reverse

/-- Two datasets have isomorphic quads. -/
private def sameDataset (a b : Dataset) : Bool :=
  (merged a).isomorphic? (merged b)

/-- The stream's document read back by the JSON-LD reader is the dataset. -/
private def streamRoundTrips (ds : Dataset) : Bool :=
  match streamDataset withJsonLd .jsonld {} ds with
  | .ok text =>
      match Source.parseDocument Source.withJsonLd .jsonld .rdf12 none text with
      | .ok ds' => sameDataset ds ds'
      | .error _ => false
  | .error _ => false

private def mixedDs : Dataset :=
  match Source.parseDocument Source.withJsonLd .jsonld .rdf11 none
      ("[{\"@id\":\"http://e/a\",\"@type\":[\"http://e/C\"],\"http://e/p\":[{\"@value\":\"v\",\"@language\":\"en\"},{\"@id\":\"_:b0\"}]," ++
       "\"http://e/l\":[{\"@list\":[{\"@value\":\"1\"},{\"@id\":\"http://e/x\"}]}]}," ++
       "{\"@id\":\"http://e/g\",\"@graph\":[{\"@id\":\"http://e/a\",\"http://e/q\":[{\"@value\":\"7\",\"@type\":\"http://www.w3.org/2001/XMLSchema#integer\"}]}," ++
       "{\"@id\":\"_:b0\",\"http://e/q\":[{\"@id\":\"http://e/g\"}]}]}," ++
       "{\"@id\":\"_:g2\",\"@graph\":[{\"@id\":\"http://e/a\",\"http://e/r\":[{\"@id\":\"http://e/a\"}]}]}]") with
  | .ok ds => ds
  | .error _ => Dataset.empty

-- A type, a language string, a blank node, a list, two named graphs (one a blank
-- node), a subject in three graphs, a graph name that is also a subject.
#guard mixedDs.named.length == 2 && streamRoundTrips mixedDs
#guard streamRoundTrips exDs

-- A named graph with no triple (RDF 1.1 Concepts section 4): JSON-LD writes a node object
-- with an empty `@graph`, and the JSON-LD reader reads the graph back.
private def emptyGraphDs : Dataset :=
  { default := [], named := [{ name := .iri ⟨"http://e/g0", rfl⟩, graph := [] }] }

#guard streamRoundTrips emptyGraphDs
#guard match streamDataset withJsonLd .jsonld {} emptyGraphDs with
       | .ok text =>
           (text.splitOn "\"@graph\":[]").length == 2 &&
           (match Source.parseDocument Source.withJsonLd .jsonld .rdf12 none text with
            | .ok ds => ds.named.length == 1 && ds.named.all (·.graph.isEmpty)
            | .error _ => false)
       | .error _ => false

-- A triple term: the default writer refuses it; the JSON-LD-star writer writes `@triple`.
private def ttDs : Dataset :=
  { default := [⟨.iri ⟨"http://e/s", rfl⟩, ⟨"http://e/p", rfl⟩,
                 .tripleTerm (.iri ⟨"http://e/a", rfl⟩) ⟨"http://e/q", rfl⟩ (.iri ⟨"http://e/b", rfl⟩)⟩],
    named := [] }

#guard (serializeDataset withJsonLd .jsonld .rdf12 ttDs).toOption.isNone
#guard (serializeDataset withJsonLdStar .jsonld .rdf12 ttDs).toOption ==
  some "[{\"@id\":\"http://e/s\",\"http://e/p\":[{\"@triple\":{\"@id\":\"http://e/a\",\"http://e/q\":[{\"@id\":\"http://e/b\"}]}}]}]"
#guard (subjectNodeWith { rdfstar := true } (.iri ⟨"http://e/s", rfl⟩) ttDs.default).toOption.isSome
#guard (subjectNode (.iri ⟨"http://e/s", rfl⟩) ttDs.default).toOption.isNone

-- JSON-LD-star round trip: the star writer's text, read by the star reader
-- (`Source.withJsonLdStar`), is the dataset. The JSON-LD 1.1 reader ignores the
-- unknown keyword `@triple`, so the value is an empty node object: a blank node.
#guard ((serializeDataset withJsonLdStar .jsonld .rdf12 ttDs).toOption.bind fun txt =>
          (Source.parseDocument Source.withJsonLdStar .jsonld .rdf12 none txt).toOption) ==
        some ttDs
#guard ((serializeDataset withJsonLdStar .jsonld .rdf12 ttDs).toOption.bind fun txt =>
          (Source.parseDocument Source.withJsonLd .jsonld .rdf12 none txt).toOption.map
            (·.default.map (fun t => match t.o with | Term.bnode _ => true | _ => false))) == some [true]

-- An annotated triple: `<s> <p> <o>` asserted, and a blank-node reifier with one
-- property. The star writer folds the reifier into `@annotation`; the star reader
-- gives the three triples back (the reifier label may differ).
private def annDs : Dataset :=
  let s : Subject := .iri ⟨"http://e/s", rfl⟩
  let p : WfIri := ⟨"http://e/p", rfl⟩
  let o : Term := .iri ⟨"http://e/o", rfl⟩
  { default := [⟨s, p, o⟩,
                ⟨.bnode "r", ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies", rfl⟩,
                 .tripleTerm s p o⟩,
                ⟨.bnode "r", ⟨"http://e/certainty", rfl⟩, .iri ⟨"http://e/high", rfl⟩⟩],
    named := [] }

-- An RDF 1.2 directional language string: the star writer writes `@direction`
-- (rdfDirection `rdf-1.2`, the default under `rdfstar`) and the star reader gives
-- `rdf:dirLangString` back. The JSON-LD 1.1 writer drops the direction
-- (https://github.com/danbri/factoidal/issues/984).
private def dirDs : Dataset :=
  match Source.parseDocument {} .nt .rdf12 none
      "<http://e/s> <http://e/p> \"y\"@ar--rtl .\n" with
  | .ok ds => ds
  | .error _ => Dataset.empty
#guard dirDs.default.length == 1
#guard ((serializeDataset withJsonLdStar .jsonld .rdf12 dirDs).toOption.bind fun txt =>
          (Source.parseDocument Source.withJsonLdStar .jsonld .rdf12 none txt).toOption) ==
        some dirDs
#guard ((serializeDataset withJsonLd .jsonld .rdf12 dirDs).toOption.bind fun txt =>
          (Source.parseDocument Source.withJsonLd .jsonld .rdf12 none txt).toOption) != some dirDs

#guard ((serializeDataset withJsonLdStar .jsonld .rdf12 annDs).toOption.map
          (fun txt => (txt.splitOn "@annotation").length)) == some 2
#guard ((serializeDataset withJsonLdStar .jsonld .rdf12 annDs).toOption.bind fun txt =>
          (Source.parseDocument Source.withJsonLdStar .jsonld .rdf12 none txt).toOption.map
            (·.default.length)) == some 3

end L4Factoidal.RDF.Sink
