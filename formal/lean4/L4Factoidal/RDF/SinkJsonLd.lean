/-
L4Factoidal.RDF.SinkJsonLd — the JSON-LD writer of the serialiser layer.

`L4Factoidal/RDF/Sink.lean` writes JSON-LD through a writer the caller links in
(`Sink.Extra.jsonld`), so that a build without the JSON-LD library does not carry
it, as `L4Factoidal/RDF/SourceJsonLd.lean` does for the reader. A tool that writes
JSON-LD (`l4sbm11 export`, `l4source-convert`) imports this module and passes
`Sink.withJsonLd`.

The writer is JSON-LD 1.1 "Serialize RDF as JSON-LD" (JSON-LD 1.1 API section
8.5) through `JSONLD.FromRdf.fromRdf` with its default options, in the canonical
form of RFC 8785 (`jcsDocument`). The document is in expanded form. An RDF 1.2
triple term has no JSON-LD form, and the writer says so. JSON-LD has no RDF 1.1 or
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

/-- A dataset as expanded-form JSON-LD text. -/
def jsonLdWriter : DatasetWriter := fun _version ds =>
  match L4Factoidal.JSONLD.FromRdf.fromRdf ds {} with
  | some doc => .ok (L4Factoidal.JSONLD.jcsDocument doc)
  | none => .error "from_rdf returned none (an rdf:JSON literal that is not valid JSON, or a triple term)"

/-- The node object of subject `s` from its triples in one graph (every triple has
    subject `s`): the node `fromRdf` builds for `s`, with no `@graph`. -/
def subjectNode (s : Subject) (ts : List Triple) : Except String L4Factoidal.JSON.Json :=
  open L4Factoidal.JSONLD.FromRdf in
  match buildNodemap {} [] ts with
  | none => .error "from_rdf returned none (an rdf:JSON literal that is not valid JSON, or a triple term)"
  | some nm =>
      match findNode nm (subjId s) with
      | some n => .ok (nodeToJson n none)
      | none => .ok (.object [("@id", .string (subjId s))])

/-- The triples of one subject's quads, by graph, in the order each graph first
    appears. A subject is in few graphs, so the groups are a list. -/
def byGraph (qs : List (Triple × Option Subject)) : List (Option Subject × List Triple) :=
  let step := fun (acc : Array (Option Subject × Array Triple)) (q : Triple × Option Subject) =>
    match acc.findIdx? (fun e => e.1 == q.2) with
    | some i => acc.modify i (fun (g, ts) => (g, ts.push q.1))
    | none => acc.push (q.2, #[q.1])
  (qs.foldl step #[]).toList.map fun (g, ts) => (g, ts.toList)

/-- The elements of one subject's quads, as JSON text. -/
def subjectElems (qs : List (Triple × Option Subject)) : Except String (List String) := do
  match qs with
  | [] => pure []
  | (t, _) :: _ =>
      let mut out : Array String := #[]
      for (g, ts) in byGraph qs do
        let node ← subjectNode t.s ts
        let elem := match g with
          | none => node
          | some name => .object [("@id", .string (L4Factoidal.JSONLD.FromRdf.subjId name)), ("@graph", .array [node])]
        out := out.push (L4Factoidal.JSONLD.jcsDocument elem)
      pure out.toList

/-- The element of a named graph with no triple. -/
def emptyGraphElem (name : Subject) : String :=
  L4Factoidal.JSONLD.jcsDocument
    (.object [("@id", .string (L4Factoidal.JSONLD.FromRdf.subjId name)), ("@graph", .array [])])

/-- The JSON-LD stream writer. -/
def jsonLdStream : JsonLdStream := { subject := subjectElems, emptyGraph := emptyGraphElem }

/-- The writers a native tool links: JSON-LD, whole (`serializeDataset`) and by subject
    (`Writer`). -/
def withJsonLd : Extra := { jsonld := some jsonLdWriter, jsonldStream := some jsonLdStream }

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

end L4Factoidal.RDF.Sink
