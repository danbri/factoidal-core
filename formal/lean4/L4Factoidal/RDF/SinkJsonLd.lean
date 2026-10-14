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

JSON-LD is written whole (`Sink.writesWhole`):
https://github.com/danbri/factoidal/issues/847.
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

/-- The writers a native tool links: JSON-LD. -/
def withJsonLd : Extra := { jsonld := some jsonLdWriter }

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

-- The stream writer gives the batch writer's document.
#guard (match Writer.init withJsonLd .jsonld {} with
        | .error _ => false
        | .ok (w, header) =>
            (w.writeAll header (exDs.default.map fun t => (t, none))).toOption ==
              (serializeDataset withJsonLd .jsonld .rdf12 exDs).toOption)

end L4Factoidal.RDF.Sink
