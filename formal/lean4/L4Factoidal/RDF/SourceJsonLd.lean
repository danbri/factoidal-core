/-
L4Factoidal.RDF.SourceJsonLd — the JSON-LD reader of the source layer.

`L4Factoidal/RDF/Source.lean` reads JSON-LD through a parser the caller links
in (`Source.Extra.jsonld`), so that a build without the JSON-LD library does
not carry it: the core wasm (`Wasm/CoreDispatch.lean`,
https://github.com/danbri/factoidal/issues/713 stage 4) imports `Source` and
not this module. A tool that reads JSON-LD (`l4sbm11-pack`, `l4sbm11 canon`,
`l4block-shard-pack`, the full wasm dispatch) imports this module and passes
`Source.withJsonLd`.

The parser is JSON-LD 1.1 to RDF (JSON-LD 1.1 API section 8.2, "Deserialize
JSON-LD to RDF") through `JSONLD.parseJsonLd`, with no document loader: a
remote `@context` is the error `loading remote context failed`. The F*
entry installs no loader either. JSON-LD has no RDF 1.1 or RDF 1.2 mode, so
the mode argument is ignored.

The parser also takes no processing mode, no `rdfDirection` and no
`expandContext`. 18 of the 345 positive evaluation tests of the W3C toRdf
manifest need a loader or one of these options, and fail through this reader
while `l4jsonld-probe` passes them. They are the rows of
`tests/sbm11/w3c_roundtrip_xfail.tsv`; the work is tracked in
https://github.com/danbri/factoidal/issues/848.

JSON-LD is read whole (`Source.readsWhole`):
https://github.com/danbri/factoidal/issues/839.
-/
import L4Factoidal.RDF.Source
import L4Factoidal.JSONLD.ToRdf

namespace L4Factoidal.RDF.Source

open L4Factoidal.Syntax

/-- JSON-LD 1.1 to a dataset. A JSON-LD failure becomes a `ParseError` that
    names the error code; the JSON-LD parser reports no position, so it is 0. -/
def jsonLdParser : DocParser := fun _mode base text =>
  match L4Factoidal.JSONLD.parseJsonLd L4Factoidal.JSONLD.Loader.none text base none none none with
  | .ok ds => .ok ds
  | .error e => .error ⟨s!"invalid or unsupported JSON-LD ({e.code})", 0⟩

/-- The readers a native tool links: JSON-LD. -/
def withJsonLd : Extra := { jsonld := some jsonLdParser }

/-! ## Build-time checks -/

private def jlDoc : String :=
  "{\"@id\":\"http://e/a\",\"http://e/p\":[{\"@value\":\"v\"},{\"@id\":\"http://e/b\"}]}"

-- The reader parses the document and the quads come in the dataset's order.
#guard (match parseDocument withJsonLd .jsonld .rdf11 none jlDoc with
        | .ok ds => ds.default.length == 2 && ds.named.isEmpty
        | .error _ => false)

-- The chunk reader gives the quads of the batch parse, whatever the cut.
#guard (let want := (parseDocument withJsonLd .jsonld .rdf11 none jlDoc).toOption.map
                      (foldDataset (fun (a : List (Triple × Option Subject)) t g => (t, g) :: a) [])
        let cs := jlDoc.toList
        want.isSome && (List.range (cs.length + 1)).all fun cut =>
          match Reader.init withJsonLd .jsonld .rdf11 none "" ([] : List (Triple × Option Subject)) with
          | .error _ => false
          | .ok r =>
            (r.readAll (fun a t g => (t, g) :: a)
              [String.ofList (cs.take cut), String.ofList (cs.drop cut)]).toOption == want)

-- A document that is not JSON is refused with the JSON-LD error code.
#guard (match parseDocument withJsonLd .jsonld .rdf11 none "{" with
        | .error e => e.msg.startsWith "invalid or unsupported JSON-LD ("
        | .ok _ => false)

-- Without the reader the format is refused by name, at `init`.
#guard (match Reader.init ({} : Extra) .jsonld .rdf11 none "" (0 : Nat) with
        | .error m => m == "JSON-LD is not available in this build"
        | .ok _ => false)

end L4Factoidal.RDF.Source
