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

JSON-LD is read one top-level node object at a time when `Source.Prepass`
finds the document in streaming form (`Syntax/JsonLdChunkFold.lean`,
https://github.com/danbri/factoidal/issues/839), and whole otherwise.
`jsonLdOps` is the item reader: it expands the node object with the shared
context and converts it with the counter of the blank nodes so far, the two
steps `JSONLD.parseJsonLd` takes for the whole document.
-/
import L4Factoidal.RDF.Source
import L4Factoidal.JSONLD.ToRdf

namespace L4Factoidal.RDF.Source

open L4Factoidal.Syntax

/-- JSON-LD 1.1 to a dataset. A JSON-LD failure becomes a `ParseError` that
    names the error code; the JSON-LD parser reports no position, so it is 0. -/
def jsonLdParserWith (rdfstar : Bool) : DocParser := fun _mode base text =>
  match L4Factoidal.JSONLD.parseJsonLd L4Factoidal.JSONLD.Loader.none text base none none none
          rdfstar with
  | .ok ds => .ok ds
  | .error e => .error ⟨s!"invalid or unsupported JSON-LD ({e.code})", 0⟩

/-- JSON-LD 1.1 to a dataset (`@triple`, `@reifies`, `@annotation` are ignored). -/
def jsonLdParser : DocParser := jsonLdParserWith false

open L4Factoidal.JSONLD L4Factoidal.JSON in
/-- The item reader. `begin mode base ctx` mirrors the branch of
    `parseJsonLd`: a document with an inline `@context` or a base is expanded
    first, and one with neither goes to `datasetOfJsonAt` as written. A node
    object is expanded in a document of its own, `{"@context":C,"@graph":[node]}`
    (shape B) or `[node]` (shape A), so the expansion is the one the whole
    document gives that node (the `@graph` of the object, free-floating
    values dropped). The generated prefix is `generatedPrefix` of a document
    that has no label beginning with `_jld_anon`, which `Prepass` checked. -/
def jsonLdOpsWith (rdfstar : Bool) : JsonLdChunkFold.Ops where
  notJson := ⟨"invalid or unsupported JSON-LD (notJsonLd)", 0⟩
  begin := fun _ base ctx =>
    let fail (e : JsonLdError) : ParseError := ⟨s!"invalid or unsupported JSON-LD ({e.code})", 0⟩
    let acSeed : ActiveContext :=
      { cur := { emptyContextCore with base := base, mode10 := false, rdfstar := rdfstar },
        prev := [] }
    let pfx := JsonLdChunkFold.streamPrefix
    let convert (ctr : Nat) (root : Json) : Except ParseError (Dataset × Nat) :=
      match datasetOfJsonAt .drop pfx ctr root rdfstar with
      | some r => .ok r
      | none => .error (fail .notJsonLd)
    let viaExpand (wrap : Json → Json) : Except ParseError JsonLdChunkFold.ItemFn :=
      .ok fun ctr item =>
        match expand Loader.none acSeed (wrap item) with
        | .error e => .error (fail e)
        | .ok expanded => convert ctr expanded
    match ctx with
    | some c =>
      let wrap : Json → Json := fun item =>
        .object [("@context", c), ("@graph", .array [item])]
      -- the context is processed once now, so that its error is the first
      match expand Loader.none acSeed (wrap (.array [])) with
      | .error e => .error (fail e)
      | .ok _ => viaExpand wrap
    | none =>
      if base.isSome then viaExpand (fun item => .array [item])
      else .ok fun ctr item => convert ctr (.array [item])

/-- The item reader of JSON-LD 1.1. -/
def jsonLdOps : JsonLdChunkFold.Ops := jsonLdOpsWith false

/-- The readers a native tool links: JSON-LD, whole and item by item. -/
def withJsonLd : Extra := { jsonld := some jsonLdParser, jsonldStream := some jsonLdOps }

/-- The JSON-LD readers in JSON-LD-star mode (`rdfstar`): `@triple` is an RDF 1.2
    triple term, `@reifies` is `rdf:reifies`, and `@annotation` makes a reifier of
    the triple it is on (`docs/designissues/2026-10-26-jsonld-star.md`). Opt-in, like
    `Sink.withJsonLdStar`: `withJsonLd` reads JSON-LD 1.1. -/
def withJsonLdStar : Extra :=
  { jsonld := some (jsonLdParserWith true), jsonldStream := some (jsonLdOpsWith true) }

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

-- The item reader: a document in streaming form, read in two chunks at every cut,
-- gives the quads of the whole reader, in the same order (blank nodes included).
private def streamDoc : String :=
  "{\"@context\":{\"e\":\"http://e/\"},\"@graph\":[{\"@id\":\"e:a\",\"e:p\":{\"e:q\":\"x\"}},{\"e:p\":[{\"e:q\":1},{\"@id\":\"e:b\"}]},{\"@id\":\"e:c\",\"e:r\":\"s,]\\\"}\"}]}"

#guard (let pfx := (Prepass.forFormat .jsonld |>.feed streamDoc.toUTF8).toOption.bind (·.finish.toOption)
        let want := (parseDocument withJsonLd .jsonld .rdf11 none streamDoc).toOption.map
                      (foldDataset (fun (a : List (Triple × Option Subject)) t g => (t, g) :: a) [])
        let cs := streamDoc.toList
        pfx == some "_jld_anon" && want.isSome && (List.range (cs.length + 1)).all fun cut =>
          match Reader.init withJsonLd .jsonld .rdf11 none "_jld_anon" ([] : List (Triple × Option Subject)) with
          | .error _ => false
          | .ok r =>
            (r.readAll (fun a t g => (t, g) :: a)
              [String.ofList (cs.take cut), String.ofList (cs.drop cut)]).toOption == want)

-- A document not in streaming form (an object with other members) falls back.
#guard ((Prepass.forFormat .jsonld |>.feed jlDoc.toUTF8).toOption.bind (·.finish.toOption)) == some ""

-- A document that is not JSON is refused with the JSON-LD error code.
#guard (match parseDocument withJsonLd .jsonld .rdf11 none "{" with
        | .error e => e.msg.startsWith "invalid or unsupported JSON-LD ("
        | .ok _ => false)

-- Without the reader the format is refused by name, at `init`.
#guard (match Reader.init ({} : Extra) .jsonld .rdf11 none "" (0 : Nat) with
        | .error m => m == "JSON-LD is not available in this build"
        | .ok _ => false)

end L4Factoidal.RDF.Source
