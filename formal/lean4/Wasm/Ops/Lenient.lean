/-
Wasm.Ops.Lenient — `parseDocument(text, formatTag, baseIRI, optionsJson)`,
the lenient (recovery) parse op (https://github.com/danbri/factoidal/issues/716).

The F* npm entry serves the same name (`bin/npm-entry/entry_core.ml`,
`parse_document_json`); `npm/factoidal/lib/api.js` calls it for
`parse(text, {lenient: true})`.

  optionsJson: "" or a JSON object
    {"lenient": bool, "maxErrors": non-negative integer}
  Not lenient (absent, false, "", or text that is not a JSON object):
    exactly the `parseToDatasetJson` envelope, as the F* entry answers.
  Lenient:
    {"ok":true,"count":N,"nquads":"…","prefixes":{…},
     "diagnostics":[{"message":"…","offset":O,"line":L,"column":C,
                     "class":"<DiagnosticClass.tag>"}, …]}
    one diagnostic per skipped statement, in source order. `offset`,
    `line` and `column` follow `Syntax/Diagnostics.lean`: 0-based offset and
    1-based column in Unicode scalar values, 1-based line counted at LINE
    FEED, the convention of the strict error envelope. `maxErrors` stops the
    parse with one final `too-many-errors` diagnostic.

Turtle, TriG, N-Triples and N-Quads recover (`Syntax/TurtleLenient.lean`,
`Syntax/NQuadsLenient.lean`); the F* entry recovers in the same four. An
RDF/XML or JSON-LD document is parsed strictly: success has
`"diagnostics":[]`, failure is the strict error envelope, as in the F* entry.

The F* entry reports at most one diagnostic (its `Parser.Diagnostics` keeps
the first error only) and an empty dataset for N-Triples and N-Quads; this op
reports every skipped statement and keeps every statement that parses.

`callIO` serves the op with a fresh blank-node scope per document, as it
serves `parseToDatasetJson`; the pure `call` keeps labels as written.

Targeted imports only (`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import Wasm.Ops.Parse
import L4Factoidal.Syntax.Diagnostics
import L4Factoidal.Syntax.NQuadsLenient
import L4Factoidal.Syntax.TurtleLenient

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-- The options of `parseDocument`. -/
structure ParseDocumentOptions where
  lenient : Bool := false
  maxErrors : Option Nat := none
  deriving DecidableEq, Repr

/-- Read `optionsJson`. Text that is not a JSON object is "not lenient", as
the F* entry's `parse_lenient_of_json` reads it. -/
def parseDocumentOptionsOfJson (optionsJson : String) : ParseDocumentOptions :=
  if optionsJson == "" then {}
  else
    match parseJson optionsJson with
    | .ok (.object fields) =>
        let root := Json.object fields
        { lenient := root.getBool? "lenient" == some true,
          maxErrors := match root.field? "maxErrors" with
            | some (.number n) => n.toNat?
            | _ => none }
    | _ => {}

/-- The text the lenient N-Triples and N-Quads readers read: under `.rdf12`, the
version directive lines (RDF 1.2 N-Triples section 5.3 [3] `directive ::=
versionDirective`) blanked by `blankVersionDirectives`, so that a directive is
read as a statement and not reported as an error
(https://github.com/danbri/factoidal/issues/1055). Offsets do not move. -/
def lineText (mode : L4Factoidal.Syntax.Mode) (text : String) : String :=
  match mode with
  | .rdf11 => text
  | .rdf12 => String.ofList (L4Factoidal.Syntax.blankVersionDirectives text.toList)

/-- The lenient parse of `text` under `formatTag`: the outcome and the
diagnostics. The dataset is a set of quads: the Turtle and N-Triples readers
list a repeated triple two times, so their graph goes through `Dataset.toSet`
(the N-Quads and TriG readers add with `addQuad`). RDF/XML, the syntaxes `extra` reads (JSON-LD in the full
dispatch) and unknown tags are the strict `parseDocumentOutcomeBy`. -/
def lenientDocumentOutcomeBy (extra : ExtraReader) (text formatTag baseIRI : String)
    (opts : LenientOptions) :
    Except ParseFailure (ParseOutcome × List Diagnostic) :=
  let base : Option String := if baseIRI == "" then none else some baseIRI
  let (mode, tag) := resolveModeAndTag formatTag
  match tag with
  | "" | "turtle" | "ttl" =>
      let (g, ds, ps) := parseTurtleLenientWithPrefixes text base mode opts
      .ok ({ ds := Dataset.toSet { default := g, named := [] },
             prefixes := declarationOrderPrefixes ps }, ds)
  | "ntriples" | "nt" | "n-triples" =>
      let (g, ds) := parseNTriplesLenient (lineText mode text) mode opts
      .ok ({ ds := Dataset.toSet { default := g, named := [] }, prefixes := [] }, ds)
  | "nquads" | "nq" | "n-quads" =>
      let (d, ds) := parseNQuadsFastLenient (lineText mode text) mode opts
      .ok ({ ds := d, prefixes := [] }, ds)
  | "trig" =>
      let (d, ds, ps) := parseTriGLenientWithPrefixes text base mode opts
      .ok ({ ds := d, prefixes := declarationOrderPrefixes ps }, ds)
  | _ => (parseDocumentOutcomeBy extra text formatTag baseIRI).map fun o => (o, [])

/-- `parseDocument`, with `scope` the blank-node label prefix (`none`: keep
labels as written). -/
def parseDocumentWithBy (extra : ExtraReader) (scope : Option String)
    (text formatTag baseIRI optionsJson : String) : String :=
  let o := parseDocumentOptionsOfJson optionsJson
  if !o.lenient then parseToDatasetJsonWithBy extra scope text formatTag baseIRI
  else
    match lenientDocumentOutcomeBy extra text formatTag baseIRI { maxErrors := o.maxErrors } with
    | .error f => parseFailureEnvelope formatTag f
    | .ok (out, diags) =>
        let ds := match scope with
          | some pre => scopeBnodes pre out.ds
          | none => out.ds
        okWith ([("count", .number (toString (datasetQuadCount ds))),
                ("nquads", .string (Dataset.toCanonicalNQuads ds)),
                ("prefixes", prefixesJson out.prefixes),
                ("diagnostics", .array (diags.map diagnosticJson))] ++
                warningsMembers (readerWarnings text formatTag out.ds))

/-- `parseDocument` through the pure `call`: labels as written. -/
def parseDocumentBy (extra : ExtraReader) (text formatTag baseIRI optionsJson : String) :
    String :=
  parseDocumentWithBy extra none text formatTag baseIRI optionsJson

/-- `parseDocument` through `callIO`: a fresh blank-node scope per document. -/
def parseDocumentScopedBy (extra : ExtraReader)
    (text formatTag baseIRI optionsJson : String) : IO String := do
  let scope ← nextDocumentScope
  pure (parseDocumentWithBy extra (some scope) text formatTag baseIRI optionsJson)

/-- The op names this module adds to the dispatch. -/
def lenientOpNames : List String := [ "parseDocument" ]

/-- Serve one of `lenientOpNames` through the pure `call`, or `none`. -/
def callLenientBy (extra : ExtraReader) (op : String) (args : List String) :
    Option String :=
  match op, args with
  | "parseDocument", [a, b, c, d] => some (parseDocumentBy extra a b c d)
  | "parseDocument", _ =>
      some (errJson s!"parseDocument expects 4 arguments, got {args.length}")
  | _, _ => none

/-- Serve one of `lenientOpNames` through `callIO`, or `none`. -/
def callLenientIOBy (extra : ExtraReader) (op : String) (args : List String) :
    Option (IO String) :=
  match op, args with
  | "parseDocument", [a, b, c, d] => some (parseDocumentScopedBy extra a b c d)
  | "parseDocument", _ =>
      some (pure (errJson s!"parseDocument expects 4 arguments, got {args.length}"))
  | _, _ => none

/-! ## Build-time checks -/

private def numberLexeme? (j : Json) (key : String) : Option String :=
  match j.field? key with
  | some (.number s) => some s
  | _ => none

private def emptyArray? (j : Json) (key : String) : Bool :=
  match j.field? key with
  | some (.array []) => true
  | _ => false

#guard parseDocumentOptionsOfJson "" == {}
#guard parseDocumentOptionsOfJson "{\"lenient\":true}" == { lenient := true }
#guard parseDocumentOptionsOfJson "{\"lenient\":true,\"maxErrors\":3}"
        == { lenient := true, maxErrors := some 3 }
#guard parseDocumentOptionsOfJson "{\"lenient\":\"yes\"}" == {}
#guard parseDocumentOptionsOfJson "[true]" == {}
#guard parseDocumentOptionsOfJson "{" == {}

private def ttlDoc : String :=
  "<http://x/a> <http://x/p> \"1\" .\n<http://x/b> <http://x/p> .\n<http://x/c> <http://x/p> \"3\" .\n"

-- The l4-core xfail document of issue 716: two triples kept, one diagnostic on line 2.
#guard (match parseJson (parseDocumentBy noExtraReader ttlDoc "turtle" "" "{\"lenient\":true}") with
        | .ok j =>
            numberLexeme? j "count" == some "2" &&
            (match j.field? "diagnostics" with
             | some (.array [d]) => numberLexeme? d "line" == some "2" &&
                                    d.getString? "class" == some "unexpected-token"
             | _ => false)
        | .error _ => false)
-- Not lenient: the strict error envelope.
#guard (match parseJson (parseDocumentBy noExtraReader ttlDoc "turtle" "" "") with
        | .ok j => j.getBool? "ok" == some false && numberLexeme? j "line" == some "2"
        | .error _ => false)
-- A good document: diagnostics [] and the strict count, in every format.
#guard (match parseJson (parseDocumentBy noExtraReader "<http://x/a> <http://x/p> <http://x/g> <http://x/g> .\n"
          "nquads" "" "{\"lenient\":true}") with
        | .ok j => numberLexeme? j "count" == some "1" &&
                   emptyArray? j "diagnostics"
        | .error _ => false)
-- https://github.com/danbri/factoidal/issues/1055: an RDF 1.2 version directive
-- is a statement for the lenient N-Triples and N-Quads readers too, and a bad
-- line after it keeps its line number.
#guard (match parseJson (parseDocumentBy noExtraReader
          "VERSION \"1.2\"\n<http://x/a> <http://x/p> <http://x/o> .\n<http://x/b> <http://x/p> .\n"
          "ntriples12" "" "{\"lenient\":true}") with
        | .ok j => numberLexeme? j "count" == some "1" &&
                   (match j.field? "diagnostics" with
                    | some (.array [d]) => numberLexeme? d "line" == some "3"
                    | _ => false)
        | .error _ => false)
#guard (match parseJson (parseDocumentBy noExtraReader
          "VERSION \"1.2\"\n<http://x/a> <http://x/p> <http://x/o> <http://x/g> .\n"
          "nquads12" "" "{\"lenient\":true}") with
        | .ok j => numberLexeme? j "count" == some "1" && emptyArray? j "diagnostics"
        | .error _ => false)
-- RDF/XML is strict even when lenient is asked for: success has no diagnostics.
#guard (match parseJson (parseDocumentBy noExtraReader
          "<rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"/>" "rdfxml" "" "{\"lenient\":true}") with
        | .ok j => j.getBool? "ok" == some true && emptyArray? j "diagnostics"
        | .error _ => false)
-- maxErrors.
#guard (match parseJson (parseDocumentBy noExtraReader (ttlDoc ++ ttlDoc) "turtle" "" "{\"lenient\":true,\"maxErrors\":1}") with
        | .ok j => (match j.field? "diagnostics" with
                    | some (.array [_, d]) => d.getString? "class" == some "too-many-errors"
                    | _ => false)
        | .error _ => false)

end L4Wasm.Ops
