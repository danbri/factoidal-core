/-
Wasm.Ops.Parse — parseToDatasetJson / serializeNQuads / serializeTurtle.

Envelopes match `bin/npm-entry/entry_jsoo.ml`:

  parseToDatasetJson(text, formatTag, baseIRI)
    -> {"ok":true,"count":N,"nquads":"…"} | {"ok":false,"error":"…"}
  serializeNQuads(nquads)
    -> {"ok":true,"nquads":"…"}
  serializeTurtle(nquads)
    -> {"ok":true,"turtle":"…"}

The dataset handle IS the returned N-Quads string, exactly as in the F*
entry.

Envelope parity with the F* entry (https://github.com/danbri/factoidal/issues/685),
added after the lines above were written:

  * `parseToDatasetJson` also answers `"prefixes":{label:iri}` (Turtle and TriG;
    `{}` for the other formats), each label once, in declaration order, with its
    latest binding.
  * A parse failure of Turtle, TriG, N-Triples or N-Quads answers
    `{"ok":false,"error":"<msg> at line L, column C","offset":N,"line":L,
    "column":C,"format":"<tag>"}`. The line and the column are 1-based, the
    column counted in Unicode scalar values; `offset` is a count of Unicode
    scalar values from the start of the text (the F* entry counts UTF-8 bytes,
    which the two agree with on ASCII text). RDF/XML and a missing format carry
    the message and `format` only.
  * `serializeTurtleWith(nquads, optionsJson)`, with `{"prefixes":{label:iri},
    "literalShorthand":bool}`.
  * Per-document blank-node scope: the IO entry (`parseToDatasetJsonScoped`,
    which `callIO` serves under the name `parseToDatasetJson`) prefixes every
    blank-node label of a document with `d<N>_`, `N` counting parses in the
    process, as `RDF.Dataset.Merge.rename_dataset_bnodes` does in the F* entry.
    Two documents that both write `_:b0` stay two nodes when their N-Quads are
    concatenated. The pure entry keeps the labels as written, because it has no
    counter. Format tags follow `RDF.Format.fst`'s `format_of_string` table
for the formats the Lean engine parses; a `*12` tag routes to the RDF
1.2 (`Mode.rdf12`) entry points, mirroring `entry_jsoo.ml`'s
consumer-side dispatch. `jsonld` is a named gap, not a silent one.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note: the umbrella initializer dies under
wasm32).
-/
import Wasm.Ops.Support
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.NTriples
import L4Factoidal.Syntax.NQuads
import L4Factoidal.Syntax.TriG
import L4Factoidal.Syntax.RdfXml
import L4Factoidal.Syntax.TurtleSerialize
import L4Factoidal.Syntax.NQuadsFast
import L4Factoidal.RDF.DatasetMerge

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-- Total quad count of a dataset (the F* `dataset_triple_count`).
Not private: `Wasm/Ops/Handles.lean`'s count envelopes use it too. -/
def datasetQuadCount (ds : Dataset) : Nat :=
  ds.default.length + (ds.named.map (·.graph.length)).foldl (· + ·) 0

/-- Consumer-side RDF 1.2 opt-in, exactly as entry_jsoo.ml: a "*12" tag
selects Mode.rdf12; every other tag keeps the 1.1 path. Returns the mode and
the lower-cased base tag. -/
def resolveModeAndTag (formatTag : String) : Mode × String :=
  let lo := formatTag.toLower
  match lo with
  | "ttl12" | "turtle12"   => (Mode.rdf12, "ttl")
  | "nt12"  | "ntriples12" => (Mode.rdf12, "nt")
  | "nq12"  | "nquads12"   => (Mode.rdf12, "nq")
  | "trig12"               => (Mode.rdf12, "trig")
  | _                      => (Mode.rdf11, lo)

/-- Parse `text` under `formatTag` into a `Dataset`. Graph-shaped
formats (Turtle, N-Triples, RDF/XML) wrap as the default graph.
Not private: `Wasm/Ops/Handles.lean`'s `datasetOpen` is the same parse. -/
def parseTextToDataset (text formatTag baseIRI : String) :
    Except String Dataset :=
  let base : Option String := if baseIRI == "" then none else some baseIRI
  let (mode, tag) := resolveModeAndTag formatTag
  let wrapGraph (r : Except ParseError Graph) : Except String Dataset :=
    match r with
    | .error e => .error (fmtParseError e)
    | .ok g    => .ok { default := g, named := [] }
  match tag with
  | "" | "turtle" | "ttl" => wrapGraph (parseTurtle text base mode)
  | "ntriples" | "nt" | "n-triples" => wrapGraph (parseNTriples text mode)
  | "nquads" | "nq" | "n-quads" =>
      (parseNQuadsFast text mode).mapError fmtParseError
  | "trig" => (parseTriG text base mode).mapError fmtParseError
  | "rdfxml" | "rdf/xml" | "rdf" | "xml" =>
      wrapGraph (RdfXml.parseRdfXml text base)
  | "jsonld" | "json-ld" | "application/ld+json" =>
      .error "JSON-LD is not in the Lean engine's v1 surface"
  | _ => .error s!"unknown format tag '{formatTag}'"

/-- `parseToDatasetJson(text, formatTag, baseIRI)`. -/
def parseToDatasetJson (text formatTag baseIRI : String) : String :=
  match parseTextToDataset text formatTag baseIRI with
  | .error msg => errJson msg
  | .ok ds =>
      okWith [("count", .number (toString (datasetQuadCount ds))),
              ("nquads", .string (Dataset.toCanonicalNQuads ds))]

/-- `serializeNQuads(nquads)` — reparse and re-serialise in canonical
N-Quads form. -/
def serializeNQuads (nq : String) : String :=
  match parseNQuadsFast nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds   => okWith [("nquads", .string (Dataset.toCanonicalNQuads ds))]

/-- `serializeTurtle(nquads)` — prefix-compacted pretty-print. Named
graphs are flattened into the default graph for this path (the
fidelity-preserving path is serializeNQuads / canonicalizeToNQuads),
mirroring `entry_jsoo.ml`'s `serialize_turtle`. -/
def serializeTurtle (nq : String) : String :=
  match parseNQuadsFast nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
      let g := ds.default ++ ds.named.flatMap (·.graph)
      okWith [("turtle", .string (turtleOfGraphAuto g))]

/-! ## Positions, prefixes and blank-node scope (issue 685) -/

/-- A parse failure in the shape the envelope reports. `position` is
(offset, line, column) when the failing grammar reports one. -/
structure ParseFailure where
  message  : String
  position : Option (Nat × Nat × Nat) := none

/-- A parsed document and the prefixes it declared: each label once, in
declaration order, with its latest binding. -/
structure ParseOutcome where
  ds       : Dataset
  prefixes : List (String × String)

/-- 1-based line and 1-based column, counted in Unicode scalar values, of the
character at codepoint `offset` in `text`. An offset past the end gives the
position just after the last character. Port of `position_of_offset`. -/
def lineColumnOfOffset (text : String) (offset : Nat) : Nat × Nat :=
  go (text.toList.take offset) 1 1
where
  go : List Char → Nat → Nat → Nat × Nat
    | [], line, col => (line, col)
    | ch :: rest, line, col =>
        if ch == '\n' then go rest (line + 1) 1 else go rest line (col + 1)

def failureAt (text : String) (e : ParseError) : ParseFailure :=
  let (line, col) := lineColumnOfOffset text e.pos
  { message := e.msg, position := some (e.pos, line, col) }

/-- Keep each label once with its LATEST binding, in the order those latest
bindings were declared. The parsers hold prefixes most recent first and a
re-binding does not remove the older one. Port of
`declaration_order_prefixes`. -/
def declarationOrderPrefixes (mostRecentFirst : List (String × String)) :
    List (String × String) :=
  go [] [] mostRecentFirst
where
  go (seen : List String) (acc : List (String × String)) :
      List (String × String) → List (String × String)
    | [] => acc
    | (label, iri) :: rest =>
        if seen.contains label then go seen acc rest
        else go (label :: seen) ((label, iri) :: acc) rest

/-- `parseTextToDataset`, with the position of a failure and the prefixes of
the document. The two share one dispatch table of formats; only the failure
and the extra result differ. RDF/XML failures carry no position, as in the F*
entry; so does JSON-LD, which the Lean engine does not parse here. -/
def parseDocumentOutcome (text formatTag baseIRI : String) :
    Except ParseFailure ParseOutcome :=
  let base : Option String := if baseIRI == "" then none else some baseIRI
  let (mode, tag) := resolveModeAndTag formatTag
  let noPosition (m : String) : ParseFailure := { message := m }
  match tag with
  | "" | "turtle" | "ttl" =>
      match parseTurtleWithPrefixes text base mode with
      | .error e => .error (failureAt text e)
      | .ok (g, ps) =>
          .ok { ds := { default := g, named := [] }, prefixes := declarationOrderPrefixes ps }
  | "ntriples" | "nt" | "n-triples" =>
      match parseNTriples text mode with
      | .error e => .error (failureAt text e)
      | .ok g => .ok { ds := { default := g, named := [] }, prefixes := [] }
  | "nquads" | "nq" | "n-quads" =>
      match parseNQuadsFast text mode with
      | .error e => .error (failureAt text e)
      | .ok ds => .ok { ds := ds, prefixes := [] }
  | "trig" =>
      match parseTriGWithPrefixes text base mode with
      | .error e => .error (failureAt text e)
      | .ok (ds, ps) => .ok { ds := ds, prefixes := declarationOrderPrefixes ps }
  | "rdfxml" | "rdf/xml" | "rdf" | "xml" =>
      match RdfXml.parseRdfXml text base with
      | .error e => .error (noPosition e.msg)
      | .ok g => .ok { ds := { default := g, named := [] }, prefixes := [] }
  | "jsonld" | "json-ld" | "application/ld+json" =>
      .error (noPosition "JSON-LD is not in the Lean engine's v1 surface")
  | _ => .error (noPosition s!"unknown format tag '{formatTag}'")

/-- The display tag of an error envelope: the caller's own spelling,
lower-cased, or `turtle` for the empty default. -/
def displayFormatTag (formatTag : String) : String :=
  if formatTag == "" then "turtle" else formatTag.toLower

/-- `{"ok":false,"error":"<msg>[ at line L, column C]","offset"?,"line"?,
"column"?,"format":"<tag>"}`. Shared by `parseToDatasetJson` and `datasetOpen`. -/
def parseFailureEnvelope (formatTag : String) (f : ParseFailure) : String :=
  let fmt := ("format", Json.string (displayFormatTag formatTag))
  match f.position with
  | none =>
      (Json.object [("ok", .bool false), ("error", .string f.message), fmt]).toString
  | some (offset, line, col) =>
      (Json.object
        [ ("ok", .bool false)
        , ("error", .string s!"{f.message} at line {line}, column {col}")
        , ("offset", .number (toString offset))
        , ("line", .number (toString line))
        , ("column", .number (toString col))
        , fmt ]).toString

/-- `{label: iri, …}` in the order given. -/
def prefixesJson (ps : List (String × String)) : Json :=
  .object (ps.map fun (label, iri) => (label, Json.string iri))

/-- Give the dataset a document scope: every blank-node label gets `scope`
in front of it. -/
def scopeBnodes (scope : String) (ds : Dataset) : Dataset :=
  L4Factoidal.RDF.renameDatasetBnodes scope ds

/-- `parseToDatasetJson`, the parity envelope. `scope` is the blank-node label
prefix, or `none` to keep the labels as written. -/
def parseToDatasetJsonWith (scope : Option String) (text formatTag baseIRI : String) :
    String :=
  match parseDocumentOutcome text formatTag baseIRI with
  | .error f => parseFailureEnvelope formatTag f
  | .ok o =>
      let ds := match scope with
        | some pre => scopeBnodes pre o.ds
        | none => o.ds
      okWith [("count", .number (toString (datasetQuadCount ds))),
              ("nquads", .string (Dataset.toCanonicalNQuads ds)),
              ("prefixes", prefixesJson o.prefixes)]

/-- Parses so far in this process. The scope of the next one is `d<N>_`. -/
initialize documentScopeCounter : IO.Ref Nat ← IO.mkRef 0

/-- The next document scope prefix, `d0_`, `d1_`, … Never reused. -/
def nextDocumentScope : IO String := do
  let n ← documentScopeCounter.modifyGet fun n => (n, n + 1)
  pure s!"d{n}_"

/-- `parseToDatasetJson` with a fresh blank-node scope per call. `callIO`
serves this entry under the op name `parseToDatasetJson`. -/
def parseToDatasetJsonScoped (text formatTag baseIRI : String) : IO String := do
  let scope ← nextDocumentScope
  pure (parseToDatasetJsonWith (some scope) text formatTag baseIRI)

/-! ## `serializeTurtleWith` -/

/-- Options of `serializeTurtleWith` and `datasetSerializeWith`: `""` or
`{"prefixes":{label:iri},"literalShorthand":bool}`. `prefixes` maps each label
(the key, without a colon) to its namespace; the renderer wants
(namespace, `label:`) pairs, so this transposes and appends the colon. A
`prefixes` member that is absent keeps `defaultPrefixes`; one entry whose value
is not a string is skipped. `literalShorthand` absent, or not a boolean, is
`true`. -/
def turtleOptionsOfJson (defaultPrefixes : PrefixTable) (optionsJson : String) :
    Except String TurtleRenderOptions :=
  if optionsJson == "" then .ok { prefixes := defaultPrefixes }
  else
    match parseJson optionsJson with
    | .error _ => .error "invalid optionsJson (not valid JSON)"
    | .ok root =>
        let prefixes := match root.field? "prefixes" with
          | some (.object fields) =>
              fields.filterMap fun (label, v) => match v with
                | .string iri => some (iri, label ++ ":")
                | _ => none
          | _ => defaultPrefixes
        let shorthand := match root.field? "literalShorthand" with
          | some (.bool b) => b
          | _ => true
        .ok { prefixes := prefixes, literalShorthand := shorthand }

/-- The graph the pretty-print path renders: named graphs are flattened into
the default graph (the fidelity-preserving path is `serializeNQuads`). -/
def flattenedGraph (ds : Dataset) : Graph :=
  ds.default ++ ds.named.flatMap (·.graph)

/-- `serializeTurtleWith(nquads, optionsJson)`. -/
def serializeTurtleWith (nq optionsJson : String) : String :=
  match parseNQuadsFast nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
      match turtleOptionsOfJson [] optionsJson with
      | .error msg => errJson msg
      | .ok opts => okWith [("turtle", .string (turtleOfGraphOpts opts (flattenedGraph ds)))]

/-- The op names this module adds to the pure dispatch. -/
def parityOpNames : List String := [ "serializeTurtleWith" ]

/-- Serve one of `parityOpNames`, or `none`. -/
def callParity (op : String) (args : List String) : Option String :=
  match op, args with
  | "serializeTurtleWith", [a, b] => some (serializeTurtleWith a b)
  | "serializeTurtleWith", _ =>
      some (errJson s!"serializeTurtleWith expects 2 arguments, got {args.length}")
  | _, _ => none

/-! ## Build-time checks -/

-- Lines are 1-based, columns are 1-based and count Unicode scalar values.
#guard lineColumnOfOffset "" 0 == (1, 1)
#guard lineColumnOfOffset "abc" 0 == (1, 1)
#guard lineColumnOfOffset "abc" 2 == (1, 3)
#guard lineColumnOfOffset "ab\ncd" 3 == (2, 1)
#guard lineColumnOfOffset "ab\ncd" 4 == (2, 2)
-- A multi-byte character is one column.
#guard lineColumnOfOffset "\u00e9\u00e9x" 2 == (1, 3)
#guard lineColumnOfOffset "\u00e9\n\u00e9x" 3 == (2, 2)
-- An offset past the end is the position after the last character.
#guard lineColumnOfOffset "ab\ncd" 99 == (2, 3)

-- Each label once, its latest binding, in the order those bindings were made.
#guard declarationOrderPrefixes [] == []
#guard declarationOrderPrefixes [("a", "3"), ("b", "2"), ("a", "1")] == [("b", "2"), ("a", "3")]
#guard declarationOrderPrefixes [("b", "2"), ("a", "1")] == [("a", "1"), ("b", "2")]

-- The caller's `prefixes` replace the defaults; an absent one keeps them.
#guard (match turtleOptionsOfJson [("http://d/", "d:")] "" with
        | .ok o => o.prefixes == [("http://d/", "d:")] && o.literalShorthand
        | .error _ => false)
#guard (match turtleOptionsOfJson [("http://d/", "d:")] "{}" with
        | .ok o => o.prefixes == [("http://d/", "d:")] && o.literalShorthand
        | .error _ => false)
#guard (match turtleOptionsOfJson [("http://d/", "d:")]
          "{\"prefixes\":{\"x\":\"http://x/\",\"n\":3},\"literalShorthand\":false}" with
        | .ok o => o.prefixes == [("http://x/", "x:")] && !o.literalShorthand
        | .error _ => false)
#guard (match turtleOptionsOfJson [] "{\"literalShorthand\":\"no\"}" with
        | .ok o => o.literalShorthand
        | .error _ => false)
#guard (match turtleOptionsOfJson [] "{" with
        | .error m => m == "invalid optionsJson (not valid JSON)"
        | .ok _ => false)

end L4Wasm.Ops
