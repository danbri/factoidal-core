/-
Wasm.Ops.Handles — dataset handles: parse once, reference by id.

https://github.com/danbri/factoidal/issues/585 (ABI half). The
stateless ops ship the whole dataset as N-Quads text on every call and
re-parse it; these ops hold the parsed `Dataset` in a module-level
store so later calls carry only a handle string and the query:

  datasetOpen(text, formatTag, baseIri)
    -> {"ok":true,"handle":"h1","count":N,"prefixes":{label:iri}}
     | the positioned parse-error envelope of Wasm/Ops/Parse.lean
  datasetQuery(handle, sparql)
    -> the queryDataset envelope family verbatim (Wasm/Ops/Query.lean)
  datasetQuery12(handle, sparql)
    -> the same, with the query read by the SPARQL 1.2 grammar
  datasetUpdate(handle, sparqlUpdate)
    -> {"ok":true,"count":N}   — the stored dataset is REPLACED
  datasetSerialize(handle, formatTag)   — nquads | turtle
    -> {"ok":true,"nquads":"…"} | {"ok":true,"turtle":"…"}
  datasetSerializeWith(handle, formatTag, optionsJson)
    -> the same envelopes; `optionsJson` is `{"prefixes":{label:iri},
       "literalShorthand":bool}` as for `serializeTurtleWith`
       (https://github.com/danbri/factoidal/issues/685)
  datasetClose(handle)
    -> {"ok":true}

The ops below keep the data in the store between steps
(https://github.com/danbri/factoidal/issues/882 item 1): an op that makes a
dataset answers a NEW handle, and an op that reads one takes a handle, so a
host never moves N-Quads text between two steps.

  datasetSerialize(handle, formatTag)   — also ntriples | trig | rdfxml
    -> {"ok":true,"text":"…"} (and the `nquads`/`turtle` member as before)
  datasetClone(handle)
    -> the `datasetOpen` envelope of a new handle with the same dataset
  datasetCanonicalize(handle)
    -> the `canonicalizeToNQuads` envelope of the stored dataset
  datasetClosure(handle, regime)        — rdfs | owl-rl | rho-df | rdfs-plus
    -> the `datasetOpen` envelope of a new handle: the closure of the default
       graph (`closureStreamOf`, the graph the closure ops write)
  datasetShaclValidate(dataHandle, shapesHandle)
    -> the `shaclValidate` envelope

Any op naming a handle that is not in the store (never opened, or
closed) answers {"ok":false,"error":"unknown dataset handle: …"}.

The ops are thin wrappers: parsing is `parseDocumentOutcomeBy`
(Wasm/Ops/Parse.lean), query/update are `queryParsedDataset` /
`applyUpdateText` (Wasm/Ops/Query.lean), serialisation is the same
`Dataset.toCanonicalNQuads` / `turtleOfGraphAuto` the stateless ops
call. Only the store and the envelope assembly live here.

This module is the ONE place in the wasm entry layer holding mutable
state, and the state lives HERE — in `Wasm/*`, not in `L4Factoidal/*`
spec code (which stays pure; the wasm entry layer is IO-permitted).
The store is process-global, so handles are only meaningful within one
module instance (wasm) or one process (native CLI); `Wasm/Main.lean`'s
`callseq` subcommand exists so the native smoke test can exercise a
handle across several ops in one process. These ops are reachable only
through `L4Wasm.callIO` (Wasm/Dispatch.lean) — the pure `L4Wasm.call`
cannot reach the store and answers "unknown op" for them.
-/
import Std.Data.HashMap
import Wasm.Ops.Parse
import Wasm.Ops.Query
import Wasm.Ops.Clock
import Wasm.Ops.QueryExtras
import L4Factoidal.SPARQL.Update
import Wasm.Ops.Reason
import Wasm.Ops.Validate
import Wasm.Ops.Canon
import Wasm.Ops.FromDataset
import L4Factoidal.RDF.Sink
import L4Factoidal.RDF.Format
import L4Factoidal.RDF.TermJson
import L4Factoidal.RDF.Isomorphism
import L4Factoidal.Syntax.IriResolve

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.JSON

/-- Handle ids already issued; `datasetOpen` numbers handles "h1",
"h2", … in open order. Closing a handle never reuses its id. -/
initialize handleCounter : IO.Ref Nat ← IO.mkRef 0

/-- An open dataset and its indexed backend.  The backend (equivalence-aware
indexes over the default and every named graph) is built once when the
handle is opened or updated, so every `datasetQuery` on the handle runs
the optimized physical-plan path without rebuilding indexes. -/
structure OpenDataset where
  ds : Dataset
  /-- Built on the first query after an open or a change, then kept: an
  `add` of one quad does not rebuild every index. -/
  backendThunk : Thunk DatasetBackend
  /-- The prefixes the document declared, each label once, in declaration order.
  Turtle output of the handle uses them. -/
  prefixes : List (String × String) := []

private def openDataset (ds : Dataset) (prefixes : List (String × String) := []) :
    OpenDataset :=
  { ds, backendThunk := Thunk.mk (fun _ => indexedDatasetBackend ds), prefixes }

/-- The indexed backend of an open dataset. -/
private def OpenDataset.backend (od : OpenDataset) : DatasetBackend := od.backendThunk.get

/-- The open datasets, keyed by handle string. -/
initialize handleTable : IO.Ref (Std.HashMap String OpenDataset) ← IO.mkRef ∅

/-- The shared error envelope for a handle that is not in the store. -/
def unknownHandle (h : String) : String :=
  errJson s!"unknown dataset handle: {h}"

/-- Look `h` up and run `f` on the stored dataset; unknown handles get
the shared error envelope. -/
private def withHandle (h : String) (f : OpenDataset → IO String) : IO String := do
  match (← handleTable.get)[h]? with
  | none    => pure (unknownHandle h)
  | some od => f od

/-- `datasetOpen(text, formatTag, baseIri)` — parse once, index once,
store, and answer the new handle plus the quad count. A parse failure
stores nothing and issues no handle. `extra` reads the syntaxes outside
`Wasm/Ops/Parse.lean`'s table: the full dispatch passes `jsonLdReader`, the
core dispatch a reader without JSON-LD (issue 713 stage 4). -/
def datasetOpenBy (extra : ExtraReader) (text formatTag baseIri : String) : IO String := do
  match parseDocumentOutcomeBy extra text formatTag baseIri with
  | .error f => pure (parseFailureEnvelope formatTag f)
  | .ok o =>
      -- The document gets its own blank-node scope, as `parseToDatasetJsonScoped`.
      let ds := scopeBnodes (← nextDocumentScope) o.ds
      let n ← handleCounter.modifyGet fun n => (n + 1, n + 1)
      let h := s!"h{n}"
      handleTable.modify (·.insert h (openDataset ds o.prefixes))
      pure (okWith [("handle", .string h),
                    ("count", .number (toString (datasetQuadCount ds))),
                    ("prefixes", prefixesJson o.prefixes)])

/-- `datasetQuery(handle, sparql)` — the `queryDataset` envelope family
over the stored dataset and its cached indexed backend, without the
per-call N-Quads round trip. The clock is read once per call: `NOW()` is the
instant of this query (§17.4.5.1,
https://github.com/danbri/factoidal/issues/743). -/
def datasetQuery (h sparql : String) (base : Option String := none) : IO String := do
  let extIris ← extSnapshot
  let services ← serviceSnapshot
  let now ← nowDateTime
  withHandle h fun od =>
    pure (queryParsedDatasetWith od.ds (some od.backend) sparql [] extIris services .v11 base
            (some now))

/-- `datasetQuery12(handle, sparql)` — `datasetQuery` with the query read by
the SPARQL 1.2 grammar (`queryDataset12IO` in `Wasm/Ops/Query.lean`). The
envelope family is the same; a SPARQL 1.2 term in a 1.1 query is a parse
error of `datasetQuery`, and it is accepted here. The clock is read once per
call, as for `datasetQuery`. -/
def datasetQuery12 (h sparql : String) (base : Option String := none) : IO String := do
  let extIris ← extSnapshot
  let services ← serviceSnapshot
  let now ← nowDateTime
  withHandle h fun od =>
    pure (queryParsedDatasetWith od.ds (some od.backend) sparql [] extIris services .v12 base
            (some now))

/-- `datasetUpdate(handle, sparqlUpdate)` — apply the update and
REPLACE the stored dataset (and rebuild its index); answers the new quad
count. On a parse or evaluation error the stored dataset is unchanged. The
clock is read once per call: `NOW()` in a WHERE clause is the instant of this
request (§17.4.5.1, https://github.com/danbri/factoidal/issues/743). -/
def datasetUpdate (h updateText : String) (base : Option String := none) : IO String := do
  let now ← nowDateTime
  withHandle h fun od =>
    match applyUpdateText od.ds updateText base (some now) with
    | .error e => pure (errJson e)
    | .ok ds' => do
        handleTable.modify (·.insert h (openDataset ds' od.prefixes))
        pure (okWith [("count", .number (toString (datasetQuadCount ds')))])

/-- A writer tag and the RDF version it asks for: a tag ending in `11` asks
for RDF 1.1 (a dataset with an RDF 1.2 term is refused), one ending in `12`
or with no suffix writes every term the dataset has. -/
def writerTagVersion (formatTag : String) : String × Bool :=
  let t := formatTag.toLower
  if t.endsWith "11" then (t.dropEnd 2 |>.toString, true)
  else if t.endsWith "12" then (t.dropEnd 2 |>.toString, false)
  else (t, false)

/-- The refusal of an RDF 1.1 writer for a dataset with an RDF 1.2 term. -/
def rdf11WriterRefusal (fmt : String) : String :=
  s!"the dataset holds an RDF 1.2 triple term or directional language-tagged string and {fmt} in RDF 1.1 has no form for it; write it in the RDF 1.2 form"

/-- The text of `ds` in the syntax `formatTag` names (`writerTagVersion`):
N-Quads, N-Triples (refused when `ds` has a named graph, as N-Triples has no
graph name), Turtle, TriG and RDF/XML through the `Sink` writers (Turtle and
RDF/XML write the named graphs as one graph, `Sink.flatten`), and `rdfc`, the
RDFC-1.0 canonical N-Quads (`canonicalizeOf`). JSON-LD is the full engine's
`datasetToJsonLd`. `none` for any other tag. -/
def handleWriterText (formatTag : String) (ds : Dataset) : Option (Except String String) :=
  let (tag, v11) := writerTagVersion formatTag
  let checked (name : String) (k : Unit → Except String String) : Option (Except String String) :=
    if v11 && !ds.isRdf11 then some (.error (rdf11WriterRefusal name)) else some (k ())
  match tag with
  | "nquads" | "nq" | "n-quads" =>
      checked "N-Quads" fun _ => .ok (Dataset.toCanonicalNQuads ds)
  | "ntriples" | "nt" | "n-triples" =>
      if !ds.named.isEmpty then
        some (.error "the dataset has a named graph and N-Triples holds one graph; use nquads or trig")
      else checked "N-Triples" fun _ => L4Factoidal.RDF.Sink.serializeDataset {} .nt .rdf12 ds
  | "turtle" | "ttl" =>
      checked "Turtle" fun _ => L4Factoidal.RDF.Sink.serializeDataset {} .turtle .rdf12 ds
  | "trig" => checked "TriG" fun _ => L4Factoidal.RDF.Sink.serializeDataset {} .trig .rdf12 ds
  | "rdfxml" | "rdf-xml" | "rdf" =>
      checked "RDF/XML" fun _ => L4Factoidal.RDF.Sink.serializeDataset {} .rdfxml .rdf12 ds
  | "rdfc" | "canonical" =>
      match parseJson? (canonicalizeOf ds) with
      | some j =>
          match j.getString? "nquads" with
          | some text => some (.ok text)
          | none => some (.error ((j.getString? "error").getD "RDFC-1.0 canonicalisation failed"))
      | none => some (.error "RDFC-1.0 canonicalisation failed")
  | _ => none

/-- The syntaxes the engine reads and writes, for a host's capability table:
`(name, read11, read12, write11, write12, engine)`; `engine` is `core` when
both engines serve the syntax and `full` when only the full engine does. The
npm test `formats-table.test.mjs` checks each `true` write cell by writing a
dataset and reading it back. -/
def formatTable : List (String × Bool × Bool × Bool × Bool × String) :=
  [ ("nquads",   true,  true,  true,  true,  "core")
  , ("ntriples", true,  true,  true,  true,  "core")
  , ("turtle",   true,  true,  true,  true,  "core")
  , ("trig",     true,  true,  true,  true,  "core")
  , ("rdfxml",   true,  false, true,  false, "core")
  , ("jsonld",   true,  false, true,  false, "full")
  , ("rdfc",     false, false, true,  false, "core")
  , ("sparql-results-json", false, false, true, true, "core")
  , ("sparql-results-xml",  false, false, true, true, "core")
  , ("sparql-results-csv",  false, false, true, true, "core")
  , ("sparql-results-tsv",  false, false, true, true, "core") ]

/-- `datasetFormats()` — `formatTable` as JSON. -/
def datasetFormats : IO String :=
  pure (okWith [("formats", .array (formatTable.map fun (n, r11, r12, w11, w12, eng) =>
    Json.object [("name", .string n), ("read11", .bool r11), ("read12", .bool r12),
                 ("write11", .bool w11), ("write12", .bool w12), ("engine", .string eng)]))])

/-- The handle's own prefixes as the renderer's (namespace, `label:`) pairs. -/
private def handlePrefixTable (od : OpenDataset) : PrefixTable :=
  od.prefixes.map fun (label, iri) => (iri, label ++ ":")

/-- `datasetSerialize(handle, formatTag)` — canonical N-Quads, or Turtle in
which the handle's own prefixes (the ones `datasetOpen` recorded) name their
namespaces; named graphs are flattened into the default graph on the turtle
path. -/
def datasetSerialize (h formatTag : String) : IO String :=
  withHandle h fun od =>
    let ds := od.ds
    match formatTag.toLower with
    | "" | "nquads" | "nq" | "n-quads" =>
        pure (okWith [("nquads", .string (Dataset.toCanonicalNQuads ds))])
    | "turtle" | "ttl" =>
        pure (okWith [("turtle", .string
          (turtleOfGraphOpts { prefixes := handlePrefixTable od } (flattenedGraph ds)))])
    | _ =>
        match handleWriterText formatTag ds with
        | some (.ok text) => pure (okWith [("text", .string text)])
        | some (.error e) => pure (errJson s!"datasetSerialize: {e}")
        | none => pure (errJson
            s!"datasetSerialize: unknown format tag '{formatTag}' (nquads | turtle | ntriples | trig | rdfxml)")

/-- `datasetSerializeWith(handle, formatTag, optionsJson)` — as
`datasetSerialize`, with the caller's options. An absent `prefixes` member keeps
the handle's own prefixes; a present one replaces them. -/
def datasetSerializeWith (h formatTag optionsJson : String) : IO String :=
  withHandle h fun od =>
    let ds := od.ds
    match formatTag.toLower with
    | "" | "nquads" | "nq" | "n-quads" =>
        pure (okWith [("nquads", .string (Dataset.toCanonicalNQuads ds))])
    | "turtle" | "ttl" =>
        match turtleOptionsOfJson (handlePrefixTable od) optionsJson with
        | .error msg => pure (errJson msg)
        | .ok opts =>
            pure (okWith [("turtle", .string (turtleOfGraphOpts opts (flattenedGraph ds)))])
    | _ =>
        match handleWriterText formatTag ds with
        | some (.ok text) => pure (okWith [("text", .string text)])
        | some (.error e) => pure (errJson s!"datasetSerializeWith: {e}")
        | none => pure (errJson
            s!"datasetSerializeWith: unknown format tag '{formatTag}' (nquads | turtle | ntriples | trig | rdfxml)")

/-- `datasetClose(handle)` — drop the dataset from the store. Closing
an unknown (or already-closed) handle is the shared handle error. -/
def datasetClose (h : String) : IO String := do
  let table ← handleTable.get
  if table.contains h then
    handleTable.set (table.erase h)
    pure (okWith [])
  else
    pure (unknownHandle h)

/-! ## Ops that keep the data in the store (issue 882 item 1) -/

/-- Store `ds` under a new handle and answer the `datasetOpen` envelope. -/
def storeNewHandle (ds : Dataset) (prefixes : List (String × String) := [])
    (extra : List (String × Json) := []) : IO String := do
  let n ← handleCounter.modifyGet fun n => (n + 1, n + 1)
  let h := s!"h{n}"
  handleTable.modify (·.insert h (openDataset ds prefixes))
  pure (okWith ([("handle", .string h),
                ("count", .number (toString (datasetQuadCount ds))),
                ("prefixes", prefixesJson prefixes)] ++ extra))

/-- The stored dataset of `h`, or `none` when the handle is not open. -/
def lookupHandleDataset (h : String) : IO (Option (Dataset × List (String × String))) := do
  pure (((← handleTable.get)[h]?).map fun od => (od.ds, od.prefixes))

/-- Run `f` on the stored dataset of `h`; an unknown handle is the shared error. -/
def withHandleDataset (h : String) (f : Dataset → List (String × String) → IO String) :
    IO String := do
  match ← lookupHandleDataset h with
  | none => pure (unknownHandle h)
  | some (ds, prefixes) => f ds prefixes

/-- `datasetClone(handle)` — a new handle holding the same dataset and
prefixes; an update of one handle leaves the other unchanged. -/
def datasetClone (h : String) : IO String :=
  withHandleDataset h fun ds prefixes => storeNewHandle ds prefixes

/-- `datasetCanonicalize(handle)` — `canonicalizeOf` of the stored dataset:
the envelope `canonicalizeToNQuads` answers on its canonical N-Quads. -/
def datasetCanonicalize (h : String) : IO String :=
  withHandleDataset h fun ds _ => pure (canonicalizeOf ds)

/-- The regime names `datasetClosure` reads. -/
def closureRegimes : List String := ["rdfs", "owl-rl", "rho-df", "rdfs-plus"]

/-- `datasetClosure(handle, regime)` — the closure of the default graph of the
stored dataset under `regime`, stored under a new handle. The graph is
`closureStreamOf`'s, which `closureEnvelopeOf_stream` proves is the graph the
text closure ops write. The new dataset has no named graph, as the text ops'
output has none. For `rho-df` and `rdfs-plus` the envelope also has `rounds`,
the member the text ops answer (`closureEnvelopeTail`). -/
def datasetClosure (h regime : String) : IO String :=
  if !closureRegimes.contains regime then
    pure (errJson s!"datasetClosure: unknown regime '{regime}' (rdfs | owl-rl | rho-df | rdfs-plus)")
  else
  withHandleDataset h fun ds prefixes =>
    match closureStreamOf ds regime with
    | .error e => pure (errJson e)
    | .ok g =>
        let tail := match datasetForOps .rdf12 ds with
          | .ok d => (closureEnvelopeTail regime d).2
          | .error _ => []
        storeNewHandle { default := g, named := [] } prefixes tail

/-- `datasetShaclValidate(dataHandle, shapesHandle)` — `shaclValidateParsed` on
the two stored datasets, each normalised as the text op would read it
(`datasetForOps`). -/
def datasetShaclValidate (hData hShapes : String) : IO String :=
  withHandleDataset hData fun dataDs _ =>
  withHandleDataset hShapes fun shapesDs _ =>
    match datasetForOps .rdf12 dataDs, datasetForOps .rdf12 shapesDs with
    | .error e, _ => pure (errJson s!"shaclValidate(data): {fmtParseError e}")
    | _, .error e => pure (errJson s!"shaclValidate(shapes): {fmtParseError e}")
    | .ok d, .ok s => pure (shaclValidateParsed d s)

/-- `datasetQueryRaw(handle, sparql, optsJson)` — `queryRaw` over the stored
dataset: `optsJson` members `entail` (none | RDFS | OWL-RL | x-rdfscore |
x-rdfsplus) and `output` (json | xml | csv | tsv | table | ntriples). The
clock is read once per call. -/
def datasetQueryRaw (h sparql optsJson : String) : IO String := do
  let now ← nowDateTime
  let opts : Option Json := if optsJson == "" then none else parseJson? optsJson
  let field (k d : String) : String := ((opts.bind (fun j => j.getString? k))).getD d
  withHandleDataset h fun ds _ =>
    pure (queryRawParsed ds sparql (field "entail" "none") (field "output" "json") (some now))

/-- `detectFormat(text)` — `{"ok":true,"format":TAG}`, the parse tag of
`formatOfContent`; Turtle and TriG are read in RDF 1.2 mode (`turtle12`,
`trig12`), which also reads every RDF 1.1 document. -/
def detectFormat (text : String) : IO String :=
  let tag := match L4Factoidal.RDF.formatOfContent text with
    | .jsonld => "jsonld"
    | .rdfxml => "rdfxml"
    | .trig => "trig12"
    | _ => "turtle12"
  pure (okWith [("format", .string tag)])


/-! ## RDF/JS DatasetCore: add, delete, match (issue 882)

A quad pattern is a JSON array of four strings, subject, predicate, object,
graph. `""` leaves the position unbound; otherwise the string is the
N-Triples (N-Quads) form of the term, and for the graph `"DEFAULT"` names the
default graph. Matching uses the stored dataset's indexes
(`backendSearch` over `indexedDatasetBackend`). -/

/-- The term an N-Triples token denotes, read through the N-Quads reader in
RDF 1.2 mode: the token is placed at position `pos` (0 subject, 1 predicate,
2 object, 3 graph) of a line whose other positions are fixed IRIs. -/
def termOfToken (pos : Nat) (tok : String) : Option (Option Subject × Option WfIri × Option Term × Option Subject) :=
  let fill := ["<urn:x:s>", "<urn:x:p>", "<urn:x:o>"]
  let parts := (fill.set pos tok) ++ (if pos == 3 then [tok] else [])
  match parseNQuadsFast (String.intercalate " " parts ++ " .\n") .rdf12 with
  | .error _ => none
  | .ok ds =>
    match ds.default, ds.named with
    | [t], [] => some (some t.s, some t.p, some t.o, none)
    | [], [ng] =>
        match ng.graph with
        | [t] => some (some t.s, some t.p, some t.o, some ng.name)
        | _ => none
    | _, _ => none

/-- What a pattern asks for: the bound subject, predicate and object, and the
graph (`none` any graph, `some none` the default graph, `some (some g)`). -/
structure QuadPattern where
  bound : L4Factoidal.SPARQL.PatternBound := {}
  graph : Option (Option Subject) := none

/-- A pattern whose positions are JSON term objects (`TermJson`), `null` for
an unbound position, and `{"type":"default"}` for the default graph
(https://github.com/danbri/factoidal/issues/894 item 1). A host builds this
from its own term objects with no lexical decision. -/
def quadPatternOfTerms (arr : List Json) : Option QuadPattern := do
  match arr with
  | [s, p, o, g] =>
    let sB ← match s with | .null => some none | j => (TermJson.decodeSubject j).map some
    let pB ← match p with | .null => some none | j => (TermJson.decodeIri j).map some
    let oB ← match o with | .null => some none | j => (TermJson.decodeTerm j).map some
    let gB ← match g with
      | .null => some none
      | j => if j.getString? "type" == some "default" then some (some none)
             else (TermJson.decodeSubject j).map (fun x => some (some x))
    pure { bound := { s := sB, p := pB, o := oB }, graph := gB }
  | _ => none

/-- Read a pattern; `none` when a token is not a term of its position. -/
def quadPatternOf (json : String) : Option QuadPattern := do
  let j ← parseJson? json
  let arr ← match j with | .array xs => some xs | _ => none
  if arr.any (fun x => match x with | .string _ => false | _ => true) then
    quadPatternOfTerms arr
  else
  let toks ← arr.mapM (fun x => match x with | .string t => some t | _ => none)
  match toks with
  | [s, p, o, g] =>
    let sB ← if s == "" then some none else (termOfToken 0 s).bind (·.1) |>.map some
    let pB ← if p == "" then some none else (termOfToken 1 p).bind (·.2.1) |>.map some
    let oB ← if o == "" then some none else (termOfToken 2 o).bind (·.2.2.1) |>.map some
    let gB ← if g == "" then some none
             else if g == "DEFAULT" then some (some none)
             else (termOfToken 3 g).bind (·.2.2.2) |>.map (fun x => some (some x))
    pure { bound := { s := sB, p := pB, o := oB }, graph := gB }
  | _ => none

/-- The quads of `od` that match `pat`, as a dataset, through the indexes. -/
def matchDataset (od : OpenDataset) (pat : QuadPattern) : Dataset :=
  let be : DatasetBackend := od.backendThunk.get
  let wantDefault := match pat.graph with | none | some none => true | _ => false
  let dflt := if wantDefault then L4Factoidal.SPARQL.StoreBackend.backendSearch be.default pat.bound else []
  let named := (od.ds.named.zip be.named).filterMap fun (ng, nb) =>
    let take := match pat.graph with
      | none => true
      | some none => false
      | some (some g) => g == ng.name
    if !take then none
    else
      let ts := L4Factoidal.SPARQL.StoreBackend.backendSearch nb.backend pat.bound
      if ts.isEmpty then none else some { name := ng.name, graph := ts }
  { default := dflt, named }

/-- `datasetMatch(handle, patternJson)` — the matching quads under a new handle. -/
def datasetMatch (h patternJson : String) : IO String := do
  let tbl ← handleTable.get
  match tbl[h]? with
  | none => pure (unknownHandle h)
  | some od =>
    match quadPatternOf patternJson with
    | none => pure (errJson s!"datasetMatch: not a quad pattern: {patternJson}")
    | some pat => storeNewHandle (matchDataset od pat) od.prefixes

/-- `datasetMatchCount(handle, patternJson)` — `{"ok":true,"count":N}`, the
number of matching quads, with no new handle. -/
def datasetMatchCount (h patternJson : String) : IO String := do
  let tbl ← handleTable.get
  match tbl[h]? with
  | none => pure (unknownHandle h)
  | some od =>
    match quadPatternOf patternJson with
    | none => pure (errJson s!"datasetMatchCount: not a quad pattern: {patternJson}")
    | some pat => pure (okWith [("count", .number (toString (datasetQuadCount (matchDataset od pat))))])

/-- The quads of an N-Quads text as SPARQL Update quads. A graph named by a
blank node has no Update quad form and is refused. -/
def updateQuadsOf (nq : String) : Except String (List (Option WfIri × Triple)) := do
  let ds ← (parseNQuadsFast nq .rdf12).mapError fmtParseError
  let named ← ds.named.mapM fun ng =>
    match ng.name with
    | .iri i => .ok (ng.graph.map fun t => ((some i : Option WfIri), t))
    | .bnode _ => .error "a quad in a graph named by a blank node cannot be added or deleted here"
  pure (ds.default.map (fun t => ((none : Option WfIri), t)) ++ named.flatten)

/-- Replace the stored dataset of `h` with `f` of it; answers the new count. -/
private def changeHandle (who h nq : String)
    (f : Dataset → List (Option WfIri × Triple) → Dataset) : IO String := do
  let tbl ← handleTable.get
  match tbl[h]? with
  | none => pure (unknownHandle h)
  | some od =>
    match updateQuadsOf nq with
    | .error e => pure (errJson s!"{who}: {e}")
    | .ok qs =>
      let ds' := f od.ds qs
      handleTable.modify (·.insert h (openDataset ds' od.prefixes))
      pure (okWith [("count", .number (toString (datasetQuadCount ds')))])

/-- `datasetAddQuads(handle, nquads)` — add the quads (set semantics), as
INSERT DATA does (`Dataset.insertQuads`). Blank-node labels are kept as
written, so a label the dataset holds names the same node. -/
def datasetAddQuads (h nq : String) : IO String :=
  changeHandle "datasetAddQuads" h nq Dataset.insertQuads

/-- `datasetDeleteQuads(handle, nquads)` — remove the quads
(`Dataset.deleteQuads`). -/
def datasetDeleteQuads (h nq : String) : IO String :=
  changeHandle "datasetDeleteQuads" h nq Dataset.deleteQuads

/-! ## Terms as JSON values: the RDF/JS host reads and writes no RDF syntax

https://github.com/danbri/factoidal/issues/894. A host builds its term
objects from `TermJson.encodeTerm` members and sends term objects back; the
engine does every escape, every parse and every datatype decision. -/

/-- A quad of `TermJson` in the form `Dataset.insertQuads` takes; a graph named
by a blank node has no SPARQL Update quad form and is refused. -/
def updateQuadOfJsonQuad : TermJson.Quad → Except String (Option WfIri × Triple)
  | (none, t) => .ok (none, t)
  | (some (.iri i), t) => .ok (some i, t)
  | (some (.bnode _), _) =>
      .error "a quad in a graph named by a blank node cannot be added or deleted here"

/-- The quads of a JSON array of `TermJson` quads. -/
def jsonQuadsOf (text : String) : Except String (List TermJson.Quad) := do
  let j ← match parseJson? text with
    | some j => .ok j
    | none => .error "not a JSON document"
  match j with
  | .array xs =>
      xs.mapM fun x => match TermJson.decodeQuad x with
        | some q => .ok q
        | none => .error s!"not a quad: {x.toString}"
  | _ => .error "expected a JSON array of quads"

/-- Optional natural-number member of an options object. -/
private def natMember (opts : Option Json) (k : String) : Option Nat :=
  (opts.bind (·.field? k)).bind fun
    | .number n => n.toNat?
    | _ => none

/-- `datasetQuadsJson(handle, optsJson)` — the quads of `quadPage` as
`TermJson` quads: `{"ok":true,"total":N,"offset":O,"quads":[…]}`. `optsJson`
members `offset` (default 0) and `limit` (default all). The order is the line
order of `datasetSerialize` N-Quads (`TermJson.toCanonicalNQuads_eq_quadList`). -/
def datasetQuadsJson (h optsJson : String) : IO String :=
  withHandleDataset h fun ds _ =>
    let opts := if optsJson == "" then none else parseJson? optsJson
    let qs := TermJson.Dataset.quadList ds
    let off := (natMember opts "offset").getD 0
    let lim := (natMember opts "limit").getD qs.length
    let page := (qs.drop off).take lim
    pure (okWith [("total", .number (toString qs.length)), ("offset", .number (toString off)),
                  ("quads", .array (page.map TermJson.encodeQuad))])

private def changeHandleJson (who h text : String)
    (f : Dataset → List (Option WfIri × Triple) → Dataset) : IO String := do
  match (← handleTable.get)[h]? with
  | none => pure (unknownHandle h)
  | some od =>
    match jsonQuadsOf text >>= (·.mapM updateQuadOfJsonQuad) with
    | .error e => pure (errJson s!"{who}: {e}")
    | .ok qs =>
      let ds' := f od.ds qs
      handleTable.modify (·.insert h (openDataset ds' od.prefixes))
      pure (okWith [("count", .number (toString (datasetQuadCount ds')))])

/-- `datasetAddQuadsJson(handle, quadsJson)` — `datasetAddQuads` with the quads
given as `TermJson` quads. -/
def datasetAddQuadsJson (h quadsJson : String) : IO String :=
  changeHandleJson "datasetAddQuadsJson" h quadsJson Dataset.insertQuads

/-- `datasetDeleteQuadsJson(handle, quadsJson)` — `datasetDeleteQuads` with the
quads given as `TermJson` quads. -/
def datasetDeleteQuadsJson (h quadsJson : String) : IO String :=
  changeHandleJson "datasetDeleteQuadsJson" h quadsJson Dataset.deleteQuads

/-- The dataset of a list of quads, each quad once, the graphs in the order of
their first quad. -/
def datasetOfQuads (qs : List TermJson.Quad) : Dataset :=
  let step : (Std.HashSet TermJson.Quad × List Triple × List (Subject × List Triple)) →
      TermJson.Quad → (Std.HashSet TermJson.Quad × List Triple × List (Subject × List Triple)) :=
    fun (seen, dflt, named) q =>
      if seen.contains q then (seen, dflt, named)
      else
        let seen := seen.insert q
        match q with
        | (none, t) => (seen, t :: dflt, named)
        | (some g, t) =>
            if named.any (·.1 == g) then
              (seen, dflt, named.map fun (n, ts) => if n == g then (n, t :: ts) else (n, ts))
            else (seen, dflt, (g, [t]) :: named)
  let (_, dflt, named) := qs.foldl step (∅, [], [])
  { default := dflt.reverse,
    named := named.reverse.map fun (n, ts) => { name := n, graph := ts.reverse } }

/-- `parseQuadsJson(text, formatTag, baseIri)` — parse a document and answer its
quads as `TermJson` quads, `{"ok":true,"quads":[…]}`, with the blank-node
labels as written (no document scope) and nothing stored; a parse failure is
the positioned parse-error envelope of `datasetOpen`. -/
def parseQuadsJsonBy (extra : ExtraReader) (text formatTag baseIri : String) : IO String :=
  match parseDocumentOutcomeBy extra text formatTag baseIri with
  | .error f => pure (parseFailureEnvelope formatTag f)
  | .ok o => pure (okWith [("quads", .array ((TermJson.Dataset.quadList o.ds).map TermJson.encodeQuad))])

/-- `quadsToNQuads(quadsJson)` — the canonical N-Quads line of each `TermJson`
quad, in the given order (`TermJson.quadLine`): `{"ok":true,"nquads":…}`. -/
def quadsToNQuadsText (quadsJson : String) : IO String :=
  match jsonQuadsOf quadsJson with
  | .error e => pure (errJson s!"quadsToNQuads: {e}")
  | .ok qs => pure (okWith [("nquads", .string (String.join (qs.map TermJson.quadLine)))])

/-- `datasetFromQuadsJson(quadsJson)` — a new handle holding the quads. -/
def datasetFromQuadsJson (quadsJson : String) : IO String :=
  match jsonQuadsOf quadsJson with
  | .error e => pure (errJson s!"datasetFromQuadsJson: {e}")
  | .ok qs => storeNewHandle (datasetOfQuads qs)

/-- `datasetGraphNames(handle)` — the names of the named graphs that hold a
triple, as `TermJson` terms, in the order of `quadList`. An IRI and a blank
node with the same string are two names (RDF 1.1 Concepts §4). -/
def datasetGraphNames (h : String) : IO String :=
  withHandleDataset h fun ds _ =>
    let names := (ds.named.filter (!·.graph.isEmpty)).map (·.name)
    let distinct := names.foldl (fun acc n => if acc.contains n then acc else acc ++ [n]) []
    pure (okWith [("graphs", .array (distinct.map TermJson.subjectJson))])

/-- `datasetGraphAsDefault(handle, graphJson)` — a new handle whose default
graph is the graph `graphJson` names (`{"type":"default"}` the default graph,
`{"type":"union"}` the triples of every graph, each once) and which has no
named graph. -/
def datasetGraphAsDefault (h graphJson : String) : IO String :=
  withHandleDataset h fun ds prefixes =>
    match parseJson? graphJson with
    | none => pure (errJson "datasetGraphAsDefault: not a JSON term")
    | some j =>
      if j.getString? "type" == some "default" then
        storeNewHandle { default := ds.default, named := [] } prefixes
      else if j.getString? "type" == some "union" then
        -- every quad with its graph name dropped, each triple once
        let ts := (ds.default ++ ds.named.flatMap (·.graph)).foldl
          (fun (seen, acc) t => if seen.contains t then (seen, acc) else (seen.insert t, t :: acc))
          ((∅ : Std.HashSet Triple), ([] : List Triple))
        storeNewHandle { default := ts.2.reverse, named := [] } prefixes
      else match TermJson.decodeSubject j with
        | none => pure (errJson "datasetGraphAsDefault: a graph name is an IRI or a blank node")
        | some g =>
          let ts := (ds.named.filter (·.name == g)).flatMap (·.graph)
          storeNewHandle { default := ts, named := [] } prefixes

/-- `datasetIsomorphic(handle1, handle2)` — `Dataset.isomorphicOutcome`
(RDF 1.1 Concepts §3.6 and §4; blank nodes inside triple terms included):
`{"ok":true,"isomorphic":B,"outcome":"equal"|"notEqual"}`. When the
blank-node search budget is exceeded the answer is an error envelope, never
`false`. -/
def datasetIsomorphic (h1 h2 : String) : IO String :=
  withHandleDataset h1 fun d1 _ =>
  withHandleDataset h2 fun d2 _ =>
    match Dataset.isomorphicOutcome d1 d2 with
    | .equal => pure (okWith [("isomorphic", .bool true), ("outcome", .string "equal")])
    | .notEqual => pure (okWith [("isomorphic", .bool false), ("outcome", .string "notEqual")])
    | .budgetExceeded => pure (errJson
        "datasetIsomorphic: the blank-node search budget was exceeded; no answer")

/-- `termsToNTriples(termsJson)` — the canonical N-Triples form of each term of
a JSON array of `TermJson` terms: `{"ok":true,"tokens":[…]}`. For display. -/
def termsToNTriples (termsJson : String) : IO String :=
  match parseJson? termsJson with
  | some (.array xs) =>
      match xs.mapM TermJson.decodeTerm with
      | some ts => pure (okWith [("tokens", .array (ts.map fun t =>
          .string (L4Factoidal.Syntax.Term.toCanonicalNTriples t)))])
      | none => pure (errJson "termsToNTriples: an element is not a term")
  | _ => pure (errJson "termsToNTriples: expected a JSON array of terms")

/-- `resolveIri(base, reference)` — RFC 3986 §5.2 reference resolution
(`L4Factoidal.Syntax.resolveIri`): `{"ok":true,"iri":…}`. -/
def resolveIriOp (base ref : String) : IO String :=
  pure (okWith [("iri", .string (L4Factoidal.Syntax.resolveIri base ref)),
                ("referenceAbsolute", .bool (L4Factoidal.Syntax.parseIri ref).scheme.isSome)])

/-- The query form of a SPARQL text, read by the SPARQL 1.2 grammar (which
reads every SPARQL 1.1 query):
`{"ok":true,"kind":"select"|"ask"|"construct"|"describe"}`. -/
def queryForm (sparql : String) : IO String :=
  match L4Factoidal.SPARQL.parseSparql sparql none .v12 with
  | .error e => pure (errJson s!"SPARQL parse error: {fmtParseError e}")
  | .ok q => pure (okWith [("kind", .string (match q.form with
      | .select _ => "select" | .ask => "ask" | .construct _ => "construct"
      | .describe _ => "describe"))])

/-- A JSON object of string members. -/
private def strMap (kvs : List (String × String)) : Json :=
  .object (kvs.map fun (k, v) => (k, .string v))

/-- The parse tag each format name selects (`datasetOpen`, `parseToDatasetJson`).
The plain names read RDF 1.1; the names ending in `12` read RDF 1.2
(`Mode.rdf12`). -/
def parseFormatNames : List (String × String) :=
  [ ("turtle", "turtle"), ("ttl", "turtle"), ("ntriples", "ntriples"), ("nt", "ntriples"),
    ("nquads", "nquads"), ("nq", "nquads"), ("trig", "trig"), ("rdfxml", "rdfxml"),
    ("rdf-xml", "rdfxml"), ("rdf", "rdfxml"), ("jsonld", "jsonld"), ("json-ld", "jsonld"),
    ("turtle12", "turtle12"), ("ttl12", "turtle12"), ("ntriples12", "ntriples12"),
    ("nt12", "ntriples12"), ("nquads12", "nquads12"), ("nq12", "nquads12"),
    ("trig12", "trig12") ]

/-- The writer tag each output format name selects (`datasetSerialize`,
`datasetToJsonLd` for `jsonld`). -/
def writerFormatNames : List (String × String) :=
  [ ("nquads", "nquads"), ("nq", "nquads"), ("n-quads", "nquads"),
    ("ntriples", "ntriples"), ("nt", "ntriples"), ("n-triples", "ntriples"),
    ("turtle", "turtle"), ("ttl", "turtle"), ("trig", "trig"),
    ("rdfxml", "rdfxml"), ("rdf-xml", "rdfxml"), ("rdf", "rdfxml"),
    ("jsonld", "jsonld"), ("json-ld", "jsonld"),
    ("rdfc", "rdfc"), ("canonical", "rdfc"), ("rdfc-1.0", "rdfc") ]

/-- The `dataFormat` names `queryRaw` reads. -/
def rawDataFormatNames : List (String × String) :=
  [ ("turtle", "turtle"), ("ttl", "turtle"), ("ntriples", "ntriples"), ("nt", "ntriples"),
    ("nquads", "nquads"), ("nq", "nquads"), ("trig", "trig"), ("rdfxml", "rdfxml"),
    ("rdf-xml", "rdfxml"), ("rdf", "rdfxml") ]

/-- The `entail` values `datasetQueryRaw` and `queryRaw` read, and the
case-insensitive aliases of `@factoidal/core/fn`'s `entail()`. -/
def entailRegimeNames : List String := ["none", "RDFS", "OWL-RL", "x-rdfscore", "x-rdfsplus"]

def entailRegimeAliases : List (String × String) :=
  [ ("none", "none"), ("rdfs", "RDFS"), ("owl-rl", "OWL-RL"), ("owlrl", "OWL-RL"),
    ("owl_rl", "OWL-RL") ]

/-- The refusal of the `x-ikl-*` regimes: not implemented
(https://github.com/danbri/factoidal/issues/581, dispatch deleted by
https://github.com/danbri/factoidal/issues/626). -/
def iklRefusal (who regime : String) : String :=
  s!"{who}: entail '{regime}' is not implemented. The x-ikl-* entailment regimes are the owner's design (danbri/factoidal#581); the Lean engine's dispatch for them was deleted on 2026-08-26 as collateral of the IKL-to-RDF projection purge (danbri/factoidal#626). This is not a policy exclusion."

/-- The syntaxes the streaming packer reads, the file-name suffix of each, and
the suffixes of syntaxes the engine reads elsewhere but the packer does not. -/
def packSyntaxNames : List String := ["turtle", "trig", "nquads", "ntriples"]

def packSuffixes : List (String × String) :=
  [ (".ttl", "turtle"), (".turtle", "turtle"), (".trig", "trig"), (".nq", "nquads"),
    (".nquads", "nquads"), (".nt", "ntriples"), (".ntriples", "ntriples") ]

def packUnsupportedSuffixes : List (String × String) :=
  [ (".rdf", "RDF/XML"), (".owl", "RDF/XML"), (".xml", "RDF/XML"), (".jsonld", "JSON-LD"),
    (".json", "JSON-LD"), (".n3", "Notation3"), (".csv", "CSV"), (".tsv", "TSV"),
    (".hdt", "HDT") ]

/-- Every name table a host validates arguments against, so no host keeps its
own copy (https://github.com/danbri/factoidal/issues/894 item 5). -/
def engineTablesJson : Json :=
  .object
    [ ("parseFormats", strMap parseFormatNames)
    , ("writerFormats", strMap writerFormatNames)
    , ("rawDataFormats", strMap rawDataFormatNames)
    , ("entailRegimes", .array (entailRegimeNames.map Json.string))
    , ("entailAliases", strMap entailRegimeAliases)
    , ("iklRefusal", .string (iklRefusal "WHO" "REGIME"))
    , ("closureRegimes", .array (closureRegimes.map Json.string))
    , ("queryOutputs", .array (["json", "csv", "tsv", "xml", "table", "ntriples"].map Json.string))
    , ("packSyntaxes", .array (packSyntaxNames.map Json.string))
    , ("packSuffixes", strMap packSuffixes)
    , ("packUnsupportedSuffixes", strMap packUnsupportedSuffixes) ]

/-- `engineTables()` — `engineTablesJson`. -/
def engineTables : IO String :=
  pure (okWith [("tables", engineTablesJson)])

#guard (datasetOfQuads [(none, ⟨.bnode "a", ⟨"http://e/p", rfl⟩, .bnode "b"⟩),
                        (none, ⟨.bnode "a", ⟨"http://e/p", rfl⟩, .bnode "b"⟩)]).default.length == 1
#guard (datasetOfQuads [(some (.bnode "g"), ⟨.bnode "a", ⟨"http://e/p", rfl⟩, .bnode "b"⟩),
                        (some (.iri ⟨"http://e/g", rfl⟩), ⟨.bnode "a", ⟨"http://e/p", rfl⟩, .bnode "b"⟩)]).named.length == 2
#guard (quadPatternOf "[null,null,null,{\"type\":\"default\"}]").map (·.graph) == some (some none)
#guard (quadPatternOf "[{\"type\":\"literal\",\"value\":\"x\",\"datatype\":\"http://e/d\"},null,null,null]").isNone

/-! ## Build-time checks (positive and negative) -/

#guard writerTagVersion "turtle11" == ("turtle", true)
#guard writerTagVersion "TriG12" == ("trig", false)
#guard writerTagVersion "rdfxml" == ("rdfxml", false)
#guard (quadPatternOf "[\"<http://e/a>\",\"\",\"\",\"DEFAULT\"]").isSome
#guard ((quadPatternOf "[\"<http://e/a>\",\"\",\"\",\"\"]").map (·.graph)) == some none
#guard (quadPatternOf "[\"not a term\",\"\",\"\",\"\"]").isNone
#guard (quadPatternOf "[\"\",\"_:b\",\"\",\"\"]").isNone
#guard (quadPatternOf "[\"\",\"\"]").isNone
#guard match updateQuadsOf "<http://e/a> <http://e/p> \"x\" <http://e/g> .\n" with
  | .ok [(some _, _)] => true | _ => false
#guard match updateQuadsOf "<http://e/a> <http://e/p> \"x\" _:g .\n" with
  | .error _ => true | _ => false

private def tt12 : Dataset :=
  match parseNQuadsFast "<http://e/a> <http://e/p> <<( <http://e/s> <http://e/p> <http://e/o> )>> .\n" .rdf12 with
  | .ok ds => ds
  | .error _ => Dataset.empty

#guard match handleWriterText "ntriples11" tt12 with | some (.error _) => true | _ => false
#guard match handleWriterText "ntriples12" tt12 with | some (.ok _) => true | _ => false
#guard match handleWriterText "rdfxml" tt12 with | some (.error _) => true | _ => false
#guard (handleWriterText "hdt" tt12).isNone

end L4Wasm.Ops
