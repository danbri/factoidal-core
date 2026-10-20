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
import Wasm.Ops.Reason
import Wasm.Ops.Validate
import Wasm.Ops.Canon
import Wasm.Ops.FromDataset
import L4Factoidal.RDF.Sink
import L4Factoidal.RDF.Format

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
  backend : DatasetBackend
  /-- The prefixes the document declared, each label once, in declaration order.
  Turtle output of the handle uses them. -/
  prefixes : List (String × String) := []

private def openDataset (ds : Dataset) (prefixes : List (String × String) := []) :
    OpenDataset :=
  { ds, backend := indexedDatasetBackend ds, prefixes }

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

end L4Wasm.Ops
