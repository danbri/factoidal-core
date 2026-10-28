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
  datasetSparqlRlInfer(handle, rulesText)
    -> the `datasetOpen` envelope of a new handle: the SPARQL 1.2 RL
       inference graph of the rule set over the default graph
       (`SPARQLRL.inferText`, https://github.com/danbri/factoidal/issues/1099)

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
import L4Factoidal.Dataflow.Reader
import L4Factoidal.Dataflow.Writer
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
import L4Factoidal.RDF.FormatOfContent
import L4Factoidal.RDF.TermJson
import L4Factoidal.RDF.QuadsBinTheorems
import L4Factoidal.RDF.Isomorphism
import L4Factoidal.Syntax.IriResolve
import L4Factoidal.RDF.CertifiedDataset
import L4Factoidal.SPARQLRL.Text
import L4Factoidal.SPARQL.SameValue
import L4Factoidal.RDF.MediaType

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
the optimized physical-plan path without rebuilding indexes.

The dataset is a `CertifiedDataset`: it carries the proof that it is a set of
quads (RDF 1.1 Concepts §3, §4; `RDF/CertifiedDataset.lean`). The store cannot
hold a dataset that lists one triple two times in one graph, or two named
graphs of one name. -/
structure OpenDataset where
  data : CertifiedDataset
  /-- Built on the first query after an open or a change, then kept: an
  `add` of one quad does not rebuild every index. -/
  backendThunk : Thunk L4Factoidal.Dataflow.LawfulDataset
  /-- The prefixes the document declared, each label once, in declaration order.
  Turtle output of the handle uses them. -/
  prefixes : List (String × String) := []
  /-- The RDF version mode of the reader that read the document (`datasetOpen`:
  the mode of the format tag, `resolveModeAndTag`); `.rdf12` for a handle made
  in any other way. The writers of the handle use it (`OpenDataset.writeMode`). -/
  readMode : L4Factoidal.Syntax.Mode := .rdf12
  /-- The distinct object literals of the dataset, each filed under its
  `L4Factoidal.SPARQL.storeKeys` (`valueIndexOf`). Built on the first match by
  value, then kept until the next change
  (https://github.com/danbri/factoidal/issues/1052). -/
  valueIndex : Thunk (Std.HashMap String (Array WfLiteral))

/-- The stored dataset. -/
def OpenDataset.ds (od : OpenDataset) : Dataset := od.data.val

/-- The stored dataset is a set of quads. -/
theorem OpenDataset.isSet (od : OpenDataset) : od.ds.IsSet := od.data.property

/-- File one object term of the dataset in the value index: a literal not seen
before goes in the list of each of its keys. -/
def valueIndexStep (st : Std.HashSet WfLiteral × Std.HashMap String (Array WfLiteral))
    (t : Term) : Std.HashSet WfLiteral × Std.HashMap String (Array WfLiteral) :=
  match t with
  | .literal l =>
      if st.1.contains l then st
      else (st.1.insert l, (L4Factoidal.SPARQL.storeKeys l.val).foldl
        (fun m k => m.insert k ((m.getD k #[]).push l)) st.2)
  | _ => st

/-- The value index of a dataset: every distinct object literal of the default
graph and of each named graph, filed under `storeKeys`. -/
def valueIndexOf (ds : Dataset) : Std.HashMap String (Array WfLiteral) :=
  let st0 := ds.default.foldl (fun st t => valueIndexStep st t.o) (∅, ∅)
  (ds.named.foldl (fun st ng => ng.graph.foldl (fun st t => valueIndexStep st t.o) st) st0).2

private def openDataset (data : CertifiedDataset) (prefixes : List (String × String) := [])
    (readMode : L4Factoidal.Syntax.Mode := .rdf12) : OpenDataset :=
  { data, backendThunk := Thunk.mk (fun _ => L4Factoidal.Dataflow.LawfulDataset.ofCertified data), prefixes, readMode
    valueIndex := Thunk.mk (fun _ => valueIndexOf data.val) }

/-- The mode the writers of the handle use: the mode of its reader when that is
RDF 1.1 and the dataset still has no RDF 1.2 term, else RDF 1.2. A document
read as RDF 1.1 is written as RDF 1.1, so a language tag that RDF 1.1 accepts
(a subtag of 9 or more characters, LANGTAG [144s]) is written, not refused. -/
def OpenDataset.writeMode (od : OpenDataset) : L4Factoidal.Syntax.Mode :=
  if od.readMode == .rdf11 && od.ds.isRdf11 then .rdf11 else .rdf12

/-- The indexed backend of an open dataset. -/
private def OpenDataset.backend (od : OpenDataset) : L4Factoidal.Dataflow.LawfulDataset :=
  od.backendThunk.get

/-- The open datasets, keyed by handle string. -/
initialize handleTable : IO.Ref (Std.HashMap String OpenDataset) ← IO.mkRef ∅

/-- The shared error envelope for a handle that is not in the store. -/
def unknownHandle (h : String) : String :=
  errJson s!"unknown dataset handle: {h}"

/-- True when `h` is `<pfx><n>` with `1 ≤ n ≤ issued`: an id this engine
handed out. -/
def handleWasIssued (pfx : String) (issued : Nat) (h : String) : Bool :=
  h.startsWith pfx &&
    match (String.ofList (h.toList.drop pfx.length)).toNat? with
    | some n => 1 ≤ n && n ≤ issued
    | none => false

/-- The error for a handle that is not open: `handle.disposed` when this
engine issued it and it was closed since, else the unknown-handle error
(`handle.unknown`). Handle ids are never reused. -/
def missingHandle (h : String) : IO String := do
  if handleWasIssued "h" (← handleCounter.get) h then
    pure (errCoded "handle.disposed"
      s!"dataset handle {h} was disposed; a closed handle cannot be used again")
  else pure (unknownHandle h)

/-- Look `h` up and run `f` on the stored dataset; unknown handles get
the shared error envelope. -/
private def withHandle (h : String) (f : OpenDataset → IO String) : IO String := do
  match (← handleTable.get)[h]? with
  | none    => missingHandle h
  | some od => f od

/-- `datasetOpen(text, formatTag, baseIri)` — parse once, index once,
store, and answer the new handle plus the quad count. A parse failure
stores nothing and issues no handle. `extra` reads the syntaxes outside
`Wasm/Ops/Parse.lean`'s table: the full dispatch passes `jsonLdReader`, the
core dispatch a reader without JSON-LD (issue 713 stage 4). -/
def datasetOpenBy (extra : ExtraReader) (text formatTag baseIri : String) : IO String := do
  match hp : parseDocumentOutcomeBy extra text formatTag baseIri with
  | .error f => pure (parseFailureEnvelope formatTag f)
  | .ok o =>
      -- The parse is a set (`parseDocumentOutcomeBy_isSet`), so it is not
      -- walked again. The document gets its own blank-node scope, as
      -- `parseToDatasetJsonScoped`; the scope keeps a set a set
      -- (`renameDatasetBnodes_isSet`).
      let parsed : CertifiedDataset :=
        ⟨o.ds, parseDocumentOutcomeBy_isSet extra text formatTag baseIri o hp⟩
      let od := openDataset (parsed.renameBnodes (← nextDocumentScope)) o.prefixes o.mode
      let n ← handleCounter.modifyGet fun n => (n + 1, n + 1)
      let h := s!"h{n}"
      handleTable.modify (·.insert h od)
      pure (okWith ([("handle", .string h),
                    ("count", .number (toString (datasetQuadCount od.ds))),
                    ("prefixes", prefixesJson o.prefixes)] ++
                    warningsMembers (readerWarnings text formatTag o.ds)))

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

/-- A SPARQL Update request applied to a set gives a set. -/
theorem applyUpdateText_isSet {ds ds' : Dataset} (h : ds.IsSet) {text : String}
    {base now : Option String} {version : L4Factoidal.SPARQL.SparqlVersion}
    (hu : applyUpdateText ds text base now version = .ok ds') : ds'.IsSet := by
  unfold applyUpdateText at hu
  split at hu
  · cases hu
  · split at hu
    · cases hu
    · next d hd => cases hu; exact applyUpdateIn_isSet _ _ h hd

#print axioms applyUpdateText_isSet

/-- `datasetUpdate(handle, sparqlUpdate)` — apply the update and
REPLACE the stored dataset (and rebuild its index); answers the new quad
count. On a parse or evaluation error the stored dataset is unchanged. The
clock is read once per call: `NOW()` in a WHERE clause is the instant of this
request (§17.4.5.1, https://github.com/danbri/factoidal/issues/743). -/
def datasetUpdate (h updateText : String) (base : Option String := none) : IO String := do
  let now ← nowDateTime
  withHandle h fun od =>
    match hu : applyUpdateText od.ds updateText base (some now) with
    | .error e => pure (errJson e)
    | .ok ds' => do
        -- An update of a set is a set (`applyUpdateText_isSet`): no new walk.
        let next := openDataset ⟨ds', applyUpdateText_isSet od.isSet hu⟩ od.prefixes
        handleTable.modify (·.insert h next)
        pure (okWith [("count", .number (toString (datasetQuadCount next.ds)))])

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

/-- The dataset that the handle's N-Quads and Turtle writers write
(https://github.com/danbri/factoidal/issues/986): a language tag outside LANGTAG
[144s] (subtags of 1 to 8 characters, RDF 1.2) is an error that names the tag,
and a blank-node label outside BLANK_NODE_LABEL [141s] gets a fresh valid label
(`Dataset.relabelForWrite`, as the `Sink` writers do). -/
def handleWriteInput (ds : Dataset) (mode : L4Factoidal.Syntax.Mode := .rdf12) :
    Except String Dataset :=
  L4Factoidal.Dataflow.writeInput mode ds

/-- The writer of syntax `fmt` of the dataset handles: the table
`Dataflow.writers` (`L4Factoidal/Dataflow/Writer.lean`) without the JSON-LD
library, which the core module does not carry. Each of its writers has its
round-trip contract as fields. -/
def handleWriter (fmt : RdfFormat) : L4Factoidal.Dataflow.RdfWriter :=
  L4Factoidal.Dataflow.writers {} {} fmt

/-- The canonical N-Quads writer of the dataset handles (`Dataflow.canonicalNQuadsRdfWriter`). -/
def handleCanonicalNQuadsWriter : L4Factoidal.Dataflow.RdfWriter :=
  L4Factoidal.Dataflow.canonicalNQuadsRdfWriter {} {}

/-- The text of `ds` in the syntax `formatTag` names (`writerTagVersion`):
N-Quads, N-Triples (refused when `ds` has a named graph, as N-Triples has no
graph name), Turtle, TriG and RDF/XML through the `Sink` writers (Turtle and
RDF/XML write the named graphs as one graph, `Sink.flatten`), and `rdfc`, the
RDFC-1.0 canonical N-Quads (`canonicalizeOf`). JSON-LD is the full engine's
`datasetToJsonLd`. `none` for any other tag. -/
def handleWriterText (formatTag : String) (ds : Dataset) (mode : L4Factoidal.Syntax.Mode := .rdf12) :
    Option (Except String String) :=
  let (tag, v11) := writerTagVersion formatTag
  let checked (name : String) (k : Unit → Except String String) : Option (Except String String) :=
    if v11 && !ds.isRdf11 then some (.error (rdf11WriterRefusal name)) else some (k ())
  match tag with
  | "nquads" | "nq" | "n-quads" =>
      checked "N-Quads" fun _ => handleCanonicalNQuadsWriter.run mode {} ds
  | "ntriples" | "nt" | "n-triples" =>
      if !ds.named.isEmpty then
        some (.error "the dataset has a named graph and N-Triples holds one graph; use nquads or trig")
      else checked "N-Triples" fun _ => (handleWriter .nt).run mode {} ds
  | "turtle" | "ttl" =>
      checked "Turtle" fun _ => (handleWriter .turtle).run mode {} ds
  | "trig" => checked "TriG" fun _ => (handleWriter .trig).run mode {} ds
  | "rdfxml" | "rdf-xml" | "rdf" =>
      checked "RDF/XML" fun _ => (handleWriter .rdfxml).run mode {} ds
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

/-- The registered media types and file extensions of a row of `formatTable`
(`L4Factoidal.RDF.mediaTypeOf`, `registeredExtensionOf`; the table that
`syntaxFor` reads, https://github.com/danbri/factoidal/issues/1053). A row that
is not an RDF syntax with a W3C registration has none. -/
def formatRegistration (name : String) : List String × List String :=
  match L4Factoidal.RDF.formatOfLabel name with
  | some f => ([L4Factoidal.RDF.mediaTypeOf f], [L4Factoidal.RDF.registeredExtensionOf f])
  | none => ([], [])

/-- `datasetFormats()` — `formatTable` as JSON, each row with its
`mediaTypes` and `extensions` (`formatRegistration`). -/
def datasetFormats : IO String :=
  pure (okWith [("formats", .array (formatTable.map fun (n, r11, r12, w11, w12, eng) =>
    let (mts, exts) := formatRegistration n
    Json.object [("name", .string n), ("read11", .bool r11), ("read12", .bool r12),
                 ("write11", .bool w11), ("write12", .bool w12), ("engine", .string eng),
                 ("mediaTypes", .array (mts.map Json.string)),
                 ("extensions", .array (exts.map Json.string))]))])

#guard formatRegistration "turtle" == (["text/turtle"], [".ttl"])
#guard formatRegistration "rdfc" == ([], [])
-- Every RDF syntax of the registrations is a row of the table, under its label.
#guard [L4Factoidal.RDF.RdfFormat.nt, .turtle, .nquads, .trig, .rdfxml, .jsonld].all fun f =>
  formatTable.any (·.1 == L4Factoidal.RDF.formatLabel f)

/-- The handle's own prefixes as the renderer's (namespace, `label:`) pairs. -/
private def handlePrefixTable (od : OpenDataset) : PrefixTable :=
  od.prefixes.map fun (label, iri) => (iri, label ++ ":")

/-- Why a writer op refuses a dataset with an IRI that is not an absolute IRI:
no reader of the engine reads the text a writer would write for it
(https://github.com/danbri/factoidal/issues/1057). -/
def unwritableIri (v : String) : String :=
  s!"{invalidIriMessage v}; no reader reads the text a writer would write for it"

/-- `datasetSerialize(handle, formatTag)` — canonical N-Quads, or Turtle in
which the handle's own prefixes (the ones `datasetOpen` recorded) name their
namespaces; named graphs are flattened into the default graph on the turtle
path. -/
def datasetSerialize (h formatTag : String) : IO String :=
  withHandle h fun od =>
    let ds := od.ds
    match firstInvalidIri? ds with
    | some v => pure (errJson s!"datasetSerialize: {unwritableIri v}")
    | none =>
    match formatTag.toLower with
    | "" | "nquads" | "nq" | "n-quads" =>
        match handleCanonicalNQuadsWriter.run od.writeMode {} ds with
        | .error e => pure (errJson s!"datasetSerialize: {e}")
        | .ok text => pure (okWith [("nquads", .string text)])
    | "turtle" | "ttl" =>
        match (handleWriter .turtle).run od.writeMode { prefixes := handlePrefixTable od } ds with
        | .error e => pure (errJson s!"datasetSerialize: {e}")
        | .ok text => pure (okWith [("turtle", .string text)])
    | _ =>
        match handleWriterText formatTag ds od.writeMode with
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
    match firstInvalidIri? ds with
    | some v => pure (errJson s!"datasetSerializeWith: {unwritableIri v}")
    | none =>
    match formatTag.toLower with
    | "" | "nquads" | "nq" | "n-quads" =>
        match handleCanonicalNQuadsWriter.run od.writeMode {} ds with
        | .error e => pure (errJson s!"datasetSerializeWith: {e}")
        | .ok text => pure (okWith [("nquads", .string text)])
    | "turtle" | "ttl" =>
        match turtleOptionsOfJson (handlePrefixTable od) optionsJson with
        | .error msg => pure (errJson msg)
        | .ok opts =>
            match (handleWriter .turtle).run od.writeMode opts ds with
            | .error e => pure (errJson s!"datasetSerializeWith: {e}")
            | .ok text => pure (okWith [("turtle", .string text)])
    | _ =>
        match handleWriterText formatTag ds od.writeMode with
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
    missingHandle h

/-! ## Ops that keep the data in the store (issue 882 item 1) -/

/-- Store a certified dataset under a new handle and answer the `datasetOpen`
envelope. -/
def storeNewCertified (data : CertifiedDataset) (prefixes : List (String × String) := [])
    (extra : List (String × Json) := []) : IO String := do
  let n ← handleCounter.modifyGet fun n => (n + 1, n + 1)
  let h := s!"h{n}"
  handleTable.modify (·.insert h (openDataset data prefixes))
  pure (okWith ([("handle", .string h),
                ("count", .number (toString (datasetQuadCount data.val))),
                ("prefixes", prefixesJson prefixes)] ++ extra))

/-- Store `ds` under a new handle: its set of quads (`Dataset.certify`). -/
def storeNewHandle (ds : Dataset) (prefixes : List (String × String) := [])
    (extra : List (String × Json) := []) : IO String :=
  storeNewCertified ds.certify prefixes extra

/-- The stored dataset of `h`, or `none` when the handle is not open. -/
def lookupHandleDataset (h : String) : IO (Option (Dataset × List (String × String))) := do
  pure (((← handleTable.get)[h]?).map fun od => (od.ds, od.prefixes))

/-- Run `f` on the stored dataset of `h`; an unknown handle is the shared error. -/
def withHandleDataset (h : String) (f : Dataset → List (String × String) → IO String) :
    IO String := do
  match ← lookupHandleDataset h with
  | none => missingHandle h
  | some (ds, prefixes) => f ds prefixes

/-- `datasetClone(handle)` — a new handle holding the same dataset and
prefixes; an update of one handle leaves the other unchanged. -/
def datasetClone (h : String) : IO String :=
  withHandle h fun od => storeNewCertified od.data od.prefixes

/-- `datasetCanonicalize(handle)` — `canonicalizeOf` of the stored dataset:
the envelope `canonicalizeToNQuads` answers on its canonical N-Quads. -/
def datasetCanonicalize (h : String) : IO String :=
  withHandleDataset h fun ds _ => pure (canonicalizeOf ds)

/-- `datasetCanonicalHash(handle)` — `canonicalHashOf` of the stored dataset:
`{"ok":true,"hash":"<64 hex>","algorithm":"sha256"}`, the SHA-256 of the
canonical N-Quads `datasetCanonicalize` answers
(https://github.com/danbri/factoidal/issues/1040). -/
def datasetCanonicalHash (h : String) : IO String :=
  withHandleDataset h fun ds _ => pure (canonicalHashOf ds)

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

/-- `datasetSparqlRlInfer(handle, rulesText)` — SPARQL 1.2 RL `infer`: a new
handle whose default graph is the inference graph (the triples the rule set
derives, data-block triples included, that are not in the default graph of
the stored dataset). The clock is read once, so every `NOW()` of the
evaluation has one value. A rule set with `IMPORTS` is refused: this op has
no document loader. -/
def datasetSparqlRlInfer (h rules : String) : IO String := do
  let now ← nowDateTime
  withHandleDataset h fun ds prefixes =>
    match datasetForOps .rdf12 ds with
    | .error e => pure (errJson s!"sparqlRlInfer(data): {fmtParseError e}")
    | .ok d =>
      match L4Factoidal.SPARQLRL.inferText rules d.default none none { now := some now } with
      | .error e => pure (errJson s!"sparqlRlInfer: {e}")
      | .ok g => storeNewHandle { default := g, named := [] } prefixes

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
`formatOfContent`; Turtle, TriG and N-Quads are read in RDF 1.2 mode
(`turtle12`, `trig12`, `nquads12`), which also reads every RDF 1.1 document. -/
def detectFormat (text : String) : IO String :=
  let tag := match L4Factoidal.RDF.formatOfContent text with
    | .jsonld => "jsonld"
    | .rdfxml => "rdfxml"
    | .trig => "trig12"
    | .nquads => "nquads12"
    | _ => "turtle12"
  pure (okWith [("format", .string tag)])


/-! ## RDF/JS DatasetCore: add, delete, match (issue 882)

A quad pattern is a JSON array of four strings, subject, predicate, object,
graph. `""` leaves the position unbound; otherwise the string is the
N-Triples (N-Quads) form of the term, and for the graph `"DEFAULT"` names the
default graph. Matching uses the stored dataset's indexes
(`LawfulStore.search` of the handle's `LawfulDataset`, the record
`indexedDatasetBackend`). -/

/-- The term an N-Triples token denotes, read through the N-Quads reader in
RDF 1.2 mode: the token is placed at position `pos` (0 subject, 1 predicate,
2 object, 3 graph) of a line whose other positions are fixed IRIs. -/
def termOfToken (pos : Nat) (tok : String) : Option (Option Subject × Option WfIri × Option Term × Option Subject) :=
  let fill := ["<urn:x:s>", "<urn:x:p>", "<urn:x:o>"]
  let parts := (fill.set pos tok) ++ (if pos == 3 then [tok] else [])
  match L4Factoidal.Dataflow.readNQuadsText .rdf12 (String.intercalate " " parts ++ " .\n") with
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
  let L := od.backendThunk.get
  let be : DatasetBackend := L.backend
  let wantDefault := match pat.graph with | none | some none => true | _ => false
  let dflt := if wantDefault then L.default.search pat.bound else []
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

/-! ### Match by value (https://github.com/danbri/factoidal/issues/1052)

The ops `datasetMatch`, `datasetMatchCount` and `datasetDeleteQuadsJson` take
an optional last argument, an options object. `{"match":"value"}` matches the
object position by value: a literal in the pattern matches each object literal
that is the same term or has the same value
(`L4Factoidal.SPARQL.valueMatches`: SPARQL 1.1 `=`, sections 17.3 and
17.4.1.7). Every other position, and an object that is not a literal, matches
by term. `{"match":"term"}`, `{}` or no argument is the term match (RDF 1.1
Concepts section 3.6, SPARQL 1.1 section 18.3): it does not change.

The candidates come from the value index (`OpenDataset.valueIndex`): the
literals filed under the probe keys of the pattern literal. Each kept
candidate is one indexed term match, so the cost is the number of candidates,
not the size of the dataset. -/

/-- The match mode of an options argument: `true` for `{"match":"value"}`.
An empty argument is the term match. -/
def matchByValueOf (who optionsJson : String) : Except String Bool :=
  if optionsJson.trimAscii.isEmpty then .ok false
  else match parseJson? optionsJson with
    | some (.object fields) =>
        match fields.find? (fun (k, _) => k != "match") with
        | some (k, _) => .error s!"{who}: unknown option '{k}'. Known options: match"
        | none =>
          match fields.lookup "match" with
          | none | some .null => .ok false
          | some (.string "term") => .ok false
          | some (.string "value") => .ok true
          | some v => .error s!"{who}: match must be 'term' or 'value' (got {v.toString})"
    | _ => .error s!"{who}: options must be a JSON object"

/-- The quads of two match results: the default graphs, and the named graphs
merged by name. -/
def unionMatches (a b : Dataset) : Dataset :=
  let named := b.named.foldl (fun acc ng =>
    if acc.any (·.name == ng.name) then
      acc.map fun x => if x.name == ng.name then { x with graph := x.graph ++ ng.graph } else x
    else acc ++ [ng]) a.named
  { default := a.default ++ b.default, named }

/-- The object literals of `od` that match the literal `q` by value, from the
value index. A literal is filed under at most one of the probe keys of `q`
(`L4Factoidal.SPARQL.storeKeys`), so no candidate comes twice. -/
def valueCandidates (od : OpenDataset) (q : WfLiteral) : Array WfLiteral :=
  let idx := od.valueIndex.get
  let cands := (L4Factoidal.SPARQL.probeKeys q.val).foldl (fun acc k => acc ++ idx.getD k #[]) #[]
  cands.filter (L4Factoidal.SPARQL.valueMatches · q)

/-- The quads of `od` that match `pat`, the object by value when it is a literal. -/
def valueMatchDataset (od : OpenDataset) (pat : QuadPattern) : Dataset :=
  match pat.bound.o with
  | some (.literal q) =>
      (valueCandidates od q).foldl (fun acc c =>
        unionMatches acc (matchDataset od { pat with bound := { pat.bound with o := some (.literal c) } }))
        Dataset.empty
  | _ => matchDataset od pat

/-- `matchDataset`, or `valueMatchDataset` when `byValue`. -/
def matchDatasetBy (byValue : Bool) (od : OpenDataset) (pat : QuadPattern) : Dataset :=
  if byValue then valueMatchDataset od pat else matchDataset od pat

/-- `datasetMatch(handle, patternJson[, optionsJson])` — the matching quads under
a new handle. -/
def datasetMatchWith (h patternJson optionsJson : String) : IO String := do
  let tbl ← handleTable.get
  match tbl[h]? with
  | none => missingHandle h
  | some od =>
    match matchByValueOf "datasetMatch" optionsJson with
    | .error e => pure (errCoded "option.invalid-value" e)
    | .ok byValue =>
      match quadPatternOf patternJson with
      | none => pure (errJson s!"datasetMatch: not a quad pattern: {patternJson}")
      | some pat => storeNewHandle (matchDatasetBy byValue od pat) od.prefixes

def datasetMatch (h patternJson : String) : IO String := datasetMatchWith h patternJson ""

/-- `datasetMatchCount(handle, patternJson[, optionsJson])` — `{"ok":true,"count":N}`,
the number of matching quads, with no new handle. -/
def datasetMatchCountWith (h patternJson optionsJson : String) : IO String := do
  let tbl ← handleTable.get
  match tbl[h]? with
  | none => missingHandle h
  | some od =>
    match matchByValueOf "datasetMatchCount" optionsJson with
    | .error e => pure (errCoded "option.invalid-value" e)
    | .ok byValue =>
      match quadPatternOf patternJson with
      | none => pure (errJson s!"datasetMatchCount: not a quad pattern: {patternJson}")
      | some pat => pure (okWith [("count", .number (toString (datasetQuadCount (matchDatasetBy byValue od pat))))])

def datasetMatchCount (h patternJson : String) : IO String := datasetMatchCountWith h patternJson ""

/-- The quads of an N-Quads text as SPARQL Update quads. A graph named by a
blank node has no Update quad form and is refused. -/
def updateQuadsOf (nq : String) : Except String (List (Option WfIri × Triple)) := do
  let ds ← (L4Factoidal.Dataflow.readNQuadsText .rdf12 nq).mapError fmtParseError
  let named ← ds.named.mapM fun ng =>
    match ng.name with
    | .iri i => .ok (ng.graph.map fun t => ((some i : Option WfIri), t))
    | .bnode _ => .error "a quad in a graph named by a blank node cannot be added or deleted here"
  pure (ds.default.map (fun t => ((none : Option WfIri), t)) ++ named.flatten)

/-- Replace the stored dataset of `h` with `f` of it; answers the new count. -/
private def changeHandle (who h nq : String)
    (f : CertifiedDataset → List (Option WfIri × Triple) → CertifiedDataset) : IO String := do
  let tbl ← handleTable.get
  match tbl[h]? with
  | none => missingHandle h
  | some od =>
    match updateQuadsOf nq with
    | .error e => pure (errJson s!"{who}: {e}")
    | .ok qs =>
      let next := openDataset (f od.data qs) od.prefixes od.readMode
      handleTable.modify (·.insert h next)
      pure (okWith [("count", .number (toString (datasetQuadCount next.ds)))])

/-- `datasetAddQuads(handle, nquads)` — add the quads (set semantics), as
INSERT DATA does (`Dataset.insertQuads`). Blank-node labels are kept as
written, so a label the dataset holds names the same node. -/
def datasetAddQuads (h nq : String) : IO String :=
  changeHandle "datasetAddQuads" h nq CertifiedDataset.insertQuads

/-- `datasetDeleteQuads(handle, nquads)` — remove the quads
(`Dataset.deleteQuads`). -/
def datasetDeleteQuads (h nq : String) : IO String :=
  changeHandle "datasetDeleteQuads" h nq CertifiedDataset.deleteQuads

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

/-- The first `{"type":"uri","value":v}` member in the worklist whose `v` is
not an IRI (RDF 1.2 Concepts §3.2), visiting at most `fuel` JSON values. One
frame for any input: a worklist, never one frame per nesting level. -/
def badIriLoop : Nat → List Json → Option String
  | 0, _ => none
  | _ + 1, [] => none
  | n + 1, j :: rest =>
      match j with
      | .object fields =>
          if j.getString? "type" == some "uri" then
            match j.getString? "value" with
            | some v => if isIri v && isAbsoluteIri v then badIriLoop n rest else some v
            | none => badIriLoop n rest
          else badIriLoop n (fields.map (·.2) ++ rest)
      | .array items => badIriLoop n (items ++ rest)
      | _ => badIriLoop n rest

#guard badIriLoop 100 [Json.array [.object [("type", .string "uri"), ("value", .string "a b")]]]
  == some "a b"
#guard badIriLoop 100 [Json.array [.object [("type", .string "uri"), ("value", .string "http://e/a")]]]
  == none

/-- Why `x` is not a quad: an invalid IRI is named (`term.invalid-iri`), any
other shape is `term.invalid`. -/
def notAQuadMessage (x : Json) : String :=
  match badIriLoop 10000 [x] with
  | some v => s!"invalid IRI '{v}' in quad: {x.toString}"
  | none => s!"not a quad: {x.toString}"

/-- Decode each quad, one frame for any number of quads. -/
def jsonQuadsLoop : List Json → Array TermJson.Quad → Except String (List TermJson.Quad)
  | [], acc => .ok acc.toList
  | x :: r, acc =>
      match TermJson.decodeQuad x with
      | some q =>
          -- RDF 1.2 Concepts section 3.2 (https://github.com/danbri/factoidal/issues/1057).
          match (quadIris q.1 q.2).find? (fun v => !isAbsoluteIriFast v) with
          | some v => .error s!"{invalidIriMessage v} in quad: {x.toString}"
          | none => jsonQuadsLoop r (acc.push q)
      | none => .error (notAQuadMessage x)

/-- Each quad as an Update quad, one frame for any number of quads. -/
def updateQuadsLoop : List TermJson.Quad → Array (Option WfIri × Triple) →
    Except String (List (Option WfIri × Triple))
  | [], acc => .ok acc.toList
  | q :: r, acc =>
      match updateQuadOfJsonQuad q with
      | .ok u => updateQuadsLoop r (acc.push u)
      | .error e => .error e

/-- The quads of a JSON array of `TermJson` quads. -/
def jsonQuadsOf (text : String) : Except String (List TermJson.Quad) := do
  let j ← match parseJson? text with
    | some j => .ok j
    | none => .error "not a JSON document"
  match j with
  | .array xs => jsonQuadsLoop xs #[]
  | _ => .error "expected a JSON array of quads"

/-- Optional natural-number member of an options object. -/
private def natMember (opts : Option Json) (k : String) : Option Nat :=
  (opts.bind (·.field? k)).bind fun
    | .number n => n.toNat?
    | _ => none

/-- `datasetQuadsJson(handle, optsJson)` — the quads of `quadPage` as
`TermJson` quads: `{"ok":true,"total":N,"offset":O,"quads":[…]}`. `optsJson`
members `offset` (default 0), `limit` (default all) and `compact`: with
`"compact":true` the answer is `"terms":[…]` (each distinct term once) and
`"ixs":[[i,…],…]` (each quad as indices into `terms`, subject, predicate,
object, graph), certified by `TermJson.compactCertified`. The table has one
entry per RDF term and writes language tags in lower case (RDF 1.1 Concepts
section 3.3; https://github.com/danbri/factoidal/issues/977). The order is the
line order of `datasetSerialize` N-Quads (`TermJson.toCanonicalNQuads_eq_quadList`). -/
def datasetQuadsJson (h optsJson : String) : IO String :=
  withHandleDataset h fun ds _ =>
    let opts := if optsJson == "" then none else parseJson? optsJson
    let qs := TermJson.Dataset.quadList ds
    let off := (natMember opts "offset").getD 0
    let lim := (natMember opts "limit").getD qs.length
    let page := (qs.drop off).take lim
    let compact := ((opts.bind (·.field? "compact")).map fun | .bool b => b | _ => false).getD false
    let head := [("total", Json.number (toString qs.length)), ("offset", .number (toString off))]
    match (if compact then TermJson.compactCertified page else none) with
    | some (tbl, ixs) =>
        -- `TermJson.compactCertified_sound`: the indices read back as `page`
        -- with its language tags in lower case;
        -- each term is the text of `encodeTerm` (`TermJson.termText_eq`)
        let termsText := tbl.foldl (fun (acc : String) t =>
          (if acc.isEmpty then acc else acc ++ ",") ++ TermJson.termText t) ""
        let ixText := ixs.foldl (fun (acc : String) ix =>
          (if acc.isEmpty then acc else acc ++ ",") ++ "[" ++
            (ix.foldl (fun (a : String) i => (if a.isEmpty then a else a ++ ",") ++ toString i) "") ++ "]") ""
        pure ("{\"ok\":true,\"total\":" ++ toString qs.length ++ ",\"offset\":" ++ toString off ++
          ",\"terms\":[" ++ termsText ++ "],\"ixs\":[" ++ ixText ++ "]}")
    | none => pure (okWith (head ++ [("quads", .array (page.map TermJson.encodeQuad))]))

/-- `datasetQuadsBin(handle, optsJson)` — the quads of `quadPage` as ONE byte
region (`l4_call_blob_io`), in the layout of `QuadsBin.binSpec`: the distinct
terms in the term codec of DLOG version 2 and each quad as four u32 indices.
The envelope is `{"ok":true,"total":N,"offset":O,"count":C}`. `optsJson`
members `offset` (default 0) and `limit` (default all), as `datasetQuadsJson`.
`QuadsBin.decodeBin_quadsBin`: the region reads back as exactly the page with
its language tags in lower case (one table entry per RDF term, issue 977), in
the line order of `datasetSerialize` N-Quads. A page the region cannot hold
(a string of 2^32 bytes or more) is refused; `datasetQuadsJson` serves it.
https://github.com/danbri/factoidal/issues/900 -/
def datasetQuadsBin (h optsJson : String) : IO (String × ByteArray) := do
  match ← lookupHandleDataset h with
  | none => do pure (← missingHandle h, ByteArray.empty)
  | some (ds, _) =>
    let opts := if optsJson == "" then none else parseJson? optsJson
    -- `QuadsBin.quadPage_eq`, `QuadsBin.quadCount_eq`: the page and the count
    -- of `Dataset.quadList`, with no whole quad list built.
    let n := QuadsBin.quadCount ds
    let off := (natMember opts "offset").getD 0
    let lim := (natMember opts "limit").getD n
    let page := QuadsBin.quadPage ds off lim
    match QuadsBin.quadsBin page with
    | some b =>
        pure ("{\"ok\":true,\"total\":" ++ toString n ++ ",\"offset\":" ++ toString off ++
          ",\"count\":" ++ toString page.length ++ "}", b)
    | none => pure (errJson "datasetQuadsBin: a term string of 2^32 bytes or more; use datasetQuadsJson",
        ByteArray.empty)

private def changeHandleJson (who h text : String)
    (f : CertifiedDataset → List (Option WfIri × Triple) → CertifiedDataset) : IO String := do
  match (← handleTable.get)[h]? with
  | none => missingHandle h
  | some od =>
    match jsonQuadsOf text >>= (updateQuadsLoop · #[]) with
    | .error e => pure (errJson s!"{who}: {e}")
    | .ok qs =>
      let next := openDataset (f od.data qs) od.prefixes od.readMode
      handleTable.modify (·.insert h next)
      pure (okWith [("count", .number (toString (datasetQuadCount next.ds)))])

/-- `datasetAddQuadsJson(handle, quadsJson)` — `datasetAddQuads` with the quads
given as `TermJson` quads. -/
def datasetAddQuadsJson (h quadsJson : String) : IO String :=
  changeHandleJson "datasetAddQuadsJson" h quadsJson CertifiedDataset.insertQuads

/-- `datasetDeleteQuadsJson(handle, quadsJson)` — `datasetDeleteQuads` with the
quads given as `TermJson` quads. -/
def datasetDeleteQuadsJson (h quadsJson : String) : IO String :=
  changeHandleJson "datasetDeleteQuadsJson" h quadsJson CertifiedDataset.deleteQuads

/-- The quads of `od` that a quad to delete names, by value: a quad whose
object is a literal names each stored quad of the same subject, predicate and
graph whose object matches it by value (`valueMatchDataset`); any other quad
names itself. -/
def valueDeleteQuads (od : OpenDataset) (qs : List (Option WfIri × Triple)) :
    List (Option WfIri × Triple) :=
  qs.flatMap fun (g, t) =>
    match t.o with
    | .literal _ =>
        let pat : QuadPattern :=
          { bound := { s := some t.s, p := some t.p, o := some t.o },
            graph := some (g.map Subject.iri) }
        let m := valueMatchDataset od pat
        m.default.map (fun u => (g, u)) ++ m.named.flatMap (fun ng => ng.graph.map fun u => (g, u))
    | _ => [(g, t)]

/-- `datasetDeleteQuadsJson(handle, quadsJson, optionsJson)` — with
`{"match":"value"}`, delete every stored quad that a given quad names by value
(`valueDeleteQuads`); else the term delete. -/
def datasetDeleteQuadsJsonWith (h quadsJson optionsJson : String) : IO String := do
  match matchByValueOf "datasetDeleteQuadsJson" optionsJson with
  | .error e => pure (errCoded "option.invalid-value" e)
  | .ok false => datasetDeleteQuadsJson h quadsJson
  | .ok true =>
    match (← handleTable.get)[h]? with
    | none => missingHandle h
    | some od =>
      match jsonQuadsOf quadsJson >>= (updateQuadsLoop · #[]) with
      | .error e => pure (errJson s!"datasetDeleteQuadsJson: {e}")
      | .ok qs =>
        let next := openDataset (CertifiedDataset.deleteQuads od.data (valueDeleteQuads od qs))
          od.prefixes od.readMode
        handleTable.modify (·.insert h next)
        pure (okWith [("count", .number (toString (datasetQuadCount next.ds)))])

/-- Store `data` as the new state of the handle `h` (its prefixes and reader
mode kept, the indexes and the value index built again on first use); the new
state. For the ops of other modules that change a handle
(`Wasm/Ops/Collections.lean`). -/
def replaceHandleData (h : String) (od : OpenDataset) (data : CertifiedDataset) : IO OpenDataset := do
  let next := openDataset data od.prefixes od.readMode
  handleTable.modify (·.insert h next)
  pure next

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

/-- The case-insensitive names of `datasetClosure`'s regimes. -/
def closureRegimeAliases : List (String × String) :=
  [ ("rdfs", "rdfs"), ("owl-rl", "owl-rl"), ("owlrl", "owl-rl"), ("owl_rl", "owl-rl"),
    ("rho-df", "rho-df"), ("rhodf", "rho-df"), ("core-rdfs", "rho-df"),
    ("rdfs-plus", "rdfs-plus"), ("rdfsplus", "rdfs-plus") ]

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

/-- The suffixes of the syntaxes that the pack which reads the whole document
(`sbm11PackFiles`, `Wasm/Ops/Sbm11Pack.lean`) reads beyond `packSuffixes`,
each with its `RDF.formatOfLabel` label. -/
def packWholeSuffixes : List (String × String) :=
  [ (".rdf", "rdfxml"), (".owl", "rdfxml"), (".xml", "rdfxml"), (".rdfxml", "rdfxml"),
    (".jsonld", "jsonld"), (".json-ld", "jsonld"), (".json", "jsonld") ]

/-- Every name table a host validates arguments against, so no host keeps its
own copy (https://github.com/danbri/factoidal/issues/894 item 5). -/
def engineTablesJson : Json :=
  .object
    [ ("parseFormats", strMap parseFormatNames)
    , ("writerFormats", strMap writerFormatNames)
    , ("rawDataFormats", strMap rawDataFormatNames)
    , ("entailRegimes", .array (entailRegimeNames.map Json.string))
    , ("entailAliases", strMap entailRegimeAliases)
    -- a regime name with one of these prefixes (compared without case) is
    -- refused with the message, WHO and REGIME filled in by the host
    , ("refusedRegimePrefixes", .object [("x-ikl", .string (iklRefusal "WHO" "REGIME"))])
    , ("closureRegimes", .array (closureRegimes.map Json.string))
    , ("closureAliases", strMap closureRegimeAliases)
    , ("queryOutputs", .array (["json", "csv", "tsv", "xml", "table", "ntriples"].map Json.string))
    , ("packSyntaxes", .array (packSyntaxNames.map Json.string))
    , ("packSuffixes", strMap packSuffixes)
    , ("packUnsupportedSuffixes", strMap packUnsupportedSuffixes)
    , ("packWholeSuffixes", strMap packWholeSuffixes) ]

/-- `engineTables()` — `engineTablesJson`, plus `errorCodes`: each declared
error code with its specification section and summary
(`Wasm/Ops/ErrorModel.lean`). -/
def engineTables : IO String :=
  let codes := errorCodeTable.map fun c =>
    Json.object ([("code", Json.string c.code), ("summary", .string c.summary)]
      ++ (match c.spec with | some u => [("spec", Json.string u)] | none => []))
  pure (okWith [("tables", engineTablesJson), ("errorCodes", .array codes),
                ("errorModelExemptOps", .array (uncodedOps.map Json.string))])

/-! ## Argument values of the public API (https://github.com/danbri/factoidal/issues/882 item 4)

The host sends the name of a public function and the options object it was
given; the engine decides whether every key is one the function takes and
whether every enumerated value is in its table. A host keeps no copy of either
list. -/

/-- The value domain of an option. -/
inductive OptionDomain where
  | any
  | parseFormat
  | writerFormat
  | rawFormat
  | entail
  | output
  | version
  | oneOf (values : List String)

private def parseOpts : List (String × OptionDomain) :=
  [("format", .parseFormat), ("baseIRI", .any)]

private def serializeOpts : List (String × OptionDomain) :=
  [ ("format", .writerFormat), ("version", .version), ("prefixes", .any)
  , ("literalShorthand", .any), ("useNativeTypes", .any), ("useRdfType", .any)
  , ("rdfDirection", .any), ("rdfstar", .any) ]

/-- The options each public function takes, with their value domains. A
positional mode argument is checked as the option of its name (`mode`,
`sourceKind`). -/
def apiOptionTable : List (String × List (String × OptionDomain)) :=
  [ ("parse", parseOpts ++ [("lenient", .any), ("maxErrors", .any), ("rdfstar", .any)])
  , ("openDataset", parseOpts), ("registerServiceEndpoint", parseOpts)
  , ("update", parseOpts), ("canonicalize", parseOpts), ("isomorphic", parseOpts)
  , ("shaclValidate", parseOpts), ("shexValidate", parseOpts), ("closure", parseOpts)
  , ("sparqlRlInfer", parseOpts)
  , ("coreRdfsCheck", parseOpts), ("tableauMaterialise", parseOpts)
  , ("tableauDlInconsistent", parseOpts), ("rifEval", parseOpts)
  , ("rmlMap", parseOpts ++ [("sourceKind", .oneOf ["json", "csv"])])
  , ("owlClosure", parseOpts ++ [("mode", .oneOf ["rdfs", "owl-rl"])])
  , ("owlIsConsistent", parseOpts ++ [("fuel", .any)])
  , ("owlEntails", parseOpts ++ [("fuel", .any)])
  , ("query", parseOpts ++ [("entail", .entail), ("sparql12", .any), ("version", .version),
                            ("output", .output)])
  , ("serialize", serializeOpts ++ [("inputFormat", .parseFormat), ("baseIRI", .any)])
  , ("csvwToRdf", [("mode", .any), ("base", .any), ("url", .any)])
  , ("jsonldToRdf", [("base", .any), ("rdfDirection", .any), ("expandContext", .any),
                     ("processingMode", .any), ("rdfstar", .any)])
  , ("jsonldFromRdf", [("useNativeTypes", .any), ("useRdfType", .any),
                       ("rdfDirection", .any), ("rdfstar", .any)] ++ parseOpts)
  , ("queryRaw", [("dataFormat", .rawFormat), ("entail", .entail), ("output", .output)])
  , ("Dataset.query", [("sparql12", .any), ("version", .version), ("entail", .entail),
                       ("output", .output)])
  , ("Dataset.update", [])
  , ("Dataset.closure", [("regime", .oneOf ["rdfs", "owl-rl", "rho-df", "rdfs-plus"])])
  , ("Dataset.validateShacl", parseOpts)
  , ("Dataset.validateShex", [("focus", .any), ("shape", .any)])
  , ("Dataset.serialize", serializeOpts)
  , ("Dataset.toString", serializeOpts)
  -- https://github.com/danbri/factoidal/issues/1052: match the object by value.
  , ("Dataset.match", [("match", .oneOf ["term", "value"])])
  , ("Dataset.has", [("match", .oneOf ["term", "value"])])
  , ("Dataset.delete", [("match", .oneOf ["term", "value"])]) ]

private def queryOutputNames : List String := ["json", "csv", "tsv", "xml", "table", "ntriples"]

/-- The refusal of `value` for option `key` of `who`, or `none`. -/
def optionValueRefusal (who key value : String) : OptionDomain → Option String
  | .any => none
  | .parseFormat =>
      if (parseFormatNames.lookup value.toLower).isSome then none
      else some (errCoded "format.unknown"
        s!"{who}: unknown format '{value}'. Expected one of: {", ".intercalate (parseFormatNames.map (·.1))}")
  | .writerFormat =>
      if (writerFormatNames.lookup value.toLower).isSome then none
      else some (errCoded "format.unknown"
        s!"{who}: unknown format '{value}'. Known formats: {", ".intercalate (writerFormatNames.map (·.2)).eraseDups}")
  | .rawFormat =>
      if (rawDataFormatNames.lookup value.toLower).isSome then none
      else some (errCoded "format.unknown"
        s!"{who}: unknown dataFormat '{value}'. Expected one of: {", ".intercalate (rawDataFormatNames.map (·.1))}")
  | .entail =>
      if value.toLower.startsWith "x-ikl" then some (errCoded "regime.refused" (iklRefusal who value))
      else if entailRegimeNames.contains value then none
      else some (errCoded "option.invalid-value"
        s!"{who}: {key} must be one of {", ".intercalate entailRegimeNames} (got '{value}')")
  | .output =>
      if queryOutputNames.contains value then none
      else some (errCoded "option.invalid-value"
        s!"{who}: {key} must be one of {", ".intercalate queryOutputNames} (got '{value}')")
  | .version =>
      if value == "1.1" || value == "1.2" then none
      else some (errCoded "option.invalid-value" s!"{who}: {key} must be '1.1' or '1.2' (got '{value}')")
  | .oneOf values =>
      let v := (closureRegimeAliases.lookup value.toLower).getD value.toLower
      if values.contains v then none
      else some (errCoded "option.invalid-value"
        s!"{who}: {key} must be one of {", ".intercalate values} (got '{value}')")

/-- Options that cannot be combined, given the string values of `fields`. -/
def optionConflict (who : String) (fields : List (String × Json)) : Option String :=
  let str (k : String) : Option String := match fields.lookup k with
    | some (.string v) => some v
    | _ => none
  -- a key the caller set to `undefined` arrives as `null`: not given
  let present (k : String) : Bool := match fields.lookup k with
    | some .null | none => false
    | some _ => true
  if ["query", "Dataset.query"].contains who then
    let rdf12 := str "sparql12" == some "true" || str "version" == some "1.2"
    let rawPath := present "output" || (match str "entail" with
      | some e => e != "none" | none => false)
    if rdf12 && rawPath then
      some (errCoded "option.conflict"
        s!"{who}: entail/output and SPARQL 1.2 cannot be combined; that path reads SPARQL 1.1")
    else none
  else if ["serialize", "Dataset.serialize", "Dataset.toString"].contains who then
    let tag := ((str "format").getD "nquads").toLower
    let writer := (writerFormatNames.lookup tag).getD tag
    if writer != "turtle" && (present "prefixes" || present "literalShorthand") then
      some (errCoded "option.conflict"
        s!"{who}: 'prefixes' and 'literalShorthand' apply to format 'turtle' only")
    else if writer != "jsonld" &&
        (present "useNativeTypes" || present "useRdfType" || present "rdfDirection" ||
         present "rdfstar") then
      some (errCoded "option.conflict"
        s!"{who}: useNativeTypes, useRdfType, rdfDirection, rdfstar apply to format 'jsonld' only")
    else none
  else if who == "parse" && present "rdfstar" then
    -- JSON-LD-star has one reader, the JSON-LD one; no lenient mode
    let fmt := (str "format").map (fun t => (parseFormatNames.lookup t.toLower).getD t.toLower)
    if fmt.isSome && fmt != some "jsonld" then
      some (errCoded "option.conflict" s!"{who}: rdfstar applies to format 'jsonld' only")
    else if str "lenient" == some "true" then
      some (errCoded "option.conflict" s!"{who}: rdfstar and lenient cannot be combined")
    else none
  else none

/-- `apiCheck(who, optionsJson)`: `optionsJson` is the options object the
function was given, each value a string (its JavaScript `String` form) or
`{}` (an object, array or function value), or `null` (`undefined`). Answers `{"ok":true}`, or the first refusal
in key order: `option.unknown`, `format.unknown`, `option.invalid-value` or
`regime.refused`. -/
def apiCheck (who optionsJson : String) : String :=
  match apiOptionTable.lookup who with
  | none => errCoded "option.unknown" s!"apiCheck: no option table for '{who}'"
  | some allowed =>
      match parseJson? optionsJson with
      | some (.object fields) =>
          let refusal := fields.findSome? fun (k, v) =>
            match allowed.lookup k with
            | none => some (errCoded "option.unknown"
                s!"{who}: unknown option '{k}'. Known options: {if allowed.isEmpty then "(none)" else ", ".intercalate (allowed.map (·.1))}")
            | some dom =>
                match v with
                | .string value => optionValueRefusal who k value dom
                | _ => none
          match refusal with
          | some r => r
          | none => (optionConflict who fields).getD (okWith [])
      | _ => errCoded "call.arguments" "apiCheck: optionsJson must be a JSON object"

#guard codeOf? (apiCheck "parse" "{\"bogus\":\"1\"}") == some "option.unknown"
#guard codeOf? (apiCheck "parse" "{\"format\":\"bogus\"}") == some "format.unknown"
#guard codeOf? (apiCheck "parse" "{\"format\":\"TTL\"}") == none
#guard codeOf? (apiCheck "serialize" "{\"format\":\"rdfc\"}") == none
#guard codeOf? (apiCheck "serialize" "{\"format\":\"ttl12\"}") == some "format.unknown"
#guard codeOf? (apiCheck "query" "{\"entail\":\"x-ikl-foo\"}") == some "regime.refused"
#guard codeOf? (apiCheck "query" "{\"entail\":\"RDFS\",\"output\":\"csv\"}") == none
#guard codeOf? (apiCheck "query" "{\"output\":\"pdf\"}") == some "option.invalid-value"
#guard codeOf? (apiCheck "owlClosure" "{\"mode\":\"owlrl\"}") == none
#guard codeOf? (apiCheck "owlClosure" "{\"mode\":\"rho-df\"}") == some "option.invalid-value"
#guard codeOf? (apiCheck "Dataset.update" "{\"x\":null}") == some "option.unknown"
#guard codeOf? (apiCheck "query" "{\"version\":\"1.2\",\"output\":\"csv\"}") == some "option.conflict"
#guard codeOf? (apiCheck "Dataset.serialize" "{\"format\":\"nt\",\"prefixes\":{}}") == some "option.conflict"
#guard codeOf? (apiCheck "Dataset.serialize" "{\"format\":\"ttl\",\"prefixes\":{}}") == none
#guard codeOf? (apiCheck "Dataset.serialize" "{\"format\":\"nt\",\"prefixes\":null}") == none
#guard codeOf? (apiCheck "Dataset.match" "{\"match\":\"value\"}") == none
#guard codeOf? (apiCheck "Dataset.has" "{\"match\":\"values\"}") == some "option.invalid-value"
#guard matchByValueOf "m" "" == .ok false
#guard matchByValueOf "m" "{\"match\":\"value\"}" == .ok true
#guard matchByValueOf "m" "{\"match\":\"term\"}" == .ok false
#guard (matchByValueOf "m" "{\"mode\":\"value\"}").toOption.isNone
#guard (matchByValueOf "m" "[]").toOption.isNone
#guard codeOf? (apiCheck "parse" "{\"format\":\"json-ld\",\"rdfstar\":\"true\"}") == none
#guard codeOf? (apiCheck "parse" "{\"rdfstar\":\"true\"}") == none
#guard codeOf? (apiCheck "parse" "{\"format\":\"ttl\",\"rdfstar\":\"true\"}") == some "option.conflict"
#guard codeOf? (apiCheck "parse" "{\"format\":\"jsonld\",\"rdfstar\":\"true\",\"lenient\":\"true\"}") == some "option.conflict"

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
-- https://github.com/danbri/factoidal/issues/986: a blank-node label outside
-- BLANK_NODE_LABEL is relabelled, a language tag outside LANGTAG is an error that names it.
private def badLabelDs : Dataset :=
  { default := [{ s := .bnode "a b", p := ⟨"http://e/p", by decide⟩, o := .bnode "b1" }], named := [] }
private def badTagDs : Dataset :=
  { default := [{ s := .iri ⟨"http://e/a", by decide⟩, p := ⟨"http://e/p", by decide⟩,
                  o := .literal (Literal.langString "x" "en us") }], named := [] }
#guard match handleWriterText "nquads" badLabelDs with
  | some (.ok t) => t == "_:rrrr0 <http://e/p> _:b1 .\n" | _ => false
#guard ["nquads", "ntriples", "turtle", "trig"].all fun f => match handleWriterText f badTagDs with
  | some (.error e) => (e.splitOn "\"en us\"").length > 1 | _ => false
#guard match handleWriteInput badTagDs with | .error _ => true | .ok _ => false

-- A subtag of 9 or more characters: RDF 1.1 LANGTAG [144s] accepts it, RDF 1.2
-- does not. A document read as RDF 1.1 is written in RDF 1.1 mode
-- (`OpenDataset.writeMode`), so its writers keep the tag; in RDF 1.2 mode they
-- refuse it with an error that names it.
private def longTagDs : Dataset :=
  { default := [{ s := .iri ⟨"http://ex/s", by decide⟩, p := ⟨"http://ex/p", by decide⟩,
                  o := .literal (Literal.langString "v" "abcdefghijk") }], named := [] }
#guard match handleWriteInput longTagDs .rdf11 with | .ok _ => true | .error _ => false
#guard match handleWriteInput longTagDs .rdf12 with
  | .error e => (e.splitOn "\"abcdefghijk\"").length > 1 | .ok _ => false
#guard ["nquads", "ntriples", "turtle", "trig"].all fun f =>
  match handleWriterText f longTagDs .rdf11 with | some (.ok t) => (t.splitOn "abcdefghijk").length > 1 | _ => false
#guard ["nquads", "ntriples", "turtle", "trig"].all fun f =>
  match handleWriterText f longTagDs .rdf12 with | some (.error _) => true | _ => false

end L4Wasm.Ops
