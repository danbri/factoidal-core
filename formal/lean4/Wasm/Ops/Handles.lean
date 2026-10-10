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
per-call N-Quads round trip. -/
def datasetQuery (h sparql : String) : IO String := do
  let extIris ← extSnapshot
  let services ← serviceSnapshot
  withHandle h fun od =>
    pure (queryParsedDatasetWith od.ds (some od.backend) sparql [] extIris services)

/-- `datasetQuery12(handle, sparql)` — `datasetQuery` with the query read by
the SPARQL 1.2 grammar (`queryDataset12IO` in `Wasm/Ops/Query.lean`). The
envelope family is the same; a SPARQL 1.2 term in a 1.1 query is a parse
error of `datasetQuery`, and it is accepted here. -/
def datasetQuery12 (h sparql : String) : IO String := do
  let extIris ← extSnapshot
  let services ← serviceSnapshot
  withHandle h fun od =>
    pure (queryParsedDatasetWith od.ds (some od.backend) sparql [] extIris services .v12)

/-- `datasetUpdate(handle, sparqlUpdate)` — apply the update and
REPLACE the stored dataset (and rebuild its index); answers the new quad
count. On a parse or evaluation error the stored dataset is unchanged. -/
def datasetUpdate (h updateText : String) : IO String :=
  withHandle h fun od =>
    match applyUpdateText od.ds updateText with
    | .error e => pure (errJson e)
    | .ok ds' => do
        handleTable.modify (·.insert h (openDataset ds' od.prefixes))
        pure (okWith [("count", .number (toString (datasetQuadCount ds')))])

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
        pure (errJson s!"datasetSerialize: unknown format tag '{formatTag}' (nquads | turtle)")

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
        pure (errJson
          s!"datasetSerializeWith: unknown format tag '{formatTag}' (nquads | turtle)")

/-- `datasetClose(handle)` — drop the dataset from the store. Closing
an unknown (or already-closed) handle is the shared handle error. -/
def datasetClose (h : String) : IO String := do
  let table ← handleTable.get
  if table.contains h then
    handleTable.set (table.erase h)
    pure (okWith [])
  else
    pure (unknownHandle h)

end L4Wasm.Ops
