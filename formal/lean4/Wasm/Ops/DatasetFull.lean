/-
Wasm.Ops.DatasetFull — the dataset-handle ops of the FULL engine
(https://github.com/danbri/factoidal/issues/882 item 1).

`Wasm/Ops/Handles.lean` holds the store and the handle ops of the core
engine. The ops here call library modules outside the core subset (CSVW, RML,
JSON-LD, ShEx, RIF), so only the full table (`Wasm/Dispatch.lean`) imports
this module. Each op makes or reads a stored dataset, so a host keeps the
data in the engine between two steps and moves no N-Quads text:

  datasetFromCsvw(csv, metadataJson, optsJson)   -> the `datasetOpen` envelope
  datasetFromRml(mappingHandle, source, kind)    -> the `datasetOpen` envelope
  datasetFromJsonLd(text, optsJson)              -> the `datasetOpen` envelope
  datasetToJsonLd(handle, optsJson)              -> the `jsonldFromRdf` envelope
  datasetShexValidate(handle, schema, focus, shape) -> the `shexValidate` envelope
  datasetRifEval(rifXml, handle)
    -> the `datasetOpen` envelope of the saturated graph, with the members
       `inputCount`, `derivedCount` and `fuel` of `rifEval`

Each op is the text op's body (`csvwDataset`, `rmlDataset`, `jsonldDataset`,
`jsonldFromRdfParsed`, `shexValidateParsed`, `rifSaturate`). A stored dataset
an op reads is first normalised as the text op would read its canonical
N-Quads (`datasetForOps`, `withOpsDataset_eq`). A dataset an op makes gets its
own blank-node scope, as `datasetOpen` gives a parsed document.
-/
import Wasm.Ops.Handles
import Wasm.Ops.Formats
import Wasm.Ops.ShExValidate

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-- Store a dataset an op made, in its own blank-node scope. -/
private def storeMade (ds : Dataset) : IO String := do
  storeNewHandle (scopeBnodes (← nextDocumentScope) ds)

/-- The stored dataset of `h`, normalised as the text ops read it. -/
private def withReadDataset (who h : String) (f : Dataset → IO String) : IO String :=
  withHandleDataset h fun ds _ =>
    match datasetForOps .rdf12 ds with
    | .error e => pure (errJson s!"{who}: {fmtParseError e}")
    | .ok d => f d

/-- `datasetFromCsvw(csv, metadataJson, optsJson)` — `csvwToRdf`, stored. -/
def datasetFromCsvw (csv metadataJson optsJson : String) : IO String :=
  match csvwDataset csv metadataJson optsJson with
  | .error e => pure (errJson e)
  | .ok ds => storeMade ds

/-- `datasetFromRml(mappingHandle, source, kind)` — `rmlMap` with the mapping
graph a stored dataset, the result stored. -/
def datasetFromRml (hMapping source kind : String) : IO String :=
  if kind != "json" && kind != "csv" then
    pure (errJson s!"rmlMap: unknown sourceKind '{kind}' (expected 'json' or 'csv')")
  else
  withReadDataset "rmlMap" hMapping fun mapping =>
    match rmlDataset mapping source with
    | .error e => pure (errJson e)
    | .ok ds => storeMade ds

/-- `datasetFromJsonLd(text, optsJson)` — `jsonldToRdf`, stored. -/
def datasetFromJsonLd (text optsJson : String) : IO String :=
  match jsonldDataset text optsJson with
  | .error e => pure (errJson e)
  | .ok ds => storeMade ds

/-- `datasetToJsonLd(handle, optsJson)` — `jsonldFromRdf` of the stored dataset.
An `optsJson` member `"version":"1.1"` refuses a dataset with an RDF 1.2 term. -/
def datasetToJsonLd (h optsJson : String) : IO String :=
  let v11 := ((if optsJson == "" then none else parseJson? optsJson).bind
      (fun j => j.getString? "version")) == some "1.1"
  withReadDataset "jsonldFromRdf" h fun ds =>
    if v11 && !ds.isRdf11 then pure (errJson (rdf11WriterRefusal "JSON-LD"))
    else pure (jsonldFromRdfParsed ds optsJson)

/-- A focus or shape argument: the text form `shexValidate` reads (an IRI or
`_:label`), or a `TermJson` term object, which is written in that form here
so a host sends term components only
(https://github.com/danbri/factoidal/issues/894). -/
def shexNodeArg (s : String) : String :=
  if s.startsWith "{" then
    match (parseJson? s).bind TermJson.decodeSubject with
    | some (.iri i) => i.val
    | some (.bnode b) => "_:" ++ b
    | none => s
  else s

/-- `datasetShexValidate(handle, schema, focus, shape)` — `shexValidate` over
the stored dataset. -/
def datasetShexValidate (h schemaText focus shape : String) : IO String :=
  withReadDataset "shexValidate(data)" h fun ds =>
    pure (shexValidateParsed ds schemaText (shexNodeArg focus) (shexNodeArg shape))

/-- `datasetRifEval(rifXml, handle)` — `rifEval` over the stored dataset; the
saturated graph is stored under a new handle. -/
def datasetRifEval (rifXml h : String) : IO String :=
  withReadDataset "rifEval" h fun ds =>
    match rifSaturate rifXml ds with
    | .error e => pure (errJson e)
    | .ok (premise, saturated) =>
        storeNewHandle { default := saturated, named := [] } []
          [ ("inputCount", .number (toString premise.length))
          , ("derivedCount", .number (toString (saturated.length - premise.length)))
          , ("fuel", .number (toString L4Factoidal.RIF.Saturate.defaultRounds)) ]

end L4Wasm.Ops
