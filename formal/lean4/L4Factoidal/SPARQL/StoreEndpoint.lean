/-
L4Factoidal.SPARQL.StoreEndpoint — a SPARQL 1.1 endpoint over a persisted
Shardborough collection: every decision `factoidal serve` makes about a
request, as total functions with no I/O.

Specs:
  * SPARQL 1.1 Protocol, https://www.w3.org/TR/sparql11-protocol/ (§2.1
    query, §2.2 update, §2.1.4 / §2.2.3 the protocol dataset, §2.1.7 /
    §2.2.4 status codes);
  * SPARQL 1.1 Graph Store HTTP Protocol,
    https://www.w3.org/TR/sparql11-http-rdf-update/;
  * SPARQL 1.1 Service Description §2 ("SPARQL services made available via
    the SPARQL Protocol should return a service description document at the
    service endpoint when dereferenced using the HTTP GET operation without
    any query parameter strings provided"),
    https://www.w3.org/TR/sparql11-service-description/;
  * SPARQL 1.1 Query Results JSON / XML / CSV and TSV formats, and RFC 9110
    §12 proactive negotiation (`HTTP.negotiate`).

What this module adds to `ProtocolService`, `GraphStoreService` and
`ServiceDescription`, which already decide the protocol over an in-memory
store:

  1. ROUTING of one framed request (`HTTP/Wire.lean`) to the query and
     update endpoint, the Graph Store endpoint, or the service description.
  2. The SERIALISED response: the negotiated results format for SELECT and
     ASK, an RDF syntax for CONSTRUCT and DESCRIBE, 406 when the `Accept`
     header admits none of them.
  3. Query evaluation through the INDEXED backend of the served view when
     the query names no dataset of its own, with the reference evaluator as
     the fallback — the routing `Wasm/Ops/Query.lean`'s
     `queryParsedDatasetWith` uses for the store handle, including
     `env.dataset` for EXISTS (CLAUDE.md anti-pattern 34).
  4. PERSISTENCE. An update or a Graph Store write is executed by the
     reference semantics (`SPARQL.Update.applyUpdateIn`,
     `GraphStoreService.serve`) over the served view, and the CHANGE is
     written as one delta-log batch: `datasetDelta old new` is the list of
     `DeltaEntry` values whose replay (`applyDeltaEntries`) turns `old` into
     `new`. Using the reference semantics for the change means WHERE-dependent
     updates are stored too, which `SPARQL.UpdateDelta` (the translation
     `l4block-delta-log` uses) refuses.
  5. The WRITE SCOPE a generation allows. The native readers of an IBK3
     (triples) generation replay and compact the DEFAULT GRAPH only
     (`foldDeltaBatches … none`, layout `…-compacted-default-dlog-v1`), so a
     change to a named graph there is refused with 501 rather than written
     where no other reader would see it. A quad generation (IBK4, IBK5)
     takes every graph; no native reader replays its log yet
     (https://github.com/danbri/factoidal/issues/770).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import Std.Data.HashSet
import L4Factoidal.HTTP.Server
import L4Factoidal.SPARQL.ProtocolService
import L4Factoidal.SPARQL.GraphStoreService
import L4Factoidal.SPARQL.ServiceDescription
import L4Factoidal.SPARQL.ResultsJson
import L4Factoidal.SPARQL.ResultsXml
import L4Factoidal.SPARQL.ResultsCsvTsv
import L4Factoidal.SPARQL.StoreDataset
import L4Factoidal.Storage.QuadDataset
import L4Factoidal.Storage.DeltaLog
import L4Factoidal.Syntax.NQuads
import L4Factoidal.Syntax.TriG
import L4Factoidal.JSON.Serialize

namespace L4Factoidal.SPARQL.StoreEndpoint

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.Protocol
open L4Factoidal.SPARQL.ProtocolService (Payload datasetClauses withProtocolDataset withUsing)
open L4Factoidal.SPARQL.StoreDataset (DatasetBackend indexedDatasetBackend
  runSelectQueryBackendDataset runAskQueryBackendDataset)
open L4Factoidal.Storage (DeltaEntry DeltaBatch)

/-! ## Configuration and the served view -/

/-- Which graphs a generation's delta log may change. -/
inductive WriteScope where
  /-- IBK3: the native readers replay and compact the default graph only. -/
  | defaultGraph
  /-- IBK4 and IBK5: every graph. -/
  | allGraphs
  deriving Repr, DecidableEq

def WriteScope.name : WriteScope → String
  | .defaultGraph => "default-graph"
  | .allGraphs    => "all-graphs"

structure Config where
  /-- The query and update endpoint (Protocol §2). `/query` and `/update`
  are accepted as well (`HTTP.isProtocolPath`). -/
  queryPath : String := "/sparql"
  /-- The Graph Store endpoint; a path under it identifies a graph
  directly (GSP §4.1). -/
  gspPath : String := "/data"
  /-- The URI authority when a request carries no `Host` field. -/
  authority : String := "localhost"
  scope : WriteScope := .allGraphs
  deriving Repr

/-- The dataset a generation and its replayed delta log denote, and the
indexed backend over it. `backend` is `none` when a graph name is a blank
node, which the backend seam cannot represent; queries then take the
reference evaluator, as `storeHandleQuery` does. -/
structure View where
  ds : Dataset
  backend : Option DatasetBackend

def View.of (ds : Dataset) : View :=
  { ds, backend := if Storage.QuadDataset.namesAreIris ds then some (indexedDatasetBackend ds) else none }

/-- What one request does: the response, whether only its header section
is sent (HEAD), and the change to persist. `commit = some (entries, new)`
means: append `entries` to the delta log as one batch, and once the append
is durable, serve `new` and send `response`. -/
structure Outcome where
  response : HTTP.Response
  headOnly : Bool := false
  commit : Option (List DeltaEntry × Dataset) := none

def textResponse (status : Nat) (msg : String) : HTTP.Response :=
  { status, headers := [("content-type", "text/plain; charset=utf-8")], body := msg ++ "\n" }

def text (status : Nat) (msg : String) : Outcome := { response := textResponse status msg }

/-! ## The change as delta-log entries -/

private def tripleSet (g : Graph) : Std.HashSet Triple :=
  g.foldl (fun acc t => acc.insert t) {}

/-- The entries that turn graph `old` into graph `new`, for graph `key`.
A graph that becomes empty is one `clear`, not one tombstone per triple. -/
def graphDelta (key : Option Iri) (old new : Graph) : List DeltaEntry :=
  if new.isEmpty && !old.isEmpty then [.clear key]
  else
    let o := tripleSet old
    let n := tripleSet new
    (old.filter (fun t => !n.contains t)).map (fun t => DeltaEntry.remove t key) ++
    (new.filter (fun t => !o.contains t)).map (fun t => DeltaEntry.add t key)

private def iriNamed (ds : Dataset) : List (WfIri × Graph) :=
  ds.named.filterMap fun ng => match ng.name with
    | .iri i => some (i, ng.graph)
    | .bnode _ => none

private def bnodeNamed (ds : Dataset) : List NamedGraph :=
  ds.named.filter fun ng => match ng.name with
    | .iri _ => false
    | .bnode _ => true

/-- The entries whose replay turns `old` into `new` (`applyDeltaEntries`).
A delta log names a graph by IRI, so a change to a graph named by a blank
node cannot be written; that is an error, never a silently dropped change. -/
def datasetDelta (old new : Dataset) : Except String (List DeltaEntry) := do
  if bnodeNamed old != bnodeNamed new then
    throw "the request changes a graph whose name is a blank node; the delta log names graphs by IRI"
  let oldI := iriNamed old
  let newI := iriNamed new
  let drops := (oldI.filter fun p => !(newI.any (·.1 == p.1))).map fun p => DeltaEntry.drop p.1.val
  let creates := (newI.filter fun p => !(oldI.any (·.1 == p.1))).flatMap fun p =>
    DeltaEntry.create p.1.val :: p.2.map (fun t => DeltaEntry.add t (some p.1.val))
  let changes := newI.flatMap fun p =>
    match oldI.find? (·.1 == p.1) with
    | some q => graphDelta (some p.1.val) q.2 p.2
    | none => []
  pure (graphDelta none old.default new.default ++ drops ++ creates ++ changes)

/-- Replay one entry over a dataset. A graph name that is not an IRI names
nothing, so its entry changes nothing. -/
def applyDeltaEntry (ds : Dataset) (e : DeltaEntry) : Dataset :=
  let withIri (g : Iri) (k : WfIri → Dataset) : Dataset :=
    if h : isIri g then k ⟨g, h⟩ else ds
  match e with
  | .add t none => L4Factoidal.RDF.Dataset.insertQuad ds (none, t)
  | .add t (some g) => withIri g fun i => L4Factoidal.RDF.Dataset.insertQuad ds (some i, t)
  | .remove t none => L4Factoidal.RDF.Dataset.deleteQuad ds (none, t)
  | .remove t (some g) => withIri g fun i => L4Factoidal.RDF.Dataset.deleteQuad ds (some i, t)
  | .clear none => { ds with default := [] }
  | .clear (some g) => withIri g fun i =>
      if L4Factoidal.RDF.Dataset.hasGraph i ds then L4Factoidal.RDF.Dataset.setGraph i [] ds else ds
  | .drop g => withIri g fun i => L4Factoidal.RDF.Dataset.dropGraph i ds
  | .create g => withIri g fun i => L4Factoidal.RDF.Dataset.ensureGraph i ds

def applyDeltaEntries (ds : Dataset) (es : List DeltaEntry) : Dataset :=
  es.foldl applyDeltaEntry ds

/-- Two graphs hold the same triples (order and repetition ignored). -/
def graphSetEq (a b : Graph) : Bool := a.all (b.mem ·) && b.all (a.mem ·)

/-- Two datasets denote the same default graph and the same named graphs,
each compared as a set: what a replay must reproduce. -/
def datasetSetEq (a b : Dataset) : Bool :=
  graphSetEq a.default b.default &&
  a.named.length == b.named.length &&
  a.named.all (fun ng => match b.named.find? (·.name == ng.name) with
    | some ng' => graphSetEq ng.graph ng'.graph
    | none => false)

/-- Why a write scope refuses these entries, or `none`. -/
def scopeRefusal : WriteScope → List DeltaEntry → Option String
  | .allGraphs, _ => none
  | .defaultGraph, es =>
    let named := es.any fun e => match e with
      | .add _ (some _) | .remove _ (some _) | .clear (some _) | .drop _ | .create _ => true
      | _ => false
    if named then
      some ("this collection is an IBK3 (triples) generation: its delta log is replayed and " ++
        "compacted for the default graph only, so a change to a named graph cannot be stored. " ++
        "Pack the data as a quad generation (layout ibk4 or ibk5) to change named graphs.")
    else none

/-- A successful change: refused by the write scope, or a commit. -/
def commitOutcome (scope : WriteScope) (old new : Dataset) (ok : HTTP.Response) : Outcome :=
  match datasetDelta old new with
  | .error why => text 501 why
  | .ok [] => { response := ok }
  | .ok entries =>
    match scopeRefusal scope entries with
    | some why => text 501 why
    | none => { response := ok, commit := some (entries, new) }

/-! ## The delta log of a served generation -/

/-- `Harness.CompactedEpoch.nextWriteEpoch`: a write is one epoch after the
compacted base, or epoch 1 for a base never compacted. -/
def writeEpochAfter : Option Nat → Nat
  | none => 1
  | some e => e + 1

/-- What a server must know about the log to append the next batch. -/
structure LogState where
  /-- The byte length the log file must have for the next append. -/
  size : Nat
  nextSeq : Nat
  writeEpoch : Nat
  deriving Repr, DecidableEq

/-- Open the log of a generation: `dlog` is the content of `deltas.dlog`
(`none` when absent) and `epoch` of `compacted.epoch`. Answers the state and
the batches a reader replays: exactly the suffix after the compacted epoch
(`replayBatchesSinceEpoch?`), as `l4block-id-v3-query` replays it. A torn
suffix, a malformed header or an invalid batch order is an error: a writer
appending after it would make the recovery decision silently. -/
def openLog (dlog : Option ByteArray) (epoch : Option ByteArray) :
    Except String (LogState × List DeltaBatch) := do
  let baseEpoch ← match epoch with
    | none => pure none
    | some bytes =>
      match Storage.parseEpoch bytes.toList with
      | some marker => pure (some marker.epoch)
      | none => throw "compacted.epoch is malformed or unsupported"
  match dlog with
  | none => pure ({ size := 0, nextSeq := 1, writeEpoch := writeEpochAfter baseEpoch }, [])
  | some bytes =>
    match Storage.parseLog bytes.toList with
    | none => throw "deltas.dlog: the DLOG header is malformed or unsupported"
    | some (_, _ :: _) =>
        throw "deltas.dlog has a torn or uncommitted suffix; recover it before serving the collection"
    | some (batches, []) =>
      if !Storage.validBatchHistory batches then
        throw "deltas.dlog: the batch sequence or epoch order is invalid"
      match Storage.replayBatchesSinceEpoch? baseEpoch batches with
      | none => throw "deltas.dlog: a batch at or below the compacted epoch follows a newer one"
      | some replay =>
        let nextSeq := match batches.getLast? with
          | some b => b.seq + 1
          | none => 1
        pure ({ size := bytes.size, nextSeq, writeEpoch := writeEpochAfter baseEpoch }, replay)

/-- The bytes to append for one batch of `entries`: the DLOG header first
when the log is empty, then the DLB1 frame. `none` when the batch exceeds
the wire-format limits. -/
def appendBytes (st : LogState) (entries : List DeltaEntry) : Option (ByteArray × LogState) := do
  let batch : DeltaBatch := { seq := st.nextSeq, epoch := st.writeEpoch, ops := entries }
  let frame ← Storage.serializeDeltaBatch? batch
  let header ← if st.size == 0 then Storage.serializeLog? [] else some []
  let bytes := header ++ frame
  pure (ByteArray.mk bytes.toArray,
        { st with size := st.size + bytes.length, nextSeq := st.nextSeq + 1 })

/-! ## Query evaluation and the results document -/

/-- Evaluate a parsed query over the view: the indexed backend when the
query names no dataset of its own, else (or when the backend declines) the
reference evaluator. `env.dataset` is the view's dataset, which §18.6 EXISTS
evaluates against. -/
def evalPayload (env : EvalEnv) (view : View) (q : Query) : Payload :=
  let ds := view.ds
  let env := { env with dataset := some ds }
  let backend := if q.dataset.isEmpty then view.backend else none
  match q.form with
  | .ask =>
    match backend.bind (runAskQueryBackendDataset env q) with
    | some b => .boolean b
    | none => .boolean (evalAsk env ds q)
  | .select sel =>
    match backend.bind (runSelectQueryBackendDataset env q) with
    | some rows =>
      let vars := match sel with
        | .vars items => selectItemVars items
        | .all => collectVarsInOrder rows
      .bindings vars rows
    | none =>
      let (vars, rows) := evalSelect env ds q
      .bindings vars rows
  -- CONSTRUCT and DESCRIBE read the dataset itself, as `queryParsedDatasetWith` does.
  | .construct _ => .graph (evalConstruct env ds q)
  | .describe _ => .graph (evalDescribe env ds q)

def srjType : String := "application/sparql-results+json"
def srxType : String := "application/sparql-results+xml"

/-- The media types a SELECT result is served in, in the server's order. -/
def bindingsTypes : List String :=
  [srjType, srxType, "text/csv", "text/tab-separated-values",
   "application/json", "application/xml", "text/xml"]

/-- An ASK result has no CSV or TSV form (SPARQL 1.1 Query Results CSV and
TSV Formats §1: they serialise the results of SELECT queries). -/
def booleanTypes : List String := [srjType, srxType, "application/json", "application/xml", "text/xml"]

private def withType (mt body : String) : HTTP.Response :=
  { status := 200, headers := [("content-type", mt ++ "; charset=utf-8")], body }

/-- The response carrying a protocol result in the negotiated format. -/
def payloadResponse (accept : String) : Payload → HTTP.Response
  | .boolean b =>
    match HTTP.negotiate accept booleanTypes with
    | none => HTTP.Response.notAcceptable
    | some mt =>
      match mediaTypeToFormat mt with
      | some .xml => withType srxType (QueryResult.toSrx (.boolean b))
      | _ => withType srjType (QueryResult.toSrj (.boolean b))
  | .bindings vars rows =>
    let r : QueryResult := .bindings vars rows
    match HTTP.negotiate accept bindingsTypes with
    | none => HTTP.Response.notAcceptable
    | some mt =>
      match mediaTypeToFormat mt with
      | some .xml => withType srxType (QueryResult.toSrx r)
      | some .csv =>
        match QueryResult.toCsv r with
        | .ok body => withType "text/csv" body
        | .error e => textResponse 500 s!"CSV serialisation failed: {e}"
      | some .tsv =>
        match QueryResult.toTsv r with
        | .ok body => withType "text/tab-separated-values" body
        | .error e => textResponse 500 s!"TSV serialisation failed: {e}"
      | _ => withType srjType (QueryResult.toSrj r)
  | .graph g => GraphStoreService.graphResponse accept g
  | .empty => { status := 204 }

/-! ## The three endpoints -/

private def header (req : HTTP.Request) (name : String) : String :=
  (req.header? name).getD ""

/-- §2.1 query and §2.2 update over the served view. -/
def protocolOutcome (scope : WriteScope) (env : EvalEnv) (view : View) (req : HTTP.Request)
    (serviceIri : String) : Outcome :=
  match decodeRequest req.method req.path req.queryStr (header req "content-type") req.body with
  | .bad reason =>
    if req.method != "GET" && req.method != "POST" then
      -- RFC 9110 §15.5.6: 405 carries Allow.
      { response := { (textResponse 405 reason) with
          headers := [("allow", "GET, POST, OPTIONS"), ("content-type", "text/plain; charset=utf-8")] } }
    else text 400 reason
  | .query qtext dflt named =>
    match parseSparql qtext (some serviceIri) with
    | .error e => text 400 s!"query parse error: {e.msg} (offset {e.pos})"
    | .ok q =>
      match datasetClauses dflt named with
      | none => text 400 "a dataset parameter is not an IRI"
      | some cls =>
        let q := withProtocolDataset cls q
        let env := { env with base := q.base.orElse (fun _ => some serviceIri) }
        match q.serviceFailure env view.ds with
        | some f => text 500 s!"query failed: {f.message}"
        | none => { response := payloadResponse (header req "accept") (evalPayload env view q) }
  | .update utext usingDefault usingNamed =>
    match parseSparqlUpdate utext (some serviceIri) with
    | .error e => text 400 s!"update parse error: {e.msg} (offset {e.pos})"
    | .ok u =>
      match datasetClauses usingDefault usingNamed with
      | none => text 400 "a dataset parameter is not an IRI"
      | some cls =>
        let env := { env with base := u.base.orElse (fun _ => some serviceIri) }
        match applyUpdateIn env view.ds (withUsing cls u) with
        | .error err => text 500 s!"update failed: {repr err}"
        | .ok ds' => commitOutcome scope view.ds ds' { status := 204 }

/-! ## The whole dataset at the Graph Store endpoint

SPARQL 1.1 Graph Store HTTP Protocol §5.5 leaves a request to the Graph Store
URI without a graph parameter to the service. Apache Jena Fuseki treats the
URI as the DATASET: GET answers it in a quad syntax (a triple syntax in
`Accept` selects the default graph), PUT replaces it, and POST adds to it;
DELETE is not defined there. A POST of a triple syntax keeps the §5.5 meaning
(create a new graph), which `GraphStoreService.serve` decides. -/

/-- The quad syntaxes the dataset is served and read in, in the server's
order of preference. -/
def quadTypes : List String := ["application/n-quads", "application/trig"]

/-- The dataset as TriG: the default graph's triples as N-Triples lines (TriG
accepts them as they are), then each named graph as `<name> { ... }`. -/
def datasetToTrig (ds : Dataset) : Except String String := do
  let mut out ← Syntax.Graph.toNTriples ds.default
  for ng in ds.named do
    out := out ++ Syntax.Subject.toNTriples ng.name ++ " {\n" ++ (← Syntax.Graph.toNTriples ng.graph) ++ "}\n"
  return out

/-- GET of the dataset: a quad syntax when `Accept` admits one, else the
default graph in a triple syntax. -/
def datasetResponse (accept : String) (ds : Dataset) : HTTP.Response :=
  match HTTP.negotiate accept (quadTypes ++ GraphStoreService.getMediaTypes) with
  | none => { status := 406 }
  | some "application/n-quads" =>
    match Syntax.Dataset.toNQuads ds with
    | .ok body => { status := 200, headers := [("content-type", "application/n-quads")], body }
    | .error e => textResponse 500 e
  | some "application/trig" =>
    match datasetToTrig ds with
    | .ok body => { status := 200, headers := [("content-type", "application/trig; charset=utf-8")], body }
    | .error e => textResponse 500 e
  | some _ => GraphStoreService.graphResponse accept ds.default

/-- A request body in a quad syntax. `none`: not a quad syntax. -/
def parseQuadsAs (mediaType base text : String) : Option (Except String Dataset) :=
  if mediaType == "application/n-quads" then
    some ((Syntax.parseNQuads text).mapError (·.msg))
  else if mediaType == "application/trig" || mediaType == "application/x-trig" || mediaType == "text/trig" then
    some ((Syntax.parseTriG text (some base)).mapError (·.msg))
  else none

private def hasBnodeGraphName (ds : Dataset) : Bool :=
  ds.named.any fun ng => match ng.name with
    | .bnode _ => true
    | .iri _ => false

/-- RDF merge of `new` into `old` (RDF 1.1 Semantics §4.1): the blank nodes of
`new` are renamed apart from every blank node of `old`, once for the whole
document, so a blank node shared by two graphs of `new` stays shared. -/
def mergeDataset (old new : Dataset) : Dataset :=
  let labels := (old.default :: old.named.map (·.graph)).flatMap Graph.bnodes
  let pre := GraphStoreService.freshPrefix "m" labels
  let rn (g : Graph) : Graph := GraphStoreService.prefixBnodes pre g
  let incoming := new.named.map fun ng => { ng with graph := rn ng.graph }
  let merged := old.named.map fun o =>
    match incoming.find? (·.name == o.name) with
    | some n => { o with graph := Graph.union o.graph n.graph }
    | none => o
  let added := incoming.filter fun n => !(old.named.any (·.name == n.name))
  { default := Graph.union old.default (rn new.default), named := merged ++ added }

/-- The Graph Store endpoint named with no graph parameter. `none`: the
request is not about the dataset as a whole, and `GraphStoreService.serve`
answers it. -/
def datasetOutcome (scope : WriteScope) (view : View) (req : HTTP.Request) (base : String) :
    Option Outcome :=
  let accept := header req "accept"
  let mt := contentTypeBase (header req "content-type")
  if req.method == "GET" || req.method == "HEAD" then
    some { response := datasetResponse accept view.ds, headOnly := req.method == "HEAD" }
  else if req.method == "DELETE" then
    some { response := { (textResponse 405
      "the dataset cannot be deleted; DELETE a graph with ?graph=IRI or ?default") with
        headers := [("allow", "GET, HEAD, POST, PUT, OPTIONS"),
                    ("content-type", "text/plain; charset=utf-8")] } }
  else if req.method == "PUT" || req.method == "POST" then
    match parseQuadsAs mt base req.body with
    | none =>
      if req.method == "PUT" then
        some (text 415 "PUT to the dataset takes N-Quads (application/n-quads) or TriG (application/trig); PUT a triple syntax with ?graph=IRI or ?default")
      else none
    | some (.error e) => some (text 400 s!"the request body does not parse: {e}")
    | some (.ok ds) =>
      if hasBnodeGraphName ds then some (text 400 "a graph name is a blank node; graph names are IRIs")
      else if req.method == "PUT" then
        some (commitOutcome scope view.ds ds { status := 204 })
      else
        some (commitOutcome scope view.ds (mergeDataset view.ds ds) { status := 204 })
  else none

/-- The Graph Store Protocol over the served view. Writes go through
`commitOutcome`, so a GSP PUT, POST or DELETE is stored exactly like an
update. -/
def gspOutcome (scope : WriteScope) (gspPath authority : String) (view : View)
    (req : HTTP.Request) : Outcome :=
  let ep : GraphStoreService.Endpoint := { authority, path := gspPath }
  let wholeDataset := match GraphStoreService.resolve ep req.path req.queryStr with
    | .ok .store => datasetOutcome scope view req (ep.iriOf req.path)
    | _ => none
  match wholeDataset with
  | some o => o
  | none =>
  let store : GraphStore.GraphStore :=
    { default := view.ds.default, named := (iriNamed view.ds).map fun p => (p.1.val, p.2) }
  let (store', resp) := GraphStoreService.serve ep store req.method req.path req.queryStr
    req.headers req.body
  if req.method == "GET" || req.method == "HEAD" || resp.status ≥ 300 then
    { response := resp, headOnly := req.method == "HEAD" }
  else
    let named? : Option (List NamedGraph) := store'.named.mapM fun kv =>
      if h : isIri kv.1 then some { name := .iri ⟨kv.1, h⟩, graph := kv.2 } else none
    match named? with
    | none => text 400 "a graph name is not an absolute IRI"
    | some named =>
      commitOutcome scope view.ds { default := store'.default, named := bnodeNamed view.ds ++ named } resp

/-- Service Description §2: the description of this endpoint. -/
def serviceDescriptionOutcome (req : HTTP.Request) (serviceIri : String) : Outcome :=
  if h : isIri serviceIri then
    { response := GraphStoreService.graphResponse (header req "accept")
        (ServiceDescription.buildSd ⟨serviceIri, h⟩)
    , headOnly := req.method == "HEAD" }
  else text 400 s!"the service IRI {serviceIri} is not an absolute IRI"

private def optionsOutcome (allow : String) : Outcome :=
  { response := { status := 204, headers := [("allow", allow)] } }

/-- The dataset prefix of a query path that ends in `/sparql`: `/ds` for
`/ds/sparql`, empty otherwise. With a non-empty prefix the endpoint also
answers the Apache Jena Fuseki service names `PREFIX/query`,
`PREFIX/update` (both as the Protocol endpoint) and `PREFIX/get` (Graph
Store reads only). -/
def datasetPrefix (queryPath : String) : String :=
  if queryPath.endsWith "/sparql" && queryPath.length > 7 then
    String.ofList (queryPath.toList.take (queryPath.length - 7))
  else ""

#guard datasetPrefix "/ds/sparql" == "/ds"
#guard datasetPrefix "/sparql" == ""
#guard datasetPrefix "/q" == ""

/-! ## Request counters and the read-only administration API

Apache Jena Fuseki serves an administration API under `/$/`. The read-only
part is answered here, with Fuseki's JSON member names:

  * `GET /$/ping` — the server time as text/plain;
  * `GET /$/datasets` and `/$/datasets/NAME` — `ds.name`, `ds.state` and
    `ds.services` (`srv.type`, `srv.description`, `srv.endpoints`);
  * `GET /$/stats` and `/$/stats/NAME` — per dataset and per endpoint
    `Requests`, `RequestsGood` and `RequestsBad`;
  * `GET /$/server` — `version`, `startDateTime`, `uptime` and `datasets`.

An operation that changes the server (creating or deleting a dataset, backup,
compaction, `/$/sleep`, `/$/tasks`, `/$/metrics`) answers 404 or 405.
A request is GOOD when its status is below 400 and BAD otherwise, counted
by the endpoint it addressed. A request to the administration API, to an
unknown path, or one the wire layer refused is not counted. -/

structure Counts where
  requests : Nat := 0
  good : Nat := 0
  bad : Nat := 0
  deriving Repr, DecidableEq

def Counts.add (c : Counts) (status : Nat) : Counts :=
  { requests := c.requests + 1
  , good := if status < 400 then c.good + 1 else c.good
  , bad := if status < 400 then c.bad else c.bad + 1 }

/-- Counters per endpoint name (the path relative to the dataset). -/
structure Stats where
  total : Counts := {}
  byEndpoint : List (String × Counts) := []
  deriving Repr, DecidableEq

def Stats.countsOf (s : Stats) (name : String) : Counts :=
  ((s.byEndpoint.find? (·.1 == name)).map (·.2)).getD {}

/-- What the server reports about itself and its requests so far. -/
structure ServerInfo where
  version : String := "Factoidal (Lean 4)"
  startDateTime : String := ""
  uptimeSeconds : Nat := 0
  stats : Stats := {}
  deriving Repr

/-- A path relative to the dataset prefix `p`: `ds/sparql` under `/ds` is
`sparql`; with no prefix, the path without its leading slash. A trailing
slash is ignored. -/
def relativeName (p path : String) : String :=
  let path := if path.length > 1 && path.endsWith "/" then path.dropEnd 1 |>.toString else path
  if !p.isEmpty && path.startsWith (p ++ "/") then (path.drop (p.length + 1)).toString
  else (path.drop 1).toString

/-- The endpoint a path addresses: its relative name and operation, or
`none` for a path that is no service of this dataset. -/
def serviceOf (cfg : Config) (path : String) : Option (String × String) :=
  let p := datasetPrefix cfg.queryPath
  if !p.isEmpty && path == p ++ "/get" then some ("get", "gsp-r")
  else if path == cfg.gspPath || path.startsWith (cfg.gspPath ++ "/") then
    some (relativeName p cfg.gspPath, "gsp-rw")
  else if path == cfg.queryPath || path == cfg.queryPath ++ "/" || HTTP.isProtocolPath path ||
      (!p.isEmpty && (path == p ++ "/query" || path == p ++ "/update")) then
    some (relativeName p path, if path.endsWith "/update" then "update" else "query")
  else none

/-- Count one answered request. -/
def Stats.record (s : Stats) (cfg : Config) (path : String) (status : Nat) : Stats :=
  if path.startsWith "/$/" || path.startsWith "/%24/" then s
  else
    match serviceOf cfg path with
    | none => s
    | some (name, _) =>
      let known := s.byEndpoint.any (·.1 == name)
      let updated := if known then s.byEndpoint.map fun e => if e.1 == name then (e.1, e.2.add status) else e
        else s.byEndpoint ++ [(name, ({} : Counts).add status)]
      { total := s.total.add status, byEndpoint := updated }

/-- The services of the dataset, as Fuseki lists them: type, endpoint names,
description. -/
def servicesOf (cfg : Config) : List (String × List String × String) :=
  let p := datasetPrefix cfg.queryPath
  let q := relativeName p cfg.queryPath
  [("gsp-rw", [relativeName p cfg.gspPath], "Graph Store Protocol")] ++
  (if p.isEmpty then [] else [("gsp-r", ["get"], "Graph Store Protocol (Read)")]) ++
  [("query", [q, "query"].eraseDups, "SPARQL Query"),
   ("update", [q, "update"].eraseDups, "SPARQL Update")]

/-- The dataset name Fuseki reports: the prefix, or `/` with none. -/
def dataSetName (cfg : Config) : String :=
  let p := datasetPrefix cfg.queryPath
  if p.isEmpty then "/" else p

private def jsonCounts (c : Counts) : List (String × L4Factoidal.JSON.Json) :=
  [("Requests", .number (toString c.requests)),
   ("RequestsGood", .number (toString c.good)),
   ("RequestsBad", .number (toString c.bad))]

private def datasetJson (cfg : Config) : L4Factoidal.JSON.Json :=
  .object
    [ ("ds.name", .string (dataSetName cfg))
    , ("ds.state", .bool true)
    , ("ds.services", .array ((servicesOf cfg).map fun (ty, names, desc) =>
        .object [ ("srv.type", .string ty), ("srv.description", .string desc)
                , ("srv.endpoints", .array (names.map .string)) ])) ]

private def statsJson (cfg : Config) (s : Stats) : L4Factoidal.JSON.Json :=
  let endpoints := (servicesOf cfg).flatMap fun (ty, names, desc) => names.map fun n => (n, ty, desc)
  let seen := endpoints.foldl (fun acc (n, ty, desc) =>
    if acc.any (·.1 == n) then acc else acc ++ [(n, ty, desc)]) []
  .object (jsonCounts s.total ++
    [("endpoints", .object (seen.map fun (n, ty, desc) =>
      (n, .object ([("description", .string desc), ("operation", .string ty)] ++
                   jsonCounts (s.countsOf n)))))])

private def jsonResponse (j : L4Factoidal.JSON.Json) : HTTP.Response :=
  { status := 200
  , headers := [("content-type", "application/json; charset=utf-8"),
                ("cache-control", "must-revalidate,no-cache,no-store")]
  , body := L4Factoidal.JSON.toStringCompact j ++ "\n" }

/-- A request under `/$/`. -/
def adminOutcome (cfg : Config) (env : EvalEnv) (info : ServerInfo) (req : HTTP.Request)
    (sub : String) : Outcome :=
  let sub := if sub.endsWith "/" then (sub.dropEnd 1).toString else sub
  let readOnly (allow : String) : Outcome :=
    { response := { (textResponse 405 s!"{req.path} is read-only in this server") with
        headers := [("allow", allow), ("content-type", "text/plain; charset=utf-8")] } }
  let name := (dataSetName cfg).drop 1 |>.toString
  let isRead := req.method == "GET" || req.method == "HEAD"
  let reply (r : HTTP.Response) : Outcome := { response := r, headOnly := req.method == "HEAD" }
  let noDataset := text 404 s!"no dataset at {req.path}"
  if req.method == "OPTIONS" then optionsOutcome "GET, HEAD, OPTIONS"
  else if sub == "ping" then
    if isRead || req.method == "POST" then
      let pong : HTTP.Response :=
        { status := 200
        , headers := [("content-type", "text/plain; charset=utf-8"),
                      ("cache-control", "must-revalidate,no-cache,no-store")]
        , body := (env.now.getD "") ++ "\n" }
      reply pong
    else readOnly "GET, HEAD, POST, OPTIONS"
  else if sub == "datasets" then
    if isRead then reply (jsonResponse (.object [("datasets", .array [datasetJson cfg])]))
    else readOnly "GET, HEAD, OPTIONS"
  else if sub == "datasets/" ++ name then
    if isRead then reply (jsonResponse (datasetJson cfg)) else readOnly "GET, HEAD, OPTIONS"
  else if sub == "stats" then
    if isRead then
      reply (jsonResponse (.object [("datasets",
        .object [(dataSetName cfg, statsJson cfg info.stats)])]))
    else readOnly "GET, HEAD, OPTIONS"
  else if sub == "stats/" ++ name then
    if isRead then reply (jsonResponse (statsJson cfg info.stats)) else readOnly "GET, HEAD, OPTIONS"
  else if sub == "server" then
    if isRead then
      reply (jsonResponse (.object
        [ ("version", .string info.version)
        , ("startDateTime", .string info.startDateTime)
        , ("uptime", .number (toString info.uptimeSeconds))
        , ("datasets", .array [datasetJson cfg]) ]))
    else readOnly "GET, HEAD, OPTIONS"
  else if sub.startsWith "datasets/" || sub.startsWith "stats/" then noDataset
  else text 404 s!"no administration operation {sub}; this server answers ping, datasets, stats and server"

/-- The part of a path after the administration prefix `/$/`, if any. -/
def adminSub? (path : String) : Option String :=
  if path.startsWith "/$/" then some (path.drop 3).toString
  else if path.startsWith "/%24/" then some (path.drop 5).toString
  else none

/-- One request against the served view. `info` is what the administration
API reports. -/
def handle (cfg : Config) (env : EvalEnv) (view : View) (req : HTTP.Request)
    (info : ServerInfo := {}) : Outcome :=
  match adminSub? req.path with
  | some sub => adminOutcome cfg env info req sub
  | none =>
  let authority := match req.header? "host" with
    | some h => if h.isEmpty then cfg.authority else h
    | none => cfg.authority
  let isGsp := req.path == cfg.gspPath || req.path.startsWith (cfg.gspPath ++ "/")
  let dsPrefix := datasetPrefix cfg.queryPath
  let isProtocol := req.path == cfg.queryPath || req.path == cfg.queryPath ++ "/" ||
    HTTP.isProtocolPath req.path ||
    (!dsPrefix.isEmpty && (req.path == dsPrefix ++ "/query" || req.path == dsPrefix ++ "/update"))
  let isGet := !dsPrefix.isEmpty && req.path == dsPrefix ++ "/get"
  if isGet then
    if req.method == "OPTIONS" then optionsOutcome "GET, HEAD, OPTIONS"
    else if req.method == "GET" || req.method == "HEAD" then
      gspOutcome cfg.scope cfg.gspPath authority view { req with path := cfg.gspPath }
    else
      -- RFC 9110 §15.5.6: 405 carries Allow.
      { response := { (textResponse 405 s!"{req.path} is read-only; write through {cfg.gspPath}") with
          headers := [("allow", "GET, HEAD, OPTIONS"), ("content-type", "text/plain; charset=utf-8")] } }
  else if isGsp then
    if req.method == "OPTIONS" then optionsOutcome "GET, HEAD, PUT, POST, DELETE, OPTIONS"
    else gspOutcome cfg.scope cfg.gspPath authority view req
  else if isProtocol then
    let serviceIri := "http://" ++ authority ++ req.path
    if req.method == "OPTIONS" then optionsOutcome "GET, POST, OPTIONS"
    else if (req.method == "GET" || req.method == "HEAD") && req.queryStr.isEmpty then
      serviceDescriptionOutcome req serviceIri
    else protocolOutcome cfg.scope env view req serviceIri
  else text 404 s!"no endpoint at {req.path}; the query endpoint is {cfg.queryPath} and the graph store is {cfg.gspPath}"

/-! ## Checks -/

private def exI (s : String) (h : isIri s = true := by decide) : WfIri := ⟨s, h⟩
private def tA : Triple := { s := .iri (exI "http://e/a"), p := exI "http://e/p", o := .iri (exI "http://e/b") }
private def tB : Triple := { s := .iri (exI "http://e/b"), p := exI "http://e/p", o := .literal (Literal.string "x") }
private def gI : WfIri := exI "http://e/g"
private def base0 : Dataset := { default := [tA], named := [{ name := .iri gI, graph := [tB] }] }

private def req (method target : String) (headers : List (String × String) := []) (body : String := "") :
    HTTP.Request :=
  let (path, qs) := match target.splitOn "?" with
    | [p] => (p, "")
    | p :: rest => (p, String.intercalate "?" rest)
    | [] => (target, "")
  { method, path, queryStr := qs, headers := ("host", "h.example") :: headers, body }

private def run (scope : WriteScope) (r : HTTP.Request) (ds : Dataset := base0) : Outcome :=
  handle { scope } { now := some "2026-10-10T00:00:00Z" } (View.of ds) r

private def statusOf (o : Outcome) : Nat := o.response.status
private def bodyOf (o : Outcome) : String := o.response.body
private def ctOf (o : Outcome) : String :=
  ((o.response.headers.find? (·.1 == "content-type")).map (·.2)).getD ""

-- The diff replays to the target, for adds, removes, a new graph, a dropped
-- graph and an emptied default graph.
#guard
  let new : Dataset := { default := [tB], named := [{ name := .iri (exI "http://e/h"), graph := [tA] }] }
  ((datasetDelta base0 new).toOption.map (applyDeltaEntries base0)).map (datasetSetEq · new) == some true
#guard
  let new : Dataset := { default := [], named := [{ name := .iri gI, graph := [tA, tB] }] }
  ((datasetDelta base0 new).toOption.map (applyDeltaEntries base0)).map (datasetSetEq · new) == some true
#guard (datasetDelta base0 base0).toOption == some []
-- A graph named by a blank node cannot be written to the log.
#guard
  let b : Dataset := { default := [], named := [{ name := .bnode "g", graph := [tA] }] }
  (datasetDelta b { b with named := [{ name := .bnode "g", graph := [] }] }).toOption.isNone

-- Service description on GET with no query string (SD §2), in Turtle.
#guard
  let o := run .allGraphs (req "GET" "/sparql")
  statusOf o == 200 && ctOf o == "text/turtle; charset=utf-8" &&
    Protocol.strContains (bodyOf o) "http://h.example/sparql"
-- ASK over the indexed backend; the default format is SPARQL Results JSON.
#guard
  let o := run .allGraphs (req "GET" "/sparql?query=ASK%20%7B%3Chttp%3A%2F%2Fe%2Fa%3E%20%3Fp%20%3Fo%7D")
  statusOf o == 200 && ctOf o == "application/sparql-results+json; charset=utf-8" &&
    Protocol.strContains (bodyOf o) "true"
-- SELECT negotiated to TSV; a query the grammar rejects is 400; PUT is 405.
#guard
  let o := run .allGraphs (req "POST" "/sparql" [("content-type", "application/sparql-query"),
    ("accept", "text/tab-separated-values")] "SELECT ?o WHERE { <http://e/a> <http://e/p> ?o }")
  statusOf o == 200 && ctOf o == "text/tab-separated-values; charset=utf-8" &&
    bodyOf o == "?o\n<http://e/b>\n"
#guard statusOf (run .allGraphs (req "GET" "/sparql?query=ASK%20%7B")) == 400
#guard statusOf (run .allGraphs (req "PUT" "/sparql?query=ASK%20%7B%7D")) == 405
-- ASK has no CSV form: an Accept that admits only CSV is 406.
#guard statusOf (run .allGraphs (req "GET" "/sparql?query=ASK%20%7B%7D" [("accept", "text/csv")])) == 406
-- FILTER NOT EXISTS through the backend path sees the dataset (anti-pattern 34).
#guard
  let o := run .allGraphs (req "POST" "/sparql" [("content-type", "application/sparql-query"),
    ("accept", "text/tab-separated-values")]
    "SELECT ?s WHERE { ?s <http://e/p> ?o FILTER NOT EXISTS { ?o <http://e/p> ?z } }")
  bodyOf o == "?s\n<http://e/a>\n"
#guard
  let o := run .allGraphs (req "POST" "/sparql" [("content-type", "application/sparql-query"),
    ("accept", "text/tab-separated-values")]
    "SELECT ?s WHERE { ?s <http://e/p> ?o FILTER EXISTS { ?o <http://e/q> ?z } }")
  bodyOf o == "?s\n"
-- An update is a commit: 204, the entries, and the new dataset.
#guard
  let o := run .allGraphs (req "POST" "/sparql" [("content-type", "application/sparql-update")]
    "INSERT { ?o <http://e/q> ?s } WHERE { ?s <http://e/p> ?o }")
  statusOf o == 204 &&
    (o.commit.map (fun c => c.1.length)) == some 1 &&
    (o.commit.map (fun c => datasetSetEq (applyDeltaEntries base0 c.1) c.2)) == some true
-- An update that changes nothing persists nothing.
#guard (run .allGraphs (req "POST" "/sparql" [("content-type", "application/sparql-update")]
    "DELETE DATA { <http://e/x> <http://e/y> <http://e/z> }")).commit.isNone
-- The IBK3 write scope refuses a named-graph change with 501, and admits a default-graph one.
#guard
  let o := run .defaultGraph (req "POST" "/sparql" [("content-type", "application/sparql-update")]
    "INSERT DATA { GRAPH <http://e/g> { <http://e/a> <http://e/p> <http://e/c> } }")
  statusOf o == 501 && o.commit.isNone
#guard
  let o := run .defaultGraph (req "POST" "/sparql" [("content-type", "application/sparql-update")]
    "INSERT DATA { <http://e/a> <http://e/p> <http://e/c> }")
  statusOf o == 204 && o.commit.isSome
-- Graph Store: GET a graph (200 or 404), PUT a new graph (201, committed).
#guard statusOf (run .allGraphs (req "GET" "/data?graph=http%3A%2F%2Fe%2Fg" [("accept", "application/n-triples")])) == 200
#guard statusOf (run .allGraphs (req "GET" "/data?graph=http%3A%2F%2Fe%2Fnone")) == 404
#guard
  let o := run .allGraphs (req "PUT" "/data/new" [("content-type", "text/turtle")] "<http://e/s> <http://e/p> 1 .")
  statusOf o == 201 && o.commit.isSome
-- Unknown paths are 404; OPTIONS answers Allow.
#guard statusOf (run .allGraphs (req "GET" "/elsewhere")) == 404
#guard statusOf (run .allGraphs (req "OPTIONS" "/sparql")) == 204

-- The log: an empty log gains its header with the first batch; the state advances.
#guard
  match openLog none none with
  | .ok (st, []) =>
    match appendBytes st [.add tA none] with
    | some (bytes, st') =>
      st'.size == bytes.size && st'.nextSeq == 2 &&
      (match openLog (some bytes) none with
       | .ok (st2, [b]) => st2 == st' && b.ops == [.add tA none] && b.epoch == 1
       | _ => false)
    | none => false
  | _ => false
-- A torn suffix refuses the open.
#guard
  match openLog none none with
  | .ok (st, _) =>
    match appendBytes st [.add tA none] with
    | some (bytes, _) => (openLog (some (bytes ++ ByteArray.mk #[1, 2, 3])) none).toOption.isNone
    | none => false
  | _ => false

/-! ### The whole dataset at the Graph Store endpoint (Fuseki `/ds/data`) -/

private def nqHdr (accept : String) : List (String × String) := [("accept", accept)]
private def isNq (s : String) : List (String × String) := [("content-type", s)]

-- GET: N-Quads by default and when asked; TriG when asked.
#guard
  let o := run .allGraphs (req "GET" "/data" (nqHdr "application/n-quads"))
  statusOf o == 200 && ctOf o == "application/n-quads" &&
    bodyOf o == "<http://e/a> <http://e/p> <http://e/b> .\n<http://e/b> <http://e/p> \"x\" <http://e/g> .\n"
#guard ctOf (run .allGraphs (req "GET" "/data")) == "application/n-quads"
#guard
  let o := run .allGraphs (req "GET" "/data" (nqHdr "application/trig"))
  statusOf o == 200 && ctOf o == "application/trig; charset=utf-8" &&
    bodyOf o == "<http://e/a> <http://e/p> <http://e/b> .\n<http://e/g> {\n<http://e/b> <http://e/p> \"x\" .\n}\n"
-- A triple syntax in Accept selects the default graph only (the named triple is absent).
#guard
  let o := run .allGraphs (req "GET" "/data" (nqHdr "text/turtle"))
  statusOf o == 200 && ctOf o == "text/turtle; charset=utf-8" &&
    Protocol.strContains (bodyOf o) "http://e/" && !Protocol.strContains (bodyOf o) "\"x\""
-- An Accept that admits no syntax of the dataset is 406; HEAD sends no body.
#guard statusOf (run .allGraphs (req "GET" "/data" (nqHdr "image/png"))) == 406
#guard (run .allGraphs (req "HEAD" "/data" (nqHdr "application/n-quads"))).headOnly
-- The data under a graph parameter is still one graph, not the dataset.
#guard
  let o := run .allGraphs (req "GET" "/data?default" (nqHdr "application/n-quads"))
  statusOf o == 406
-- PUT replaces the dataset (204, one commit whose replay is the new dataset).
#guard
  let body := "<http://e/s> <http://e/p> <http://e/o> <http://e/h> .\n<http://e/s> <http://e/p> <http://e/o2> .\n"
  let o := run .allGraphs (req "PUT" "/data" (isNq "application/n-quads") body)
  statusOf o == 204 &&
    (o.commit.map (fun c => c.2.default.length == 1 && c.2.named.length == 1 &&
      datasetSetEq (applyDeltaEntries base0 c.1) c.2)) == some true
-- PUT of TriG; a body that does not parse is 400; a triple syntax is 415.
#guard
  let o := run .allGraphs (req "PUT" "/data" (isNq "application/trig")
    "<http://e/h> { <http://e/s> <http://e/p> <http://e/o> . }")
  statusOf o == 204 && (o.commit.map (fun c => c.2.default.isEmpty && c.2.named.length == 1)) == some true
#guard statusOf (run .allGraphs (req "PUT" "/data" (isNq "application/n-quads") "<http://e/s> <http://e/p>")) == 400
#guard statusOf (run .allGraphs (req "PUT" "/data" (isNq "text/turtle") "<http://e/s> <http://e/p> 1 .")) == 415
-- PUT of the dataset it already is changes nothing and stores nothing.
#guard
  let o := run .allGraphs (req "PUT" "/data" (isNq "application/n-quads")
    "<http://e/a> <http://e/p> <http://e/b> .\n<http://e/b> <http://e/p> \"x\" <http://e/g> .\n")
  statusOf o == 204 && o.commit.isNone
-- POST of quads adds to the dataset and keeps what was there.
#guard
  let o := run .allGraphs (req "POST" "/data" (isNq "application/n-quads")
    "<http://e/s> <http://e/p> <http://e/o> <http://e/g> .\n<http://e/s> <http://e/p> <http://e/o> .\n")
  statusOf o == 204 &&
    (o.commit.map (fun c => c.2.default.length == 2 && c.2.named.length == 1 &&
      (c.2.named.map (·.graph.length)) == [2] && datasetSetEq (applyDeltaEntries base0 c.1) c.2)) == some true
-- POST of a triple syntax to the dataset still creates a new graph (GSP §5.5).
#guard
  let o := run .allGraphs (req "POST" "/data" (isNq "text/turtle") "<http://e/s> <http://e/p> 1 .")
  statusOf o == 201 && o.commit.isSome
-- DELETE of the dataset is 405 and names the methods that work.
#guard
  let o := run .allGraphs (req "DELETE" "/data")
  statusOf o == 405 && o.commit.isNone &&
    (o.response.headers.find? (·.1 == "allow")).map (·.2) == some "GET, HEAD, POST, PUT, OPTIONS"
-- DELETE of a graph is still 204.
#guard statusOf (run .allGraphs (req "DELETE" "/data?graph=http%3A%2F%2Fe%2Fg")) == 204
-- The IBK3 write scope refuses a dataset PUT that has a named graph (501) and admits one without.
#guard
  let o := run .defaultGraph (req "PUT" "/data" (isNq "application/n-quads") "<http://e/s> <http://e/p> <http://e/o> <http://e/h> .\n")
  statusOf o == 501 && o.commit.isNone
#guard
  let o := run .defaultGraph (req "PUT" "/data" (isNq "application/n-quads") "<http://e/s> <http://e/p> <http://e/o> .\n")
    { default := [tA], named := [] }
  statusOf o == 204 && (o.commit.map (fun c => c.1.length)).isSome
-- A shared blank node of two graphs of a POSTed document stays shared, and is
-- renamed apart from the blank nodes already stored.
#guard
  let old : Dataset := { default := [{ s := .bnode "x", p := exI "http://e/p", o := .iri (exI "http://e/b") }], named := [] }
  let new := parseQuadsAs "application/n-quads" "http://h/" "_:x <http://e/p> <http://e/c> .\n_:x <http://e/p> <http://e/d> <http://e/g> .\n"
  match new with
  | some (.ok n) =>
    let m := mergeDataset old n
    let labels := (m.default ++ m.named.flatMap (·.graph)).filterMap fun t => match t.s with
      | .bnode b => some b
      | _ => none
    m.default.length == 2 && labels.eraseDups.length == 2 && m.named.length == 1
  | _ => false

/-! ### RDF/XML for CONSTRUCT and DESCRIBE (RDF 1.1 XML Syntax) -/

private def tBad : Triple :=
  { s := .iri (exI "http://e/a"), p := exI "http://e/9", o := .iri (exI "http://e/b") }
private def dsBad : Dataset := { default := [tBad], named := [] }
private def constructAll (accept : String) (ds : Dataset) : Outcome :=
  run .allGraphs (req "POST" "/sparql" [("content-type", "application/sparql-query"), ("accept", accept)]
    "CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }") ds

#guard
  let o := constructAll "application/rdf+xml" base0
  statusOf o == 200 && ctOf o == "application/rdf+xml; charset=utf-8" &&
    Protocol.strContains (bodyOf o) "<rdf:RDF" && Protocol.strContains (bodyOf o) "rdf:about=\"http://e/a\"" &&
    Protocol.strContains (bodyOf o) "rdf:resource=\"http://e/b\""
-- The document reads back as the graph that was asked for.
#guard
  match Syntax.RdfXml.parseRdfXml (bodyOf (constructAll "application/rdf+xml" base0)) with
  | .ok g => graphSetEq g base0.default
  | .error _ => false
-- DESCRIBE too.
#guard
  let o := run .allGraphs (req "POST" "/sparql" [("content-type", "application/sparql-query"),
    ("accept", "application/rdf+xml")] "DESCRIBE <http://e/a>")
  statusOf o == 200 && ctOf o == "application/rdf+xml; charset=utf-8"
-- No Accept, and `*/*`, still answer Turtle.
#guard ctOf (constructAll "*/*" base0) == "text/turtle; charset=utf-8"
#guard ctOf (constructAll "text/turtle" base0) == "text/turtle; charset=utf-8"
-- A graph with no RDF/XML form (a predicate IRI that is no QName): 406 when only RDF/XML
-- is acceptable, the next acceptable syntax otherwise.
#guard statusOf (constructAll "application/rdf+xml" dsBad) == 406
#guard ctOf (constructAll "application/rdf+xml, text/turtle;q=0.5" dsBad) == "text/turtle; charset=utf-8"
-- A q-value of 0 refuses RDF/XML.
#guard statusOf (constructAll "application/rdf+xml;q=0" base0) == 406
-- The Graph Store answers RDF/XML as well.
#guard
  let o := run .allGraphs (req "GET" "/data?graph=http%3A%2F%2Fe%2Fg" (nqHdr "application/rdf+xml"))
  statusOf o == 200 && ctOf o == "application/rdf+xml; charset=utf-8"

/-! ### The administration API (Fuseki `/$/`) -/

private def dsCfg : Config := { queryPath := "/ds/sparql", gspPath := "/ds/data" }
private def runAdmin (method target : String) (info : ServerInfo := {}) : Outcome :=
  handle dsCfg { now := some "2026-10-10T00:00:00Z" } (View.of base0) (req method target) info

#guard (runAdmin "GET" "/$/ping").response.status == 200
#guard bodyOf (runAdmin "GET" "/$/ping") == "2026-10-10T00:00:00Z\n"
#guard ctOf (runAdmin "GET" "/$/ping") == "text/plain; charset=utf-8"
#guard statusOf (runAdmin "POST" "/$/ping") == 200
#guard statusOf (runAdmin "DELETE" "/$/ping") == 405
#guard (runAdmin "HEAD" "/$/ping").headOnly
#guard
  let o := runAdmin "GET" "/$/datasets"
  statusOf o == 200 && ctOf o == "application/json; charset=utf-8" &&
  bodyOf o == "{\"datasets\":[{\"ds.name\":\"/ds\",\"ds.state\":true,\"ds.services\":[{\"srv.type\":\"gsp-rw\",\"srv.description\":\"Graph Store Protocol\",\"srv.endpoints\":[\"data\"]},{\"srv.type\":\"gsp-r\",\"srv.description\":\"Graph Store Protocol (Read)\",\"srv.endpoints\":[\"get\"]},{\"srv.type\":\"query\",\"srv.description\":\"SPARQL Query\",\"srv.endpoints\":[\"sparql\",\"query\"]},{\"srv.type\":\"update\",\"srv.description\":\"SPARQL Update\",\"srv.endpoints\":[\"sparql\",\"update\"]}]}]}\n"
#guard Protocol.strContains (bodyOf (runAdmin "GET" "/$/datasets/ds")) "\"ds.name\":\"/ds\""
#guard !Protocol.strContains (bodyOf (runAdmin "GET" "/$/datasets/ds")) "\"datasets\""
#guard statusOf (runAdmin "GET" "/$/datasets/other") == 404
-- Creating or deleting a dataset is not offered.
#guard statusOf (runAdmin "POST" "/$/datasets") == 405
#guard statusOf (runAdmin "DELETE" "/$/datasets/ds") == 405
#guard statusOf (runAdmin "GET" "/$/nothing") == 404
-- The percent-encoded form of the prefix reaches the same endpoints.
#guard statusOf (runAdmin "GET" "/%24/ping") == 200
-- Counters: a service request is counted by its endpoint, good below 400 and bad from 400.
private def counted : Stats :=
  (((({} : Stats).record dsCfg "/ds/sparql" 200).record dsCfg "/ds/sparql" 400).record dsCfg "/ds/data" 204)
    |>.record dsCfg "/$/ping" 200 |>.record dsCfg "/elsewhere" 404
#guard counted.total == { requests := 3, good := 2, bad := 1 }
#guard counted.countsOf "sparql" == { requests := 2, good := 1, bad := 1 }
#guard counted.countsOf "data" == { requests := 1, good := 1, bad := 0 }
#guard counted.countsOf "query" == {}
#guard
  let b := bodyOf (runAdmin "GET" "/$/stats" { stats := counted })
  Protocol.strContains b "{\"datasets\":{\"/ds\":{\"Requests\":3,\"RequestsGood\":2,\"RequestsBad\":1,\"endpoints\":{" &&
  Protocol.strContains b "\"sparql\":{\"description\":\"SPARQL Query\",\"operation\":\"query\",\"Requests\":2,\"RequestsGood\":1,\"RequestsBad\":1}" &&
  Protocol.strContains b "\"update\":{\"description\":\"SPARQL Update\",\"operation\":\"update\",\"Requests\":0,\"RequestsGood\":0,\"RequestsBad\":0}"
#guard Protocol.strContains (bodyOf (runAdmin "GET" "/$/stats/ds" { stats := counted })) "\"Requests\":3"
#guard
  let b := bodyOf (runAdmin "GET" "/$/server" { startDateTime := "2026-10-10T00:00:00Z", uptimeSeconds := 7 })
  Protocol.strContains b "\"version\":\"Factoidal (Lean 4)\"" &&
  Protocol.strContains b "\"startDateTime\":\"2026-10-10T00:00:00Z\"" &&
  Protocol.strContains b "\"uptime\":7" && Protocol.strContains b "\"ds.name\":\"/ds\""
-- The administration paths are not services: with no administration prefix the same word is a 404.
#guard statusOf (runAdmin "GET" "/ping") == 404

end L4Factoidal.SPARQL.StoreEndpoint
