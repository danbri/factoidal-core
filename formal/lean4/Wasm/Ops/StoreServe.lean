/-
Wasm.Ops.StoreServe — the operations behind `factoidal serve`: a SPARQL 1.1
Protocol, Graph Store Protocol and Service Description endpoint over one
activated Shardborough generation and its delta log.

https://github.com/danbri/factoidal/issues/669 (step 1).

The host (`npm/factoidal/bin/serve.mjs`) accepts connections, reads bytes,
reads the files these operations name, appends the bytes they hand back, and
writes the bytes they answer. Every decision about HTTP and SPARQL is made
here or in the library modules this calls:

  * `L4Factoidal.HTTP.Wire` — where a request ends, its header fields, its
    body (Content-Length or chunked), persistence, the response bytes;
  * `L4Factoidal.SPARQL.StoreEndpoint` — routing, the protocol decoder,
    negotiation, evaluation, the service description, the Graph Store, the
    delta-log batch of a change and the write scope of the generation.

  storeServeKeys(manifestHex)
    -> {"ok":true,"keys":[…],"state":["deltas.dlog","compacted.epoch"]}
       `keys`: every artifact the host must read for storeServeOpen (blocks
       and, for wire version 10, the out-of-line literal blobs); `state`:
       the files it reads when they exist.
  storeServeOpen(manifestHex, artifactsJson, stateJson, configJson) + blob
    -> {"ok":true,"handle":"v1","layout":…,"wireVersion":N,"rows":N,
        "writeScope":"default-graph"|"all-graphs","deltaBatches":N,
        "logBytes":N,"graphs":N}
       `artifactsJson` and `stateJson` are `{"key","offset","len"}` windows
       into the one blob region, as for `storeOpen`. The artifacts are
       verified against the manifest by `storeOpen` itself.
  storeServeRequest(handle) + blob = the bytes a connection delivered so far
    -> {"state":"incomplete"[,"need":N]}             read more bytes
     | {"state":"respond","consumed":N,"close":B,"status":S} + out = response
     | {"state":"append","consumed":N,"close":B,"pending":"p…",
        "key":"deltas.dlog","expectedSize":N}       + out = bytes to append
  storeServeCommit(handle, pending, outcome)
    -> {"state":"respond","close":B,"status":S} + out = response
       `outcome` is "ok" once the host appended the bytes durably (the file
       had `expectedSize` bytes, the append was synced), or any other text
       naming why it did not. Only after "ok" does the served view change.
  storeServeClose(handle) -> {"ok":true}

A change is two calls because the response to an update must not say "done"
before the batch is durable, and the append is a file effect the engine
cannot perform. The host performs it and reports; the engine decides the
answer either way (a failed append is a 500 the ENGINE writes).

Concurrency: the module is single-threaded. While an append is pending the
handle refuses `storeServeRequest`; the host does the append synchronously
between the two calls, so no other request can see a half-committed view.

No `partial`, no `sorry`, no `native_decide`.
-/
import Std.Data.HashMap
import Wasm.Ops.StoreHandles
import Wasm.Ops.Clock
import Wasm.Ops.ExtFns
import L4Factoidal.HTTP.Wire
import L4Factoidal.SPARQL.StoreEndpoint

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreEndpoint
open L4Factoidal.Storage.ShardManifest
open L4Factoidal.JSON

/-- The state files a served generation may carry beside its artifacts. -/
def serveStateKeys : List String := ["deltas.dlog", "compacted.epoch"]

/-- A change the host is appending. -/
structure PendingCommit where
  id : String
  next : Dataset
  logAfter : LogState
  response : String
  close : Bool
  status : Nat

structure ServeState where
  layout : String
  wireVersion : Nat
  rows : Nat
  config : Config
  view : View
  log : LogState
  pending : Option PendingCommit := none

initialize serveCounter : IO.Ref Nat ← IO.mkRef 0
initialize serveTable : IO.Ref (Std.HashMap String ServeState) ← IO.mkRef ∅

/-- `storeServeKeys(manifestHex)`. -/
def storeServeKeys (manifestHex : String) : String :=
  match decodeManifest? "storeServeKeys" manifestHex with
  | .error e => errJson e
  | .ok manifest =>
    let blocks := manifest.entries.map fun entry => entry.artifact.key.value
    let blobs := (planBlobRefs manifest manifest.entries).map fun ref => ref.key.value
    okWith [ ("keys", .array ((blocks ++ blobs).map Json.string))
           , ("state", .array (serveStateKeys.map Json.string)) ]

private def stringMember (members : List (String × Json)) (name : String) : Option String :=
  match members.find? (·.1 == name) with
  | some (_, .string s) => some s
  | _ => none

/-- The host's configuration document: `queryPath`, `gspPath` and
`authority`, each optional. -/
def serveConfigOf (scope : WriteScope) (configJson : String) : Except String Config := do
  let members ← match parseJson configJson with
    | .ok (.object ms) => pure ms
    | .ok _ => throw "storeServeOpen: configJson must be a JSON object"
    | .error e => throw s!"storeServeOpen: configJson parse error: {e}"
  let base : Config := { scope }
  let path (name dflt : String) : Except String String :=
    match stringMember members name with
    | none => pure dflt
    | some p => if p.startsWith "/" && !p.endsWith "/" then pure p
                else throw s!"storeServeOpen: {name} must start with / and not end with /"
  pure { base with queryPath := ← path "queryPath" base.queryPath
                 , gspPath := ← path "gspPath" base.gspPath
                 , authority := (stringMember members "authority").getD base.authority }

/-- The two state files, from their windows. A key outside `serveStateKeys`
is a host fault. -/
def serveStateOf (stateJson : String) (blob : ByteArray) :
    Except String (Option ByteArray × Option ByteArray) := do
  let sources ← artifactSources "storeServeOpen" stateJson
  match sources.find? (fun p => !serveStateKeys.contains p.1) with
  | some (k, _) => throw s!"storeServeOpen: '{k}' is not a state file of a generation"
  | none => pure ()
  let files ← resolveSources "storeServeOpen" sources blob
  let find (k : String) := (files.find? (·.1 == k)).map (·.2)
  pure (find "deltas.dlog", find "compacted.epoch")

/-- The handle id `storeOpen` answered with. -/
private def handleOfEnvelope (envelope : String) : Except String String :=
  match parseJson envelope with
  | .ok j =>
    match j.field? "handle", j.field? "error" with
    | some (.string h), _ => .ok h
    | _, some (.string e) => .error e
    | _, _ => .error s!"storeServeOpen: storeOpen answered no handle: {envelope}"
  | .error e => .error s!"storeServeOpen: storeOpen answered no JSON: {e}"

/-- The base dataset of a generation: every block verified and decoded by
`storeOpen`, whose store handle is then dropped (the served view keeps the
dataset and its index; it does not use the retained sidecars). An empty
generation has no block to open and denotes the empty dataset. -/
private def baseOf (manifest : Manifest) (manifestHex artifactsJson : String)
    (blob : ByteArray) : IO (Except String (Dataset × Option StoreDataset.DatasetBackend × Nat)) := do
  if manifest.entries.isEmpty then return .ok (Dataset.empty, none, 0)
  let envelope ← storeOpen manifestHex artifactsJson blob
  match handleOfEnvelope envelope with
  | .error e => return .error e
  | .ok h =>
    let table ← storeHandleTable.get
    match table[h]? with
    | none => return .error s!"storeServeOpen: store handle {h} vanished"
    | some store =>
      storeHandleTable.set (table.erase h)
      return .ok (store.ds, store.backend, store.retainedRows)

/-- `storeServeOpen(manifestHex, artifactsJson, stateJson, configJson)`. -/
def storeServeOpen (manifestHex artifactsJson stateJson configJson : String)
    (blob : ByteArray) : IO String := do
  match decodeManifest? "storeServeOpen" manifestHex with
  | .error e => pure (errJson e)
  | .ok manifest =>
  -- IBK3 logs are replayed and compacted for the default graph only by the
  -- native tools; a quad layout takes every graph.
  let scope : WriteScope :=
    if isIbk4Layout manifest.layout || isIbk5Layout manifest.layout then .allGraphs
    else .defaultGraph
  match serveConfigOf scope configJson, serveStateOf stateJson blob with
  | .error e, _ | _, .error e => pure (errJson e)
  | .ok config, .ok (dlog, epoch) =>
  match openLog dlog epoch with
  | .error e => pure (errJson s!"storeServeOpen: {e}")
  | .ok (log, batches) =>
  match ← baseOf manifest manifestHex artifactsJson blob with
  | .error e => pure (errJson e)
  | .ok (base, baseBackend, rows) =>
    let entries := batches.flatMap (·.ops)
    -- An IBK3 generation is read as the native readers read it: the
    -- default-graph entries of the log, and no others.
    let entries := match scope with
      | .allGraphs => entries
      | .defaultGraph => entries.filter fun e => match e with
          | .add _ none | .remove _ none | .clear none => true
          | _ => false
    let view : View :=
      if entries.isEmpty then
        match baseBackend with
        | some b => { ds := base, backend := some b }
        | none => View.of base
      else View.of (applyDeltaEntries base entries)
    let n ← serveCounter.modifyGet fun n => (n + 1, n + 1)
    let handle := s!"v{n}"
    serveTable.modify (·.insert handle
      { layout := manifest.layout, wireVersion := manifest.version, rows, config, view, log })
    pure (okWith
      [ ("handle", .string handle)
      , ("layout", .string manifest.layout)
      , ("wireVersion", .number (toString manifest.version))
      , ("rows", .number (toString rows))
      , ("writeScope", .string scope.name)
      , ("deltaBatches", .number (toString batches.length))
      , ("logBytes", .number (toString log.size))
      , ("graphs", .number (toString view.ds.named.length))
      , ("queryPath", .string config.queryPath)
      , ("gspPath", .string config.gspPath) ])

private def respondEnvelope (consumed : Option Nat) (close : Bool) (status : Nat) : String :=
  okWith ([("state", .string "respond")] ++
    (consumed.map fun n => [("consumed", Json.number (toString n))]).getD [] ++
    [("close", .bool close), ("status", .number (toString status))])

def unknownServeHandle (h : String) : String := errJson s!"unknown serve handle: {h}"

/-- `storeServeRequest(handle)` over the bytes a connection delivered. -/
def storeServeRequest (h : String) (blob : ByteArray) : IO (String × ByteArray) := do
  match (← serveTable.get)[h]? with
  | none => pure (unknownServeHandle h, .empty)
  | some st =>
  if st.pending.isSome then
    pure (errJson "storeServeRequest: a change is waiting for storeServeCommit on this handle", .empty)
  else
  match L4Factoidal.HTTP.Wire.frameRequest blob with
  | .incomplete need =>
    pure (okWith ([("state", .string "incomplete")] ++
      (need.map fun n => [("need", Json.number (toString n))]).getD []), .empty)
  | .reject status reason =>
    let wire := L4Factoidal.HTTP.Wire.formatResponse (textResponse status reason) false
    pure (respondEnvelope (some blob.size) true status, wire.toUTF8)
  | .request req consumed keepAlive =>
    -- The §17.6 registrations and the clock, read once for this request.
    let extIris ← extSnapshot
    let now ← nowDateTime
    let env : EvalEnv := { ext := extFnsWith extIris, now := some now }
    let out := handle st.config env st.view req
    let wire := L4Factoidal.HTTP.Wire.formatResponse out.response keepAlive out.headOnly
    match out.commit with
    | none => pure (respondEnvelope (some consumed) (!keepAlive) out.response.status, wire.toUTF8)
    | some (entries, next) =>
      match appendBytes st.log entries with
      | none =>
        let refused := L4Factoidal.HTTP.Wire.formatResponse
          (textResponse 500 "the change exceeds the delta-log wire-format limits; nothing was stored") keepAlive
        pure (respondEnvelope (some consumed) (!keepAlive) 500, refused.toUTF8)
      | some (bytes, logAfter) =>
        let id := s!"p{st.log.nextSeq}"
        let pending : PendingCommit :=
          { id, next, logAfter, response := wire, close := !keepAlive, status := out.response.status }
        serveTable.modify (·.insert h { st with pending := some pending })
        pure (okWith
          [ ("state", .string "append")
          , ("consumed", .number (toString consumed))
          , ("close", .bool (!keepAlive))
          , ("pending", .string id)
          , ("key", .string "deltas.dlog")
          , ("expectedSize", .number (toString st.log.size)) ], bytes)

/-- `storeServeCommit(handle, pending, outcome)`. -/
def storeServeCommit (h pendingId outcome : String) : IO (String × ByteArray) := do
  match (← serveTable.get)[h]? with
  | none => pure (unknownServeHandle h, .empty)
  | some st =>
  match st.pending with
  | none => pure (errJson s!"storeServeCommit: no change is pending on handle {h}", .empty)
  | some p =>
    if p.id != pendingId then
      pure (errJson s!"storeServeCommit: the pending change is {p.id}, not {pendingId}", .empty)
    else if outcome == "ok" then
      serveTable.modify (·.insert h { st with view := View.of p.next, log := p.logAfter, pending := none })
      pure (respondEnvelope none p.close p.status, p.response.toUTF8)
    else
      serveTable.modify (·.insert h { st with pending := none })
      let failed := L4Factoidal.HTTP.Wire.formatResponse
        (textResponse 500 s!"the change was not stored: the delta-log append failed ({outcome})") (!p.close)
      pure (respondEnvelope none p.close 500, failed.toUTF8)

/-- `storeServeClose(handle)`. -/
def storeServeClose (h : String) : IO String := do
  let table ← serveTable.get
  if table.contains h then
    serveTable.set (table.erase h)
    pure (okWith [])
  else pure (unknownServeHandle h)

end L4Wasm.Ops
