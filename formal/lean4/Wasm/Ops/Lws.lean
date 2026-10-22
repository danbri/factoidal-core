/-
Wasm.Ops.Lws — LWS storage handles: open a storage, step requests through
it, close it.

  lwsOpen(configJson)
    -> {"ok":true,"handle":"lws1","root":"/"} | {"ok":false,"error":"…"}
  lwsStep(handle, requestJson)
    -> {"ok":true,"response":{"status":N,"headers":[[n,v],…],"body":"…"}}
  lwsClose(handle)
    -> {"ok":true}
  lwsDelivered(handle, {id, status, now?})
    -> {"ok":true,"changed":B,"retry"?:{"delivery":{…},"after":SECONDS}}
  lwsFlush(handle, {now?})
    -> {"ok":true,"changed":B,"deliveries"?:[…],"wake"?:SECONDS}

`lwsStep` may answer `{"ok":true,"resolve":{"host":H}}`: the engine needs
the addresses of a webhook inbox host (`Notifications.resolveNeeded?`,
issue 915). The host resolves `H` and steps the request again with the
member `resolved: [{host, addresses}]`; Lean decides what they mean
(`InboxGuard.loops`). An answer may carry `"wake": SECONDS`: deliveries
wait for a rate-limit window (`Notifications.nextWake`), and the host calls
`lwsFlush` after that many seconds.

A request document may carry `random` (base64, at least 16 bytes from the
host's random source): the name of an ANTICIPATORY AND UNSTABLE search
results resource, when the configuration says `"searchResults": true`
(`L4Factoidal.LWS.SearchResults`, issue 922).

`lwsStep` also answers `"deliveries":[{id,url,headers,body},…]` when the
step causes notifications (`L4Factoidal.LWS.Notifications`): the host POSTs
each one exactly as given and reports the status to `lwsDelivered`.

The JSON contract is `docs/lws-solid-conformance.md` § "wasm ABI"; the Node
hosts under `npm/factoidal/lws/` code against that section.

State lives HERE, in `Wasm/*`, exactly as `Wasm/Ops/Handles.lean` and
`Wasm/Ops/StoreHandles.lean` hold theirs: the protocol modules under
`L4Factoidal/LWS/` stay pure, and `L4Factoidal.LWS.Operations.step` is a
total function from a request and a state to a response and a state. This
module holds the state in an `IO.Ref`, so the operations are reachable only
through `L4Wasm.callIO`.

The clock is part of the state, not a call into a real clock. `lwsOpen`
takes `now` (seconds since the Unix epoch) and every mutation advances it by
one second; a request document may carry its own `now` to set it, which is
what a host with a real clock does.
-/
import Std.Data.HashMap
import Wasm.Ops.Support
import L4Factoidal.LWS.Operations
import L4Factoidal.LWS.Snapshot
import L4Factoidal.LWS.SnapshotSeal
import L4Factoidal.LWS.Authorization
import L4Factoidal.LWS.Notifications
import L4Factoidal.LWS.Search
import L4Factoidal.LWS.AccessGrants
import L4Factoidal.LWS.SearchResults
import L4Factoidal.LWS.MerkleHttp
import L4Factoidal.LWS.MoveRedirect
import L4Factoidal.LWS.FileLayout
import L4Factoidal.JOSE.Base64Url
import L4Factoidal.Crypto.P256Native
import L4Factoidal.Crypto.RsaNative
import L4Factoidal.Crypto.Ed25519

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.LWS
open L4Factoidal.HTTP (Request Response)

/-! ## Reading the JSON contract -/

/-- The content of a request document as bytes, or `none` for text in
`body`. See `requestOfJson`. -/
def requestBytes (j : Json) (blob : Option ByteArray) : Except String (Option ByteArray) :=
  match blob, j.getString? "bodyBase64" with
  | some b, none =>
      if (j.field? "body").isSome then
        .error "request: a request with a byte region carries no \"body\" member"
      else .ok (some b)
  | some _, some _ =>
      .error "request: a request with a byte region carries no \"bodyBase64\" member"
  | none, some t =>
      match Base64.decode? t with
      | some b => .ok (some b)
      | none => .error "request: member \"bodyBase64\" is not base64"
  | none, none => .ok none

/-- Decode a request document: `{method, target, headers, body}`, with the
optional `now` and `agent` overrides. Header names are lower-cased on the
way in, which is what `HTTP.Request.header?` expects.

The content is bytes (https://github.com/danbri/factoidal/issues/889):
`blob`, when the request came through the byte-region entry
(`L4Wasm.callBlobIO`), IS the content, and the document must then carry no
`body` or `bodyBase64`; otherwise `bodyBase64` (RFC 4648 §4) carries content
that is not UTF-8, and `body` carries text. -/
def requestOfJson (j : Json) (blob : Option ByteArray := none) :
    Except String (Request × Option Nat × Option String) := do
  let method ← match j.getString? "method" with
    | some m => .ok m
    | none   => .error "request: member \"method\" is required"
  let target ← match j.getString? "target" with
    | some t => .ok t
    | none   => .error "request: member \"target\" is required"
  let headers : List (String × String) :=
    match j.getArray? "headers" with
    | none => []
    | some items => items.filterMap (fun it =>
        match it with
        | .array [.string n, .string v] => some (n.toLower, v)
        | _ => none)
  let body := (j.getString? "body").getD ""
  let bytes ← requestBytes j blob
  let now : Option Nat :=
    match j.field? "now" with
    | some (.number s) => s.toNat?
    | _ => none
  let agent := j.getString? "agent"
  .ok ({ method, path := target, queryStr := "", headers, body, bytes }, now, agent)

/-- Encode a response document: `{status, headers, body}`.

With `blobOut := true` (the byte-region entry) the content leaves as the out
region and the document carries `bodyBytes`, its length. Otherwise content
that is UTF-8 is the string `body`, and content that is not is `bodyBase64`
(RFC 4648 §4), so no byte is altered on the way out. -/
def jsonOfResponse (r : Response) (blobOut : Bool := false) : Json :=
  let content := r.content
  .object ([ ("status", .number (toString r.status))
           , ("headers", .array (r.headers.map (fun (n, v) =>
               Json.array [.string n, .string v]))) ] ++
    (if blobOut then [("bodyBytes", .number (toString content.size))]
     else match String.fromUTF8? content with
       | some t => [("body", .string t)]
       | none => [("bodyBase64", .string (Base64.encode content))]))

/-- Decode the handle configuration. Every member is optional. -/
structure OpenConfig where
  cfg : Config := {}
  now : Nat := 0
  /-- The ACL document of the storage root, written at open time.

  Web Access Control §3.2: "Root container ACL resources MUST have
  representations. The ACL resource of the root container MUST include an
  Authorization allowing the acl:Control access privilege." A storage cannot
  bootstrap that itself under enforcement — the request that would write the
  root ACL is the first request the root ACL would authorize — so it is a
  PROVISIONING input, given by the host when the storage is created. -/
  rootAcl : Option String := none
  /-- A storage written by `lwsSnapshot` earlier, to continue from. Its
  paths are checked by `L4Factoidal.LWS.memStateOfJson`. -/
  snapshot : Option MemState := none
  /-- The authorization configuration (`L4Factoidal.LWS.Authorization`).
  The default enforces authorization with no trusted issuer; the
  development mode is the explicit `"insecureNoAuth": true`. -/
  authz : Authorization.AuthzConfig := {}
  /-- Does the storage offer notifications (LWS §Notifications)? On unless
  the configuration says `"notifications": false`. -/
  notifications : Bool := true
  /-- Does the storage let a client move a resource by changing its `up`
  link (LWS §Moving Resources, `L4Factoidal.LWS.Move`)? On unless the
  configuration says `"moves": false` or `"moves": "off"`
  (`movesOfJson`). -/
  moves : Bool := true
  /-- Does the storage offer the Type Index and Type Search services
  (lws10-index, `L4Factoidal.LWS.Search`)? On unless the configuration says
  `"typeIndex": false`. -/
  typeIndex : Bool := true
  /-- Does the storage offer access requests and grants (LWS §Access
  Requests and Grants, `L4Factoidal.LWS.AccessGrants`)? On unless the
  configuration says `"accessGrants": false`. -/
  accessGrants : Bool := true
  /-- Random bytes from the host (`entropy`, base64), read once at open:
  the seed of the notification signing key when the snapshot holds none,
  and of the run tag of activity identifiers. -/
  entropy : Option ByteArray := none
  /-- The subscriptions and the signing key of a snapshot written earlier. -/
  notif : Option Notifications.NotifState := none
  signingKey : Option ByteArray := none
  /-- ANTICIPATORY AND UNSTABLE (issue 922): does a QUERY answer of the type
  search name a search results resource with `Content-Location`? Off unless
  the configuration says `"searchResults": true`; `searchResultsTtl` and
  `searchResultsMax` set its lifetime and the number kept. -/
  searchResults : Bool := false
  searchResultsTtl : Nat := 600
  searchResultsMax : Nat := 100
  /-- The search results records of a snapshot written earlier. -/
  results : Option SearchResults.ResultsState := none
  /-- Merkle hashes (issue 919): `Repr-Digest` on resources and a Merkle
  root per container (`L4Factoidal.LWS.MerkleHttp`). Off unless the
  configuration says `"merkle": true`. -/
  merkle : Bool := false
  /-- The 32-byte storage key (configuration member `storageKey`, which the
  host fills from the environment variable `FACTOIDAL_LWS_KEY`). With a key
  the snapshot is sealed (`L4Factoidal.LWS.SnapshotSeal`); with none it is
  clear text, as before https://github.com/danbri/factoidal/issues/921. -/
  storageKey : Option ByteArray := none
  /-- The redirect table of a snapshot written earlier (issue 914). -/
  moved : List (String × String) := []
  /-- Where the storage is kept (https://github.com/danbri/factoidal/issues/918):
  `false` for the one snapshot document (`"storage": "snapshot"`, the
  default), `true` for the files of `L4Factoidal.LWS.FileLayout`
  (`"storage": "files"`): the host then reads the files `lwsOpen` names and
  passes them to `lwsLoad`, and calls `lwsPersist` after a change. -/
  files : Bool := false
  redirectsMax : Nat := 256
deriving Inhabited

/-- The other state of a storage, besides its resources: what the snapshot
document (and the metadata file of a storage kept in files) holds in the
members `moved`, `searchResults`, `access` and `notifications`. -/
structure SideState where
  moved : List (String × String) := []
  results : Option SearchResults.ResultsState := none
  access : AccessPolicy.AccessState := {}
  notif : Option Notifications.NotifState := none
  signingKey : Option ByteArray := none

/-- Read the other state from a snapshot document or a metadata file. `ms`
is the storage it belongs to (the redirect table is checked against it). -/
def sideOfDoc (baseIri : String) (authz : Authorization.AuthzConfig) (redirectsMax : Nat)
    (ms : MemState) (sj : Json) : Except String SideState := do
  let moved ← match sj.field? "moved" with
    | none | some .null => .ok []
    | some mj => MoveRedirect.stateOfJson MemStore ms redirectsMax mj
  let results ← match sj.field? "searchResults" with
    | none | some .null => .ok none
    | some rj => (SearchResults.stateOfJson rj).map some
  -- The access requests and grants, read again as documents
  -- (`AccessPolicy.stateOfJson`), into the policy.
  let access ← match sj.field? "access" with
    | none | some .null => .ok {}
    | some aj =>
        let c : Config := { baseIri }
        AccessPolicy.stateOfJson baseIri (AccessGrants.storageIris c authz) aj
  let (notif, signingKey) ← match sj.field? "notifications" with
    | none | some .null => .ok (none, none)
    | some nj => do
        let ns ← Notifications.notifStateOfJson nj
        let key := (nj.getString? "signingKey").bind Base64.decode?
        .ok (some ns, key.filter (·.size == 32))
  .ok { moved, results, access, notif, signingKey }

/-- The configuration member `moves`: absent, `true` or `"all"` (data
resources and containers move), `"data"` (data resources only:
`Config.moveContainers` false), `false` or `"off"` (no moves). The result is
(`moves`, `moveContainers`); another value is refused. -/
def movesOfJson : Option Json → Except String (Bool × Bool)
  | none | some (.bool true) | some (.string "all") => .ok (true, true)
  | some (.string "data") => .ok (true, false)
  | some (.bool false) | some (.string "off") => .ok (false, true)
  | some _ => .error "config: \"moves\" is true, false, \"all\", \"data\" or \"off\""

#guard (movesOfJson none).toOption == some (true, true)
#guard (movesOfJson (some (.string "data"))).toOption == some (true, false)
#guard (movesOfJson (some (.bool false))).toOption == some (false, true)
#guard (movesOfJson (some (.string "off"))).toOption == some (false, true)
#guard (movesOfJson (some (.string "containers"))).toOption.isNone

/-- A Boolean configuration member: `dflt` when absent, its value when a
Boolean, refused otherwise. -/
def boolOfJson (key : String) (dflt : Bool) : Option Json → Except String Bool
  | none => .ok dflt
  | some (.bool b) => .ok b
  | some _ => .error s!"config: \"{key}\" is true or false"

def openConfigOfJson (text : String) : Except String OpenConfig :=
  if text.trim == "" then .ok {}
  else match parseJson text with
    | .error e => .error s!"config: {toString e}"
    | .ok j => do
        let baseIri := (j.getString? "baseIri").getD "http://localhost/"
        let owner := j.getString? "owner"
        let agent := j.getString? "agent"
        let now := match j.field? "now" with
          | some (.number s) => (s.toNat?).getD 0
          | _ => 0
        let insecure := j.field? "insecureNoAuth" == some (.bool true)
        let authz ← match j.field? "auth", insecure with
          | some _, true =>
              .error "config: \"auth\" and \"insecureNoAuth\" are exclusive"
          | none, true => .ok { insecureNoAuth := true }
          | none, false => .ok {}
          | some aj, false => Authorization.authzConfigOfJson aj now
        -- Encryption at rest (issue 921): the key is checked first, then
        -- the document the host read is opened and authenticated before any
        -- of it is used (`Seal.openSnapshot`). With no key and a clear-text
        -- document, `snapDoc` is that document unchanged.
        let storageKey ← match j.getString? "storageKey" with
          | none => .ok none
          | some t => (Seal.parseStorageKey t).map some
        let snapDoc ← Seal.openSnapshot Seal.hacl storageKey
          (match j.field? "snapshot" with
           | none | some .null => none
           | some sj => some sj)
        -- Where the storage is kept (issue 918).
        let files ← match j.field? "storage" with
          | none | some (.string "snapshot") => .ok false
          | some (.string "files") => .ok true
          | some _ => .error "config: \"storage\" is \"snapshot\" or \"files\""
        if files && snapDoc.isSome then
          .error "config: a storage kept in files (\"storage\": \"files\") is read with lwsLoad, not from \"snapshot\"" else
        let snapshot ← match snapDoc with
          | none => .ok none
          | some sj => (memStateOfJson sj).map some
        -- Under authorization, a configured owner with no provisioned root
        -- ACL gets the owner's root ACL (`Authorization.ownerRootAcl`).
        let rootAcl ← match j.getString? "rootAcl", owner with
          | some body, _ => .ok (some body)
          | none, none => .ok none
          | none, some o =>
              if authz.insecureNoAuth then .ok none
              else match Authorization.ownerRootAcl baseIri o with
                | some body => .ok (some body)
                | none => .error "config: \"owner\" and \"baseIri\" must be IRIs with no space, <, >, \", {, }, |, ^, ` or \\"
        -- The pagination threshold and page size (LWS §Pagination); default 100.
        let pageSize := match j.field? "pageSize" with
          | some (.number s) => (s.toNat?).getD 100
          | _ => 100
        let notifications := j.field? "notifications" != some (.bool false)
        let (moves, moveContainers) ← movesOfJson (j.field? "moves")
        let linksetPut ← boolOfJson "linksetPut" true (j.field? "linksetPut")
        let paginateAlways ← boolOfJson "paginateAlways" false (j.field? "paginateAlways")
        let typeIndex := j.field? "typeIndex" != some (.bool false)
        let accessGrants := j.field? "accessGrants" != some (.bool false)
        let searchResults := j.field? "searchResults" == some (.bool true)
        let merkle := j.field? "merkle" == some (.bool true)
        let natOr (k : String) (d : Nat) : Nat := match j.field? k with
          | some (.number s) => (s.toNat?).getD d
          | _ => d
        let searchResultsTtl := natOr "searchResultsTtl" 600
        let searchResultsMax := natOr "searchResultsMax" 100
        -- Moved resources (issue 914): the redirect table and its bound.
        let redirectsMax := natOr "redirectsMax" 256
        -- The webhook delivery rate (issue 915); 0 turns the limit off.
        let deliveryLimit := natOr "deliveryLimit" 10
        let deliveryWindow := natOr "deliveryWindow" 60
        -- What the host bound (issue 915): `listen: {address, port, addresses}`.
        let (listenAddress, listenPort, localAddresses) := match j.field? "listen" with
          | some lj =>
              (lj.getString? "address",
               (match lj.field? "port" with
                | some (.number s) => s.toNat?
                | _ => none),
               ((lj.getArray? "addresses").getD []).filterMap (fun (a : Json) => match a with
                 | .string t => some t
                 | _ => none))
          | none => (none, none, [])
        -- The storage controller's inbox (issue 920).
        let controllerInbox ← match j.field? "controllerInbox" with
          | none | some .null => .ok none
          | some (.string u) =>
              if (Notifications.urlParts? u).isSome then .ok (some u)
              else .error "config: \"controllerInbox\" is an http or https URL"
          | some _ => .error "config: \"controllerInbox\" is an http or https URL"
        let entropy ← match j.getString? "entropy" with
          | none => .ok none
          | some t => match Base64.decode? t with
            | some b => if b.size ≥ 16 then .ok (some b)
                        else .error "config: \"entropy\" holds fewer than 16 bytes"
            | none => .error "config: \"entropy\" is not base64"
        -- The other state of a snapshot written earlier.
        let side ← match snapDoc, snapshot with
          | some sj, some ms => sideOfDoc baseIri authz redirectsMax ms sj
          | _, _ => .ok {}
        let authz := { authz with access := side.access }
        let (moved, results, notif, signingKey) := (side.moved, side.results, side.notif, side.signingKey)
        .ok { cfg := { baseIri, owner, agent, pageSize, moveContainers, linksetPut, paginateAlways,
                       redirectsMax, deliveryLimit, deliveryWindow, listenAddress, listenPort,
                       localAddresses, controllerInbox },
              moved,
              now, rootAcl, snapshot, authz,
              notifications, moves, typeIndex, accessGrants, entropy, notif, signingKey,
              searchResults, searchResultsTtl, searchResultsMax, results, storageKey, merkle,
              files, redirectsMax }

/-- The JWS verifiers over the vendored HACL* primitives (P-256 ECDSA,
RSA PKCS#1 v1.5, Ed25519): `skills/crypto-policy`. -/
def lwsVerifiers : L4Factoidal.JOSE.Verifiers :=
  { es256 := fun pubXY msg sig => L4Factoidal.Crypto.P256.p256VerifySha256 pubXY msg sig
    rs256 := fun n e sig msg =>
      L4Factoidal.JOSE.Pkcs1.rs256Verify L4Factoidal.Crypto.Rsa.rsaPublicOp n e sig msg
    eddsa := fun pk msg sig => L4Factoidal.Crypto.Ed25519.verify pk msg sig }

/-! ## The handle table -/

/-- One open storage: its configuration and its state. -/
structure OpenStorage where
  cfg : Config
  /-- The storage: the reference store, the Merkle hashes when they are on
  (`LwsBackend`), and the type index. -/
  mem : IxState LwsBackend
  authz : Authorization.AuthzConfig := {}
  notif : Notifications.NotifState := {}
  /-- The 32-byte Ed25519 secret key that signs webhook deliveries. -/
  signingKey : Option ByteArray := none
  /-- The search results records (ANTICIPATORY AND UNSTABLE, issue 922). -/
  results : SearchResults.ResultsState := {}
  /-- The storage key: `lwsSnapshot` seals the snapshot under it. -/
  storageKey : Option ByteArray := none
  /-- (previous path, current path) of moved resources
  (`L4Factoidal.LWS.MoveRedirect`, issue 914). -/
  moved : List (String × String) := []
  /-- A storage kept in files (issue 918): what the handle knows of its
  files. `none` for the snapshot mode. -/
  files : Option Files.FilesState := none

/-- The signer of a storage: Ed25519 (RFC 8032) through the vendored HACL*
code, under the verification method its storage description publishes. -/
def OpenStorage.signer (o : OpenStorage) : Option Notifications.Signer :=
  match o.signingKey, o.cfg.notificationKeyX with
  | some sk, some x =>
      some { keyId := notificationKeyId o.cfg.baseIri x
             sign := fun m => L4Factoidal.Crypto.Ed25519.sign sk m }
  | _, _ => none

initialize lwsCounter : IO.Ref Nat ← IO.mkRef 0
initialize lwsTable : IO.Ref (Std.HashMap String OpenStorage) ← IO.mkRef ∅

def unknownLwsHandle (h : String) : String :=
  errJson s!"unknown LWS handle: {h}"

/-- A new storage holds only its root container, stamped with the opening
clock. Solid Protocol §4.1: "Servers MUST provide one or more storages"; one
handle is one storage. -/
def initialStorage (now : Nat) (rootAcl : Option String := none) : MemState :=
  { entries :=
      { path := rootPath, kind := .storageRoot,
        contentType := "text/turtle", body := ByteArray.empty, mtime := now } ::
      (match rootAcl with
       | none => []
       | some body =>
           [{ path := aclPathOf rootPath, kind := .metadataResource,
              contentType := "text/turtle", body := textBytes body, mtime := now }])
  , clock := now + 1 }

/-- The storage of a handle, from its configuration and its resources. -/
def buildStorage (oc : OpenConfig) (ms : MemState) : OpenStorage :=
  let seeded (tag : String) : Option ByteArray :=
    oc.entropy.map (fun e => L4Factoidal.Crypto.sha256 (tag.toUTF8 ++ e))
  -- The signing key: the snapshot's, or one derived from the host's
  -- entropy; with neither, deliveries are not signed (a SHOULD).
  let signingKey := if oc.notifications then
      oc.signingKey.orElse (fun _ => seeded "lws-notification-signing-key:") else none
  let keyX := signingKey.bind (fun sk =>
    let pk := L4Factoidal.Crypto.Ed25519.secretToPublic sk
    if pk.size == 32 then some (L4Factoidal.JOSE.Base64Url.encode pk) else none)
  let run := ((seeded "lws-activity-run:").map (fun d =>
    L4Factoidal.Crypto.bytesToHex (d.extract 0 8))).getD ""
  let notif := { (oc.notif.getD {}) with run }
  { cfg := { oc.cfg with notifications := oc.notifications, notificationKeyX := keyX,
                          moves := oc.moves, typeIndex := oc.typeIndex,
                          accessGrants := oc.accessGrants,
                          searchResults := oc.searchResults,
                          searchResultsTtl := oc.searchResultsTtl,
                          searchResultsMax := oc.searchResultsMax },
    -- The type index and the Merkle hashes are built from the
    -- entries in one pass each (`TypeIndex.rebuildEntries`,
    -- `Merkle.rebuild`), then kept by the store.
    mem := IxState.ofMerkle oc.cfg.baseIri
      (if oc.merkle then some Merkle.haclHasher else none) ms,
    authz := oc.authz, notif, signingKey, results := oc.results.getD {},
    storageKey := oc.storageKey, moved := oc.moved }

/-- The other state of a storage as document members: the notification
state with the signing key, the access state, and the search results and the
redirect table when there are any. The snapshot (`lwsSnapshot`) and the
metadata file of a storage kept in files carry the same members. -/
def sideMembers (o : OpenStorage) : List (String × Json) :=
  let notif : Json := match Notifications.notifStateJson o.notif, o.signingKey with
    | .object fs, some sk => .object (fs ++ [("signingKey", .string (Base64.encode sk))])
    | other, _ => other
  [("notifications", notif), ("access", AccessPolicy.stateJson o.cfg.baseIri o.authz.access)] ++
  (if o.results.records.isEmpty then []
   else [("searchResults", SearchResults.stateJson o.results)]) ++
  (if o.moved.isEmpty then [] else [("moved", MoveRedirect.stateJson o.moved)])

/-- A storage kept in files while its files are read (issue 918). -/
inductive LoadPhase where
  /-- `lwsOpen` named the control files. -/
  | control
  /-- The metadata named the body files. -/
  | bodies (c : Files.Control)

structure Loading where
  oc : OpenConfig
  phase : LoadPhase

initialize lwsLoading : IO.Ref (Std.HashMap String Loading) ← IO.mkRef ∅

/-- The control files a start of a storage kept in files reads. -/
def controlFiles : List String := [Files.metaPath, Files.journalPath, Files.snapshotPath]

def readJson (names : List String) : Json := .array (names.map Json.string)

def lwsOpen (configJson : String) : IO String := do
  match openConfigOfJson configJson with
  | .error e => pure (errJson e)
  | .ok oc =>
      let n ← lwsCounter.modifyGet fun n => (n + 1, n + 1)
      let h := s!"lws{n}"
      if oc.files then
        -- A storage kept in files: the host reads the files named here and
        -- passes them to `lwsLoad`; the handle serves no step before that.
        lwsLoading.modify (·.insert h { oc, phase := .control })
        pure (okWith [("handle", .string h), ("root", .string rootPath),
                      ("load", .object [("read", readJson controlFiles)])])
      else
        lwsTable.modify (·.insert h
          (buildStorage oc (oc.snapshot.getD (initialStorage oc.now oc.rootAcl))))
        pure (okWith [("handle", .string h), ("root", .string rootPath)])

/-- The files of a `lwsLoad` document: `files: [{path, present, length}]`,
the bytes one after the other in the byte region. -/
def loadedFiles (j : Json) (blob : ByteArray) : Except String (Std.HashMap String (Option ByteArray)) := do
  let items := (j.getArray? "files").getD []
  let (m, off) ← items.foldlM (fun (m, off) (it : Json) => do
      let path ← (it.getString? "path").elim (.error "load: a file has no \"path\"") .ok
      if it.field? "present" == some (.bool false) then .ok (m.insert path none, off) else
      let len ← (match it.field? "length" with
        | some (.number t) => t.toNat?
        | _ => none).elim (.error s!"load: file {path} has no \"length\"") .ok
      if off + len > blob.size then .error s!"load: file {path} runs past the byte region" else
      .ok (m.insert path (some (blob.extract off (off + len))), off + len))
    ((∅ : Std.HashMap String (Option ByteArray)), 0)
  if off != blob.size then .error "load: the byte region holds more bytes than the files" else
  .ok m

def seedOf (j : Json) : Except String ByteArray :=
  match j.getString? "seed" with
  | none => .error "the host must pass \"seed\", 32 random bytes (base64)"
  | some t => match Base64.decode? t with
    | some b => if b.size ≥ 16 then .ok b else .error "\"seed\" holds fewer than 16 bytes"
    | none => .error "\"seed\" is not base64"

def planAnswer (extra : List (String × Json)) (pl : Files.Plan) : String × ByteArray :=
  (okWith (extra ++ [("plan", pl.json), ("bytes", .number (toString pl.bytes.size))]), pl.bytes)

/-- Install a storage kept in files, read from `ms` and its other state, and
answer the plan of the start (`Files.startPlan`). -/
def finishLoad (h : String) (oc : OpenConfig) (seed : ByteArray) (ms : MemState) (side : SideState)
    (c? : Option Files.Control) (hadSnapshot : Bool) : IO (String × ByteArray) := do
  let oc := { oc with moved := side.moved, results := side.results, notif := side.notif,
                      signingKey := side.signingKey, authz := { oc.authz with access := side.access } }
  let o := buildStorage oc ms
  match Files.startPlan Seal.hacl oc.storageKey seed ms (sideMembers o) c? hadSnapshot with
  | .error e =>
      lwsLoading.modify (·.erase h)
      pure (errJson e, ByteArray.empty)
  | .ok (fs, pl) =>
      lwsTable.modify (·.insert h { o with files := some fs })
      lwsLoading.modify (·.erase h)
      pure (planAnswer [("ready", .bool true), ("handle", .string h), ("root", .string rootPath)] pl)

/-- `lwsLoad(handle, {files, seed})` with the bytes of the files in the byte
region: the files `lwsOpen` or the previous `lwsLoad` named. Answers the next
files to read (`load: {read: [...]}`), or `ready: true` with the plan of the
start (`plan`, its bytes in the out region), after which the handle serves
steps. An error ends the start; the handle is gone. -/
def lwsLoad (h docJson : String) (blob : ByteArray) : IO (String × ByteArray) := do
  let noBytes (s : String) : String × ByteArray := (s, ByteArray.empty)
  match (← lwsLoading.get)[h]? with
  | none => pure (noBytes (errJson s!"unknown LWS handle to load: {h}"))
  | some ld =>
      let fail (e : String) : IO (String × ByteArray) := do
        lwsLoading.modify (·.erase h)
        pure (noBytes (errJson e))
      match parseJson docJson with
      | .error e => fail s!"load: {toString e}"
      | .ok j =>
      match loadedFiles j blob, seedOf j with
      | .error e, _ => fail e
      | _, .error e => fail s!"load: {e}"
      | .ok files, .ok seed =>
      let got (p : String) : Option ByteArray := (files[p]?).getD none
      let oc := ld.oc
      let cfgBase := oc.cfg.baseIri
      match ld.phase with
      | .control =>
          match Files.readControl Seal.hacl oc.storageKey (got Files.metaPath)
              (got Files.journalPath) (got Files.snapshotPath) with
          | .error e => fail e
          | .ok .fresh =>
              finishLoad h oc seed (initialStorage oc.now oc.rootAcl) {} none false
          | .ok (.migrate doc) =>
              -- Migration from the snapshot of the default mode: read it as
              -- `lwsOpen` reads it (sealed or clear, checked).
              let read : Except String (MemState × SideState) := do
                let inner ← Seal.openSnapshot Seal.hacl oc.storageKey (some doc)
                let sj ← inner.elim (.error "snapshot: no document") .ok
                let ms ← memStateOfJson sj
                let side ← sideOfDoc cfgBase oc.authz oc.redirectsMax ms sj
                .ok (ms, side)
              match read with
              | .error e => fail e
              | .ok (ms, side) => finishLoad h oc seed ms side none true
          | .ok (.files c) =>
              let names := Files.bodiesToRead c
              if names.isEmpty then
                match Files.entriesOf Seal.hacl oc.storageKey c {} with
                | .error e => fail e
                | .ok ms =>
                    match sideOfDoc cfgBase oc.authz oc.redirectsMax ms (.object c.side) with
                    | .error e => fail e
                    | .ok side => finishLoad h oc seed ms side (some c) false
              else
                lwsLoading.modify (·.insert h { ld with phase := .bodies c })
                pure (noBytes (okWith [("load", .object [("read", readJson names)])]))
      | .bodies c =>
          let bodies : Std.HashMap String ByteArray :=
            files.fold (fun m k v => match v with
              | some b => m.insert k b
              | none => m) {}
          match Files.entriesOf Seal.hacl oc.storageKey c bodies with
          | .error e => fail e
          | .ok ms =>
              match sideOfDoc cfgBase oc.authz oc.redirectsMax ms (.object c.side) with
              | .error e => fail e
              | .ok side => finishLoad h oc seed ms side (some c) false

/-- `lwsPersist(handle, {seed})`: the write plan of the changes since the last
persist of a storage kept in files (`Files.persist`): `plan`, its bytes in the
out region. The host performs it before it answers the request. -/
def lwsPersist (h optsJson : String) : IO (String × ByteArray) := do
  let noBytes (s : String) : String × ByteArray := (s, ByteArray.empty)
  let parsed : Except String ByteArray := match parseJson optsJson with
    | .error e => .error s!"persist: {toString e}"
    | .ok j => (seedOf j).mapError (fun e => s!"persist: {e}")
  match parsed with
  | .error e => pure (noBytes (errJson e))
  | .ok seed =>
  -- The storage is taken out of the table and taken apart while its files
  -- state is updated, so the body reference table is not shared and is
  -- updated in place (skills/lean4-performance: a value named in a later
  -- branch is alive during the call).
  match ← lwsTable.modifyGet (fun t => (t[h]?, t.erase h)) with
  | none => pure (noBytes (unknownLwsHandle h))
  | some ⟨cfg, mem, authz, notif, signingKey, results, storageKey, moved, files⟩ =>
      let o' : OpenStorage := ⟨cfg, mem, authz, notif, signingKey, results, storageKey, moved, none⟩
      match files with
      | none =>
          lwsTable.modify (·.insert h o')
          pure (noBytes (errJson "lwsPersist: this storage is not kept in files (\"storage\": \"files\")"))
      | some fs =>
          match Files.persist Seal.hacl storageKey seed fs mem.journal (sideMembers o') mem.mem.clock with
          | .error e =>
              -- Fail-stop: the handle is closed, and the files hold the
              -- storage as of the last persist (as after a crash).
              pure (noBytes (errJson s!"{e}; the storage is closed"))
          | .ok (fs', pl) =>
              lwsTable.modify (·.insert h { o' with files := some fs', mem := mem.resetJournal })
              pure (planAnswer [] pl)

/-- A delivery request as the host receives it: POST `body` to `url` with
exactly `headers`. -/
def deliveryJson (d : Notifications.Delivery) : Json :=
  .object [ ("id", .string d.id), ("url", .string d.url)
          , ("headers", .array (d.headers.map (fun (n, v) => Json.array [.string n, .string v])))
          , ("body", .string d.body) ]

/-- The request member `resolved`: `[{host, addresses: [...]}]`, the host's
answer to a `resolve`. Members of another shape are dropped. -/
def resolvedOfJson (j : Json) : List (String × List String) :=
  ((j.getArray? "resolved").getD []).filterMap (fun it =>
    match it.getString? "host", it.getArray? "addresses" with
    | some h, some xs => some (h.toLower, xs.filterMap (fun x => match x with
        | .string t => some t
        | _ => none))
    | _, _ => none)

/-- The `wake` member: seconds until deliveries that wait for a rate-limit
window may go (`Notifications.nextWake`), when any wait. -/
def wakeMember (now : Nat) (cfg : Config) (ns : Notifications.NotifState) : List (String × Json) :=
  match Notifications.nextWake now cfg.rate ns with
  | some t => [("wake", .number (toString t))]
  | none => []

/-- One LWS step. `blob` is the content when the request came through the
byte-region entry; the answer is then the envelope and the response content
as the out region (`jsonOfResponse … true`). -/
def lwsStepWith (h requestJson : String) (blob : Option ByteArray) :
    IO (String × ByteArray) := do
  let blobOut := blob.isSome
  let noBytes (s : String) : String × ByteArray := (s, ByteArray.empty)
  match (← lwsTable.get)[h]? with
  | none => pure (noBytes (unknownLwsHandle h))
  | some open_ =>
      match parseJson requestJson with
      | .error e => pure (noBytes (errJson s!"request: {toString e}"))
      | .ok j =>
          match requestOfJson j blob with
          | .error e => pure (noBytes (errJson e))
          | .ok (r, now?, agent?) => do
              let mem := match now? with
                | some t => open_.mem.withClockM t
                | none   => open_.mem
              -- A per-request agent is the host's word for who is asking;
              -- it stands only in the explicit no-auth mode.
              let cfg := match agent? with
                | some a => if open_.authz.insecureNoAuth then { open_.cfg with agent := some a }
                            else open_.cfg
                | none   => open_.cfg
              -- The addresses the host resolved for a name the engine asked
              -- about (`resolve`, issue 915): data only.
              let cfg := { cfg with resolved := resolvedOfJson j }
              let now := now?.getD mem.mem.clock
              let S := IndexedStore LwsBackend lwsBackendLaws
              -- An inbox host to resolve before a subscription is decided.
              match Notifications.resolveNeeded? lwsVerifiers S cfg open_.authz now r mem with
              | some host =>
                  pure (noBytes (okWith [("resolve", .object [("host", .string host)])]))
              | none =>
              -- The previous identifier of a moved resource (issue 914).
              match MoveRedirect.answer? lwsVerifiers S cfg open_.authz now r mem open_.moved with
              | some (.inl (issuer, url)) =>
                  pure (noBytes (okWith [("fetch", .object [("issuer", .string issuer),
                                                   ("url", .string url)])]))
              | some (.inr resp) =>
                  pure (okWith [ ("response", jsonOfResponse resp blobOut), ("changed", .bool false) ],
                        if blobOut then resp.content else ByteArray.empty)
              | none =>
              let plan? := movePlanOf? S cfg.baseIri cfg.moves cfg.moveContainers r mem
              -- Random bytes from the host for a search results name.
              let rand : Option ByteArray := (j.getString? "random").bind Base64.decode?
              match SearchResults.serverStep lwsVerifiers LwsBackend lwsBackendLaws cfg open_.authz now
                  rand r mem open_.results with
              | .fetch issuer url =>
                  pure (noBytes (okWith [("fetch", .object [("issuer", .string issuer),
                                                   ("url", .string url)])]))
              | .handled resp rs' =>
                  lwsTable.modify (·.insert h { open_ with results := rs' })
                  pure (okWith [ ("response", jsonOfResponse resp blobOut)
                               , ("changed", .bool (rs'.revision != open_.results.revision)) ],
                        if blobOut then resp.content else ByteArray.empty)
              | .pass =>
              match AccessGrants.serverStepWith lwsVerifiers (IndexedStore LwsBackend lwsBackendLaws)
                      cfg open_.authz open_.signer now r mem open_.notif
                      (fun r st ns => Search.serverStep lwsVerifiers LwsBackend lwsBackendLaws cfg
                        open_.authz open_.signer now r st ns) with
              | .inl (issuer, url) =>
                  pure (noBytes (okWith [("fetch", .object [("issuer", .string issuer),
                                                   ("url", .string url)])]))
              | .inr (resp, mem', notif', access', ds) =>
                  let authz' := { open_.authz with access := access' }
                  let moved' := MoveRedirect.after S cfg.redirectsMax plan? resp.status mem' open_.moved
                  -- Merkle fields and members (issue 919); unchanged when off.
                  let resp := Merkle.decorate LwsBase cfg mem'.base
                    (fun _ => Merkle.rootsVisible lwsVerifiers (IndexedStore LwsBackend lwsBackendLaws)
                      cfg authz' now r mem') r resp
                  -- A snapshot storage keeps no journal: forget the touched
                  -- paths now. A storage kept in files forgets them in
                  -- `lwsPersist`, after it wrote their record.
                  let memK := if open_.files.isSome then mem' else mem'.resetJournal
                  let stored : OpenStorage :=
                    { open_ with mem := memK, notif := notif', authz := authz', moved := moved' }
                  lwsTable.modify (·.insert h stored)
                  -- Every mutation advances the clock (`StoreLaws.nowTick`),
                  -- so a changed clock is exactly "the storage changed"; a
                  -- subscription change advances the notification revision.
                  -- A host that persists writes `lwsSnapshot` when this is true.
                  let changed := mem'.mem.clock != mem.mem.clock ||
                    notif'.revision != open_.notif.revision ||
                    access'.revision != open_.authz.access.revision ||
                    moved' != open_.moved
                  pure (okWith ([ ("response", jsonOfResponse resp blobOut)
                                , ("changed", .bool changed) ] ++
                                (if ds.isEmpty then []
                                 else [("deliveries", .array (ds.map deliveryJson))]) ++
                                wakeMember now cfg notif'),
                        if blobOut then resp.content else ByteArray.empty)

/-- `lwsDelivered(handle, {id, status, now})`: the host's report of one
delivery attempt (status 0 when no answer came). Lean decides what it
means (`Notifications.deliveryResult`): done, a retry after some seconds,
or a failure that may deactivate the subscription. -/
def lwsDelivered (h docJson : String) : IO String := do
  match (← lwsTable.get)[h]? with
  | none => pure (unknownLwsHandle h)
  | some open_ =>
      match parseJson docJson with
      | .error e => pure (errJson s!"delivered: {toString e}")
      | .ok j =>
          match j.getString? "id" with
          | none => pure (errJson "delivered: member \"id\" is required")
          | some id =>
              let num (k : String) (d : Nat) : Nat := match j.field? k with
                | some (.number s) => (s.toNat?).getD d
                | _ => d
              let status := num "status" 0
              let now := num "now" open_.mem.mem.clock
              let (ns', retry) := Notifications.deliveryResult open_.signer now id status open_.notif
              lwsTable.modify (·.insert h { open_ with notif := ns' })
              pure (okWith ([("changed", .bool (ns'.revision != open_.notif.revision))] ++
                (match retry with
                 | some (d, after) => [("retry", .object [ ("delivery", deliveryJson d)
                                                        , ("after", .number (toString after)) ])]
                 | none => [])))

/-- `lwsFlush(handle, {now})`: the host's call after the seconds a `wake`
named. Lean decides which waiting activities may go now
(`Notifications.flush`, one batched envelope per subscription) and when to
wake again. -/
def lwsFlush (h docJson : String) : IO String := do
  match (← lwsTable.get)[h]? with
  | none => pure (unknownLwsHandle h)
  | some open_ =>
      let now : Nat := match parseJson docJson with
        | .ok j => (match j.field? "now" with
            | some (.number s) => (s.toNat?).getD open_.mem.mem.clock
            | _ => open_.mem.mem.clock)
        | .error _ => open_.mem.mem.clock
      let (ns', ds) := Notifications.flush open_.cfg.baseIri open_.signer now open_.cfg.rate open_.notif
      lwsTable.modify (·.insert h { open_ with notif := ns' })
      pure (okWith ([("changed", .bool (ns'.revision != open_.notif.revision))] ++
        (if ds.isEmpty then [] else [("deliveries", .array (ds.map deliveryJson))]) ++
        wakeMember now open_.cfg ns'))

/-- `lwsStep(handle, requestJson)` through the string entry: the content
travels in the document (`body` or `bodyBase64`). -/
def lwsStep (h requestJson : String) : IO String := do
  return (← lwsStepWith h requestJson none).1

/-- `lwsFetched(handle, {issuer, url, status, body, now})`: the host's
answer to a `fetch` from `lwsStep`. Lean decides what the document means
(`Authorization.installFetched`); the result names the next URL to fetch,
or says the keys are installed and the request can be stepped again. -/
def lwsFetched (h docJson : String) : IO String := do
  match (← lwsTable.get)[h]? with
  | none => pure (unknownLwsHandle h)
  | some open_ =>
      match parseJson docJson with
      | .error e => pure (errJson s!"fetched: {toString e}")
      | .ok j =>
          match j.getString? "issuer", j.getString? "url" with
          | some issuer, some url =>
              let status := match j.field? "status" with
                | some (.number s) => (s.toNat?).getD 0
                | _ => 0
              let now := match j.field? "now" with
                | some (.number s) => (s.toNat?).getD open_.mem.mem.clock
                | _ => open_.mem.mem.clock
              let (authz', outcome) := Authorization.installFetched open_.authz issuer url
                status ((j.getString? "body").getD "") now
              lwsTable.modify (·.insert h { open_ with authz := authz' })
              pure <| match outcome with
                | .next u => okWith [("fetch", .object [("issuer", .string issuer),
                                                       ("url", .string u)])]
                | .installed n => okWith [("installed", .number (toString n))]
                | .refused why => okWith [("refused", .string why)]
          | _, _ => pure (errJson "fetched: members \"issuer\" and \"url\" are required")

def lwsClose (h : String) : IO String := do
  let table ← lwsTable.get
  if table.contains h then
    lwsTable.set (table.erase h)
    pure (okWith [])
  else
    pure (unknownLwsHandle h)

/-- The answer of `lwsSnapshot` and `solidSnapshot`: the snapshot document,
sealed under the storage key when the handle has one
(`Seal.sealSnapshot`). `optsJson` is the host's optional second argument,
`{"nonce":"<base64>"}`: 12 bytes from the host's random source, new for
every write. With no key the nonce is not used and the document is the
clear-text snapshot, as before. -/
def snapshotAnswer (key? : Option ByteArray) (optsJson : String) (doc : Json) : String :=
  let nonce? : Except String (Option ByteArray) :=
    if optsJson.trimAscii.toString == "" then .ok none
    else match parseJson optsJson with
      | .error e => .error s!"snapshot options: {toString e}"
      | .ok oj => match oj.getString? "nonce" with
        | none => .ok none
        | some t => match Base64.decode? t with
          | some b => .ok (some b)
          | none => .error "snapshot options: \"nonce\" is not base64"
  match nonce? with
  | .error e => errJson e
  | .ok n => match Seal.sealSnapshot Seal.hacl key? n doc with
    | .ok d => okWith [("snapshot", d)]
    | .error e => errJson e

/-- `lwsSnapshot(handle[, optionsJson])` -> `{"ok":true,"snapshot":{…}}`, the
durable form of the storage (`L4Factoidal.LWS.Snapshot`), sealed when the
handle has a storage key (`snapshotAnswer`). -/
def lwsSnapshot (h : String) (optsJson : String := "") : IO String := do
  match (← lwsTable.get)[h]? with
  | none => pure (unknownLwsHandle h)
  | some open_ =>
      -- The other state rides in the snapshot as more members, which
      -- `memStateOfJson` does not read (`sideMembers`).
      let snap := match snapshotJson open_.mem.mem with
        | .object fs => Json.object (fs ++ sideMembers open_)
        | other => other
      pure (snapshotAnswer open_.storageKey optsJson snap)

/-- The op names this module serves. -/
def lwsOpNames : List String :=
  ["lwsOpen", "lwsStep", "lwsClose", "lwsSnapshot", "lwsFetched", "lwsDelivered", "lwsFlush",
   "lwsLoad", "lwsPersist"]

/-- The LWS and Solid ops that also take and give a byte region: the
request content in, the response content out. -/
def lwsBlobIoOpNames : List String := ["lwsStep", "solidStep", "lwsLoad", "lwsPersist"]

end L4Wasm.Ops
