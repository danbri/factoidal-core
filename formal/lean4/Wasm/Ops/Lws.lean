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
import L4Factoidal.LWS.Authorization
import L4Factoidal.LWS.Notifications
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
  configuration says `"moves": false`. -/
  moves : Bool := true
  /-- Random bytes from the host (`entropy`, base64), read once at open:
  the seed of the notification signing key when the snapshot holds none,
  and of the run tag of activity identifiers. -/
  entropy : Option ByteArray := none
  /-- The subscriptions and the signing key of a snapshot written earlier. -/
  notif : Option Notifications.NotifState := none
  signingKey : Option ByteArray := none
deriving Inhabited

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
        let snapshot ← match j.field? "snapshot" with
          | none | some .null => .ok none
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
        let moves := j.field? "moves" != some (.bool false)
        let entropy ← match j.getString? "entropy" with
          | none => .ok none
          | some t => match Base64.decode? t with
            | some b => if b.size ≥ 16 then .ok (some b)
                        else .error "config: \"entropy\" holds fewer than 16 bytes"
            | none => .error "config: \"entropy\" is not base64"
        let (notif, signingKey) ← match j.field? "snapshot" with
          | some sj => match sj.field? "notifications" with
            | none | some .null => .ok (none, none)
            | some nj => do
                let ns ← Notifications.notifStateOfJson nj
                let key := (nj.getString? "signingKey").bind Base64.decode?
                .ok (some ns, key.filter (·.size == 32))
          | none => .ok (none, none)
        .ok { cfg := { baseIri, owner, agent, pageSize }, now, rootAcl, snapshot, authz,
              notifications, moves, entropy, notif, signingKey }

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
  mem : MemState
  authz : Authorization.AuthzConfig := {}
  notif : Notifications.NotifState := {}
  /-- The 32-byte Ed25519 secret key that signs webhook deliveries. -/
  signingKey : Option ByteArray := none

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

def lwsOpen (configJson : String) : IO String := do
  match openConfigOfJson configJson with
  | .error e => pure (errJson e)
  | .ok oc =>
      let n ← lwsCounter.modifyGet fun n => (n + 1, n + 1)
      let h := s!"lws{n}"
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
      lwsTable.modify (·.insert h
        { cfg := { oc.cfg with notifications := oc.notifications, notificationKeyX := keyX,
                                moves := oc.moves },
          mem := oc.snapshot.getD (initialStorage oc.now oc.rootAcl),
          authz := oc.authz, notif, signingKey })
      pure (okWith [("handle", .string h), ("root", .string rootPath)])

/-- A delivery request as the host receives it: POST `body` to `url` with
exactly `headers`. -/
def deliveryJson (d : Notifications.Delivery) : Json :=
  .object [ ("id", .string d.id), ("url", .string d.url)
          , ("headers", .array (d.headers.map (fun (n, v) => Json.array [.string n, .string v])))
          , ("body", .string d.body) ]

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
                | some t => { open_.mem with clock := t }
                | none   => open_.mem
              -- A per-request agent is the host's word for who is asking;
              -- it stands only in the explicit no-auth mode.
              let cfg := match agent? with
                | some a => if open_.authz.insecureNoAuth then { open_.cfg with agent := some a }
                            else open_.cfg
                | none   => open_.cfg
              match Notifications.serverStep lwsVerifiers MemStore cfg open_.authz
                      open_.signer (now?.getD mem.clock) r mem open_.notif with
              | .inl (issuer, url) =>
                  pure (noBytes (okWith [("fetch", .object [("issuer", .string issuer),
                                                   ("url", .string url)])]))
              | .inr (resp, mem', notif', ds) =>
                  lwsTable.modify (·.insert h { open_ with mem := mem', notif := notif' })
                  -- Every mutation advances the clock (`StoreLaws.nowTick`),
                  -- so a changed clock is exactly "the storage changed"; a
                  -- subscription change advances the notification revision.
                  -- A host that persists writes `lwsSnapshot` when this is true.
                  let changed := mem'.clock != mem.clock || notif'.revision != open_.notif.revision
                  pure (okWith ([ ("response", jsonOfResponse resp blobOut)
                                , ("changed", .bool changed) ] ++
                                (if ds.isEmpty then []
                                 else [("deliveries", .array (ds.map deliveryJson))])),
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
              let now := num "now" open_.mem.clock
              let (ns', retry) := Notifications.deliveryResult open_.signer now id status open_.notif
              lwsTable.modify (·.insert h { open_ with notif := ns' })
              pure (okWith ([("changed", .bool (ns'.revision != open_.notif.revision))] ++
                (match retry with
                 | some (d, after) => [("retry", .object [ ("delivery", deliveryJson d)
                                                        , ("after", .number (toString after)) ])]
                 | none => [])))

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
                | some (.number s) => (s.toNat?).getD open_.mem.clock
                | _ => open_.mem.clock
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

/-- `lwsSnapshot(handle)` -> `{"ok":true,"snapshot":{…}}`, the durable form
of the storage (`L4Factoidal.LWS.Snapshot`). -/
def lwsSnapshot (h : String) : IO String := do
  match (← lwsTable.get)[h]? with
  | none => pure (unknownLwsHandle h)
  | some open_ =>
      -- The notification state rides in the snapshot as one more member,
      -- which `memStateOfJson` does not read.
      let notif : Json := match Notifications.notifStateJson open_.notif, open_.signingKey with
        | .object fs, some sk => .object (fs ++ [("signingKey", .string (Base64.encode sk))])
        | other, _ => other
      let snap := match snapshotJson open_.mem with
        | .object fs => Json.object (fs ++ [("notifications", notif)])
        | other => other
      pure (okWith [("snapshot", snap)])

/-- The op names this module serves. -/
def lwsOpNames : List String :=
  ["lwsOpen", "lwsStep", "lwsClose", "lwsSnapshot", "lwsFetched", "lwsDelivered"]

/-- The LWS and Solid ops that also take and give a byte region: the
request content in, the response content out. -/
def lwsBlobIoOpNames : List String := ["lwsStep", "solidStep"]

end L4Wasm.Ops
