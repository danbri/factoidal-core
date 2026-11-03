/-
Wasm.Ops.Solid — Solid Protocol handles for the SERVER, and two stateless
operations for the CLIENT.

  solidOpen(configJson)
    -> {"ok":true,"handle":"solid1","root":"/","storage":"<baseIri>"}
  solidStep(handle, requestJson)
    -> {"ok":true,"response":{"status":N,"headers":[[n,v],…],"body":"…"}}
  solidClose(handle)
    -> {"ok":true}

  solidClientRequest(kind, argsJson)
    -> {"ok":true,"request":{"method":"…","target":"…","headers":[…],"body":"…"}}
  solidClientResponse(kind, responseJson)
    -> {"ok":true,"interpretation":{…}}

The JSON contract is `docs/lws-solid-conformance.md` § "wasm ABI"; the Node
hosts under `npm/factoidal/solid/` code against that section.

Server and client stay distinct here as they do in `L4Factoidal/Solid/`: the
server operations hold state in a handle table, the client operations hold
none, because a client's state is its own host's.

`solidStep` calls `L4Factoidal.Solid.Server.step`, which refines
`L4Factoidal.LWS.Operations.step`. The request and response documents are
the same records `Wasm/Ops/Lws.lean` reads and writes, so a host can drive
either engine through one code path.
-/
import Std.Data.HashMap
import Wasm.Ops.Lws
import L4Factoidal.Solid.Server.Methods
import L4Factoidal.Solid.Server.Oidc
import L4Factoidal.Solid.Client.Requests
import L4Factoidal.Solid.Client.Responses
import L4Factoidal.Solid.Client.Profile

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.RDF
open L4Factoidal.LWS
open L4Factoidal.Solid.Server
open L4Factoidal.Solid.Client
open L4Factoidal.HTTP (Request Response)

/-! ## The server handle table -/

structure OpenSolid where
  cfg : ServerConfig
  mem : MemState
  /-- Solid-OIDC authentication (`L4Factoidal.Solid.Server.Oidc`). `none`:
  the configuration named neither `auth` nor `insecureNoAuth`, and the
  requester is the handle configuration's agent, as before issue 899. -/
  oidc : Option Oidc.OidcConfig := none
  /-- The storage key (issue 921): `solidSnapshot` seals the snapshot under
  it, exactly as `lwsSnapshot` does. -/
  storageKey : Option ByteArray := none
  /-- The `Host` and `Origin` guard of a server with no authentication
  (`insecureNoAuth`, https://github.com/danbri/factoidal/issues/1124). -/
  guard : Option L4Factoidal.HTTP.LocalGuard.LocalGuard := none

initialize solidCounter : IO.Ref Nat ← IO.mkRef 0
initialize solidTable : IO.Ref (Std.HashMap String OpenSolid) ← IO.mkRef ∅

def unknownSolidHandle (h : String) : String :=
  errJson s!"unknown Solid handle: {h}"

/-- **A Solid handle refuses a storage that LWS wrote** (owner requirement
for 0.21.0: only the LWS request handler reads or changes the data of an LWS
storage, `L4Factoidal.LWS.AccessTheorems`). `snapshotLws`: the snapshot
document is one `lwsSnapshot` wrote (`lwsWrittenDoc`); `listed`: the names in
the storage directory the host listed (configuration member `dirFiles`),
which name the files of a storage LWS keeps in files (`lwsFilesListed`). -/
def solidRefusesLws (snapshotLws : Bool) (listed : List String) : Option String :=
  if snapshotLws || lwsFilesListed listed then
    some ("config: this directory holds a Linked Web Storage storage (written by lws-serve); " ++
      "only lws-serve serves it, through LWS authorization")
  else none

theorem solidRefusesLws_snapshot (listed : List String) :
    (solidRefusesLws true listed).isSome := by
  simp [solidRefusesLws]

theorem solidRefusesLws_files (snapshotLws : Bool) (listed : List String)
    (h : lwsFilesListed listed = true) : (solidRefusesLws snapshotLws listed).isSome := by
  simp [solidRefusesLws, h]

/-- `enforceWac` is read from the configuration, defaulting to false — the
first slice serves public resources (see `L4Factoidal/Solid/README.md`). -/
def serverConfigOfJson (text : String) :
    Except String (ServerConfig × Nat × Option String × Option MemState ×
      Option Oidc.OidcConfig × Option ByteArray × Option L4Factoidal.HTTP.LocalGuard.LocalGuard) :=
  match openConfigOfJson text with
  | .error e => .error e
  | .ok oc =>
      let j? : Option Json :=
        if text.trim == "" then none
        else match parseJson text with
          | .ok j => some j
          | .error _ => none
      let listed : List String := match j? with
        | some j => ((j.getArray? "dirFiles").getD []).filterMap (fun (v : Json) => match v with
            | .string t => some t
            | _ => none)
        | none => []
      match solidRefusesLws oc.snapshotLws listed with
      | some e => .error e
      | none =>
      -- `auth` turns Solid-OIDC on (and Web Access Control with it, unless
      -- the configuration says otherwise); `insecureNoAuth` is the
      -- explicit development mode. `openConfigOfJson` has already refused
      -- the two together.
      let oidc : Except String (Option Oidc.OidcConfig) :=
        match j? with
        | none => .ok none
        | some j =>
            match j.field? "auth" with
            | some aj => (Oidc.oidcConfigOfJson aj oc.now).map some
            | none => if oc.authz.insecureNoAuth then .ok (some { insecureNoAuth := true })
                      else .ok none
      match oidc with
      | .error e => .error e
      | .ok oidc =>
          let wacDefault := match oidc with
            | some o => !o.insecureNoAuth
            | none => false
          let enforce := match j? with
            | some j => (j.getBool? "enforceWac").getD wacDefault
            | none => false
          .ok ({ lws := oc.cfg, enforceWac := enforce }, oc.now, oc.rootAcl, oc.snapshot, oidc,
               oc.storageKey, oc.guard)

def solidOpen (configJson : String) : IO String := do
  match serverConfigOfJson configJson with
  | .error e => pure (errJson e)
  | .ok (cfg, now, rootAcl, snapshot, oidc, storageKey, guard) =>
      let n ← solidCounter.modifyGet fun n => (n + 1, n + 1)
      let h := s!"solid{n}"
      -- The storage root advertises an LDN inbox (Solid Protocol §6, LDN
      -- §3.1), so the storage has to hold one: a Receiver answers a POST to
      -- its inbox with 201, and a container with no representation answers
      -- 404 (Solid Protocol §5.3).
      let mem := snapshot.getD (memPut (initialStorage now rootAcl) (inboxEntry now))
      solidTable.modify (·.insert h { cfg, mem, oidc, storageKey, guard })
      pure (okWith [ ("handle", .string h)
                   , ("root", .string rootPath)
                   , ("storage", .string cfg.lws.baseIri) ])

/-- One Solid step; `blob` and the out region as `lwsStepWith`. -/
def solidStepWith (h requestJson : String) (blob : Option ByteArray) :
    IO (String × ByteArray) := do
  let noBytes (s : String) : String × ByteArray := (s, ByteArray.empty)
  match (← solidTable.get)[h]? with
  | none => pure (noBytes (unknownSolidHandle h))
  | some open_ =>
      match parseJson requestJson with
      | .error e => pure (noBytes (errJson s!"request: {toString e}"))
      | .ok j =>
          match requestOfJson j blob with
          | .error e => pure (noBytes (errJson e))
          | .ok (r, now?, agent?) => do
              -- A server with no authentication answers only its own names,
              -- and no write from another origin (issue 1124): first.
              match open_.guard.bind (fun g => L4Factoidal.HTTP.LocalGuard.admit g r) with
              | some resp =>
                  return (okWith [ ("response", jsonOfResponse resp blob.isSome), ("changed", .bool false) ],
                          if blob.isSome then resp.content else ByteArray.empty)
              | none =>
              let mem := match now? with
                | some t => { open_.mem with clock := t }
                | none   => open_.mem
              -- A per-request agent is the host's word for who is asking;
              -- it stands only when authentication is off.
              let agentStands := match open_.oidc with
                | none => true
                | some o => o.insecureNoAuth
              let cfg := match agent? with
                | some a => if agentStands then { open_.cfg with
                              lws := { open_.cfg.lws with agent := some a } } else open_.cfg
                | none   => open_.cfg
              match open_.oidc with
              | none =>
                  let (resp, mem') := L4Factoidal.Solid.Server.step MemStore cfg r mem
                  solidTable.modify (·.insert h { open_ with mem := mem' })
                  pure (okWith [ ("response", jsonOfResponse resp blob.isSome)
                               , ("changed", .bool (mem'.clock != mem.clock)) ],
                        if blob.isSome then resp.content else ByteArray.empty)
              | some o =>
                  match Oidc.authenticatedStep lwsVerifiers MemStore cfg o
                          (now?.getD mem.clock) r mem with
                  | .inl (k, key, url) =>
                      pure (noBytes (okWith [("fetch", .object [("kind", .string k.name),
                        ("key", .string key), ("url", .string url)])]))
                  | .inr (resp, mem', o') =>
                      solidTable.modify (·.insert h { open_ with mem := mem', oidc := some o' })
                      pure (okWith [ ("response", jsonOfResponse resp blob.isSome)
                                   , ("changed", .bool (mem'.clock != mem.clock)) ],
                            if blob.isSome then resp.content else ByteArray.empty)


/-- `solidStep(handle, requestJson)` through the string entry. -/
def solidStep (h requestJson : String) : IO String := do
  return (← solidStepWith h requestJson none).1

/-- `solidFetched(handle, {kind, key, url, status, body, now})`: the host's
answer to a `fetch` from `solidStep`. Lean decides what the document means
(`Oidc.installFetched`); the result names the next URL to fetch, or says
the document was installed and the request can be stepped again. -/
def solidFetched (h docJson : String) : IO String := do
  match (← solidTable.get)[h]? with
  | none => pure (unknownSolidHandle h)
  | some open_ =>
      match open_.oidc with
      | none => pure (errJson "solidFetched: this storage does not authenticate")
      | some o =>
          match parseJson docJson with
          | .error e => pure (errJson s!"fetched: {toString e}")
          | .ok j =>
              let kind? : Option Oidc.FetchKind := match j.getString? "kind" with
                | some "issuer" => some .issuer
                | some "profile" => some .profile
                | _ => none
              match kind?, j.getString? "key", j.getString? "url" with
              | some kind, some key, some url =>
                  let status := match j.field? "status" with
                    | some (.number s) => (s.toNat?).getD 0
                    | _ => 0
                  let now := match j.field? "now" with
                    | some (.number s) => (s.toNat?).getD open_.mem.clock
                    | _ => open_.mem.clock
                  let (o', outcome) := Oidc.installFetched o kind key url status
                    ((j.getString? "body").getD "") now
                  solidTable.modify (·.insert h { open_ with oidc := some o' })
                  pure <| match outcome with
                    | .next u => okWith [("fetch", .object [("kind", .string kind.name),
                        ("key", .string key), ("url", .string u)])]
                    | .installed n => okWith [("installed", .number (toString n))]
                    | .refused why => okWith [("refused", .string why)]
              | _, _, _ => pure (errJson "fetched: members \"kind\", \"key\" and \"url\" are required")

/-- `solidSnapshot(handle[, optionsJson])`: the durable form of the storage,
as `lwsSnapshot`, sealed when the handle has a storage key. -/
def solidSnapshot (h : String) (optsJson : String := "") : IO String := do
  match (← solidTable.get)[h]? with
  | none => pure (unknownSolidHandle h)
  | some open_ => pure (snapshotAnswer open_.storageKey optsJson (snapshotJson open_.mem))

def solidClose (h : String) : IO String := do
  let table ← solidTable.get
  if table.contains h then
    solidTable.set (table.erase h)
    pure (okWith [])
  else
    pure (unknownSolidHandle h)

/-! ## The client operations

Both are pure functions of their arguments; they are declared `IO` only so
they sit beside the handle operations in one dispatch table. -/

/-- `solidClientRequest(kind, argsJson)` — build a conformant request. -/
def solidClientRequest (kind argsJson : String) : String :=
  match RequestKind.ofString? kind with
  | none => errJson s!"solidClientRequest: unknown kind '{kind}' (read | create | replace | patch | delete | discoverStorage | readProfile)"
  | some k =>
      match parseJson argsJson with
      | .error e => errJson s!"args: {toString e}"
      | .ok j =>
          match j.getString? "target" with
          | none => errJson "args: member \"target\" is required"
          | some target =>
              let a : RequestArgs :=
                { target
                , body := (j.getString? "body").getD ""
                , contentType := (j.getString? "contentType").getD "text/turtle"
                , slug := j.getString? "slug"
                , ifNoneMatchStar := (j.getBool? "ifNoneMatchStar").getD false
                , state := j.getString? "state" }
              let r := buildRequest k a
              okWith [("request", .object
                [ ("method", .string r.method)
                , ("target", .string r.path)
                , ("headers", .array (r.headers.map (fun (n, v) =>
                    Json.array [.string n, .string v])))
                , ("body", .string r.body) ])]

private def stringsJson (xs : List String) : Json := .array (xs.map Json.string)

private def optJson : Option String → Json
  | some s => .string s
  | none   => .null

/-- `solidClientResponse(kind, responseJson)` — interpret a response.

The response document is the one `solidStep` answers, with extra members two
kinds need: `webId` and `baseIri` for `profile`, and `target` — the request
target the reply answers — for `storage`, which the walk of §4.1 needs to
move up the path hierarchy. -/
def solidClientResponse (kind responseJson : String) : String :=
  match parseJson responseJson with
  | .error e => errJson s!"response: {toString e}"
  | .ok j =>
      let headers : List (String × String) :=
        match j.getArray? "headers" with
        | none => []
        | some items => items.filterMap (fun it =>
            match it with
            | .array [.string n, .string v] => some (n.toLower, v)
            | _ => none)
      let status := match j.field? "status" with
        | some (.number s) => (s.toNat?).getD 0
        | _ => 0
      let body := (j.getString? "body").getD ""
      let resp : Response := { status, headers, body }
      match kind with
      | "storage" =>
          -- The optional "target" member is the resource the reply
          -- answers. With it the interpretation decides the storage walk
          -- of Solid Protocol §4.1 and answers "continue" and "state";
          -- without it the reply is read as facts about one resource.
          let r := storageReading (j.getString? "target") resp
          let f := r.facts
          okWith [("interpretation", .object
            [ ("isStorage", .bool f.isStorage)
            , ("storage", optJson r.storage)
            , ("storageDescription", optJson f.storageDescription)
            , ("owner", optJson f.owner)
            , ("lastModified", optJson f.lastModified)
            , ("allow", stringsJson f.allow)
            , ("continue", .bool r.more)
            , ("state", optJson r.next) ])]
      | "auxiliaries" =>
          let f := resourceFacts resp
          okWith [("interpretation", .object
            [ ("acl", optJson f.acl)
            , ("describedby", optJson f.describedBy)
            , ("inbox", optJson f.inbox) ])]
      | "containment" =>
          -- The base of the listing is the request URI (`requestUri`),
          -- or the target when that is already absolute.
          let base := (j.getString? "requestUri").orElse (fun _ =>
            (j.getString? "target").filter (fun t => (t.splitOn "://").length > 1))
          let members := containmentMembers base resp
          okWith [("interpretation", .object
            [ ("contains", stringsJson members)
            , ("count", .number (toString members.length)) ])]
      | "wacAllow" =>
          okWith [("interpretation", .object
            ((wacAllowOf resp).map (fun (g, ms) => (g, stringsJson ms))))]
      | "profile" =>
          match j.getString? "webId" with
          | none => errJson "response: the profile kind needs a \"webId\" member"
          | some webId =>
              let baseIri := (j.getString? "baseIri").getD webId
              let p := readProfile webId baseIri body
              okWith [("interpretation", .object
                [ ("webId", .string p.webId)
                , ("storages", stringsJson p.storages)
                , ("inbox", optJson p.inbox)
                , ("oidcIssuers", stringsJson p.oidcIssuers)
                , ("names", stringsJson p.names) ])]
      | "created" =>
          okWith [("interpretation", .object
            [ ("status", .number (toString resp.status))
            , ("location", optJson (createdLocation? resp))
            , ("mayRetryWithCredentials", .bool (mayRetryWithCredentials resp)) ])]
      | _ => errJson s!"solidClientResponse: unknown kind '{kind}' (storage | containment | auxiliaries | profile | wacAllow | created)"

/-- The op names this module serves. -/
def solidOpNames : List String :=
  ["solidOpen", "solidStep", "solidClose", "solidFetched", "solidClientRequest",
   "solidClientResponse"]

end L4Wasm.Ops
