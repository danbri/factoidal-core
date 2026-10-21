/-
L4Factoidal.LWS.AccessGrants — the access request and access grant
endpoints of LWS 1.0 core §Access Requests and Grants, decided in Lean.
https://github.com/danbri/factoidal/issues/913

Source: w3c/lws-protocol 9a08ff65 (2026-10-19), `lws10-core/lws-access-requests.html`.
The data model, the access profile and what a grant permits are
`L4Factoidal.LWS.AccessPolicy`; enforcement is `Authorization.decide`.

## What the draft requires of the endpoints

* Discovery: "A storage MAY advertise support for access requests and
  access grants in its storage description resource. When such support is
  advertised, a service object describing an endpoint for access requests
  MUST have a type equal to the string AccessRequestService, and a service
  object describing an endpoint for access grants MUST have a type equal to
  the string AccessGrantService. A service object SHOULD include a
  conformsTo property". `Binding.storageDescription` with
  `Config.accessGrants`; both carry `conformsTo`
  `["https://www.w3.org/ns/lws#AccessProfile"]`.
* Protocol: "The access request and access grant endpoints are LWS
  containers and MUST conform to the rules defined in this specification."
  GET on an endpoint answers an `application/lws+json` container listing
  (paged at `Config.pageSize`) with `Link: <lws#Container>; rel="type"`.
* "These endpoints minimally require support for GET and POST operations.
  The DELETE operation is RECOMMENDED." All three are supported: "POST / —
  Create an access request", "GET / — Retrieve a list of access requests",
  "GET /:id — Retrieve a specific access request", "DELETE /:id — Cancel an
  access request", and the same four for grants ("DELETE /:id — Revoke an
  access grant").
* "These endpoints MUST support the JSON-LD serialization [...] for both
  request and response payloads." Requests are `application/lws+json`
  (also `application/ld+json` and `application/json`; another media type is
  415); responses are `application/lws+json`.
* "An agent creates an access request by submitting a POST request to the
  access request endpoint. A storage controller creates an access grant by
  submitting a POST request to the access grant endpoint." and "A
  successful POST operation MUST respond with a Location header set to the
  URL of the new resource." 201 with `Location`.
* Notifications: "When an inbox property is present on an access request
  or access grant, the server SHOULD deliver notifications to that
  endpoint, informing an assignee of the event." and "Access Grant
  creation: When a new access grant is created, the requesting agent SHOULD
  be notified at the inbox specified in the associated access request."
  `announce`: one `Notification` (the core notification data model) with a
  `Create` activity whose object is the new grant, POSTed to the grant's
  inbox and to the inbox of every access request that names one of the
  grant's assignees.

## Server choices the draft leaves open, each stated once

* The storage controller ("an agent that controls all resources in a
  storage") is an agent with `acl:Control` on the storage root under Web
  Access Control (`isController`); in the development mode with no
  authorization every agent is.
* Only the storage controller creates or revokes grants (403 otherwise).
  Any authenticated agent creates access requests. A request is visible to
  the agent that made it and to the controller; a grant to the controller
  and to the agents it names as assignee. Another agent gets 404. The agent
  that made a request, and the controller, may cancel it.
* A storage controller answers an access request by creating a grant (the
  requesting agent is notified, above) or by deleting the request. The
  draft defines no other answer and no link from a grant to a request.
* An inbox inside this storage is not delivered to (a delivery there would
  create a resource).
* Not done: "Access Request creation: When a new access request is
  submitted, the storage controller SHOULD be notified." The draft names no
  inbox for the controller. https://github.com/danbri/factoidal/issues/916,
  an expected failure in `tests/lws/draft-binding.mjs`.
-/
import L4Factoidal.LWS.Notifications

namespace L4Factoidal.LWS.AccessGrants

open L4Factoidal.JSON
open L4Factoidal.LWS
open L4Factoidal.LWS.AccessPolicy
open L4Factoidal.LWS.Notifications
open L4Factoidal.HTTP (Request Response)
open L4Factoidal.Solid.Server (allowed aclGraphOf)

variable {σ : Type}

/-- The two endpoints. -/
inductive Endpoint where
  | requests | grants
deriving DecidableEq, Repr

def Endpoint.path : Endpoint → String
  | .requests => accessRequestsPath
  | .grants => accessGrantsPath

/-- The document type each endpoint holds. -/
def Endpoint.kind : Endpoint → String
  | .requests => "AccessRequest"
  | .grants => "AccessGrant"

def Endpoint.idPrefix : Endpoint → String
  | .requests => "r"
  | .grants => "g"

def endpointOf? (p : String) : Option Endpoint :=
  if p.startsWith accessRequestsPath then some .requests
  else if p.startsWith accessGrantsPath then some .grants
  else none

def Endpoint.records (e : Endpoint) (s : AccessState) : List Record :=
  match e with
  | .requests => s.requests
  | .grants => s.grants

def Endpoint.setRecords (e : Endpoint) (s : AccessState) (rs : List Record) : AccessState :=
  match e with
  | .requests => { s with requests := rs }
  | .grants => { s with grants := rs }

/-- The storage controller: `acl:Control` on the storage root. -/
def isController (S : Store σ) (cfg : Config) (a : Authorization.AuthzConfig)
    (who : Option String) (st : σ) : Bool :=
  a.insecureNoAuth ||
    allowed S aclGraphOf cfg.baseIri st rootPath { webId := who } .control

/-- The IRIs a document's `storage` may give for this storage: its
canonical URI (the storage description) and the storage root. -/
def storageIris (cfg : Config) (a : Authorization.AuthzConfig) : List String :=
  [Authorization.storageIri cfg a, storageIdOf cfg.baseIri, cfg.baseIri].eraseDups

def recordIri (baseIri : String) (e : Endpoint) (id : String) : String :=
  iriOfPath baseIri (e.path ++ id)

/-- A record as it is served: its document with `id`, the record's IRI. -/
def servedDoc (baseIri : String) (e : Endpoint) (r : Record) : Json :=
  match r.doc with
  | .object fs =>
      .object (fs.filter (·.1 == "@context") ++ [("id", .string (recordIri baseIri e r.id))] ++
        fs.filter (·.1 != "@context"))
  | other => other

/-- May this agent see this record? -/
def visible (e : Endpoint) (controller : Bool) (agent : Option String) (r : Record) : Bool :=
  controller || match e with
    | .requests => r.creator == agent && agent.isSome
    | .grants => agent.isSome && r.policies.any (fun p => agent == some p.assignee)

private def lwsJson (status : Nat) (doc : String) (extra : List (String × String))
    (head : Bool := false) : Response :=
  ⟨status, [("content-type", mediaLwsJson)] ++ extra, if head then "" else doc, none⟩

private def etagOf (doc : String) : String := "\"access-" ++ hex8 (fnv1a32 doc.toUTF8) ++ "\""

/-- The listing of an endpoint (an LWS container). -/
def listingJson (baseIri : String) (e : Endpoint) (items : List Record) (total : Nat) : String :=
  toStringCompact (.object
    [ ("@context", .string lwsProfile)
    , ("id", .string (iriOfPath baseIri e.path))
    , ("type", .string "Container")
    , ("totalItems", .number (toString total))
    , ("items", .array (items.map (fun r =>
        let doc := toStringCompact (servedDoc baseIri e r)
        Json.object
          [ ("id", .string (recordIri baseIri e r.id))
          , ("type", .string "DataResource")
          , ("format", .string mediaLwsJson)
          , ("size", .number (toString doc.utf8ByteSize))
          , ("modified", .string (isoDateTime r.created)) ]))) ])

/-- Is this a media type of the JSON-LD serialization? -/
def jsonMedia (ct : Option String) : Bool :=
  match ct.map baseMedia with
  | some m => m == mediaLwsJson || m == "application/ld+json" || m == "application/json"
  | none => false

/-- One request to an access endpoint by `agent` (already authenticated by
`Authorization.decide`). The answer, the new access state, and the grant
it created, if any. -/
def accessStep (S : Store σ) (cfg : Config) (a : Authorization.AuthzConfig) (now : Nat)
    (agent : Option String) (r : Request) (path : String) (st : σ) :
    Response × AccessState × Option Record :=
  let acc := a.access
  let base := cfg.baseIri
  let storageLink : Link := { target := storageIdOf base, rel := lwsStorageRel }
  let controller := isController S cfg a agent st
  match endpointOf? path with
  | none => (problem 404 "no access endpoint has this name" path, acc, none)
  | some e =>
  if path == e.path then
    let allow := "GET, HEAD, OPTIONS, POST"
    match r.method with
    | "GET" | "HEAD" =>
        let (_, query0) := splitTarget r.path
        let query := if r.queryStr != "" then r.queryStr else query0
        let mine := (e.records acc).filter (visible e controller agent)
        let k := cfg.pageSize
        let count := pageCount mine.length k
        let pageNo : Option Nat := if query == "" then some 1 else pageOfQuery? query
        match pageNo with
        | none => (problem 404 "no page of the listing has this name" path, acc, none)
        | some n =>
            if n == 0 || n > count then (problem 404 "the listing has no such page" path, acc, none)
            else
            let items := if paginated mine.length k then pageAt mine k (n - 1) else mine
            let pageLink (rel : String) (m : Nat) : Link := { target := path ++ "?" ++ pageQuery m, rel }
            let links : List Link :=
              [{ target := lwsContainerType, rel := "type" }, storageLink] ++
              (if paginated mine.length k then
                 [pageLink "first" 1, pageLink "last" count] ++
                 (if n < count then [pageLink "next" (n + 1)] else []) ++
                 (if n > 1 then [pageLink "prev" (n - 1)] else [])
               else [])
            let doc := listingJson base e items mine.length
            (lwsJson 200 doc [("allow", allow), ("accept-post", mediaLwsJson),
                ("etag", etagOf doc), ("link", renderLinks links)] (r.method == "HEAD"), acc, none)
    | "OPTIONS" => (⟨204, [("allow", allow), ("accept-post", mediaLwsJson)], "", none⟩, acc, none)
    | "POST" =>
        if !jsonMedia (r.header? "content-type") then
          (problem 415 ("an " ++ e.kind ++ " is application/lws+json") path
            [("accept-post", mediaLwsJson)], acc, none)
        else if e == .grants && !controller then
          (Authorization.forbidden cfg path, acc, none)
        else
        match (String.fromUTF8? r.content).bind parseJson? with
        | none => (problem 400 "the request is not a JSON document" path, acc, none)
        | some j =>
            match parseDoc base (storageIris cfg a) e.kind j with
            | .error msg => (problem 400 msg path, acc, none)
            | .ok p =>
                let id := e.idPrefix ++ toString acc.seq
                let rec_ : Record :=
                  { id, creator := agent, created := now, doc := p.doc, policies := p.policies
                    inbox := p.inbox }
                let acc' := { e.setRecords acc (e.records acc ++ [rec_]) with
                              seq := acc.seq + 1, revision := acc.revision + 1 }
                let doc := toStringCompact (servedDoc base e rec_)
                (lwsJson 201 doc [("location", recordIri base e id), ("etag", etagOf doc),
                   ("link", renderLinks [storageLink])], acc',
                 if e == .grants then some rec_ else none)
    | _ => (problem 405 ("the " ++ e.kind ++ " endpoint accepts GET, HEAD, OPTIONS and POST") path
              [("allow", allow)], acc, none)
  else
    let id := (path.drop e.path.length).toString
    let allow := "GET, HEAD, OPTIONS, DELETE"
    match (e.records acc).find? (fun x => x.id == id && visible e controller agent x) with
    | none => (problem 404 "no access record visible to this agent has this name" path, acc, none)
    | some x =>
        match r.method with
        | "GET" | "HEAD" =>
            let doc := toStringCompact (servedDoc base e x)
            (lwsJson 200 doc [("allow", allow), ("etag", etagOf doc),
               ("link", renderLinks [{ target := lwsDataResourceType, rel := "type" },
                                     { target := e.path, rel := "up" }, storageLink])]
               (r.method == "HEAD"), acc, none)
        | "OPTIONS" => (⟨204, [("allow", allow)], "", none⟩, acc, none)
        | "DELETE" =>
            let mayDelete := controller || (e == .requests && x.creator == agent)
            if !mayDelete then (Authorization.forbidden cfg path, acc, none)
            else
              (⟨204, [], "", none⟩,
               { e.setRecords acc ((e.records acc).filter (fun y => y.id != id)) with
                 revision := acc.revision + 1 }, none)
        | _ => (problem 405 ("an " ++ e.kind ++ " accepts GET, HEAD, OPTIONS and DELETE") path
                  [("allow", allow)], acc, none)

/-- The inboxes to tell of a new grant: its own, and those of the access
requests that name one of its assignees; never one inside this storage. -/
def inboxesFor (baseIri : String) (acc : AccessState) (g : Record) : List String :=
  let assignees := g.policies.map (·.assignee)
  let fromRequests := (acc.requests.filter (fun q =>
    q.policies.any (fun p => assignees.contains p.assignee))).filterMap (·.inbox)
  (g.inbox.toList ++ fromRequests).eraseDups.filter (fun u =>
    (urlParts? u).isSome && !u.startsWith baseIri)

/-- The notification of a new grant: one `Create` activity about the grant
(an LWS data resource in the grant endpoint), one delivery per inbox. -/
def announce (baseIri : String) (signer : Option Signer) (now : Nat) (acc : AccessState)
    (g : Record) (ns : NotifState) : NotifState × List Delivery :=
  let inboxes := inboxesFor baseIri acc g
  if inboxes.isEmpty then (ns, []) else
  let change : Change := { type := .create, path := accessGrantsPath ++ g.id, kind := .dataResource }
  let body := toStringCompact (envelopeJson baseIri
    [activityJson baseIri (activityId ns.run ns.seq) (isoDateTime now) change])
  let pend : List Pending := inboxes.zipIdx.map (fun (u, k) =>
    { id := "d" ++ toString (ns.seq + 1 + k), subId := "", inbox := u, body, attempt := 1 })
  ({ ns with seq := ns.seq + 1 + inboxes.length
             pending := (pend.reverse ++ ns.pending).take pendingLimit },
   pend.map (deliveryOf signer now))

/-- One request to a storage with access requests and grants: the access
endpoints here, everything else through `next` (the notification layer,
or the index services above it). The answer carries the new access state
(to keep in `AuthzConfig.access`). -/
def serverStepWith (V : JOSE.Verifiers) (S : Store σ) (cfg : Config)
    (a : Authorization.AuthzConfig) (signer : Option Signer) (now : Nat) (r : Request)
    (st : σ) (ns : NotifState)
    (next : Request → σ → NotifState →
      Sum (String × String) (Response × σ × NotifState × List Delivery)) :
    Sum (String × String) (Response × σ × NotifState × AccessState × List Delivery) :=
  let (path, _) := splitTarget r.path
  if cfg.accessGrants && isAccessPath path && validTarget path then
    match Authorization.decide V S cfg a now r st with
    | .fetch i u => .inl (i, u)
    | .respond resp => .inr (resp, st, ns, a.access, [])
    | .proceed agent =>
        let (resp, acc', created) := accessStep S cfg a now agent r path st
        match created with
        | none => .inr (resp, st, ns, acc', [])
        | some g =>
            let (ns', ds) := announce cfg.baseIri signer now acc' g ns
            .inr (resp, st, ns', acc', ds)
  else
    match next r st ns with
    | .inl x => .inl x
    | .inr (resp, st', ns', ds) => .inr (resp, st', ns', a.access, ds)

/-- `serverStepWith` over the notification layer. -/
def serverStep (V : JOSE.Verifiers) (S : Store σ) (cfg : Config)
    (a : Authorization.AuthzConfig) (signer : Option Signer) (now : Nat) (r : Request)
    (st : σ) (ns : NotifState) :
    Sum (String × String) (Response × σ × NotifState × AccessState × List Delivery) :=
  serverStepWith V S cfg a signer now r st ns
    (fun r st ns => Notifications.serverStep V S cfg a signer now r st ns)

/-! ## Theorems -/

/-- **Only the storage controller creates grants.** A POST to the grant
endpoint by an agent that is not the controller changes nothing and creates
no grant. (`endpointOf? accessGrantsPath = some .grants` is a `#guard` in
`AccessGrantsTests`.) -/
theorem accessStep_grant_needs_controller (S : Store σ) (cfg : Config)
    (a : Authorization.AuthzConfig) (now : Nat) (agent : Option String) (r : Request) (st : σ)
    (hm : r.method = "POST") (hc : isController S cfg a agent st = false)
    (he : endpointOf? accessGrantsPath = some .grants) :
    (accessStep S cfg a now agent r accessGrantsPath st).2 = (a.access, none) := by
  unfold accessStep
  simp only [he, Endpoint.path, hm, hc]
  split
  · split <;> rfl
  · rename_i hne
    simp at hne

end L4Factoidal.LWS.AccessGrants
