/-
L4Factoidal.LWS.Client.Machine — the LWS client as one pure state machine.
https://github.com/danbri/factoidal/issues/917

Design record: `docs/designissues/2026-10-22-lws-client.md` (the
requirements table there names, for each client statement of the drafts,
the definition below that decides it).

    step : Verifiers → ClientState → Event → ClientState × Action

The caller states an operation (`Op`). `step` names the next HTTP request
(`Action.fetch`), reads each answer (`Event.response`), and ends with
`Action.done` or `Action.fail`. A host only sends what `fetch` names and
gives the answer back. The state is a JSON document between steps
(`stateJson`, `stateOfJson`), so the wasm ops hold nothing.

Sources, w3c/lws-protocol commit 9a08ff65 (2026-10-19), verbatim:

lws10-core §Authorization
* Discovery Validation by a Client: "Before requesting an access token, a
  client MUST perform the following checks, each of which compares a
  discovered value against the requested URI that produced the 401
  response. If any check fails, the client MUST NOT use the discovered
  values to request an access token." The three checks: "The
  resource_metadata URL MUST have the same scheme and authority as the
  requested URI." "The resource value of the protected resource metadata
  document MUST be identical to the requested URI" "The client MUST obtain
  the storage description of the storage identified by the Link header, and
  the serviceEndpoint of its StorageRoot service MUST have the same scheme
  and authority as the requested URI." — `on401`, `authStep`, `validated`.
* Authorization Server Metadata: "This metadata resource MUST be available
  at a URL with the path /.well-known/lws-configuration." —
  `Wire.asMetadataUrl`; the `issuer` of the document must be the issuer the
  URL was built from (RFC 8414 §3.3).
* Token Exchange: "The resource parameter is REQUIRED. ... The supplied
  value MUST be the URI of the storage that contains the requested
  resource, as provided in the Link header of an unauthorized response."
  and "The subject_token parameter is REQUIRED." — `tokenRequest`.
* Presentation: "A client MUST present an access token to a storage server
  using the Authorization header with an authentication scheme as defined
  in [RFC6750]." — `attachToken`. A token goes only to URLs under the
  StorageRoot endpoint of the storage it was issued for.

lws10-core §Operations
* Create: "To create a Container, the client MUST include a Link header
  with rel="type" pointing to the Container type" and "Repeating it may
  create duplicates; clients SHOULD avoid unintentional retries or use
  unique identifiers/checks to prevent this." — `createReq`, phase
  `createCheck`.
* Create: "Server-managed metadata MUST be generated automatically by the
  server upon creation and MUST NOT be overridden by client-provided
  links." — `clientLinksOk` refuses a caller's link with a server-managed
  relation before anything is sent.
* Update: "Clients SHOULD use conditional requests as defined in [RFC9110]
  to avoid overwriting concurrent changes." and "clients MAY include Link
  headers in the PUT/PATCH request to the resource URI and specify the
  preference 'Prefer: set-linkset'" — `preconditionHeaders`, `updateReq`.
* Delete: "Clients MUST use the Depth: infinity header to request for a
  recursive delete" and "Clients MAY include an If-Match header with an
  ETag for concurrency checks." — `deleteReq`.
* Metadata: "Clients SHOULD NOT assume support for PUT or specific patch
  formats unless they are advertised in the resource headers and MUST
  handle 405 Method Not Allowed or 415 Unsupported Media Type responses
  gracefully." — phases `linksetMeta` and `linksetRecheck`.
* Moving Resources: "A client moves a resource by applying a partial update
  to the resource's linkset resource, replacing the target of the up link
  with the identifier of the destination container." and "Clients MUST NOT
  assume that the up link is modifiable in the absence of this capability."
  — op `move`, `movePatch`.

lws10-index: "The query format is identified by the request's Content-Type
header field, which MUST be present" and, for a page refused with 404 or
410, "Clients SHOULD restart" — op `search`.

lws10-notifications-webhook §5.2: "The keyid value MUST be a URL with a
fragment component." and "The id property of the top-level document map
MUST match the storage identifier." — op `verifyNotification`.

Retry rules, each decided here: a 412 is retried only when the caller set
`retry412`; after a 405 or 415 the same request is never sent again; after
a POST answered 5xx or lost, the same POST is never sent again; a search
page refused with 404 or 410 restarts the QUERY once; a 401 with a token
attached drops it and exchanges again, at most twice per operation.

`step` ends with `enforce`, which turns any action that breaks one of the
four properties of `Client/Theorems.lean` into `fail`. The theorems hold
for every state and event; the `#guard`s of `Client/Tests.lean` show that
the ordinary flows never reach the refusal.
-/
import L4Factoidal.LWS.Client.Wire
import L4Factoidal.JOSE.Jws
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.LWS.Client

open L4Factoidal.JSON
open L4Factoidal.LWS

/-! ## Vocabulary -/

def tokenExchangeGrant : String := "urn:ietf:params:oauth:grant-type:token-exchange"
def mediaForm : String := "application/x-www-form-urlencoded"
def mediaJson : String := "application/json"

/-- The kinds of operation. -/
def opKinds : List String :=
  [ "discover", "read", "head", "create", "update", "patch", "delete", "readLinkset"
  , "updateLinkset", "move", "list", "typeIndex", "search", "subscribe", "unsubscribe"
  , "requestAccess", "grantAccess", "getAccess", "revokeAccess", "verifyNotification" ]

/-- The kinds whose write takes a precondition. -/
def conditionalKinds : List String := ["update", "patch", "delete", "updateLinkset", "move"]

/-! ## The operation a caller asks for -/

/-- One operation. Members not used by a kind are ignored. -/
structure Op where
  kind : String
  /-- The target: a resource, a container, a subscription, an access
  request or grant, or (for `verifyNotification`) the inbox URL as
  subscribed. -/
  url : String := ""
  body : ByteArray := ByteArray.empty
  mediaType : String := ""
  slug : String := ""
  /-- `create`: make a container. -/
  container : Bool := false
  /-- `create`: `rel="type"` links to the caller's classes. -/
  types : List String := []
  /-- `create`, `update`, `patch`: client links, as `Link` field values. -/
  links : List String := []
  /-- `none`, `ifMatch`, `ifMatchCurrent`, `ifNoneMatchStar`, `ifUnmodifiedSince`;
  empty: the default of the kind (`defaultPrecondition`, applied by `start`). -/
  precondition : String := ""
  /-- The entity tag of `ifMatch`, the HTTP-date of `ifUnmodifiedSince`. -/
  tag : String := ""
  retry412 : Nat := 0
  recursive : Bool := false
  accept : String := ""
  /-- `search`: the `application/lws-query+json` filter. -/
  query : Json := .object []
  /-- `subscribe`. -/
  topics : List String := []
  inbox : String := ""
  /-- `requestAccess`, `grantAccess`: one policy. -/
  actions : List String := []
  assignee : String := ""
  targets : List String := []
  constraint : Json := .null
  /-- `move`: the destination container. -/
  destination : String := ""
  /-- `verifyNotification`: the method and the header fields received. -/
  method : String := ""
  headers : List (String × String) := []
  /-- `verifyNotification`: the request target received; the inbox URL as
  subscribed is `url` resolved with it (RFC 3986 §5.2). Empty: `url` itself. -/
  requestTarget : String := ""

/-- The precondition a kind takes when the caller names none: the current
entity tag for the writes that replace or patch (lws10-core §Update
Resource, "Clients SHOULD use conditional requests"), none for the rest. -/
def defaultPrecondition (kind : String) : String :=
  if kind == "update" || kind == "patch" || kind == "updateLinkset" || kind == "move" then
    "ifMatchCurrent" else "none"

/-- The operation with an empty precondition replaced by the default of its
kind. -/
def Op.normalize (op : Op) : Op :=
  if op.precondition == "" then { op with precondition := defaultPrecondition op.kind } else op

def opJson (op : Op) : Json :=
  .object
    [ ("kind", .string op.kind), ("url", .string op.url)
    , ("bodyBase64", .string (Base64.encode op.body)), ("mediaType", .string op.mediaType)
    , ("slug", .string op.slug), ("container", .bool op.container)
    , ("types", strsJson op.types), ("links", strsJson op.links)
    , ("precondition", .string op.precondition), ("tag", .string op.tag)
    , ("retry412", natJson op.retry412), ("recursive", .bool op.recursive)
    , ("accept", .string op.accept), ("query", op.query), ("topics", strsJson op.topics)
    , ("inbox", .string op.inbox), ("actions", strsJson op.actions)
    , ("assignee", .string op.assignee), ("targets", strsJson op.targets)
    , ("constraint", op.constraint), ("destination", .string op.destination)
    , ("method", .string op.method), ("headers", headersJson op.headers)
    , ("requestTarget", .string op.requestTarget) ]

/-- Read an operation document. `kind` is required. -/
def opOfJson (j : Json) : Except String Op := do
  let kind ← (j.getString? "kind").elim (.error "op: member \"kind\" is required") .ok
  if !opKinds.contains kind then
    .error ("op: unknown kind \"" ++ kind ++ "\" (" ++ ", ".intercalate opKinds ++ ")")
  let precondition := (j.getString? "precondition").getD ""
  if !["", "none", "ifMatch", "ifMatchCurrent", "ifNoneMatchStar", "ifUnmodifiedSince"].contains precondition then
    .error ("op: unknown precondition \"" ++ precondition ++ "\"")
  .ok { kind, url := jStr j "url", body := jBody j, mediaType := jStr j "mediaType"
      , slug := jStr j "slug", container := jBool j "container", types := jStrs j "types"
      , links := jStrs j "links", precondition, tag := jStr j "tag"
      , retry412 := jNat j "retry412", recursive := jBool j "recursive"
      , accept := jStr j "accept", query := (j.field? "query").getD (.object [])
      , topics := jStrs j "topics", inbox := jStr j "inbox", actions := jStrs j "actions"
      , assignee := jStr j "assignee", targets := jStrs j "targets"
      , constraint := jAny j "constraint", destination := jStr j "destination"
      , method := jStr j "method", headers := jHeaders j "headers"
      , requestTarget := jStr j "requestTarget" }

/-! ## Session: tokens kept between operations -/

/-- An access token and the storage it was issued for. `root` is the
StorageRoot endpoint: the token goes only to URLs under it. -/
structure TokenEntry where
  storage : String
  root : String
  token : String

/-- What a client keeps between operations: its tokens and the subject
token (an authentication credential) it exchanges for them. -/
structure Session where
  tokens : List TokenEntry := []
  subjectToken : String := ""
  subjectTokenType : String := ""

def sessionJson (s : Session) : Json :=
  .object [ ("tokens", .array (s.tokens.map (fun t => .object
              [("storage", .string t.storage), ("root", .string t.root), ("token", .string t.token)])))
          , ("subjectToken", .string s.subjectToken)
          , ("subjectTokenType", .string s.subjectTokenType) ]

def sessionOfJson (j : Json) : Session :=
  { tokens := ((j.getArray? "tokens").getD []).filterMap (fun t =>
      match t.getString? "storage", t.getString? "root", t.getString? "token" with
      | some s, some r, some k => some { storage := s, root := r, token := k }
      | _, _, _ => none)
    subjectToken := jStr j "subjectToken", subjectTokenType := jStr j "subjectTokenType" }

/-! ## The validation record of lws10-core §Discovery Validation by a Client -/

/-- What a 401 told the client, and what the client found when it checked.
-/
structure AuthCtx where
  /-- The requested URI that produced the 401. -/
  requestUri : String
  /-- The `resource_metadata` URL of the challenge. -/
  metadataUrl : String
  /-- The storage of the 401's `Link rel="…lws#storage"`. -/
  storage : String
  /-- The `resource` of the protected resource metadata document. -/
  metadataResource : String := ""
  asIssuer : String := ""
  /-- The `serviceEndpoint` of the StorageRoot service of the storage
  description. -/
  rootEndpoint : String := ""
  tokenEndpoint : String := ""

/-- The three checks, over the recorded values. -/
def validated (c : AuthCtx) : Bool :=
  sameOrigin c.metadataUrl c.requestUri && c.metadataResource == c.requestUri &&
  sameOrigin c.rootEndpoint c.requestUri

/-- The three checks as a proposition. -/
def Validated (c : AuthCtx) : Prop :=
  sameOrigin c.metadataUrl c.requestUri = true ∧ c.metadataResource = c.requestUri ∧
  sameOrigin c.rootEndpoint c.requestUri = true

theorem validated_iff (c : AuthCtx) : validated c = true ↔ Validated c := by
  unfold validated Validated
  simp [Bool.and_eq_true, beq_iff_eq, and_assoc]

def authJson (c : AuthCtx) : Json :=
  .object [ ("requestUri", .string c.requestUri), ("metadataUrl", .string c.metadataUrl)
          , ("storage", .string c.storage), ("metadataResource", .string c.metadataResource)
          , ("asIssuer", .string c.asIssuer), ("rootEndpoint", .string c.rootEndpoint)
          , ("tokenEndpoint", .string c.tokenEndpoint) ]

def authOfJson (j : Json) : AuthCtx :=
  { requestUri := jStr j "requestUri", metadataUrl := jStr j "metadataUrl"
    storage := jStr j "storage", metadataResource := jStr j "metadataResource"
    asIssuer := jStr j "asIssuer", rootEndpoint := jStr j "rootEndpoint"
    tokenEndpoint := jStr j "tokenEndpoint" }

/-! ## State, events, actions -/

inductive Phase where
  | init | main | tagRead | discoverHead | discoverDesc | linksetFind | linksetMeta
  | linksetRecheck | paging | createCheck | inboxDesc
  | authMeta | authDesc | authAsMeta | authToken | finished
deriving DecidableEq, Repr

def Phase.name : Phase → String
  | .init => "init" | .main => "main" | .tagRead => "tagRead"
  | .discoverHead => "discoverHead" | .discoverDesc => "discoverDesc"
  | .linksetFind => "linksetFind" | .linksetMeta => "linksetMeta"
  | .linksetRecheck => "linksetRecheck" | .paging => "paging"
  | .createCheck => "createCheck" | .inboxDesc => "inboxDesc"
  | .authMeta => "authMeta" | .authDesc => "authDesc" | .authAsMeta => "authAsMeta"
  | .authToken => "authToken" | .finished => "finished"

def phases : List Phase :=
  [ .init, .main, .tagRead, .discoverHead, .discoverDesc, .linksetFind, .linksetMeta
  , .linksetRecheck, .paging, .createCheck, .inboxDesc, .authMeta, .authDesc, .authAsMeta
  , .authToken, .finished ]

def phaseOfName (n : String) : Phase := (phases.find? (fun p => p.name == n)).getD .finished

/-- The state of one operation. -/
structure ClientState where
  op : Op
  phase : Phase := .init
  session : Session := {}
  /-- The request the next response answers. -/
  sent : Option Req := none
  /-- The request to send again once a token arrives, and its phase. -/
  pending : Option Req := none
  pendingPhase : Phase := .main
  auth : Option AuthCtx := none
  /-- The entity tag last read (`ifMatchCurrent`, a 412, a linkset). -/
  etag : String := ""
  retries : Nat := 0
  /-- Token exchanges left for this operation. -/
  exchanges : Nat := 2
  /-- The items collected so far (`list`, `typeIndex`, `search`). -/
  items : List Json := []
  pages : Nat := 0
  restarted : Bool := false
  /-- The storage description in use. -/
  storage : Json := .null
  /-- The service endpoint the operation uses. -/
  endpoint : String := ""
  linkset : String := ""
  allow : List String := []
  acceptPatch : List String := []
  linksetDoc : Json := .null
  /-- A status kept for the result (the refused status, the lost create). -/
  note : Nat := 0
  /-- Steps left: every step spends one. -/
  fuel : Nat := 512

inductive Event where
  | start
  | response (r : Resp)
  | transportError (message : String)

inductive Action where
  | fetch (r : Req)
  | done (result : Json)
  | fail (error : Json)

/-! ## Small helpers -/

def errJ (code : String) (extra : List (String × Json) := []) : Json :=
  .object (("code", .string code) :: extra)

def finish (s : ClientState) (a : Action) : ClientState × Action :=
  ({ s with phase := .finished }, a)

def failWith (s : ClientState) (code : String) (extra : List (String × Json) := []) :
    ClientState × Action :=
  finish s (.fail (errJ code extra))

/-- Attach the access token of the storage whose root the URL is under
(lws10-core §Presentation: the `Authorization` header, RFC 6750 §2.1). -/
def attachToken (ses : Session) (r : Req) : Req :=
  if (r.header? "authorization").isSome then r else
  match ses.tokens.find? (fun t => t.root != "" && r.url.startsWith t.root) with
  | some t => { r with headers := r.headers ++ [("Authorization", "Bearer " ++ t.token)] }
  | none => r

/-- Send a request to the storage (with its token, if any). -/
def send (s : ClientState) (ph : Phase) (r : Req) : ClientState × Action :=
  let r := attachToken s.session r
  ({ s with phase := ph, sent := some r }, .fetch r)

/-- Send a request that carries no access token (metadata, the
authorization server, a storage description read to verify a
notification). -/
def sendPublic (s : ClientState) (ph : Phase) (r : Req) : ClientState × Action :=
  ({ s with phase := ph, sent := some r }, .fetch r)

def getReq (url accept : String) : Req :=
  { method := "GET", url, headers := if accept == "" then [] else [("Accept", accept)] }

def headReq (url : String) : Req := { method := "HEAD", url }

/-- The URL the last request went to. -/
def sentUrl (s : ClientState) : String := (s.sent.map (·.url)).getD s.op.url

/-- The response details a result reports. -/
def respSummary (r : Resp) : List (String × Json) :=
  [ ("status", natJson r.status), ("headers", headersJson r.headers) ] ++
  (if r.body.size == 0 then [] else
    match String.fromUTF8? r.body with
    | some t => [("body", .string t)]
    | none => [("bodyBase64", .string (Base64.encode r.body))])

def statusFail (s : ClientState) (r : Resp) : ClientState × Action :=
  failWith s "status" (respSummary r)

/-! ## Preconditions (lws10-core §Update Resource, §Delete Resource) -/

/-- The precondition header fields of a write. `current` is the entity tag
last read; it replaces the caller's tag after a 412 re-read. -/
def preconditionHeaders (op : Op) (current : String) : List (String × String) :=
  match op.precondition with
  | "ifMatch" => [("If-Match", if current != "" then current else op.tag)]
  | "ifMatchCurrent" => [("If-Match", current)]
  | "ifNoneMatchStar" => [("If-None-Match", "*")]
  | "ifUnmodifiedSince" => [("If-Unmodified-Since", op.tag)]
  | _ => []

/-- Does the operation ask for a precondition on its write? -/
def wantsPrecondition (op : Op) : Bool :=
  conditionalKinds.contains op.kind && op.precondition != "none"

/-- A write: PUT, PATCH or DELETE. -/
def isWrite (r : Req) : Bool := r.method == "PUT" || r.method == "PATCH" || r.method == "DELETE"

/-- Does a request carry the header field of the operation's
precondition? -/
def carriesPrecondition (op : Op) (r : Req) : Bool :=
  match op.precondition with
  | "ifMatch" | "ifMatchCurrent" => (r.header? "if-match").any (· != "")
  | "ifNoneMatchStar" => r.header? "if-none-match" == some "*"
  | "ifUnmodifiedSince" => (r.header? "if-unmodified-since").any (· != "")
  | _ => true

/-! ## Request builders -/

/-- The caller's client links, parsed. -/
def callerLinks (op : Op) : List Link :=
  op.links.flatMap (fun v => match parseLinkField v with
    | .ok ls => ls
    | .error _ => [])

/-- Every caller link parses, and none has a server-managed relation other
than `type` (lws10-core §Create Resource: server-managed metadata "MUST NOT
be overridden by client-provided links"; §Metadata lists `linkset`, `type`,
`format`, `size`, `modified`; a `type` link to the caller's own class is
the metadata the index services read). -/
def clientLinksOk (op : Op) : Bool :=
  op.links.all (fun v => (parseLinkField v).toBool) &&
  (callerLinks op).all (fun l => l.rel.toLower == "type" || !serverManaged l.rel)

/-- The `Link` field values of a create: the container type
(lws10-core §Create Resource), the caller's types, the caller's links. -/
def createLinks (op : Op) : List String :=
  (if op.container then ["<" ++ lwsContainerType ++ ">; rel=\"type\""] else []) ++
  op.types.map (fun t => "<" ++ t ++ ">; rel=\"type\"") ++ op.links

def createReq (op : Op) : Req :=
  { method := "POST", url := op.url
    headers :=
      (if op.mediaType != "" then [("Content-Type", op.mediaType)] else []) ++
      (if op.slug != "" then [("Slug", op.slug)] else []) ++
      (createLinks op).map (fun v => ("Link", v))
    body := op.body }

/-- PUT of new content. Link fields are a combined update, which "MUST be
invoked explicitly via the Prefer header": they always go with
`Prefer: set-linkset`. -/
def updateReq (op : Op) (current : String) : Req :=
  { method := "PUT", url := op.url
    headers :=
      (if op.mediaType != "" then [("Content-Type", op.mediaType)] else []) ++
      preconditionHeaders op current ++
      (if op.links.isEmpty then [] else op.links.map (fun v => ("Link", v)) ++ [("Prefer", "set-linkset")])
    body := op.body }

def patchReq (op : Op) (current : String) : Req :=
  { method := "PATCH", url := op.url
    headers :=
      [("Content-Type", if op.mediaType != "" then op.mediaType else mediaJsonPatch)] ++
      preconditionHeaders op current ++
      (if op.links.isEmpty then [] else op.links.map (fun v => ("Link", v)) ++ [("Prefer", "set-linkset")])
    body := op.body }

def deleteReq (op : Op) (current : String) : Req :=
  { method := "DELETE", url := op.url
    headers := (if op.recursive then [("Depth", "infinity")] else []) ++ preconditionHeaders op current }

/-- The write of `update`, `patch` or `delete`. -/
def writeReq (op : Op) (current : String) : Req :=
  match op.kind with
  | "update" => updateReq op current
  | "patch" => patchReq op current
  | _ => deleteReq op current

/-! ## The storage description (lws10-core §Discovery) -/

/-- The `type` of a JSON object as a list (a string or an array). -/
def typesOf (j : Json) : List String :=
  match j.field? "type" with
  | some (.string t) => [t]
  | some (.array xs) => xs.filterMap Json.asString?
  | _ => []

/-- The service object of a type in a storage description. -/
def service? (desc : Json) (ty : String) : Option Json :=
  ((desc.getArray? "service").getD []).find? (fun sv => (typesOf sv).contains ty)

/-- The endpoint of a service, resolved against the description's URL. -/
def serviceEndpoint? (base : String) (desc : Json) (ty : String) : Option String :=
  (service? desc ty).bind (fun sv => (sv.getString? "serviceEndpoint").map (resolve base))

/-- Does the description describe a capability? -/
def hasCapability (desc : Json) (ty : String) : Bool :=
  ((desc.getArray? "capability").getD []).any (fun c => (typesOf c).contains ty)

/-! ## Access requests and grants (lws10-core §Access Requests and Grants) -/

def isAbsoluteUri (s : String) : Bool := (L4Factoidal.Syntax.parseIri s).scheme.isSome

/-- The arguments of an access document are usable: one or more actions, an
assignee that is a URI, targets that are URIs, an inbox that is a URI. -/
def accessArgsOk (op : Op) : Bool :=
  !op.actions.isEmpty && isAbsoluteUri op.assignee && op.targets.all isAbsoluteUri &&
  (op.inbox == "" || isAbsoluteUri op.inbox) &&
  (match op.constraint with
   | .null => true
   | .array cs => cs.all (fun c => (c.getString? "leftOperand").isSome &&
       (c.getString? "operator").isSome && (c.field? "rightOperand").isSome)
   | _ => false)

/-- An access request or grant with one policy: `@context`, `type`,
`storage`, `access` (each policy `type`, `action`, `assignee`, `target`,
`constraint`), `inbox`. -/
def accessDoc (ty storage : String) (op : Op) : Json :=
  .object ([ ("@context", .array [.string lwsProfile]), ("type", .array [.string ty])
           , ("storage", .string storage)
           , ("access", .array [ .object (
                [ ("type", .array [.string "AccessPolicy"]), ("action", strsJson op.actions)
                , ("assignee", .string op.assignee) ] ++
                (if op.targets.isEmpty then [] else
                  [("target", .object [("type", .string "StorageResource"), ("value", strsJson op.targets)])]) ++
                (match op.constraint with
                 | .array (c :: cs) => [("constraint", .array (c :: cs))]
                 | _ => [])) ]) ] ++
    (if op.inbox == "" then [] else [("inbox", .string op.inbox)]))

/-- A webhook subscription (lws10-core §Subscription Request,
lws10-notifications-webhook §Webhook Subscription). -/
def subscriptionDoc (op : Op) : Json :=
  .object [ ("type", .string webhookSubscriptionType)
          , ("topic", strsJson (if op.topics.isEmpty then [op.url] else op.topics))
          , ("inbox", .string op.inbox) ]

def jsonReq (method url : String) (doc : Json) : Req :=
  { method, url, headers := [("Content-Type", mediaLwsJson), ("Accept", mediaLwsJson)]
    body := (toStringCompact doc).toUTF8 }

/-- The search QUERY (lws10-index §Type Search, the baseline format). -/
def queryReq (url : String) (q : Json) : Req :=
  { method := "QUERY", url
    headers := [("Content-Type", mediaLwsQuery), ("Accept", mediaLwsJson)]
    body := (toStringCompact q).toUTF8 }

/-! ## Moving a resource (lws10-core §Moving Resources) -/

/-- The JSON Patch that moves `resource` to `dest`: a `test` of the current
`up` target and a `replace` of it, at the positions read from the linkset
document. -/
def movePatch (base resource dest : String) (doc : Json) : Option Json := do
  let ctxs ← doc.getArray? "linkset"
  let idx := (ctxs.zipIdx).find? (fun (c, _) => match c.getString? "anchor" with
    | some a => resolve base a == resource
    | none => false)
  let (ctx, i) ← idx.orElse (fun _ => (ctxs.head?).map (fun c => (c, 0)))
  let ups ← ctx.getArray? "up"
  let up ← ups.head?
  let cur ← up.getString? "href"
  let path := "/linkset/" ++ toString i ++ "/up/0/href"
  pure (.array [ .object [("op", .string "test"), ("path", .string path), ("value", .string cur)]
               , .object [("op", .string "replace"), ("path", .string path), ("value", .string dest)] ])

/-! ## Verifying a notification (lws10-notifications-webhook §5.2) -/

/-- The label and the parameters of a `Signature-Input` field with one
signature: `label=(...);params` (RFC 9421 §4.1). -/
def sigInput? (v : String) : Option (String × String) :=
  match v.splitOn "=" with
  | label :: rest =>
      let params := trimS (String.intercalate "=" rest)
      if params.startsWith "(" then some (trimS label, params) else none
  | [] => none

/-- The signature bytes of label `label` in a `Signature` field:
`label=:base64:` (RFC 9421 §4.2, RFC 8941 §3.3.5). -/
def sigBytes? (v label : String) : Option ByteArray :=
  let v := trimS v
  if !v.startsWith (label ++ "=:") then none else
  match (String.ofList (v.toList.drop (label.length + 2))).splitOn ":" with
  | b64 :: _ => Base64.decode? b64
  | [] => none

/-- A quoted parameter after the inner list of a signature's parameters. -/
def sigParam? (params name : String) : Option String :=
  let after := String.ofList (params.toList.dropWhile (· != ')'))
  match after.splitOn (";" ++ name ++ "=\"") with
  | _ :: v :: _ => some (String.ofList (v.toList.takeWhile (· != '"')))
  | _ => none

/-- The covered components of the inner list. -/
def sigComponents (params : String) : List String :=
  let inner := String.ofList ((params.toList.drop 1).takeWhile (· != ')'))
  (inner.splitOn " ").filter (· != "") |>.map (fun c => String.ofList (c.toList.filter (· != '"')))

/-- The signature base (RFC 9421 §2.5), rebuilt from the inbox URL as
subscribed and the header fields received. -/
def inboxBase (method inbox : String) (hs : List (String × String)) (params : String) :
    Option String := do
  let (sch, auth, path) ← Notifications.urlParts? inbox
  let comps := sigComponents params
  let vals ← comps.mapM (fun c => match c with
    | "@method" => some method.toUpper
    | "@scheme" => some sch
    | "@authority" => some auth
    | "@path" => some path
    | name => (headerIn hs name).map trimS)
  pure (String.join ((comps.zip vals).map (fun (c, v) => "\"" ++ c ++ "\": " ++ v ++ "\n")) ++
    "\"@signature-params\": " ++ params)

/-- The inbox URL as subscribed: `url`, resolved with the request target
received when there is one. -/
def inboxUrl (op : Op) : String :=
  if op.requestTarget == "" then op.url else resolve op.url op.requestTarget

/-- The RFC 9530 `Content-Digest` of a body, SHA-256. -/
def digestOf (body : ByteArray) : String :=
  "sha-256=:" ++ Base64.encode (L4Factoidal.Crypto.sha256 body) ++ ":"

def accept (s : ClientState) : ClientState × Action :=
  finish s (.done (.object [("accept", .bool true), ("status", natJson 204)]))

def reject (s : ClientState) (reason : String) (status : Nat := 401) : ClientState × Action :=
  finish s (.done (.object [("accept", .bool false), ("status", natJson status), ("reason", .string reason)]))

/-- The first steps of the verification, before the storage description is
read: a signature, a keyid with a fragment, the body's digest. -/
def verifyStart (s : ClientState) : ClientState × Action :=
  let op := s.op
  if op.method.toUpper != "POST" then reject s "a notification is a POST" 405 else
  match (headerIn op.headers "signature-input").bind sigInput? with
  | none => reject s "the notification is not signed"
  | some (label, params) =>
    match (headerIn op.headers "signature").bind (fun v => sigBytes? v label) with
    | none => reject s "Signature and Signature-Input do not share a label"
    | some _ =>
      match sigParam? params "keyid" with
      | none => reject s "no keyid"
      | some keyid =>
        -- Step 1: "The keyid value MUST be a URL with a fragment component."
        if !keyid.contains '#' then reject s "the keyid is not a URL with a fragment" else
        let storage := String.ofList (keyid.toList.takeWhile (· != '#'))
        if (headerIn op.headers "content-digest").map trimS != some (digestOf op.body) then
          reject s "the body does not have the Content-Digest the signature covers"
        else sendPublic s .inboxDesc (getReq storage mediaLwsCid)

/-- The end of the verification, with the storage description read. -/
def verifyFinish (V : L4Factoidal.JOSE.Verifiers) (s : ClientState) (r : Resp) :
    ClientState × Action :=
  let op := s.op
  if r.status != 200 then reject s ("the storage description answered " ++ toString r.status) else
  match (headerIn op.headers "signature-input").bind sigInput? with
  | none => reject s "the notification is not signed"
  | some (label, params) =>
  match (headerIn op.headers "signature").bind (fun v => sigBytes? v label),
        sigParam? params "keyid" with
  | some sig, some keyid =>
    let storage := String.ofList (keyid.toList.takeWhile (· != '#'))
    let frag := String.ofList ((keyid.toList.dropWhile (· != '#')).drop 1)
    match r.json? with
    | none => reject s "the storage description is not JSON"
    | some desc =>
      -- Step 3: "The id property of the top-level document map MUST match
      -- the storage identifier."
      if desc.getString? "id" != some storage then reject s "the document names another id" else
      let vm := ((desc.getArray? "verificationMethod").getD []).find? (fun m =>
        match m.getString? "id" with
        | some id => id == keyid || id == "#" ++ frag || id == frag
        | none => false)
      match vm.bind (fun m => m.field? "publicKeyJwk") |>.bind L4Factoidal.JOSE.parsePublicJwk? with
      | none => reject s ("no verification method " ++ keyid)
      | some jwk =>
        match inboxBase op.method (inboxUrl op) op.headers params with
        | none => reject s "a covered component is missing"
        | some base =>
          let alg := sigParam? params "alg"
          let ok := match jwk with
            | .ec x y => (alg.isNone || alg == some "ecdsa-p256-sha256") && V.es256 (x ++ y) base.toUTF8 sig
            | .okp x => (alg.isNone || alg == some "ed25519") && V.eddsa x base.toUTF8 sig
            | _ => false
          if ok then accept s else reject s "the signature does not verify"
  | _, _ => reject s "the notification is not signed"

/-! ## Paging (lws10-core §Pagination, lws10-index) -/

/-- The items of one page: the `items` array, each item an object with an
`id`. `none` for a page that is not such a listing (a malformed listing is
a failure, never an empty list). -/
def pageItemsOf (r : Resp) : Option (List Json) := do
  let j ← r.json?
  let items ← j.getArray? "items"
  if items.all (fun it => (it.getString? "id").isSome) then some items else none

def idsOf (items : List Json) : List String := items.filterMap (fun it => it.getString? "id")

def pagingDone (s : ClientState) : ClientState × Action :=
  finish s (.done (.object [ ("items", strsJson (idsOf s.items)), ("members", .array s.items)
                           , ("pages", natJson s.pages) ]))

/-- One page answered: collect its items, follow `next` (never a URL the
client builds). -/
def onPage (s : ClientState) (r : Resp) : ClientState × Action :=
  if r.ok then
    match pageItemsOf r with
    | none => failWith s "malformedListing" (respSummary r)
    | some items =>
      let s := { s with items := s.items ++ items, pages := s.pages + 1 }
      match linkTarget? (sentUrl s) r "next" with
      | some u => send s .paging (getReq u mediaLwsJson)
      | none => pagingDone s
  else if s.op.kind == "search" && (r.status == 404 || r.status == 410) && !s.restarted &&
      s.endpoint != "" then
    -- lws10-index §Errors: a page reference the server no longer
    -- recognizes; the client restarts the search, once.
    send { s with items := [], pages := 0, restarted := true } .paging (queryReq s.endpoint s.op.query)
  else statusFail s r

/-! ## The authorization flow (lws10-core §Authorization) -/

/-- The token request (lws10-core §Token Exchange, RFC 8693 §2.1). -/
def tokenRequest (c : AuthCtx) (ses : Session) : Req :=
  { method := "POST", url := c.tokenEndpoint
    headers := [("Content-Type", mediaForm), ("Accept", mediaJson)]
    body := (formBody [ ("grant_type", tokenExchangeGrant), ("resource", c.storage)
                      , ("subject_token", ses.subjectToken)
                      , ("subject_token_type", ses.subjectTokenType) ]).toUTF8 }

/-- Is a request a token exchange request? -/
def isTokenExchange (r : Req) : Bool :=
  r.method == "POST" && (formPairs r.body).lookup "grant_type" == some tokenExchangeGrant

/-- The `resource` a token request asks for. -/
def tokenResource? (r : Req) : Option String := (formPairs r.body).lookup "resource"

/-- A 401 from the storage: check, then ask for a token. -/
def on401 (s : ClientState) (r : Resp) : ClientState × Action :=
  match s.sent with
  | none => statusFail s r
  | some sent =>
    let challenge := (r.header? "www-authenticate").getD ""
    if s.session.subjectToken == "" then
      failWith s "unauthorized" (respSummary r)
    else if s.exchanges == 0 then
      failWith s "unauthorized" ([("reason", .string "the storage refused the token it was given")] ++ respSummary r)
    else
    match resourceMetadata? r, linkTarget? sent.url r lwsStorageRel with
    | some rmeta, some storage =>
      -- Check 1: the resource_metadata URL has the scheme and authority of
      -- the requested URI.
      if !sameOrigin rmeta sent.url then
        failWith s "discoveryValidation" [("check", .string "resourceMetadataOrigin"), ("challenge", .string challenge)]
      else
        let ses := { s.session with tokens := s.session.tokens.filter (fun t => t.storage != storage) }
        let pending : Req := { sent with headers := sent.headers.filter (fun (n, _) => n.toLower != "authorization") }
        sendPublic { s with session := ses, pending := some pending, pendingPhase := s.phase
                          , auth := some { requestUri := sent.url, metadataUrl := rmeta, storage }
                          , exchanges := s.exchanges - 1 }
          .authMeta (getReq rmeta mediaJson)
    | _, _ => failWith s "unauthorized"
        ([("reason", .string "the 401 has no resource_metadata or no storage link")] ++ respSummary r)

/-- The next request of the flow, after each answer. -/
def authStep (s : ClientState) (c : AuthCtx) (r : Resp) : ClientState × Action :=
  if !r.ok then
    failWith s "authorization" ([("phase", .string s.phase.name)] ++ respSummary r)
  else
  match s.phase with
  | .authMeta =>
    match r.json? with
    | none => failWith s "authorization" [("phase", .string "authMeta"), ("reason", .string "not JSON")]
    | some j =>
      let res := jStr j "resource"
      -- Check 2: the metadata's resource is identical to the requested URI.
      if res != c.requestUri then
        failWith s "discoveryValidation" [("check", .string "metadataResource"), ("resource", .string res)]
      else
      match jStrs j "authorization_servers" with
      | iss :: _ =>
        sendPublic { s with auth := some { c with metadataResource := res, asIssuer := iss } }
          .authDesc (getReq c.storage mediaLwsCid)
      | [] => failWith s "discoveryValidation" [("check", .string "authorizationServers")]
  | .authDesc =>
    match r.json? with
    | none => failWith s "authorization" [("phase", .string "authDesc"), ("reason", .string "not JSON")]
    | some desc =>
      match serviceEndpoint? c.storage desc "StorageRoot" with
      | none => failWith s "discoveryValidation" [("check", .string "storageRoot")]
      | some root =>
        -- Check 3: the StorageRoot endpoint has the scheme and authority
        -- of the requested URI.
        if !sameOrigin root c.requestUri then
          failWith s "discoveryValidation" [("check", .string "storageRootOrigin"), ("root", .string root)]
        else
          sendPublic { s with auth := some { c with rootEndpoint := root } }
            .authAsMeta (getReq (asMetadataUrl c.asIssuer) mediaJson)
  | .authAsMeta =>
    match r.json? with
    | none => failWith s "authorization" [("phase", .string "authAsMeta"), ("reason", .string "not JSON")]
    | some j =>
      -- RFC 8414 §3.3: the issuer in the metadata is the issuer the URL was
      -- built from.
      if jStr j "issuer" != c.asIssuer then
        failWith s "authorization" [("phase", .string "authAsMeta"), ("reason", .string "issuer mismatch")]
      else
      match j.getString? "token_endpoint" with
      | none => failWith s "authorization" [("phase", .string "authAsMeta"), ("reason", .string "no token_endpoint")]
      | some te =>
        let c := { c with tokenEndpoint := resolve (asMetadataUrl c.asIssuer) te }
        sendPublic { s with auth := some c } .authToken (tokenRequest c s.session)
  | .authToken =>
    match r.json? with
    | none => failWith s "authorization" [("phase", .string "authToken"), ("reason", .string "not JSON")]
    | some j =>
      match j.getString? "access_token" with
      | none => failWith s "authorization" [("phase", .string "authToken"), ("reason", .string "no access_token")]
      | some tok =>
        if (jStr j "token_type").toLower != "bearer" then
          failWith s "authorization" [("phase", .string "authToken"), ("reason", .string "token_type is not Bearer")]
        else
        let entry : TokenEntry := { storage := c.storage, root := c.rootEndpoint, token := tok }
        let kept := s.session.tokens.filter (fun t => t.storage != c.storage)
        let ses : Session := { s.session with tokens := entry :: kept }
        let s := { s with session := ses, auth := none }
        match s.pending with
        -- The new token goes with the request that was refused: check 3
        -- found its origin to be the storage root's.
        | some p => sendPublic { s with pending := none } s.pendingPhase
            { p with headers := p.headers ++ [("Authorization", "Bearer " ++ tok)] }
        | none => failWith s "internal" [("reason", .string "no pending request")]
  | _ => failWith s "internal" [("reason", .string "not an authorization phase")]

def isAuthPhase : Phase → Bool
  | .authMeta | .authDesc | .authAsMeta | .authToken => true
  | _ => false

/-! ## Beginning an operation -/

def begin (s : ClientState) : ClientState × Action :=
  let op := s.op
  match op.kind with
  | "verifyNotification" => verifyStart s
  | "discover" | "typeIndex" | "search" | "subscribe" | "requestAccess" | "grantAccess" | "move" =>
      if op.kind == "subscribe" && !isAbsoluteUri op.inbox then
        failWith s "badArguments" [("reason", .string "a webhook subscription needs an inbox URI")]
      else if (op.kind == "requestAccess" || op.kind == "grantAccess") && !accessArgsOk op then
        failWith s "badArguments" [("reason", .string "an access document needs actions, an assignee URI and target URIs")]
      else if op.kind == "move" && !isAbsoluteUri op.destination then
        failWith s "badArguments" [("reason", .string "a move needs a destination container URI")]
      else send s .discoverHead (headReq op.url)
  | "read" | "getAccess" => send s .main (getReq op.url (if op.accept != "" then op.accept
      else if op.kind == "getAccess" then mediaLwsJson else ""))
  | "head" => send s .main (headReq op.url)
  | "create" =>
      if !clientLinksOk op then
        failWith s "badArguments" [("reason", .string "a client link is malformed or has a server-managed relation")]
      else send s .main (createReq op)
  | "update" | "patch" | "delete" =>
      if op.kind != "delete" && !clientLinksOk op then
        failWith s "badArguments" [("reason", .string "a client link is malformed or has a server-managed relation")]
      else if op.precondition == "ifMatchCurrent" then send s .tagRead (headReq op.url)
      else if (op.precondition == "ifMatch" || op.precondition == "ifUnmodifiedSince") && op.tag == "" then
        failWith s "badArguments" [("reason", .string "the precondition needs a tag")]
      else send s .main (writeReq op "")
  | "readLinkset" | "updateLinkset" => send s .linksetFind (headReq op.url)
  | "list" => send s .paging (getReq op.url mediaLwsJson)
  | "unsubscribe" | "revokeAccess" => send s .main { method := "DELETE", url := op.url }
  | k => failWith s "badArguments" [("reason", .string ("unknown kind " ++ k))]

/-! ## Each phase's answer -/

/-- The write of a linkset change, from the advertised methods and formats
(lws10-core §Metadata: "Clients SHOULD NOT assume support for PUT or
specific patch formats unless they are advertised"). -/
def linksetWrite (s : ClientState) : ClientState × Action :=
  let op := s.op
  let pre := preconditionHeaders op s.etag
  if op.precondition == "ifMatchCurrent" && s.etag == "" then failWith s "noEtag" else
  if op.kind == "move" then
    if !s.acceptPatch.contains mediaJsonPatch then
      failWith s "notAdvertised" [("acceptPatch", strsJson s.acceptPatch)]
    else
    match movePatch s.linkset op.url op.destination s.linksetDoc with
    | none => failWith s "malformedLinkset" [("reason", .string "no up link in the linkset")]
    | some p =>
      send s .main { method := "PATCH", url := s.linkset
                     headers := [("Content-Type", mediaJsonPatch)] ++ pre
                     body := (toStringCompact p).toUTF8 }
  else
    let media := if op.mediaType != "" then op.mediaType.toLower else mediaJsonPatch
    if media == mediaLinkset then
      if s.allow.contains "PUT" then
        send s .main { method := "PUT", url := s.linkset, headers := [("Content-Type", mediaLinkset)] ++ pre, body := op.body }
      else failWith s "notAdvertised" [("allow", strsJson s.allow)]
    else if s.acceptPatch.contains media then
      send s .main { method := "PATCH", url := s.linkset, headers := [("Content-Type", media)] ++ pre, body := op.body }
    else failWith s "notAdvertised" [("acceptPatch", strsJson s.acceptPatch)]

/-- What the service operations do once the storage description is read. -/
def afterDiscovery (s : ClientState) (desc : Json) : ClientState × Action :=
  let op := s.op
  let base := sentUrl s
  let storageId := (desc.getString? "id").getD base
  let s := { s with storage := desc }
  let need (ty : String) (k : String → ClientState × Action) : ClientState × Action :=
    match serviceEndpoint? base desc ty with
    | some e => k e
    | none => failWith s "noService" [("service", .string ty)]
  match op.kind with
  | "discover" => finish s (.done (.object [("storage", .string storageId), ("description", desc)]))
  | "typeIndex" => need "TypeIndexService" (fun e => send { s with endpoint := e } .paging (getReq e mediaLwsJson))
  | "search" => need "TypeSearchService" (fun e => send { s with endpoint := e } .paging (queryReq e op.query))
  | "subscribe" =>
      match service? desc "NotificationService" with
      | none => failWith s "noService" [("service", .string "NotificationService")]
      | some sv =>
        if !(jStrs sv "subscriptionType").contains webhookSubscriptionType then
          failWith s "noSubscriptionType" [("subscriptionType", strsJson (jStrs sv "subscriptionType"))]
        else need "NotificationService" (fun e => send { s with endpoint := e } .main (jsonReq "POST" e (subscriptionDoc op)))
  | "requestAccess" => need "AccessRequestService" (fun e =>
      send { s with endpoint := e } .main (jsonReq "POST" e (accessDoc "AccessRequest" storageId op)))
  | "grantAccess" => need "AccessGrantService" (fun e =>
      send { s with endpoint := e } .main (jsonReq "POST" e (accessDoc "AccessGrant" storageId op)))
  | "move" =>
      -- "Clients MUST NOT assume that the up link is modifiable in the
      -- absence of this capability."
      if !hasCapability desc "MoveResource" then failWith s "noMoveCapability"
      else send s .linksetFind (headReq op.url)
  | _ => failWith s "internal" [("reason", .string "not a service operation")]

/-- The answer to the operation's own request. -/
def onMain (s : ClientState) (r : Resp) : ClientState × Action :=
  let op := s.op
  let base := sentUrl s
  let location := (r.header? "location").map (resolve base)
  let withLoc := match location with
    | some l => [("location", .string l)]
    | none => []
  match op.kind with
  | "create" =>
    if r.ok then finish s (.done (.object (withLoc ++ respSummary r)))
    else if 500 ≤ r.status then
      -- The create may have happened: read the container, never POST again.
      send { s with note := r.status } .createCheck (getReq op.url mediaLwsJson)
    else statusFail s r
  | "update" | "patch" | "delete" | "updateLinkset" | "move" =>
    if r.ok then
      let extra := match (r.header? "content-location").map (resolve base) with
        | some cl => [("contentLocation", .string cl)]
        | none => []
      let moved := if op.kind == "move" then
          match r.json? |>.bind (fun j => j.getArray? "linkset") |>.bind List.head? |>.bind (fun c => c.getString? "anchor") with
          | some a => [("identifier", .string (resolve base a))]
          | none => [("identifier", .string op.url)]
        else []
      finish s (.done (.object (extra ++ moved ++ respSummary r)))
    else if r.status == 412 && s.retries > 0 &&
        (op.precondition == "ifMatch" || op.precondition == "ifMatchCurrent") then
      -- The caller allowed a retry: read the current tag again.
      let s := { s with retries := s.retries - 1 }
      if op.kind == "updateLinkset" || op.kind == "move" then
        send s .linksetMeta (getReq s.linkset mediaLinkset)
      else send s .tagRead (headReq op.url)
    else if r.status == 412 then failWith s "preconditionFailed" (respSummary r)
    else if (r.status == 405 || r.status == 415) && (op.kind == "updateLinkset" || op.kind == "move") then
      -- Never the same request again: read what the linkset advertises now.
      send { s with note := r.status } .linksetRecheck (getReq s.linkset mediaLinkset)
    else statusFail s r
  | "readLinkset" =>
    if r.ok then
      finish s (.done (.object ([ ("linkset", (r.json?).getD .null), ("url", .string s.linkset)
                                , ("etag", .string ((r.header? "etag").getD ""))
                                , ("allow", strsJson (allowOf r)), ("acceptPatch", strsJson (acceptPatchOf r)) ])))
    else statusFail s r
  | "subscribe" | "requestAccess" | "grantAccess" =>
    if r.ok then finish s (.done (.object (withLoc ++ respSummary r)))
    else if 500 ≤ r.status then failWith s "outcomeUnknown" (respSummary r)
    else statusFail s r
  | _ =>
    if r.ok then finish s (.done (.object (withLoc ++ respSummary r))) else statusFail s r

/-- The answer to a request of the operation (not of the authorization
flow). -/
def onResponse (V : L4Factoidal.JOSE.Verifiers) (s : ClientState) (r : Resp) : ClientState × Action :=
  let op := s.op
  let base := sentUrl s
  match s.phase with
  | .main => onMain s r
  | .tagRead =>
    if !r.ok then statusFail s r else
    match r.header? "etag" with
    | none => failWith s "noEtag" (respSummary r)
    | some t => send { s with etag := t } .main (writeReq op t)
  | .discoverHead =>
    match linkTarget? base r lwsStorageRel with
    | none => failWith s "noStorageLink" (respSummary r)
    | some st => send s .discoverDesc (getReq st mediaLwsCid)
  | .discoverDesc =>
    if !r.ok then statusFail s r else
    match r.json? with
    | some desc => afterDiscovery s desc
    | none => failWith s "malformedDescription" (respSummary r)
  | .linksetFind =>
    if !r.ok then statusFail s r else
    match linkTarget? base r "linkset" with
    | none => failWith s "noLinkset" (respSummary r)
    | some ls =>
      let s := { s with linkset := ls }
      if op.kind == "readLinkset" then send s .main (getReq ls mediaLinkset)
      else send s .linksetMeta (getReq ls mediaLinkset)
  | .linksetMeta =>
    if !r.ok then statusFail s r else
    linksetWrite { s with etag := (r.header? "etag").getD "", allow := allowOf r
                        , acceptPatch := acceptPatchOf r, linksetDoc := (r.json?).getD .null }
  | .linksetRecheck =>
    failWith s "methodRefused" [ ("status", natJson s.note), ("allow", strsJson (allowOf r))
                               , ("acceptPatch", strsJson (acceptPatchOf r)) ]
  | .paging => onPage s r
  | .createCheck =>
    failWith s "createOutcomeUnknown"
      ([("status", natJson s.note), ("containerStatus", natJson r.status)] ++
       (match pageItemsOf r with
        | some items => [("items", strsJson (idsOf items))]
        | none => []))
  | .inboxDesc => verifyFinish V s r
  | _ => failWith s "internal" [("reason", .string ("no response expected in phase " ++ s.phase.name))]

/-! ## The step function -/

/-- The step before `enforce`. -/
def core (V : L4Factoidal.JOSE.Verifiers) (s : ClientState) (e : Event) : ClientState × Action :=
  if s.phase == .finished then finish s (.fail (errJ "finished")) else
  if s.fuel == 0 then failWith s "stepLimit" else
  let s := { s with fuel := s.fuel - 1 }
  match e with
  | .start =>
    if s.phase == .init then begin { s with retries := s.op.retry412 }
    else failWith s "internal" [("reason", .string "start in a running operation")]
  | .transportError msg =>
    match s.sent with
    | some sent =>
      if sent.method == "POST" && s.op.kind == "create" && s.phase == .main then
        send { s with note := 0 } .createCheck (getReq s.op.url mediaLwsJson)
      else failWith s "transport" [("message", .string msg), ("url", .string sent.url)]
    | none => failWith s "transport" [("message", .string msg)]
  | .response r =>
    if s.phase == .init then failWith s "internal" [("reason", .string "a response before start")] else
    if isAuthPhase s.phase then
      match s.auth with
      | some c => authStep s c r
      | none => failWith s "internal" [("reason", .string "no validation record")]
    else if r.status == 401 && s.phase != .inboxDesc then on401 s r
    else onResponse V s r

/-- Does an action send the same request again after the answer that
refused it: a POST answered 5xx or lost, any request answered 405 or 415?
-/
def repeatsRefused (s : ClientState) (e : Event) (r : Req) : Bool :=
  match s.sent with
  | none => false
  | some prev =>
    match e with
    | .response resp =>
        ((prev.method == "POST" && 500 ≤ resp.status) || resp.status == 405 || resp.status == 415) &&
        prev.same r
    | .transportError _ => prev.method == "POST" && prev.same r
    | .start => false

/-- Is a token request backed by a validation record whose three checks
hold, for the storage it asks for? -/
def tokenBacked (s : ClientState) (r : Req) : Bool :=
  match s.auth with
  | some c => validated c && tokenResource? r == some c.storage
  | none => false

/-- The last word of `step`: an action that breaks one of the properties
of `Client/Theorems.lean` becomes `fail`. -/
def enforce (s : ClientState) (e : Event) (out : ClientState × Action) : ClientState × Action :=
  match out with
  | (s', .fetch r) =>
    if wantsPrecondition s.op && isWrite r && !carriesPrecondition s.op r then
      failWith s' "enforce" [("rule", .string "precondition")]
    else if isTokenExchange r && !tokenBacked s' r then
      failWith s' "enforce" [("rule", .string "discoveryValidation")]
    else if repeatsRefused s e r then
      failWith s' "enforce" [("rule", .string "noRepeat")]
    else out
  | _ => out

/-- One step of the client. -/
def step (V : L4Factoidal.JOSE.Verifiers) (s : ClientState) (e : Event) : ClientState × Action :=
  enforce s e (core V s e)

/-- The first step of an operation. -/
def start (V : L4Factoidal.JOSE.Verifiers) (op : Op) (ses : Session) : ClientState × Action :=
  step V { op := op.normalize, session := ses } .start

/-! ## JSON form of the state, events and actions (the wasm ABI) -/

def optReqJson : Option Req → Json
  | some r => reqJson r
  | none => .null

def optReqOfJson (j : Json) : Option Req :=
  match j with
  | .object _ => some (reqOfJson j)
  | _ => none

def stateJson (s : ClientState) : Json :=
  .object
    [ ("op", opJson s.op), ("phase", .string s.phase.name), ("session", sessionJson s.session)
    , ("sent", optReqJson s.sent), ("pending", optReqJson s.pending)
    , ("pendingPhase", .string s.pendingPhase.name)
    , ("auth", match s.auth with | some c => authJson c | none => .null)
    , ("etag", .string s.etag), ("retries", natJson s.retries), ("exchanges", natJson s.exchanges)
    , ("items", .array s.items), ("pages", natJson s.pages), ("restarted", .bool s.restarted)
    , ("storage", s.storage), ("endpoint", .string s.endpoint), ("linkset", .string s.linkset)
    , ("allow", strsJson s.allow), ("acceptPatch", strsJson s.acceptPatch)
    , ("linksetDoc", s.linksetDoc), ("note", natJson s.note), ("fuel", natJson s.fuel) ]

def stateOfJson (j : Json) : Except String ClientState := do
  let op ← opOfJson (jAny j "op")
  pure { op, phase := phaseOfName (jStr j "phase"), session := sessionOfJson (jAny j "session")
         sent := optReqOfJson (jAny j "sent"), pending := optReqOfJson (jAny j "pending")
         pendingPhase := phaseOfName (jStr j "pendingPhase")
         auth := (match jAny j "auth" with | .object fs => some (authOfJson (.object fs)) | _ => none)
         etag := jStr j "etag", retries := jNat j "retries", exchanges := jNat j "exchanges"
         items := (j.getArray? "items").getD [], pages := jNat j "pages"
         restarted := jBool j "restarted", storage := jAny j "storage"
         endpoint := jStr j "endpoint", linkset := jStr j "linkset", allow := jStrs j "allow"
         acceptPatch := jStrs j "acceptPatch", linksetDoc := jAny j "linksetDoc"
         note := jNat j "note", fuel := jNat j "fuel" }

/-- An event document: `{status, headers, bodyBase64 | body}` for a
response, `{error}` for a transport error. -/
def eventOfJson (j : Json) : Event :=
  match j.getString? "error" with
  | some m => .transportError m
  | none => .response (respOfJson j)

/-- An action document. `done` and `fail` carry the session, which the
caller passes to the next operation. -/
def actionJson (s : ClientState) : Action → Json
  | .fetch r => .object [("fetch", reqJson r)]
  | .done res => .object [("done", res), ("session", sessionJson s.session)]
  | .fail err => .object [("fail", err), ("session", sessionJson s.session)]

end L4Factoidal.LWS.Client
