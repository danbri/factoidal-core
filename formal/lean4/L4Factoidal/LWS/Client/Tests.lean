/-
L4Factoidal.LWS.Client.Tests — build-time checks of the LWS client
(https://github.com/danbri/factoidal/issues/917) through `Client.step`, the
function the hosts call. Two kinds:

* scripts: the machine against canned responses, to reach each rule and
  each refusal (decoy 401s, a stale `If-Match`, 405 on a linkset, POST 503,
  a malformed listing, a refused search page, forged notifications);
* a loopback: the machine against this repository's own server
  (`LWS.step MemStore`), in process, so client and server meet with no
  host in between.

Each behaviour has a positive and a negative case.
-/
import L4Factoidal.LWS.Client.Theorems
import L4Factoidal.LWS.Client.Keys
import L4Factoidal.LWS.Tests

namespace L4Factoidal.LWS.Client.Tests

open L4Factoidal.JSON
open L4Factoidal.LWS
open L4Factoidal.LWS.Client

/-! ## Scripts -/

/-- A verifier for the scripts: a signature is good when its bytes are
`good`. The real verifiers are HACL* (`Wasm.Ops.lwsVerifiers`). -/
def Vt : L4Factoidal.Authz.Crypto :=
  { verifiers :=
      { es256 := fun _ _ sig => sig.data == "good".toUTF8.data
        rs256 := fun _ _ _ _ => false
        eddsa := fun _ _ sig => sig.data == "good".toUTF8.data }
    -- A stand-in signer: 64 copies of the nonce's first byte, or a refusal
    -- for a key of the wrong length.
    es256Sign := fun sk _ nonce =>
      if sk.size == 32 then some (ByteArray.mk (Array.replicate 64 (nonce.get! 0))) else none
    es256Public := fun _ => none
    eddsaSign := fun _ _ => ByteArray.empty
    eddsaPublic := fun _ => none
    p256Decompress := fun _ => none }

def rsp (status : Nat) (headers : List (String × String) := []) (body : String := "") : Resp :=
  { status, headers, body := body.toUTF8 }

/-- Run an operation against canned responses, one per request. The
requests the client sent, and its last action. -/
def script (op : Op) (resps : List Resp) (ses : Session := {}) : List Req × Action :=
  let rec go (s : ClientState) (a : Action) (acc : List Req) : List Resp → List Req × Action
    | [] => match a with
      | .fetch r => (acc ++ [r], a)
      | _ => (acc, a)
    | x :: xs => match a with
      | .fetch r =>
        let (s', a') := Client.step Vt s (.response x)
        go s' a' (acc ++ [r]) xs
      | _ => (acc, a)
  let (s, a) := Client.start Vt op ses
  go s a [] resps

/-- The session at the end of an operation against canned responses. -/
def scriptSession (op : Op) (resps : List Resp) (ses : Session := {}) : Session :=
  let rec go (s : ClientState) (a : Action) : List Resp → Session
    | [] => s.session
    | x :: xs => match a with
      | .fetch _ =>
        let (s', a') := Client.step Vt s (.response x)
        go s' a' xs
      | _ => s.session
  let (s, a) := Client.start Vt op ses
  go s a resps

def failCode : Action → String
  | .fail e => (e.getString? "code").getD ""
  | _ => ""

def isDone : Action → Bool
  | .done _ => true
  | _ => false

def doneJson : Action → Json
  | .done j => j
  | _ => .null

def sentAt (rs : List Req) (i : Nat) : Req := rs.getD i default

def B : String := "https://s.example/"

/-! ### Create (lws10-core §Create Resource) -/

-- A container create carries Link rel="type" to lws#Container.
#guard (sentAt (script { kind := "create", url := B ++ "c/", container := true, slug := "notes" } []).1 0).header? "link" ==
  some ("<" ++ lwsContainerType ++ ">; rel=\"type\"")
#guard (sentAt (script { kind := "create", url := B ++ "c/", container := true, slug := "notes" } []).1 0).header? "slug" == some "notes"
-- A data resource create carries no type link.
#guard ((sentAt (script { kind := "create", url := B ++ "c/", mediaType := "text/plain", body := "x".toUTF8 } []).1 0).header? "link").isNone
-- 201 with Location: done, the location resolved.
#guard (doneJson (script { kind := "create", url := B ++ "c/" } [rsp 201 [("Location", "/c/a")]]).2).getString? "location" ==
  some "https://s.example/c/a"
-- A caller link with a server-managed relation is refused before sending.
#guard failCode (script { kind := "create", url := B ++ "c/", links := ["<https://s.example/x>; rel=\"linkset\""] } []).2 == "badArguments"
#guard ((script { kind := "create", url := B ++ "c/", links := ["<https://s.example/x>; rel=\"linkset\""] } []).1).isEmpty
-- A caller type link to its own class is kept.
#guard isDone (script { kind := "create", url := B ++ "c/", links := ["<https://e.example/T>; rel=\"type\""] } [rsp 201]).2

-- POST answered 503: the client reads the container and never POSTs again.
def lost := script { kind := "create", url := B ++ "c/", body := "x".toUTF8 }
  [rsp 503, rsp 200 [] "{\"items\":[{\"id\":\"https://s.example/c/res1\"}]}"]
#guard lost.1.map (·.method) == ["POST", "GET"]
#guard failCode lost.2 == "createOutcomeUnknown"
#guard (match lost.2 with | .fail e => e.getArray? "items" == some [.string "https://s.example/c/res1"] | _ => false)

/-! ### Update and delete (§Update Resource, §Delete Resource) -/

-- By default an update reads the current tag and sends If-Match with it.
def upd := script { kind := "update", url := B ++ "a", mediaType := "text/plain", body := "y".toUTF8 }
  [rsp 200 [("ETag", "\"t1\"")], rsp 204]
#guard upd.1.map (·.method) == ["HEAD", "PUT"]
#guard (sentAt upd.1 1).header? "if-match" == some "\"t1\""
#guard isDone upd.2
-- No tag in the answer: no write.
#guard failCode (script { kind := "update", url := B ++ "a" } [rsp 200]).2 == "noEtag"
-- A stale tag without retry412: 412 ends the operation.
def stale := script { kind := "update", url := B ++ "a", precondition := "ifMatch", tag := "\"old\"" } [rsp 412]
#guard (sentAt stale.1 0).header? "if-match" == some "\"old\""
#guard failCode stale.2 == "preconditionFailed"
-- With retry412 = 1: read again, send again with the new tag, once.
def retried := script { kind := "update", url := B ++ "a", precondition := "ifMatch", tag := "\"old\"", retry412 := 1 }
  [rsp 412, rsp 200 [("ETag", "\"new\"")], rsp 412]
#guard retried.1.map (·.method) == ["PUT", "HEAD", "PUT"]
#guard (sentAt retried.1 2).header? "if-match" == some "\"new\""
#guard failCode retried.2 == "preconditionFailed"
-- Links on an update go with Prefer: set-linkset.
#guard (sentAt (script { kind := "update", url := B ++ "a", precondition := "none", links := ["<https://e.example/T>; rel=\"type\""] } []).1 0).header? "prefer" == some "set-linkset"
#guard ((sentAt (script { kind := "update", url := B ++ "a", precondition := "none" } []).1 0).header? "prefer").isNone
-- A recursive delete carries Depth: infinity; a plain one does not.
#guard (sentAt (script { kind := "delete", url := B ++ "c/", recursive := true } []).1 0).header? "depth" == some "infinity"
#guard ((sentAt (script { kind := "delete", url := B ++ "c/" } []).1 0).header? "depth").isNone
-- If-None-Match: * for a create-only PUT.
#guard (sentAt (script { kind := "update", url := B ++ "n", precondition := "ifNoneMatchStar" } []).1 0).header? "if-none-match" == some "*"

/-! ### Linksets (§Metadata) -/

def lsHead : Resp := rsp 200 [("Link", "<https://s.example/a.meta>; rel=\"linkset\"")]
def lsGet (allow patch : String) : Resp :=
  rsp 200 [("ETag", "\"m1\""), ("Allow", allow), ("Accept-Patch", patch), ("Content-Type", mediaLinkset)]
    "{\"linkset\":[{\"anchor\":\"https://s.example/a\",\"up\":[{\"href\":\"https://s.example/\"}]}]}"

-- PUT of a linkset document only when Allow lists PUT, with If-Match.
def lsPut := script { kind := "updateLinkset", url := B ++ "a", mediaType := mediaLinkset, body := "{\"linkset\":[]}".toUTF8 }
  [lsHead, lsGet "GET, HEAD, PUT, PATCH" mediaJsonPatch, rsp 204]
#guard lsPut.1.map (·.method) == ["HEAD", "GET", "PUT"]
#guard (sentAt lsPut.1 2).url == "https://s.example/a.meta"
#guard (sentAt lsPut.1 2).header? "if-match" == some "\"m1\""
#guard isDone lsPut.2
-- Not advertised: no PUT at all.
#guard failCode (script { kind := "updateLinkset", url := B ++ "a", mediaType := mediaLinkset, body := "{\"linkset\":[]}".toUTF8 }
  [lsHead, lsGet "GET, HEAD, PATCH" mediaJsonPatch]).2 == "notAdvertised"
-- A JSON Patch only in an advertised format.
#guard (sentAt (script { kind := "updateLinkset", url := B ++ "a", body := "[]".toUTF8 }
  [lsHead, lsGet "GET, HEAD, PATCH" mediaJsonPatch]).1 2).method == "PATCH"
#guard failCode (script { kind := "updateLinkset", url := B ++ "a", body := "[]".toUTF8 }
  [lsHead, lsGet "GET, HEAD, PATCH" "application/merge-patch+json"]).2 == "notAdvertised"
-- 405 on the PUT: the linkset is read again, the PUT is never repeated.
def refused := script { kind := "updateLinkset", url := B ++ "a", mediaType := mediaLinkset, body := "{\"linkset\":[]}".toUTF8 }
  [lsHead, lsGet "GET, HEAD, PUT, PATCH" mediaJsonPatch, rsp 405 [("Allow", "GET, HEAD, PUT")],
   lsGet "GET, HEAD, PUT, PATCH" mediaJsonPatch]
#guard refused.1.map (·.method) == ["HEAD", "GET", "PUT", "GET"]
#guard failCode refused.2 == "methodRefused"
-- No linkset link: no guessed URL.
#guard failCode (script { kind := "readLinkset", url := B ++ "a" } [rsp 200]).2 == "noLinkset"

/-! ### Paging (§Pagination) -/

def page (ids : List String) (next : Option String) : Resp :=
  rsp 200 (match next with | some n => [("Link", "<" ++ n ++ ">; rel=\"next\"")] | none => [])
    (toStringCompact (.object [("items", .array (ids.map (fun i => Json.object [("id", .string i)])))]))

def listed := script { kind := "list", url := B ++ "c/" }
  [page ["a", "b"] (some "/_t/p/xyz"), page ["c", "d"] (some "/_t/p/uvw"), page ["e"] none]
-- The client follows the next links it is given, builds none.
#guard listed.1.map (·.url) == ["https://s.example/c/", "https://s.example/_t/p/xyz", "https://s.example/_t/p/uvw"]
#guard (doneJson listed.2).getArray? "items" == some (["a", "b", "c", "d", "e"].map Json.string)
-- A malformed listing is a failure, never an empty list.
#guard failCode (script { kind := "list", url := B ++ "c/" } [rsp 200 [] "{\"member\":[]}"]).2 == "malformedListing"
#guard failCode (script { kind := "list", url := B ++ "c/" } [rsp 200 [] "{\"items\":[{\"name\":\"a\"}]}"]).2 == "malformedListing"

/-! ### Discovery and services (§Discovery, lws10-index, §Notifications, §Access) -/

def descHead : Resp := rsp 200 [("Link", "<https://s.example/.well-known/lws-storage>; rel=\"" ++ lwsStorageRel ++ "\"")]
def desc : Resp := rsp 200 [("Content-Type", mediaLwsCid)] (toStringCompact (.object
  [ ("id", .string "https://s.example/.well-known/lws-storage"), ("type", .string "Storage")
  , ("capability", .array [.object [("type", .string "MoveResource")]])
  , ("service", .array
      [ .object [("type", .string "StorageRoot"), ("serviceEndpoint", .string "https://s.example/")]
      , .object [("type", .string "TypeSearchService"), ("serviceEndpoint", .string "https://s.example/search")]
      , .object [("type", .string "NotificationService"), ("serviceEndpoint", .string "https://s.example/subs")
                , ("subscriptionType", .array [.string "WebhookSubscription"])]
      , .object [("type", .string "AccessRequestService"), ("serviceEndpoint", .string "https://s.example/ar")] ]) ]))

#guard (doneJson (script { kind := "discover", url := B ++ "a" } [descHead, desc]).2).getString? "storage" ==
  some "https://s.example/.well-known/lws-storage"
-- A search QUERY names its format in Content-Type.
def searched := script { kind := "search", url := B, query := .object [("type", .array [.string "https://e.example/T"])] }
  [descHead, desc, page ["x"] (some "/search?p=2"), rsp 410, page ["x", "y"] none]
#guard (sentAt searched.1 2).method == "QUERY"
#guard (sentAt searched.1 2).header? "content-type" == some mediaLwsQuery
-- A page refused with 410: the QUERY is sent again, and its answer is the result.
#guard searched.1.map (·.method) == ["HEAD", "GET", "QUERY", "GET", "QUERY"]
#guard (doneJson searched.2).getArray? "items" == some [.string "x", .string "y"]
-- A richer query format first: after its 415 the baseline format.
def richer := script { kind := "search", url := B, mediaType := "application/sparql-query", body := "ASK {}".toUTF8, query := .object [("type", .array [.string "https://e.example/T"])] } [descHead, desc, rsp 415, page ["z"] none]
#guard (richer.1.map (fun r => r.header? "content-type")) == [none, none, some "application/sparql-query", some mediaLwsQuery]
#guard (doneJson richer.2).getArray? "items" == some [.string "z"]
-- A 415 to the baseline itself ends the search.
#guard failCode (script { kind := "search", url := B } [descHead, desc, rsp 415]).2 == "status"
-- A webhook subscription: lws+json, type, topic array, inbox.
def subscribed := script { kind := "subscribe", url := B ++ "a", inbox := "https://in.example/1" } [descHead, desc, rsp 201 [("Location", "/subs/1")]]
#guard (sentAt subscribed.1 2).header? "content-type" == some mediaLwsJson
#guard (String.fromUTF8? (sentAt subscribed.1 2).body) ==
  some "{\"type\":\"WebhookSubscription\",\"topic\":[\"https://s.example/a\"],\"inbox\":\"https://in.example/1\"}"
#guard failCode (script { kind := "subscribe", url := B ++ "a" } []).2 == "badArguments"
-- An access request: @context array, type, storage, access array of policies.
def asked := script { kind := "requestAccess", url := B, actions := ["read"], assignee := "https://bob.example/#me", targets := [B ++ "a"] } [descHead, desc, rsp 201]
#guard (String.fromUTF8? (sentAt asked.1 2).body) == some ("{\"@context\":[\"https://www.w3.org/ns/lws/v1\"]," ++
  "\"type\":[\"AccessRequest\"],\"storage\":\"https://s.example/.well-known/lws-storage\"," ++
  "\"access\":[{\"type\":[\"AccessPolicy\"],\"action\":[\"read\"],\"assignee\":\"https://bob.example/#me\"," ++
  "\"target\":{\"type\":\"StorageResource\",\"value\":[\"https://s.example/a\"]}}]}")
#guard failCode (script { kind := "requestAccess", url := B, actions := [], assignee := "bob" } []).2 == "badArguments"
-- No service: a failure naming it.
#guard failCode (script { kind := "grantAccess", url := B, actions := ["read"], assignee := "https://b.example/" }
  [descHead, desc]).2 == "noService"
-- A move: only with the MoveResource capability, by a JSON Patch of the up link.
def moved := script { kind := "move", url := B ++ "a", destination := B ++ "d/" }
  [descHead, desc, lsHead, lsGet "GET, HEAD, PATCH" mediaJsonPatch, rsp 204]
-- After the PATCH the client asks for the resource where it is now.
#guard moved.1.map (·.method) == ["HEAD", "GET", "HEAD", "GET", "PATCH", "HEAD"]
#guard (String.fromUTF8? (sentAt moved.1 4).body) == some
  ("[{\"op\":\"test\",\"path\":\"/linkset/0/up/0/href\",\"value\":\"https://s.example/\"}," ++
   "{\"op\":\"replace\",\"path\":\"/linkset/0/up/0/href\",\"value\":\"https://s.example/d/\"}]")
#guard (sentAt moved.1 4).header? "if-match" == some "\"m1\""
#guard failCode (script { kind := "move", url := B ++ "a", destination := B ++ "d/" }
  [descHead, rsp 200 [] "{\"id\":\"x\",\"service\":[]}"]).2 == "noMoveCapability"

/-! ### Authorization (§Authorization) -/

def ses : Session := { subjectToken := "ASSERTION", subjectTokenType := "urn:ietf:params:oauth:token-type:saml2" }

def challenge (rm storage : String) : Resp :=
  rsp 401 [ ("WWW-Authenticate", "Bearer resource_metadata=\"" ++ rm ++ "\"")
          , ("Link", "<" ++ storage ++ ">; rel=\"" ++ lwsStorageRel ++ "\"") ]
def prm (resource : String) : Resp :=
  rsp 200 [] ("{\"resource\":\"" ++ resource ++ "\",\"authorization_servers\":[\"https://as.example/t\"]}")
def descRoot (root : String) : Resp :=
  rsp 200 [] ("{\"id\":\"https://s.example/st\",\"service\":[{\"type\":\"StorageRoot\",\"serviceEndpoint\":\"" ++ root ++ "\"}]}")
def asMeta : Resp :=
  rsp 200 [] "{\"issuer\":\"https://as.example/t\",\"token_endpoint\":\"https://as.example/t/token\"}"
def tokenResp : Resp := rsp 200 [] "{\"access_token\":\"AT1\",\"token_type\":\"Bearer\",\"expires_in\":300}"

def authed := script { kind := "read", url := B ++ "a" }
  [ challenge "https://s.example/.well-known/oauth-protected-resource/a" "https://s.example/st"
  , prm "https://s.example/a", descRoot "https://s.example/", asMeta, tokenResp, rsp 200 [] "hello" ] ses
#guard authed.1.map (·.url) ==
  [ "https://s.example/a", "https://s.example/.well-known/oauth-protected-resource/a", "https://s.example/st"
  , "https://as.example/.well-known/lws-configuration/t", "https://as.example/t/token", "https://s.example/a" ]
-- The token request: form, grant type, resource = the storage of the 401's link, the subject token.
#guard (sentAt authed.1 4).header? "content-type" == some mediaForm
#guard formPairs (sentAt authed.1 4).body ==
  [ ("grant_type", tokenExchangeGrant), ("resource", "https://s.example/st"), ("subject_token", "ASSERTION")
  , ("subject_token_type", "urn:ietf:params:oauth:token-type:saml2") ]
-- The token goes in the Authorization header, and only to the storage.
#guard (sentAt authed.1 5).header? "authorization" == some "Bearer AT1"
#guard (authed.1.take 5).all (fun r => (r.header? "authorization").isNone)
#guard (doneJson authed.2).getString? "body" == some "hello"

-- The decoy: a 401 whose storage puts its root on another origin. No token request.
def decoy := script { kind := "read", url := B ++ "decoy" }
  [ challenge "https://s.example/.well-known/oauth-protected-resource/decoy" "https://s.example/other"
  , prm "https://s.example/decoy", descRoot "https://evil.example/" ] ses
#guard failCode decoy.2 == "discoveryValidation"
#guard decoy.1.all (fun r => !isTokenExchange r)
-- resource_metadata on another origin: not even fetched.
def decoy1 := script { kind := "read", url := B ++ "a" }
  [ challenge "https://evil.example/.well-known/oauth-protected-resource/a" "https://s.example/st" ] ses
#guard decoy1.1.length == 1
#guard failCode decoy1.2 == "discoveryValidation"
-- The metadata's resource is not the requested URI.
#guard failCode (script { kind := "read", url := B ++ "a" }
  [ challenge "https://s.example/.well-known/oauth-protected-resource/a" "https://s.example/st"
  , prm "https://s.example/b" ] ses).2 == "discoveryValidation"
-- No subject token: the 401 is the answer.
#guard failCode (script { kind := "read", url := B ++ "a" }
  [ challenge "https://s.example/.well-known/oauth-protected-resource/a" "https://s.example/st" ]).2 == "unauthorized"
-- A token refused (expired): it is dropped and exchanged again.
def expired := script { kind := "read", url := B ++ "a" }
  [ rsp 401 [ ("WWW-Authenticate", "Bearer resource_metadata=\"https://s.example/.well-known/oauth-protected-resource/a\", error=\"invalid_token\"")
            , ("Link", "<https://s.example/st>; rel=\"" ++ lwsStorageRel ++ "\"") ]
  , prm "https://s.example/a", descRoot "https://s.example/", asMeta
  , rsp 200 [] "{\"access_token\":\"AT2\",\"token_type\":\"Bearer\"}", rsp 200 ]
  { ses with tokens := [{ storage := "https://s.example/st", root := "https://s.example/", token := "AT1" }] }
#guard (sentAt expired.1 0).header? "authorization" == some "Bearer AT1"
#guard (sentAt expired.1 5).header? "authorization" == some "Bearer AT2"
#guard isDone expired.2

-- A self-issued credential (lws10-authn-ssi-cid): no subject token, a key; the
-- token request carries a three-part JWT of type jwt for the authorization
-- server, signed with the nonce from the host's random bytes.
def cidKey : SelfIssued :=
  { subject := "https://id.example/alice", keyId := "https://id.example/alice#k1"
    privateKey := ByteArray.mk (Array.replicate 32 1) }
def cidSes : Session := { selfIssued := some cidKey }
def asMetaR : Resp := { asMeta with now := 1000, random := ByteArray.mk (Array.replicate 48 9) }
def cid := script { kind := "read", url := B ++ "a" }
  [ challenge "https://s.example/.well-known/oauth-protected-resource/a" "https://s.example/st"
  , prm "https://s.example/a", descRoot "https://s.example/", asMetaR, tokenResp, rsp 200 ] cidSes
def cidToken : String := ((formPairs (sentAt cid.1 4).body).lookup "subject_token").getD ""
#guard (formPairs (sentAt cid.1 4).body).lookup "subject_token_type" == some jwtTokenType
#guard (cidToken.splitOn ".").length == 3
#guard isDone cid.2
-- The claims: iss, sub and client_id the agent, aud the authorization server, iat and exp.
#guard ((L4Factoidal.JOSE.Base64Url.decode ((cidToken.splitOn ".").getD 1 "")).bind String.fromUTF8?) ==
  some ("{\"iss\":\"https://id.example/alice\",\"sub\":\"https://id.example/alice\"," ++
    "\"client_id\":\"https://id.example/alice\",\"aud\":[\"https://as.example/t\"],\"iat\":1000," ++
    "\"exp\":1300,\"jti\":\"09090909090909090909090909090909\"}")
-- Without random bytes from the host there is no nonce: no token request.
#guard failCode (script { kind := "read", url := B ++ "a" }
  [ challenge "https://s.example/.well-known/oauth-protected-resource/a" "https://s.example/st"
  , prm "https://s.example/a", descRoot "https://s.example/", asMeta ] cidSes).2 == "credential"
#guard (sessionOfJson (sessionJson cidSes)).selfIssued.map (·.privateKey.data) == some (Array.replicate 32 1)

/-! ### Interop defects (https://github.com/danbri/factoidal/issues/1115) -/

-- 1. The challenge of the drafts before 2026-10-19, `Bearer as_uri, realm`,
-- with no resource_metadata and no storage link (css, sparq-lws). Opt-in.
def legacy401 (asUri realm : String) : Resp :=
  rsp 401 [("WWW-Authenticate", "Bearer as_uri=\"" ++ asUri ++ "\", realm=\"" ++ realm ++ "\"")]
def legacySes : Session := { ses with legacyChallenge := true }
def legacyRun := script { kind := "read", url := B ++ "a" }
  [ legacy401 "https://as.example/t" B, asMeta, tokenResp, rsp 200 [] "hello" ] legacySes
-- No protected resource metadata, no storage description: the authorization
-- server metadata, the token, the request again.
#guard legacyRun.1.map (·.url) ==
  [ B ++ "a", "https://as.example/.well-known/lws-configuration/t", "https://as.example/t/token", B ++ "a" ]
-- The token's resource is the realm.
#guard (formPairs (sentAt legacyRun.1 2).body).lookup "resource" == some B
#guard (sentAt legacyRun.1 3).header? "authorization" == some "Bearer AT1"
#guard (doneJson legacyRun.2).getString? "body" == some "hello"
-- The token is kept for the realm, and goes under it only.
#guard (scriptSession { kind := "read", url := B ++ "a" }
  [ legacy401 "https://as.example/t" B, asMeta, tokenResp, rsp 200 [] "hello" ] legacySes).tokens.map
  (fun t => (t.storage, t.root)) == [(B, B)]
-- Off by default: the same 401 is the answer, and nothing more is sent.
def legacyOff := script { kind := "read", url := B ++ "a" } [legacy401 "https://as.example/t" B] ses
#guard failCode legacyOff.2 == "unauthorized"
#guard legacyOff.1.length == 1
-- A realm on another origin: no token request.
def legacyEvil := script { kind := "read", url := B ++ "a" }
  [legacy401 "https://as.example/t" "https://evil.example/"] legacySes
#guard failCode legacyEvil.2 == "discoveryValidation"
#guard legacyEvil.1.all (fun r => !isTokenExchange r)
-- A realm that does not contain the requested URL: no token request.
#guard failCode (script { kind := "read", url := B ++ "a" }
  [legacy401 "https://as.example/t" (B ++ "other/")] legacySes).2 == "discoveryValidation"
-- A 401 with resource_metadata still takes the full checks with the option on.
#guard failCode (script { kind := "read", url := B ++ "decoy" }
  [ challenge "https://s.example/.well-known/oauth-protected-resource/decoy" "https://s.example/other"
  , prm "https://s.example/decoy", descRoot "https://evil.example/" ] legacySes).2 == "discoveryValidation"
-- The option goes through the session document.
#guard (sessionOfJson (sessionJson legacySes)).legacyChallenge
#guard !(sessionOfJson (sessionJson ses)).legacyChallenge
#guard (sessionOfJson (.object [("legacyChallenge", .bool true)])).legacyChallenge

-- 2. The token also goes to the service endpoints of the storage description
-- on the requested URI's origin (lws-drupal's type index is outside its
-- StorageRoot path), never to another origin.
def descServices : Resp := rsp 200 [] ("{\"id\":\"https://s.example/st\",\"service\":[" ++
  "{\"type\":\"StorageRoot\",\"serviceEndpoint\":\"https://s.example/root/\"}," ++
  "{\"type\":\"TypeIndexService\",\"serviceEndpoint\":\"/types\"}," ++
  "{\"type\":\"NotificationService\",\"serviceEndpoint\":\"https://other.example/n\"}]}")
def epSession : Session := scriptSession { kind := "read", url := "https://s.example/root/a" }
  [ challenge "https://s.example/.well-known/oauth-protected-resource/root/a" "https://s.example/st"
  , prm "https://s.example/root/a", descServices, asMeta, tokenResp, rsp 200 [] "x" ] ses
#guard epSession.tokens.map (·.endpoints) == [["https://s.example/types"]]
#guard (sentAt (script { kind := "typeIndex", url := "https://s.example/types", endpoint := "https://s.example/types" }
  [] epSession).1 0).header? "authorization" == some "Bearer AT1"
#guard ((sentAt (script { kind := "typeIndex", url := "https://other.example/n", endpoint := "https://other.example/n" }
  [] epSession).1 0).header? "authorization").isNone
#guard ((sentAt (script { kind := "read", url := "https://s.example/elsewhere" } [] epSession).1 0).header?
  "authorization").isNone
-- The endpoints go through the session document; a document without them reads as none.
#guard (sessionOfJson (sessionJson epSession)).tokens.map (·.endpoints) == [["https://s.example/types"]]
#guard (sessionOfJson (sessionJson ses)).tokens.isEmpty

-- 3. A subscription to a notification endpoint the caller names: POST to it,
-- with no HEAD for a storage link (lwsd's endpoint sends none).
def subDirect := script { kind := "subscribe", url := B ++ "a", endpoint := "https://s.example/subs"
                        , inbox := "https://in.example/1" } [rsp 201 [("Location", "/subs/1")]]
#guard subDirect.1.map (fun r => (r.method, r.url)) == [("POST", "https://s.example/subs")]
#guard (String.fromUTF8? (sentAt subDirect.1 0).body) ==
  some "{\"type\":\"WebhookSubscription\",\"topic\":[\"https://s.example/a\"],\"inbox\":\"https://in.example/1\"}"
#guard ((doneJson subDirect.2).field? "report" |>.bind (·.getString? "subscription")) == some "https://s.example/subs/1"
-- Without a named endpoint the client still finds it, and a HEAD with no
-- storage link stops it.
#guard failCode (script { kind := "subscribe", url := B ++ "a", inbox := "https://in.example/1" } [rsp 200]).2 ==
  "noStorageLink"

/-! ### Verifying a notification (lws10-notifications-webhook §5.2) -/

def nbody : String := "{\"type\":\"Notification\"}"
def nheaders (keyid sig digest : String) : List (String × String) :=
  [ ("Content-Type", mediaLwsJson), ("Content-Digest", digest)
  , ("Signature-Input", "sig1=(\"@method\" \"@scheme\" \"@authority\" \"@path\" \"content-type\" \"content-digest\");created=1;keyid=\"" ++ keyid ++ "\";alg=\"ed25519\"")
  , ("Signature", "sig1=:" ++ Base64.encode sig.toUTF8 ++ ":") ]
def nop (keyid sig : String) (digest : String := digestOf nbody.toUTF8) : Op :=
  { kind := "verifyNotification", url := "http://in.example/inbox/1", method := "POST"
    headers := nheaders keyid sig digest, body := nbody.toUTF8 }
def sdesc (id : String) : Resp := rsp 200 [] (toStringCompact (.object
  [ ("id", .string id)
  , ("verificationMethod", .array [ .object [ ("id", .string (id ++ "#k1")), ("type", .string "JsonWebKey")
      , ("publicKeyJwk", .object [("kty", .string "OKP"), ("crv", .string "Ed25519"),
          ("x", .string "11qYAYKxCrfVS_7TyWQHOg7hcvPapiMlrwIaaPcHURo")]) ] ]) ]))
def verdict (a : Action) : Option Bool := (doneJson a).getBool? "accept"

#guard verdict (script (nop "https://s.example/st#k1" "good") [sdesc "https://s.example/st"]).2 == some true
#guard (sentAt (script (nop "https://s.example/st#k1" "good") []).1 0).url == "https://s.example/st"
-- A signature that does not verify.
#guard verdict (script (nop "https://s.example/st#k1" "bad") [sdesc "https://s.example/st"]).2 == some false
-- A keyid without a fragment: refused before anything is fetched.
#guard verdict (script (nop "https://s.example/st" "good") []).2 == some false
-- A body altered after signing: the digest does not match.
#guard verdict (script (nop "https://s.example/st#k1" "good" "sha-256=:AAAA:") []).2 == some false
-- The inbox URL as subscribed: the receiver's base and the request target.
#guard inboxUrl { kind := "verifyNotification", url := "http://in.example/", requestTarget := "/inbox/1" } ==
  "http://in.example/inbox/1"
-- A document that names another id.
#guard verdict (script (nop "https://s.example/st/fake#k1" "good") [sdesc "https://s.example/st"]).2 == some false

/-! ## Loopback: the client against this repository's server -/

def lcfg : Config := { L4Factoidal.LWS.Tests.cfg with pageSize := 2, owner := none }
def LB : String := "http://example.org/"

def toServer (r : Req) : L4Factoidal.HTTP.Request :=
  { method := r.method, path := String.ofList (r.url.toList.drop (LB.length - 1)), queryStr := ""
    headers := r.headers.map (fun (n, v) => (n.toLower, v)), body := "", bytes := some r.body }

def ofServer (r : L4Factoidal.HTTP.Response) : Resp :=
  { status := r.status, headers := r.headers, body := r.content }

/-- Drive one operation to its end against the server, at most `n` steps. -/
def loop (st : MemState) (s : ClientState) (a : Action) : Nat → Action × MemState
  | 0 => (a, st)
  | n + 1 => match a with
    | .fetch r =>
      let (resp, st') := L4Factoidal.LWS.step MemStore lcfg (toServer r) st
      let (s', a') := Client.step Vt s (.response (ofServer resp))
      loop st' s' a' n
    | _ => (a, st)

def runOp (st : MemState) (op : Op) : Action × MemState :=
  let (s, a) := Client.start Vt op {}
  loop st s a 32

def afterCreates : Action × MemState :=
  let st := L4Factoidal.LWS.Tests.emptyStorage
  let (_, st) := runOp st { kind := "create", url := LB, container := true, slug := "c" }
  ["e", "b", "d", "a", "c"].foldl (fun (acc : Action × MemState) n =>
    runOp acc.2 { kind := "create", url := LB ++ "c/", slug := n, mediaType := "text/plain", body := n.toUTF8 })
    (.done .null, st)

-- Five members over three pages of two: each once, in path order.
#guard (doneJson (runOp afterCreates.2 { kind := "list", url := LB ++ "c/" }).1).getArray? "items" ==
  some (["a", "b", "c", "d", "e"].map (fun n => Json.string (LB ++ "c/" ++ n)))
#guard (doneJson (runOp afterCreates.2 { kind := "list", url := LB ++ "c/" }).1).field? "pages" == some (.number "3")
-- A conditional update with the current tag succeeds; a stale tag gets 412.
#guard isDone (runOp afterCreates.2 { kind := "update", url := LB ++ "c/a", mediaType := "text/plain", body := "A".toUTF8 }).1
#guard failCode (runOp afterCreates.2 { kind := "update", url := LB ++ "c/a", precondition := "ifMatch", tag := "\"stale\"", mediaType := "text/plain", body := "A".toUTF8 }).1 == "preconditionFailed"
-- Discovery reads the storage description.
#guard ((doneJson (runOp afterCreates.2 { kind := "discover", url := LB ++ "c/a" }).1).getString? "storage").isSome
-- A linkset update by JSON Patch, conditional on the linkset's tag.
#guard isDone (runOp afterCreates.2 { kind := "updateLinkset", url := LB ++ "c/a", body := "[{\"op\":\"add\",\"path\":\"/linkset/0/https:~1~1e.example~1rel\",\"value\":[{\"href\":\"https://e.example/x\"}]}]".toUTF8 }).1
-- A container with members needs Depth: infinity.
#guard isDone (runOp afterCreates.2 { kind := "delete", url := LB ++ "c/", recursive := true }).1
#guard failCode (runOp afterCreates.2 { kind := "delete", url := LB ++ "c/" }).1 == "status"

/-! ## The state as JSON (the wasm ABI carries it between steps) -/

def roundTrips (s : ClientState) : Bool :=
  match stateOfJson (stateJson s) with
  | .ok s' => toStringCompact (stateJson s') == toStringCompact (stateJson s)
  | .error _ => false

def s0 : ClientState := (Client.start Vt { kind := "read", url := B ++ "a" } ses).1
def s1 : ClientState := (Client.step Vt s0 (.response
  (challenge "https://s.example/.well-known/oauth-protected-resource/a" "https://s.example/st"))).1
#guard roundTrips s0 && roundTrips s1
#guard s1.phase == .authMeta && s1.auth.isSome
#guard roundTrips (Client.start Vt (nop "https://s.example/st#k1" "good") {}).1
#guard roundTrips (Client.start Vt { kind := "update", url := B ++ "a", body := ByteArray.mk #[0, 255, 7] } {}).1
-- An operation document with an unknown kind is refused.
#guard (opOfJson (.object [("kind", .string "frobnicate")])).toOption.isNone
#guard ((opOfJson (.object [("kind", .string "update"), ("url", .string "https://s.example/a")])).toOption.map
  (fun o => o.normalize.precondition)) == some "ifMatchCurrent"

/-! ## Driver features (https://github.com/danbri/factoidal/issues/1065) -/

def repOf (a : Action) : Json := (doneJson a).field? "report" |>.getD .null
def fld (j : Json) (k : String) : Option Json := j.field? k
def strAt (j : Json) (k : String) : Option String := j.getString? k

/-! ### Read: range, condition, preference -/

#guard (sentAt (script { kind := "read", url := B ++ "a", rangeStart := some 0, rangeEnd := some 4 } []).1 0).header? "range" ==
  some "bytes=0-4"
#guard (sentAt (script { kind := "read", url := B ++ "a", rangeStart := some 5 } []).1 0).header? "range" == some "bytes=5-"
#guard (sentAt (script { kind := "read", url := B ++ "a", rangeEnd := some 3 } []).1 0).header? "range" == some "bytes=0-3"
#guard ((sentAt (script { kind := "read", url := B ++ "a" } []).1 0).header? "range").isNone
#guard (sentAt (script { kind := "read", url := B ++ "a", ifNoneMatch := "\"t1\"" } []).1 0).header? "if-none-match" == some "\"t1\""
#guard (sentAt (script { kind := "read", url := B ++ "a", prefer := "return=minimal" } []).1 0).header? "prefer" == some "return=minimal"
-- A range that ends before it starts is refused before anything is sent.
#guard failCode (script { kind := "read", url := B ++ "a", rangeStart := some 5, rangeEnd := some 2 } []).2 == "badArguments"
-- 304 answers a conditional read: not modified, no failure.
def condRead := script { kind := "read", url := B ++ "a", ifNoneMatch := "\"t1\"" } [rsp 304 [("ETag", "\"t1\"")]]
#guard isDone condRead.2
#guard fld (repOf condRead.2) "notModified" == some (.bool true)
-- 304 to a read that did not ask for a condition is a status failure.
#guard failCode (script { kind := "read", url := B ++ "a" } [rsp 304]).2 == "status"
-- 206 and its Content-Range.
def ranged := script { kind := "read", url := B ++ "a", rangeStart := some 0, rangeEnd := some 4 }
  [rsp 206 [("Content-Range", "bytes 0-4/11"), ("Content-Type", "text/plain")] "Hello"]
#guard strAt (repOf ranged.2) "contentRange" == some "bytes 0-4/11"
#guard fld (repOf ranged.2) "body" == some (.object [("text", .string "Hello")])
#guard fld (repOf ranged.2) "notModified" == some (.bool false)
#guard ((fld (repOf ranged.2) "metadata").bind (fun m => m.field? "status")) == some (.number "206")

/-! ### Metadata, pages, storage descriptions (the report) -/

def metaResp : Resp := rsp 200
  [ ("ETag", "W/\"3\""), ("Last-Modified", "Tue, 06 Oct 2026 12:00:00 GMT"), ("Content-Type", "text/plain")
  , ("Content-Length", "11"), ("Allow", "get, HEAD"), ("Accept-Patch", "application/json-patch+json; charset=utf-8")
  , ("Link", "</a.meta>; rel=\"linkset\"; type=\"application/linkset+json\", </>; rel=\"up\"")
  , ("Link", "<https://www.w3.org/ns/lws#DataResource>; rel=\"type\", <https://s.example/st>; rel=\"" ++ lwsStorageRel ++ "\"") ]
def metaDone := script { kind := "head", url := B ++ "a" } [metaResp]
def metaOf : Json := (fld (repOf metaDone.2) "url").map (fun _ => repOf metaDone.2) |>.getD .null
#guard strAt metaOf "etag" == some "W/\"3\""
#guard strAt metaOf "lastModified" == some "Tue, 06 Oct 2026 12:00:00 GMT"
#guard strAt metaOf "contentType" == some "text/plain"
#guard fld metaOf "contentLength" == some (.number "11")
#guard strAt metaOf "linkset" == some "https://s.example/a.meta"
#guard strAt metaOf "parent" == some "https://s.example/"
#guard strAt metaOf "storage" == some "https://s.example/st"
#guard (fld metaOf "types") == some (.array [.string "https://www.w3.org/ns/lws#DataResource"])
#guard (fld metaOf "allow") == some (.array [.string "GET", .string "HEAD"])
#guard (fld metaOf "acceptPatch") == some (.array [.string "application/json-patch+json"])
#guard ((fld metaOf "links").bind Json.asArray?).map List.length == some 4
#guard (((fld metaOf "links").bind Json.asArray?).bind List.head?).bind (fun l => l.field? "params") ==
  some (.object [("type", .string "application/linkset+json")])
-- A response without those fields reports none of them.
#guard (fld (repOf (script { kind := "head", url := B ++ "a" } [rsp 200]).2) "etag").isNone

def pageResp : Resp := rsp 200
  [("Link", "</c/?p=2>; rel=\"next\", </c/>; rel=\"first\"")]
  "{\"id\":\"/c/\",\"type\":[\"Container\"],\"totalItems\":3,\"items\":[{\"id\":\"a\",\"type\":[\"DataResource\"],\"format\":\"text/plain\",\"size\":2,\"modified\":\"2026-10-06T12:00:00Z\"},{\"id\":\"b\"}]}"
def pagedDone := script { kind := "readPage", url := B ++ "c/" } [pageResp]
#guard pagedDone.1.length == 1
#guard strAt (repOf pagedDone.2) "id" == some "https://s.example/c/"
#guard strAt (repOf pagedDone.2) "next" == some "https://s.example/c/?p=2"
#guard strAt (repOf pagedDone.2) "first" == some "https://s.example/c/"
#guard (fld (repOf pagedDone.2) "prev").isNone
#guard fld (repOf pagedDone.2) "totalItems" == some (.number "3")
#guard ((fld (repOf pagedDone.2) "items").bind Json.asArray?).bind List.head? ==
  some (.object [ ("id", .string "https://s.example/c/a"), ("types", .array [.string "DataResource"])
                , ("format", .string "text/plain"), ("size", .number "2"), ("modified", .string "2026-10-06T12:00:00Z") ])
-- A page without an id member is identified by the URL it was read from.
#guard strAt (repOf (script { kind := "readPage", url := B ++ "c/" } [rsp 200 [] "{\"items\":[]}"]).2) "id" == some "https://s.example/c/"
-- A page that is not a listing is a failure.
#guard failCode (script { kind := "readPage", url := B ++ "c/" } [rsp 200 [] "{\"member\":[]}"]).2 == "malformedListing"

-- The storage description as the driver reports it.
def richDesc : Resp := rsp 200 [("Content-Type", mediaLwsCid)] (toStringCompact (.object
  [ ("id", .string "https://s.example/.well-known/lws-storage"), ("type", .string "Storage")
  , ("capability", .array [.object [("type", .string "MoveResource"), ("preservesIdentifier", .bool true)]])
  , ("verificationMethod", .array [.object [("id", .string "#k1"), ("type", .string "JsonWebKey"), ("controller", .string "https://s.example/")]])
  , ("service", .array
      [ .object [("type", .string "StorageRoot"), ("serviceEndpoint", .string "/root/")]
      , .object [("id", .string "https://s.example/n"), ("type", .string "NotificationService"), ("serviceEndpoint", .string "https://s.example/subs")
                , ("subscriptionType", .string "WebhookSubscription")] ]) ]))
def describing := script { kind := "describe", url := B ++ ".well-known/lws-storage" } [richDesc]
#guard (sentAt describing.1 0).method == "GET" && (sentAt describing.1 0).header? "accept" == some mediaLwsCid
#guard strAt (repOf describing.2) "storageRoot" == some "https://s.example/root/"
#guard strAt (repOf describing.2) "id" == some "https://s.example/.well-known/lws-storage"
#guard (fld (repOf describing.2) "moveCapability") ==
  some (.object [("appliesTo", .array [.string "DataResource"]), ("preservesIdentifier", .bool true)])
#guard ((fld (repOf describing.2) "services").bind Json.asArray?).map List.length == some 2
#guard ((fld (repOf describing.2) "verificationMethods").bind Json.asArray?).bind List.head? ==
  some (.object [("id", .string "#k1"), ("type", .string "JsonWebKey"), ("controller", .string "https://s.example/")])
-- The same shape from a discovery that follows the storage link.
#guard strAt (repOf (script { kind := "discover", url := B ++ "a" } [descHead, desc]).2) "storageRoot" == some "https://s.example/"
-- No capability, no moveCapability member.
#guard (fld (repOf (script { kind := "describe", url := B } [rsp 200 [] "{\"id\":\"x\"}"]).2) "moveCapability").isNone

/-! ### Services given directly: a storage, a service endpoint, a linkset -/

-- A storage description URL replaces the HEAD and the storage link.
def viaStorage := script { kind := "search", url := B, storage := "https://s.example/.well-known/lws-storage", query := .object [("type", .array [.string "https://e.example/T"])] } [desc, page ["x"] none]
#guard viaStorage.1.map (·.method) == ["GET", "QUERY"]
#guard (sentAt viaStorage.1 0).url == "https://s.example/.well-known/lws-storage"
#guard isDone viaStorage.2
-- A service endpoint replaces the discovery altogether.
def viaEndpoint := script { kind := "search", url := "", endpoint := "https://s.example/search", query := .object [("type", .array [.string "https://e.example/T"])] } [page ["x"] none]
#guard viaEndpoint.1.map (·.method) == ["QUERY"]
#guard (sentAt viaEndpoint.1 0).url == "https://s.example/search"
#guard (sentAt viaEndpoint.1 0).header? "content-type" == some mediaLwsQuery
#guard (repOf viaEndpoint.2).field? "items" == some (.array [Json.object [("id", .string "x"), ("types", .array [])]]) ||
  ((fld (repOf viaEndpoint.2) "items").bind Json.asArray?).map List.length == some 1
def indexEndpoint := script { kind := "typeIndex", url := "", endpoint := "https://s.example/types" } [page ["https://e.example/T"] none]
#guard indexEndpoint.1.map (·.method) == ["GET"]
#guard fld (repOf indexEndpoint.2) "types" == some (.array [.string "https://e.example/T"])
-- A query that is not a filter is refused before anything is sent.
#guard failCode (script { kind := "search", url := "", endpoint := "https://s.example/search", query := .object [("type", .array [.number "42"])] } []).2 == "badArguments"
#guard failCode (script { kind := "search", url := "", endpoint := "https://s.example/search", query := .array [] } []).2 == "badArguments"

-- One page of a search: its own `next`, no further request.
def onePageSearch := script { kind := "search", url := "", endpoint := "https://s.example/search", onePage := true, query := .object [("type", .array [.string "https://e.example/T"])] }
  [rsp 200 [("Link", "</search?p=2>; rel=\"next\"")] "{\"id\":\"/search?p=1\",\"items\":[{\"id\":\"x\"}]}", page ["y"] none]
#guard onePageSearch.1.length == 1
#guard strAt (repOf onePageSearch.2) "id" == some "https://s.example/search?p=1"
#guard strAt (repOf onePageSearch.2) "next" == some "https://s.example/search?p=2"
-- Without onePage the client follows `next`.
#guard (script { kind := "search", url := "", endpoint := "https://s.example/search", query := .object [("type", .array [.string "https://e.example/T"])] }
  [rsp 200 [("Link", "</search?p=2>; rel=\"next\"")] "{\"items\":[{\"id\":\"x\"}]}", page ["y"] none]).1.length == 2
-- One page of a type index keeps its links.
def onePageIndex := script { kind := "typeIndex", url := "", endpoint := "https://s.example/types", onePage := true }
  [rsp 200 [("Link", "</types?p=2>; rel=\"next\"")] "{\"totalItems\":5,\"items\":[{\"id\":\"https://e.example/T\"}]}"]
#guard onePageIndex.1.length == 1
#guard strAt (repOf onePageIndex.2) "next" == some "https://s.example/types?p=2"
#guard fld (repOf onePageIndex.2) "totalItems" == some (.number "5")
#guard fld (repOf onePageIndex.2) "types" == some (.array [.string "https://e.example/T"])

-- The accepted query formats come from Accept-Query after an OPTIONS.
def formats := script { kind := "queryFormats", url := "https://s.example/search" }
  [rsp 204 [("Accept-Query", "\"application/lws-query+json\", application/sparql-query;charset=utf-8")]]
#guard (sentAt formats.1 0).method == "OPTIONS"
#guard fld (repOf formats.2) "formats" == some (.array [.string "application/lws-query+json", .string "application/sparql-query"])
#guard fld (repOf (script { kind := "queryFormats", url := "https://s.example/search" } [rsp 204]).2) "formats" == some (.array [])

-- A linkset the caller has: read it, write it; the resource is not asked.
def putDirect := script { kind := "putLinkset", linksetUrl := "https://s.example/a.meta", body := "{\"linkset\":[]}".toUTF8 }
  [lsGet "GET, HEAD, PUT, PATCH" mediaJsonPatch, rsp 204 [("ETag", "\"m2\"")]]
#guard putDirect.1.map (·.method) == ["GET", "PUT"]
#guard (sentAt putDirect.1 0).url == "https://s.example/a.meta"
#guard (sentAt putDirect.1 1).header? "content-type" == some mediaLinkset
#guard (sentAt putDirect.1 1).header? "if-match" == some "\"m1\""
#guard strAt (repOf putDirect.2) "etag" == some "\"m2\""
#guard ((fld (repOf putDirect.2) "metadata").bind (fun m => m.getString? "url")) == some "https://s.example/a.meta"
-- A document that is not a linkset is refused before anything is sent.
#guard failCode (script { kind := "putLinkset", linksetUrl := "https://s.example/a.meta", body := "{\"linkset\":\"x\"}".toUTF8 } []).2 == "badArguments"
def patchDirect := script { kind := "updateLinkset", linksetUrl := "https://s.example/a.meta", body := "[{\"op\":\"remove\",\"path\":\"/linkset/0/up\"}]".toUTF8 }
  [lsGet "GET, HEAD, PATCH" mediaJsonPatch, rsp 204]
#guard patchDirect.1.map (·.method) == ["GET", "PATCH"]
-- A JSON Patch with an unknown operation is refused, for a resource and for a linkset.
#guard failCode (script { kind := "patch", url := B ++ "a", body := "[{\"op\":\"jump\",\"path\":\"/a\"}]".toUTF8 } []).2 == "badArguments"
#guard failCode (script { kind := "updateLinkset", linksetUrl := "https://s.example/a.meta", body := "{}".toUTF8 } []).2 == "badArguments"
#guard isDone (script { kind := "patch", url := B ++ "a", precondition := "none", body := "[]".toUTF8 } [rsp 204]).2
-- A patch in another format is not checked as a JSON Patch.
#guard isDone (script { kind := "patch", url := B ++ "a", precondition := "none", mediaType := "application/merge-patch+json", body := "{}".toUTF8 } [rsp 204]).2
-- The linkset of a resource, found with a HEAD.
def foundLinkset := script { kind := "findLinkset", url := B ++ "a" } [lsHead]
#guard foundLinkset.1.length == 1
#guard strAt (repOf foundLinkset.2) "linkset" == some "https://s.example/a.meta"

/-! ### Update, create and move: the results -/

def updatedDone := script { kind := "update", url := B ++ "a", precondition := "none", mediaType := "text/plain", body := "z".toUTF8 }
  [rsp 204 [("ETag", "\"t9\"")]]
#guard strAt (repOf updatedDone.2) "etag" == some "\"t9\""
#guard fld (repOf updatedDone.2) "status" == some (.number "204")
def createdDone := script { kind := "create", url := B ++ "c/", slug := "n", mediaType := "text/plain", body := "z".toUTF8 }
  [rsp 201 [("Location", "/c/n"), ("ETag", "\"t1\"")]]
#guard strAt (repOf createdDone.2) "location" == some "https://s.example/c/n"
#guard ((fld (repOf createdDone.2) "metadata").bind (fun m => m.getString? "url")) == some "https://s.example/c/n"
#guard (repOf (script { kind := "delete", url := B ++ "a", precondition := "none" } [rsp 204]).2) == .object []
-- Links given as {href, rel} objects become Link field values.
#guard ((opOfJson (.object [ ("kind", .string "create"), ("url", .string (B ++ "c/"))
    , ("linkObjects", .array [.object [("href", .string "https://e.example/T"), ("rel", .string "type")]]) ])).toOption.map (·.links)) ==
  some ["<https://e.example/T>; rel=\"type\""]
-- A move ends with a HEAD of the resource where it is now.
def movedFull := script { kind := "move", url := B ++ "a", destination := B ++ "d/" }
  [ descHead, desc, lsHead, lsGet "GET, HEAD, PATCH" mediaJsonPatch
  , rsp 200 [] "{\"linkset\":[{\"anchor\":\"https://s.example/d/a\"}]}"
  , rsp 200 [("ETag", "\"n1\""), ("Link", "<https://s.example/d/a.meta>; rel=\"linkset\"")] ]
#guard (sentAt movedFull.1 5).method == "HEAD" && (sentAt movedFull.1 5).url == "https://s.example/d/a"
#guard strAt (repOf movedFull.2) "location" == some "https://s.example/d/a"
#guard strAt (repOf movedFull.2) "linkset" == some "https://s.example/d/a.meta"
#guard strAt (repOf movedFull.2) "etag" == some "\"n1\""
#guard fld (repOf movedFull.2) "identifierPreserved" == some (.bool false)
#guard fld (repOf movedFull.2) "status" == some (.number "200")
-- The HEAD after the move is not a write, so a failed HEAD is a status failure.
#guard failCode (script { kind := "move", url := B ++ "a", destination := B ++ "d/" }
  [ descHead, desc, lsHead, lsGet "GET, HEAD, PATCH" mediaJsonPatch
  , rsp 200 [] "{\"linkset\":[{\"anchor\":\"https://s.example/d/a\"}]}", rsp 404 ]).2 == "status"

/-! ### Subscriptions: expires -/

def withExpiry := script { kind := "subscribe", url := B ++ "a", inbox := "https://in.example/1", expires := "2027-01-01T00:00:00Z" }
  [descHead, desc, rsp 201 [("Location", "/subs/1")] "{\"id\":\"/subs/1\",\"type\":\"WebhookSubscription\",\"expires\":\"2027-01-01T00:00:00Z\"}"]
#guard (String.fromUTF8? (sentAt withExpiry.1 2).body) ==
  some "{\"type\":\"WebhookSubscription\",\"topic\":[\"https://s.example/a\"],\"inbox\":\"https://in.example/1\",\"expires\":\"2027-01-01T00:00:00Z\"}"
#guard strAt (repOf withExpiry.2) "subscription" == some "https://s.example/subs/1"
#guard fld (repOf withExpiry.2) "expires" == some (.string "2027-01-01T00:00:00Z")
#guard failCode (script { kind := "subscribe", url := B ++ "a", inbox := "https://in.example/1", expires := "tomorrow" } []).2 == "badArguments"
-- Without expires the document has none.
#guard (String.fromUTF8? (sentAt subscribed.1 2).body).any (fun t => (t.splitOn "expires").length == 1)
def gotSub := script { kind := "getSubscription", url := B ++ "subs/1" } [rsp 200 [] "{\"id\":\"/subs/1\",\"type\":[\"WebhookSubscription\"]}"]
#guard strAt (repOf gotSub.2) "subscription" == some "https://s.example/subs/1"

/-! ### Notifications from trusted storages -/

def nbody2 : String := "{\"id\":\"n1\",\"type\":[\"Notification\"],\"activity\":[{\"id\":\"a1\",\"type\":\"Update\",\"object\":{\"id\":\"https://s.example/a\",\"type\":[\"DataResource\"]}},{\"type\":[\"Delete\"],\"object\":\"https://s.example/b\"}]}"
def nop2 (trusted : List String) : Op :=
  { kind := "verifyNotification", url := "http://in.example/inbox/1", method := "POST"
    headers := nheaders "https://s.example/st#k1" "good" (digestOf nbody2.toUTF8), body := nbody2.toUTF8
    trustedStorages := trusted }
-- No list: every storage whose description verifies the signature.
#guard verdict (script (nop2 []) [sdesc "https://s.example/st"]).2 == some true
-- The storage is in the list: the description is read and the signature checked.
#guard verdict (script (nop2 ["https://other.example/", "https://s.example/st"]) [sdesc "https://s.example/st"]).2 == some true
-- The storage is not in the list: refused, and its description is never requested.
#guard (script (nop2 ["https://other.example/"]) [sdesc "https://s.example/st"]).1.isEmpty
#guard verdict (script (nop2 ["https://other.example/"]) [sdesc "https://s.example/st"]).2 == some false
-- The refusal carries the driver's error.
#guard ((repOf (script (nop2 ["https://other.example/"]) []).2).getString? "kind") == some "SignatureVerificationError"
-- What an accepted notification says.
def acceptedN : Json := repOf (script (nop2 []) [sdesc "https://s.example/st"]).2
#guard strAt acceptedN "storage" == some "https://s.example/st"
#guard strAt acceptedN "keyid" == some "https://s.example/st#k1"
#guard fld acceptedN "activities" == some (.array
  [ .object [ ("id", .string "a1"), ("types", .array [.string "Update"]), ("object", .string "https://s.example/a")
            , ("objectTypes", .array [.string "DataResource"]) ]
  , .object [ ("types", .array [.string "Delete"]), ("object", .string "https://s.example/b"), ("objectTypes", .array []) ] ])
-- A bad signature from a trusted storage is still refused.
#guard verdict (script { nop2 ["https://s.example/st"] with headers := nheaders "https://s.example/st#k1" "bad" (digestOf nbody2.toUTF8) } [sdesc "https://s.example/st"]).2 == some false

/-! ### Credentials: Ed25519, ID tokens, bearer tokens -/

def hexB (h : String) : ByteArray := (L4Factoidal.VC.Multibase.byteArrayOfHex? h).getD ByteArray.empty
def p256G : ByteArray := hexB ("6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296" ++
  "4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5")
def edPub : ByteArray := ByteArray.mk ((Array.range 32).map fun i => (i + 1).toUInt8)
/-- Stand-ins for the primitives: a scalar that starts with a zero byte is
refused; the public keys are fixed. -/
def Vk : L4Factoidal.Authz.Crypto :=
  { Vt with
    es256Public := fun sk => if sk.get! 0 == 0 then none else some p256G
    eddsaSign := fun _ _ => ByteArray.mk (Array.replicate 64 7)
    eddsaPublic := fun sk => if sk.get! 0 == 0 then none else some edPub }
def rnd (a b : UInt8) : ByteArray := ByteArray.mk (Array.replicate 32 a ++ Array.replicate 32 b)

-- A P-256 did:key: the multicodec 0x1200 prefix and the compressed point (y is odd).
#guard p256PublicKeyToMultikey p256G == "zDnaepsL7AXenJkVYdkh5KuKsSU7Ykh7kyXaLLU7auN9FWSiZ"
#guard (newAgent Vk .es256 (rnd 5 6)).map (·.agent) == some "did:key:zDnaepsL7AXenJkVYdkh5KuKsSU7Ykh7kyXaLLU7auN9FWSiZ"
#guard (newAgent Vk .es256 (rnd 5 6)).map (·.kid) ==
  some "did:key:zDnaepsL7AXenJkVYdkh5KuKsSU7Ykh7kyXaLLU7auN9FWSiZ#zDnaepsL7AXenJkVYdkh5KuKsSU7Ykh7kyXaLLU7auN9FWSiZ"
-- The first candidate is the first 32 bytes; when the primitive refuses it, the next 32.
#guard (newAgent Vk .es256 (rnd 5 6)).map (·.key.privateKey.data) == some (Array.replicate 32 5)
#guard (newAgent Vk .es256 (rnd 0 6)).map (·.key.privateKey.data) == some (Array.replicate 32 6)
-- Both refused, or too few bytes: no agent.
#guard (newAgent Vk .es256 (rnd 0 0)).isNone
#guard (newAgent Vk .es256 (ByteArray.mk (Array.replicate 32 0))).isNone
-- An Ed25519 did:key (the multicodec 0xed prefix).
#guard (newAgent Vk .eddsa (rnd 5 6)).map (·.agent) == some "did:key:z6MkeXCES4onVW4up9Qgz1KRnZsKmGufcaZxF6Zpv2w5QwUK"
#guard (newAgent Vk .eddsa (rnd 0 6)).map (·.key.privateKey.data) == some (Array.replicate 32 6)
-- Its did:key is the one the VC module parses back to the public key.
#guard ((newAgent Vk .eddsa (rnd 5 6)).bind fun a => L4Factoidal.VC.DidKey.parseDidKey a.agent).map (·.pubkey) ==
  some (L4Factoidal.VC.Multibase.ofByteArray edPub)
-- The key crosses the session as a JWK, for both algorithms.
def keyBack (alg : L4Factoidal.Authz.SigAlg) : Option (Bool × String × Array UInt8) :=
  (newAgent Vk alg (rnd 5 6)).bind fun a =>
    (selfIssuedOfJson (selfIssuedJson a.key)).map fun k => (k.alg == alg, k.subject, k.privateKey.data)
#guard keyBack .es256 == some (true, "did:key:zDnaepsL7AXenJkVYdkh5KuKsSU7Ykh7kyXaLLU7auN9FWSiZ", Array.replicate 32 5)
#guard keyBack .eddsa == some (true, "did:key:z6MkeXCES4onVW4up9Qgz1KRnZsKmGufcaZxF6Zpv2w5QwUK", Array.replicate 32 5)
#guard ((newAgent Vk .eddsa (rnd 5 6)).map fun a => ((selfIssuedJson a.key).field? "jwk").bind (fun j => j.getString? "crv")) == some (some "Ed25519")
-- A key that is neither P-256 nor Ed25519, or whose private part is not 32 bytes, is not a key.
#guard (selfIssuedOfJson (.object [("subject", .string "a"), ("keyId", .string "k"),
  ("jwk", .object [("crv", .string "secp256k1"), ("d", .string "AAAA")])])).isNone
#guard (selfIssuedOfJson (.object [("subject", .string "a"), ("keyId", .string "k"),
  ("jwk", .object [("crv", .string "Ed25519"), ("d", .string "AAAA")])])).isNone

-- A self-issued credential signed with EdDSA: header alg EdDSA, a three-part JWT.
def edKey : SelfIssued :=
  { subject := "did:key:z6Mkx", keyId := "did:key:z6Mkx#z6Mkx", alg := .eddsa, privateKey := ByteArray.mk (Array.replicate 32 1) }
def edJwt : String := (selfIssuedJwt Vk edKey "https://as.example/t" 1000 (ByteArray.mk (Array.replicate 48 9))).getD ""
#guard (edJwt.splitOn ".").length == 3
#guard ((L4Factoidal.JOSE.Base64Url.decode ((edJwt.splitOn ".").getD 0 "")).bind String.fromUTF8?) ==
  some "{\"alg\":\"EdDSA\",\"typ\":\"JWT\",\"kid\":\"did:key:z6Mkx#z6Mkx\"}"
#guard L4Factoidal.JOSE.Base64Url.decode ((edJwt.splitOn ".").getD 2 "") == some (ByteArray.mk (Array.replicate 64 7))
def edFlow := script { kind := "read", url := B ++ "a" }
  [ challenge "https://s.example/.well-known/oauth-protected-resource/a" "https://s.example/st"
  , prm "https://s.example/a", descRoot "https://s.example/", asMetaR, tokenResp, rsp 200 ] { selfIssued := some edKey }
#guard isDone edFlow.2
#guard (formPairs (sentAt edFlow.1 4).body).lookup "subject_token_type" == some jwtTokenType
-- ES256 keeps its header.
#guard ((L4Factoidal.JOSE.Base64Url.decode ((cidToken.splitOn ".").getD 0 "")).bind String.fromUTF8?) ==
  some "{\"alg\":\"ES256\",\"typ\":\"JWT\",\"kid\":\"https://id.example/alice#k1\"}"

-- An ID Token is exchanged with the ID Token type URI.
def idSes : Session := sessionOfJson (.object [("idToken", .string "IDT")])
#guard idSes.subjectToken == "IDT" && idSes.subjectTokenType == "urn:ietf:params:oauth:token-type:id_token"
def idFlow := script { kind := "read", url := B ++ "a" }
  [ challenge "https://s.example/.well-known/oauth-protected-resource/a" "https://s.example/st"
  , prm "https://s.example/a", descRoot "https://s.example/", asMeta, tokenResp, rsp 200 ] idSes
#guard (formPairs (sentAt idFlow.1 4).body).lookup "subject_token" == some "IDT"
#guard (formPairs (sentAt idFlow.1 4).body).lookup "subject_token_type" == some "urn:ietf:params:oauth:token-type:id_token"

-- A bearer token with no realm goes to every request; with a realm, only under it.
def anyBearer : Session := sessionOfJson (.object [("bearer", .object [("token", .string "T0")])])
def realmBearer : Session := sessionOfJson (.object [("bearer", .object [("token", .string "T1"), ("realm", .string "https://s.example/")])])
#guard anyBearer.anyToken == "T0" && anyBearer.tokens.isEmpty
#guard realmBearer.anyToken == "" && realmBearer.tokens.length == 1
#guard (sentAt (script { kind := "read", url := B ++ "a" } [] anyBearer).1 0).header? "authorization" == some "Bearer T0"
#guard (sentAt (script { kind := "read", url := "https://other.example/a" } [] anyBearer).1 0).header? "authorization" == some "Bearer T0"
#guard (sentAt (script { kind := "read", url := B ++ "a" } [] realmBearer).1 0).header? "authorization" == some "Bearer T1"
#guard ((sentAt (script { kind := "read", url := "https://other.example/a" } [] realmBearer).1 0).header? "authorization").isNone
-- The token is not sent to the authorization flow's metadata requests.
#guard (script { kind := "read", url := B ++ "a" }
  [ challenge "https://s.example/.well-known/oauth-protected-resource/a" "https://s.example/st" ] anyBearer).1.length == 1
-- The session survives the JSON form, with the any-token.
#guard (sessionOfJson (sessionJson anyBearer)).anyToken == "T0"

-- A session key that is not a P-256 or Ed25519 private JWK is found before an operation starts.
#guard sessionKeyOk (.object []) && sessionKeyOk (.object [("selfIssued", .null)])
#guard !sessionKeyOk (.object [("selfIssued", .object [("subject", .string "a"), ("keyId", .string "k"), ("jwk", .object [("crv", .string "P-384"), ("d", .string "AAAA")])])])
#guard sessionKeyOk (.object [("selfIssued", selfIssuedJson edKey)])

/-! ### Errors as the driver names them -/

def errKind (e : Json) : Option String := (errorReport e).getString? "kind"
#guard errKind (errJ "status" [("status", .number "404")]) == some "NotFoundError"
#guard errKind (errJ "status" [("status", .number "409")]) == some "ConflictError"
#guard errKind (errJ "status" [("status", .number "418")]) == some "HttpError"
#guard errKind (errJ "badArguments") == some "InvalidArguments"
#guard errKind (errJ "transport") == some "TransportError"
#guard errKind (errJ "discoveryValidation") == some "AuthenticationError"
#guard errKind (errJ "noLinkset") == some "ProtocolError"
#guard errKind (errJ "stepLimit") == some "InternalError"
-- A 405 reports Allow, a 415 Accept-Patch, a JSON body its problem details.
#guard (errorReport (errJ "status" [("status", .number "405"), ("headers", headersJson [("Allow", "GET, HEAD")])])).field? "allow" ==
  some (.array [.string "GET", .string "HEAD"])
#guard (errorReport (errJ "status" [("status", .number "415"), ("headers", headersJson [("Accept-Patch", "application/json-patch+json")])])).field? "acceptPatch" ==
  some (.array [.string "application/json-patch+json"])
#guard (errorReport (errJ "status" [ ("status", .number "409"), ("headers", headersJson [("Content-Type", "application/problem+json")])
  , ("body", .string "{\"status\":409,\"title\":\"Conflict\"}") ])).field? "problem" ==
  some (.object [("status", .number "409"), ("title", .string "Conflict")])
-- A token endpoint's refusal reports the OAuth error.
#guard (errorReport (errJ "authorization" [ ("status", .number "400")
  , ("body", .string "{\"error\":\"invalid_grant\",\"error_description\":\"expired\"}") ])).field? "oauthError" == some (.string "invalid_grant")
-- The failure document of an action carries the report.
#guard ((actionJson (Client.start Vt { kind := "frobnicate" } {}).1 (.fail (errJ "badArguments"))).field? "fail").bind (fun f => f.field? "report") |>.isSome
#guard (failCode (script { kind := "head", url := B ++ "a" } [rsp 404]).2) == "status"
#guard (match (script { kind := "head", url := B ++ "a" } [rsp 404]).2 with
  | .fail e => errKind e
  | _ => none) == some "NotFoundError"

end L4Factoidal.LWS.Client.Tests
