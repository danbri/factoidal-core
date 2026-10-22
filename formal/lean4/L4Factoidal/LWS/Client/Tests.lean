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
def lsPut := script { kind := "updateLinkset", url := B ++ "a", mediaType := mediaLinkset, body := "{}".toUTF8 }
  [lsHead, lsGet "GET, HEAD, PUT, PATCH" mediaJsonPatch, rsp 204]
#guard lsPut.1.map (·.method) == ["HEAD", "GET", "PUT"]
#guard (sentAt lsPut.1 2).url == "https://s.example/a.meta"
#guard (sentAt lsPut.1 2).header? "if-match" == some "\"m1\""
#guard isDone lsPut.2
-- Not advertised: no PUT at all.
#guard failCode (script { kind := "updateLinkset", url := B ++ "a", mediaType := mediaLinkset }
  [lsHead, lsGet "GET, HEAD, PATCH" mediaJsonPatch]).2 == "notAdvertised"
-- A JSON Patch only in an advertised format.
#guard (sentAt (script { kind := "updateLinkset", url := B ++ "a", body := "[]".toUTF8 }
  [lsHead, lsGet "GET, HEAD, PATCH" mediaJsonPatch]).1 2).method == "PATCH"
#guard failCode (script { kind := "updateLinkset", url := B ++ "a", body := "[]".toUTF8 }
  [lsHead, lsGet "GET, HEAD, PATCH" "application/merge-patch+json"]).2 == "notAdvertised"
-- 405 on the PUT: the linkset is read again, the PUT is never repeated.
def refused := script { kind := "updateLinkset", url := B ++ "a", mediaType := mediaLinkset, body := "{}".toUTF8 }
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
#guard moved.1.map (·.method) == ["HEAD", "GET", "HEAD", "GET", "PATCH"]
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

end L4Factoidal.LWS.Client.Tests
