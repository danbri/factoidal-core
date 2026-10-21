/-
L4Factoidal.LWS.AccessGrantsTests — `#guard`s for LWS access requests and
grants (`L4Factoidal.LWS.AccessPolicy`, `L4Factoidal.LWS.AccessGrants`),
https://github.com/danbri/factoidal/issues/913.

Each check runs `AccessGrants.serverStep` (authorization with grants, the
access endpoints, the storage operation) on the reference store `MemStore`
under enforcement. The token verifier is a stub: a signature verifies when
its octets are `good`. alice has `acl:Control` on the storage root, so she
is the storage controller; bob has no ACL authorization at all.
-/
import L4Factoidal.LWS.AccessGrants

namespace L4Factoidal.LWS.AccessGrantsTests

open L4Factoidal.JSON
open L4Factoidal.LWS
open L4Factoidal.LWS.AccessPolicy
open L4Factoidal.LWS.AccessGrants
open L4Factoidal.LWS.Notifications (NotifState Delivery)
open L4Factoidal.JOSE
open L4Factoidal.HTTP (Request Response)

private def stubV : Verifiers :=
  { es256 := fun _ _ sig => sig == "good".toUTF8
    rs256 := fun _ _ _ _ => false
    eddsa := fun _ _ _ => false }

private def zeros : ByteArray := ⟨Array.replicate 32 0⟩
private def issuerA : String := "https://as.example"
private def alice : String := "https://id.example/alice"
private def bob : String := "https://id.example/bob"
private def base : String := "http://localhost/"
private def storageId : String := "http://localhost/.well-known/lws-storage"

private def cfg : Config :=
  { baseIri := base, accessGrants := true, notifications := true, moves := true }

private def az0 : Authorization.AuthzConfig :=
  { issuers := [{ issuer := issuerA, keys := [{ kid := some "k1", key := .ec zeros zeros }],
                  fetchedAt := some 1000 }] }

private def b64 (s : String) : String := Base64Url.encodeUtf8 s

private def tok (sub : String) (client : String := "https://app.example/touchstone") : String :=
  b64 "{\"alg\":\"ES256\",\"typ\":\"at+jwt\",\"kid\":\"k1\"}" ++ "." ++
  b64 ("{\"iss\":\"" ++ issuerA ++ "\",\"sub\":\"" ++ sub ++ "\",\"aud\":\"" ++ storageId ++
       "\",\"client_id\":\"" ++ client ++ "\",\"exp\":5000,\"iat\":1000}") ++ "." ++
  Base64Url.encode "good".toUTF8

private def asAlice : List (String × String) := [("authorization", "Bearer " ++ tok alice)]
private def asBob : List (String × String) := [("authorization", "Bearer " ++ tok bob)]
private def asBobClient (c : String) : List (String × String) :=
  [("authorization", "Bearer " ++ tok bob c)]

private def st0 : MemState :=
  { entries :=
      [ { path := "/", kind := .storageRoot, contentType := "text/turtle", body := .empty, mtime := 1 }
      , { path := "/.acl", kind := .metadataResource, contentType := "text/turtle",
          body := textBytes ((Authorization.ownerRootAcl base alice).getD ""), mtime := 1 }
      , { path := "/doc.txt", kind := .dataResource, contentType := "text/plain",
          body := textBytes "for bob", mtime := 1 }
      , { path := "/c.csv", kind := .dataResource, contentType := "text/csv",
          body := textBytes "a,b", mtime := 1 }
      , { path := "/box/", kind := .container, contentType := "text/turtle", body := .empty, mtime := 1 }
      , { path := "/dest/", kind := .container, contentType := "text/turtle", body := .empty, mtime := 1 }
      , { path := "/m.txt", kind := .dataResource, contentType := "text/plain",
          body := textBytes "moved", mtime := 1 } ]
    clock := 1100 }

/-- One storage: the store, the authorization state (with the grants), the
notification state, the last answer and its deliveries. -/
structure W where
  st : MemState
  az : Authorization.AuthzConfig
  ns : NotifState
  resp : Response
  ds : List Delivery

private def w0 : W := ⟨st0, az0, {}, ⟨200, [], "", none⟩, []⟩

private def req (m t : String) (hs : List (String × String) := []) (body : String := "") : Request :=
  { method := m, path := t, queryStr := "", headers := hs, body }

private def run1 (w : W) (r : Request) : W :=
  match serverStep stubV MemStore cfg w.az none 1100 r w.st w.ns with
  | .inl _ => { w with resp := ⟨599, [], "", none⟩, ds := [] }
  | .inr (resp, st', ns', acc', ds) => ⟨st', { w.az with access := acc' }, ns', resp, ds⟩

private def status (w : W) (r : Request) : Nat := (run1 w r).resp.status
private def hdr (w : W) (n : String) : String :=
  ((w.resp.headers.find? (·.1 == n)).map (·.2)).getD ""
private def j (s : String) : Json := (parseJson? s).getD .null

/-- A grant document: `actions` for `assignee` on `targets` (IRIs), with
`extra` members of the policy (constraints) and of the document. -/
private def grantDoc (actions : List String) (assignee : String) (targets : List String)
    (policyExtra : String := "") (docExtra : String := "") (kind : String := "AccessGrant") : String :=
  "{\"@context\":[\"https://www.w3.org/ns/lws/v1\"],\"type\":[\"" ++ kind ++ "\"]," ++
  "\"storage\":\"" ++ storageId ++ "\"," ++ docExtra ++
  "\"access\":[{\"type\":[\"AccessPolicy\"],\"action\":[" ++
  ",".intercalate (actions.map (fun a => "\"" ++ a ++ "\"")) ++ "],\"assignee\":\"" ++ assignee ++
  "\",\"target\":{\"type\":\"StorageResource\",\"value\":[" ++
  ",".intercalate (targets.map (fun t => "\"" ++ base ++ t ++ "\"")) ++ "]}" ++ policyExtra ++ "}]}"

private def postGrant (w : W) (body : String) (who := asAlice) : W :=
  run1 w (req "POST" accessGrantsPath (("content-type", "application/lws+json") :: who) body)

/-! ## Discovery -/

private def descr : Json := j (run1 w0 (req "GET" storagePath)).resp.body
private def service? (t : String) : Option Json :=
  (descr.getArray? "service").bind (·.find? (fun s => s.getString? "type" == some t))

#guard (service? "AccessGrantService").bind (·.getString? "serviceEndpoint") ==
  some "http://localhost/.well-known/lws-access-grants/"
#guard (service? "AccessRequestService").bind (·.getString? "serviceEndpoint") ==
  some "http://localhost/.well-known/lws-access-requests/"
#guard (service? "AccessGrantService").bind (·.field? "conformsTo") ==
  some (.array [.string "https://www.w3.org/ns/lws#AccessProfile"])
-- Off: no service, and the endpoint is an ordinary (missing) path.
#guard ((j (match serverStep stubV MemStore { cfg with accessGrants := false } az0 none 1100
    (req "GET" storagePath) st0 {} with
    | .inr (r, _) => r.body | .inl _ => "")).getArray? "service").map
      (·.any (fun s => s.getString? "type" == some "AccessGrantService")) == some false
#guard endpointOf? accessGrantsPath == some .grants
#guard endpointOf? accessRequestsPath == some .requests

/-! ## The endpoints are LWS containers -/

#guard status w0 (req "GET" accessGrantsPath asAlice) == 200
#guard hdr (run1 w0 (req "GET" accessGrantsPath asAlice)) "link" |>.startsWith
  "<https://www.w3.org/ns/lws#Container>; rel=\"type\""
#guard (j (run1 w0 (req "GET" accessGrantsPath asAlice)).resp.body).getArray? "items" == some []
-- anonymous: 401
#guard status w0 (req "GET" accessGrantsPath) == 401
#guard status w0 (req "PUT" accessGrantsPath asAlice) == 405

/-! ## Creating, reading, enforcing and revoking a grant -/

private def wG : W := postGrant w0 (grantDoc ["read"] bob ["doc.txt"])

#guard wG.resp.status == 201
#guard hdr wG "location" == "http://localhost/.well-known/lws-access-grants/g0"
#guard (j (run1 wG (req "GET" (accessGrantsPath ++ "g0") asAlice)).resp.body).field? "type" ==
  some (.array [.string "AccessGrant"])
#guard (j (run1 wG (req "GET" (accessGrantsPath ++ "g0") asAlice)).resp.body).getString? "id" ==
  some "http://localhost/.well-known/lws-access-grants/g0"
#guard (j (run1 wG (req "GET" (accessGrantsPath ++ "g0") asAlice)).resp.body).getString? "storage" ==
  some storageId
-- Before the grant bob cannot read; with it he can read, and no more.
#guard status w0 (req "GET" "/doc.txt" asBob) == 403
#guard status wG (req "GET" "/doc.txt" asBob) == 200
#guard status wG (req "PUT" "/doc.txt" (("content-type", "text/plain") :: asBob) "x") == 403
#guard status wG (req "DELETE" "/doc.txt" asBob) == 403
#guard status wG (req "GET" "/c.csv" asBob) == 403
#guard status wG (req "GET" "/doc.txt") == 401
-- A grant never reaches the ACL resource.
#guard status (postGrant w0 (grantDoc ["read"] bob [".acl"])) (req "GET" "/.acl" asBob) == 403
#guard (postGrant w0 (grantDoc ["read"] bob [".acl"])).resp.status == 400
-- bob is named by the grant, so he may see it; he may not revoke it.
#guard status wG (req "GET" (accessGrantsPath ++ "g0") asBob) == 200
#guard status wG (req "DELETE" (accessGrantsPath ++ "g0") asBob) == 403
-- Only the storage controller creates a grant.
#guard (postGrant w0 (grantDoc ["read"] bob ["doc.txt"]) asBob).resp.status == 403
-- Revocation: 204, then bob is refused again.
private def wR : W := run1 wG (req "DELETE" (accessGrantsPath ++ "g0") asAlice)
#guard wR.resp.status == 204
#guard status wR (req "GET" "/doc.txt" asBob) == 403
#guard status wR (req "GET" (accessGrantsPath ++ "g0") asAlice) == 404
-- Public access through foaf:Agent.
#guard status (postGrant w0 (grantDoc ["read"] foafAgent ["doc.txt"])) (req "GET" "/doc.txt") == 200
-- A grant on a container does not reach its members.
#guard status (postGrant w0 (grantDoc ["read"] bob [""])) (req "GET" "/doc.txt" asBob) == 403
#guard status (postGrant w0 (grantDoc ["read"] bob [""])) (req "GET" "/" asBob) == 200
-- create on a container lets bob POST into it, and nothing else.
private def wC : W := postGrant w0 (grantDoc ["create"] bob ["box/"])
#guard status wC (req "POST" "/box/" (("content-type", "text/plain") :: asBob) "new") == 201
#guard status wC (req "GET" "/box/" asBob) == 403
-- A grant with an extra member and no inbox or constraint is accepted.
#guard (postGrant w0 (grantDoc ["read"] bob ["doc.txt"] "" "\"urn:x:note\":\"n\",")).resp.status == 201

/-! ## Incomplete or malformed grants are refused and grant nothing -/

private def refused (body : String) : Bool :=
  let w := postGrant w0 body
  w.resp.status == 400 && status w (req "GET" "/doc.txt" asBob) == 403

#guard refused ("{\"@context\":[\"https://www.w3.org/ns/lws/v1\"],\"storage\":\"" ++ storageId ++
  "\",\"access\":[{\"type\":[\"AccessPolicy\"],\"action\":[\"read\"],\"assignee\":\"" ++ bob ++ "\"}]}")
#guard refused ("{\"@context\":[\"https://www.w3.org/ns/lws/v1\"],\"type\":[\"AccessGrant\"]," ++
  "\"access\":[{\"type\":[\"AccessPolicy\"],\"action\":[\"read\"],\"assignee\":\"" ++ bob ++ "\"}]}")
#guard refused ("{\"@context\":[\"https://www.w3.org/ns/lws/v1\"],\"type\":[\"AccessGrant\"]," ++
  "\"storage\":\"" ++ storageId ++ "\"}")
#guard refused ("{\"@context\":[\"https://www.w3.org/ns/lws/v1\"],\"type\":[\"AccessGrant\"]," ++
  "\"storage\":\"" ++ storageId ++ "\",\"access\":[]}")
#guard refused ((grantDoc ["read"] bob ["doc.txt"]).replace "\"type\":[\"AccessPolicy\"]," "")
#guard refused ((grantDoc ["read"] bob ["doc.txt"]).replace "AccessPolicy" "urn:x:not-a-policy")
#guard refused ((grantDoc ["read"] bob ["doc.txt"]).replace "\"action\":[\"read\"]," "")
#guard refused ((grantDoc ["read"] bob ["doc.txt"]).replace ("\"assignee\":\"" ++ bob ++ "\",") "")
#guard refused (grantDoc ["write"] bob ["doc.txt"])
#guard refused (grantDoc ["read"] bob ["doc.txt"] "" "\"inbox\":\"not a uri\",")
#guard refused ((grantDoc ["read"] bob ["doc.txt"]).replace "https://www.w3.org/ns/lws/v1" "urn:x:ctx")
#guard refused ((grantDoc ["read"] bob ["doc.txt"]).replace storageId "https://other.example/")
#guard refused ((grantDoc ["read"] bob ["doc.txt"]).replace
  "{\"type\":\"StorageResource\",\"value\":[\"http://localhost/doc.txt\"]}" "\"http://localhost/doc.txt\"")
#guard refused (grantDoc ["read"] bob ["doc.txt"]
  ",\"constraint\":[{\"leftOperand\":\"spatial\",\"operator\":\"eq\",\"rightOperand\":\"x\"}]")
#guard (run1 w0 (req "POST" accessGrantsPath (("content-type", "text/turtle") :: asAlice) "x")).resp.status == 415

/-! ## Constraints (§Constraints) -/

private def withC (c : String) : String := ",\"constraint\":[" ++ c ++ "]"
private def dt (op v : String) : String :=
  "{\"leftOperand\":\"dateTime\",\"operator\":\"" ++ op ++ "\",\"rightOperand\":\"" ++ v ++ "\"}"

-- The clock is 1100 s after the epoch: 1970-01-01T00:18:20Z.
-- A closed window: one constraint met, one not.
#guard status (postGrant w0 (grantDoc ["read"] bob ["doc.txt"]
    (withC (dt "gteq" "1970-01-01T00:00:00Z" ++ "," ++ dt "lteq" "1970-01-01T00:10:00Z"))))
  (req "GET" "/doc.txt" asBob) == 403
-- An open window.
#guard status (postGrant w0 (grantDoc ["read"] bob ["doc.txt"]
    (withC (dt "gteq" "1970-01-01T00:00:00Z" ++ "," ++ dt "lteq" "2999-12-31T23:59:59Z"))))
  (req "GET" "/doc.txt" asBob) == 200
-- A window that has not opened yet.
#guard status (postGrant w0 (grantDoc ["read"] bob ["doc.txt"] (withC (dt "gteq" "2999-01-01T00:00:00Z"))))
  (req "GET" "/doc.txt" asBob) == 403
-- format: text/plain or application/json.
private def wF : W := postGrant w0 (grantDoc ["read"] bob ["doc.txt", "c.csv"]
  (withC "{\"leftOperand\":\"format\",\"operator\":\"isAnyOf\",\"rightOperand\":[\"text/plain\",\"application/json\"]}"))
#guard wF.resp.status == 201
#guard status wF (req "GET" "/doc.txt" asBob) == 200
#guard status wF (req "GET" "/c.csv" asBob) == 403
-- type: data resources only.
private def wT : W := postGrant w0 (grantDoc ["read"] bob ["box/", "doc.txt"]
  (withC "{\"leftOperand\":\"type\",\"operator\":\"eq\",\"rightOperand\":\"https://www.w3.org/ns/lws#DataResource\"}"))
#guard status wT (req "GET" "/doc.txt" asBob) == 200
#guard status wT (req "GET" "/box/" asBob) == 403
-- client: the token's client_id.
private def wK : W := postGrant w0 (grantDoc ["read"] bob ["doc.txt"]
  (withC "{\"leftOperand\":\"client\",\"operator\":\"eq\",\"rightOperand\":\"urn:x:not-bobs\"}"))
#guard wK.resp.status == 201
#guard status wK (req "GET" "/doc.txt" asBob) == 403
#guard status wK (req "GET" "/doc.txt" (asBobClient "urn:x:not-bobs")) == 200
-- purpose is accepted, and no request satisfies it.
private def wP : W := postGrant w0 (grantDoc ["read"] bob ["doc.txt"]
  (withC "{\"leftOperand\":\"purpose\",\"operator\":\"isAnyOf\",\"rightOperand\":[\"urn:x:p\"]}"))
#guard wP.resp.status == 201
#guard status wP (req "GET" "/doc.txt" asBob) == 403

/-! ## Moving needs delete of the resource and create in the destination -/

private def moveReq (who : List (String × String)) : Request :=
  req "PATCH" "/m.txt?linkset" (("content-type", "application/json-patch+json") :: who)
    "[{\"op\":\"replace\",\"path\":\"/linkset/0/up/0/href\",\"value\":\"http://localhost/dest/\"}]"

-- modify and delete of the resource, read of the destination: refused.
#guard status (postGrant (postGrant w0 (grantDoc ["read", "modify", "delete"] bob ["m.txt"]))
  (grantDoc ["read"] bob ["dest/"])) (moveReq asBob) == 403
-- modify of the resource, create in the destination, no delete: refused.
#guard status (postGrant (postGrant w0 (grantDoc ["read", "modify"] bob ["m.txt"]))
  (grantDoc ["read", "create"] bob ["dest/"])) (moveReq asBob) == 403
-- all three: the move is made.
#guard status (postGrant (postGrant w0 (grantDoc ["read", "modify", "delete"] bob ["m.txt"]))
  (grantDoc ["read", "create"] bob ["dest/"])) (moveReq asBob) == 200

/-! ## Access requests -/

private def wQ : W :=
  run1 w0 (req "POST" accessRequestsPath (("content-type", "application/lws+json") :: asBob)
    (grantDoc ["read"] bob ["box/"] "" "\"inbox\":\"https://inbox.example/bob/\"," "AccessRequest"))

#guard wQ.resp.status == 201
#guard hdr wQ "location" == "http://localhost/.well-known/lws-access-requests/r0"
#guard (j (run1 wQ (req "GET" (accessRequestsPath ++ "r0") asAlice)).resp.body).field? "type" ==
  some (.array [.string "AccessRequest"])
#guard status wQ (req "GET" (accessRequestsPath ++ "r0") asBob) == 200
-- A request is not a grant.
#guard status wQ (req "GET" "/box/" asBob) == 403
-- An access request posted to the grant endpoint, or a grant to the request endpoint: 400.
#guard (run1 w0 (req "POST" accessRequestsPath (("content-type", "application/lws+json") :: asBob)
    (grantDoc ["read"] bob ["box/"]))).resp.status == 400
-- The controller answers by granting: the requesting agent's inbox is notified.
private def wQG : W := postGrant wQ (grantDoc ["read"] bob ["box/"])
#guard wQG.ds.map (·.url) == ["https://inbox.example/bob/"]
#guard (j (wQG.ds.headD default).body).getString? "type" == some "Notification"
#guard ((j (wQG.ds.headD default).body).field? "activity").bind (·.field? "type") ==
  some (.array [.string "Create"])
-- or by deleting the request.
#guard status wQ (req "DELETE" (accessRequestsPath ++ "r0") asAlice) == 204
-- A grant with its own inbox is announced there.
#guard (postGrant w0 (grantDoc ["read"] bob ["doc.txt"] "" "\"inbox\":\"https://inbox.example/g/\",")).ds.map
  (·.url) == ["https://inbox.example/g/"]
-- No inbox, no delivery.
#guard wG.ds.isEmpty

/-! ## Persistence -/

private def reloaded (w : W) : Option AccessState :=
  match stateOfJson base (storageIris cfg az0) (stateJson w.az.access) with
  | .ok s => some s
  | .error _ => none

#guard (reloaded wQG).map (fun s => (s.requests.length, s.grants.length, s.seq)) == some (1, 1, 2)
private def bobReads (p : String) : Ctx :=
  { agent := some bob, now := 1100, action := .read, path := p, entry := memLookup st0 p }

#guard (reloaded wF).map (fun s => grantsPermit s.grants (bobReads "/c.csv")) == some false
#guard (reloaded wF).map (fun s => grantsPermit s.grants (bobReads "/doc.txt")) == some true

/-! ## xsd:dateTime -/

#guard parseXsdDateTime? "1970-01-01T00:00:00Z" == some 0
#guard parseXsdDateTime? "1970-01-01T01:00:00+01:00" == some 0
#guard parseXsdDateTime? "1970-01-01T00:00:00.5-00:30" == some 1800
#guard parseXsdDateTime? "2026-06-09T10:00:00Z" == some 1780999200
#guard parseXsdDateTime? "2026-02-30T10:00:00Z" == none
#guard parseXsdDateTime? "not a date" == none
#guard isUri "https://id.example/bob" && isUri "urn:x:y" && !isUri "not a uri" && !isUri "relative/path"

/-! ## The registry checks (`Harness/LwsProbe`) -/

def lwsGuardAccessDiscovery : Bool :=
  (service? "AccessGrantService").isSome && (service? "AccessRequestService").isSome

def lwsGuardAccessCreate : Bool :=
  wG.resp.status == 201 && hdr wG "location" == "http://localhost/.well-known/lws-access-grants/g0" &&
    wQ.resp.status == 201 && hdr wQ "location" == "http://localhost/.well-known/lws-access-requests/r0"

def lwsGuardAccessConstraints : Bool :=
  status wF (req "GET" "/doc.txt" asBob) == 200 && status wF (req "GET" "/c.csv" asBob) == 403 &&
    status wK (req "GET" "/doc.txt" asBob) == 403 && status wP (req "GET" "/doc.txt" asBob) == 403

#guard lwsGuardAccessDiscovery
#guard lwsGuardAccessCreate
#guard lwsGuardAccessConstraints

end L4Factoidal.LWS.AccessGrantsTests
