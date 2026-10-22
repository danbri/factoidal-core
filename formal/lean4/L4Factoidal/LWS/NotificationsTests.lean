/-
L4Factoidal.LWS.NotificationsTests — `#guard`s for LWS notifications and
the webhook notification suite (`L4Factoidal.LWS.Notifications`),
https://github.com/danbri/factoidal/issues/890.

Each check runs `serverStep` (authorization, the storage operation, the
change set, the routing and the delivery requests) on the reference store
`MemStore`, in the development mode with no authorization, except where a
check passes its own access function. The signer is a stub (the SHA-256 of
the signature base); real Ed25519 signatures are checked against the
published key by `node tests/lws/draft-binding.mjs`.
-/
import L4Factoidal.LWS.Notifications

namespace L4Factoidal.LWS.NotificationsTests

open L4Factoidal.JSON
open L4Factoidal.LWS
open L4Factoidal.LWS.Notifications
open L4Factoidal.HTTP (Request Response)

private def stubV : JOSE.Verifiers :=
  { es256 := fun _ _ _ => false, rs256 := fun _ _ _ _ => false, eddsa := fun _ _ _ => false }

private def cfg : Config := { baseIri := "http://localhost/", notifications := true }
private def az : Authorization.AuthzConfig := { insecureNoAuth := true }

private def stubSigner : Signer :=
  { keyId := "http://localhost/.well-known/lws-storage#notification-key-0", sign := L4Factoidal.Crypto.sha256 }

private def st0 : MemState :=
  { entries := [{ path := "/", kind := .storageRoot, contentType := "text/turtle",
                  body := .empty, mtime := 1000 }], clock := 1001 }

private def req (m t : String) (hs : List (String × String) := []) (body : String := "") : Request :=
  { method := m, path := t, queryStr := "", headers := hs, body }

private def putText (t body : String) : Request := req "PUT" t [("content-type", "text/plain")] body

private def subReq (body : String) (ct : String := "application/lws+json") : Request :=
  req "POST" subscriptionsPath [("content-type", ct)] body

structure W where
  st : MemState
  ns : NotifState
  resp : Response
  ds : List Delivery

private def run1 (w : W) (r : Request) (signer : Option Signer := none)
    (c : Config := cfg) : W :=
  match serverStep stubV MemStore c az signer w.st.clock r w.st w.ns with
  | .inl _ => { w with resp := ⟨599, [], "", none⟩, ds := [] }
  | .inr (resp, st', ns', ds) => ⟨st', ns', resp, ds⟩

private def w0 : W := ⟨st0, {}, ⟨200, [], "", none⟩, []⟩

private def j (s : String) : Json := (parseJson? s).getD .null
private def bodyJ (d : Delivery) : Json := j d.body
private def respJ (w : W) : Json := j w.resp.body

/-- The activities of a delivery, as an array whatever the batching. -/
private def acts (d : Delivery) : List Json :=
  match (bodyJ d).field? "activity" with
  | some (.array xs) => xs
  | some o => [o]
  | none => []

private def actType (a : Json) : Option String :=
  match a.field? "type" with
  | some (.array [.string t]) => some t
  | _ => none

private def objId (a : Json) : Option String := (a.field? "object").bind (·.getString? "id")
private def objType (a : Json) : Option String :=
  match (a.field? "object").bind (·.field? "type") with
  | some (.array [.string t]) => some t
  | _ => none

private def subBody : String :=
  "{\"@context\":[\"https://www.w3.org/ns/lws/v1\"],\"type\":\"WebhookSubscription\"," ++
  "\"topic\":[\"http://localhost/docs/\"],\"inbox\":\"http://hook.example:8080/in/1/\"}"

/-! ## Discovery (LWS §Notification Discovery) -/

private def descr (c : Config) : Json :=
  j (run1 w0 (req "GET" storagePath) (c := c)).resp.body

private def notifService (c : Config) : Option Json :=
  ((descr c).getArray? "service").bind (·.find? (fun s => s.getString? "type" == some "NotificationService"))

#guard (notifService cfg).bind (·.getString? "serviceEndpoint") ==
  some "http://localhost/.well-known/lws-subscriptions/"
#guard (notifService cfg).bind (·.field? "subscriptionType") ==
  some (.array [.string "WebhookSubscription"])
-- Negative: a storage that does not offer notifications advertises no service.
#guard notifService { cfg with notifications := false } == none
-- With a signing key: a JsonWebKey verification method referenced from authentication.
#guard
  let d := descr { cfg with notificationKeyX := some "AAAA" }
  let kid := notificationKeyId "http://localhost/" "AAAA"
  d.getArray? "authentication" == some [.string kid] &&
  ((d.getArray? "verificationMethod").bind (·.head?)).bind (·.getString? "id") == some kid &&
  kid.startsWith "http://localhost/.well-known/lws-storage#"
#guard (descr cfg).field? "verificationMethod" == none

/-! ## Subscribing (LWS §Subscriptions, webhook suite §Creating a Webhook Subscription) -/

private def w1 : W := run1 w0 (putText "/docs/a.txt" "one")
private def w2 : W := run1 w1 (subReq subBody)

#guard w1.resp.status == 201 && w1.ds.isEmpty
#guard w2.resp.status == 201
#guard w2.resp.headers.lookup "content-type" == some "application/lws+json"
#guard (respJ w2).getString? "type" == some "WebhookSubscription"
#guard (respJ w2).getString? "subscription" == some "http://localhost/.well-known/lws-subscriptions/sub0"
#guard w2.resp.headers.lookup "location" == some "http://localhost/.well-known/lws-subscriptions/sub0"
#guard w2.ns.subs.length == 1 && w2.ns.subs.head?.map (·.topics) == some ["/docs/"]

-- Negative requests: each is refused and makes no subscription.
private def refused (body : String) (ct : String := "application/lws+json") : Nat × Nat :=
  let w := run1 w1 (subReq body ct)
  (w.resp.status, w.ns.subs.length)

#guard refused "{\"topic\":[\"http://localhost/docs/\"],\"inbox\":\"http://h.example/\"}" == (400, 0)
#guard refused "{\"type\":\"TouchstoneUnadvertisedSubscription\",\"topic\":[\"http://localhost/docs/\"],\"inbox\":\"http://h.example/\"}" == (400, 0)
#guard refused "{\"type\":\"WebhookSubscription\",\"inbox\":\"http://h.example/\"}" == (400, 0)
#guard refused "{\"type\":\"WebhookSubscription\",\"topic\":[],\"inbox\":\"http://h.example/\"}" == (400, 0)
#guard refused "{\"type\":\"WebhookSubscription\",\"topic\":\"http://localhost/docs/\",\"inbox\":\"http://h.example/\"}" == (400, 0)
#guard refused "{\"type\":\"WebhookSubscription\",\"topic\":[\"http://elsewhere.example/docs/\"],\"inbox\":\"http://h.example/\"}" == (400, 0)
#guard refused "{\"type\":\"WebhookSubscription\",\"topic\":[\"http://localhost/docs/\"]}" == (400, 0)
#guard refused "{\"type\":\"WebhookSubscription\",\"topic\":[\"http://localhost/docs/\"],\"inbox\":\"ftp://h.example/\"}" == (400, 0)
#guard refused "{\"type\":\"WebhookSubscription\",\"topic\":[\"http://localhost/docs/\"],\"inbox\":\"http://h.example/\",\"expires\":\"tomorrow\"}" == (400, 0)
#guard refused "{\"type\":\"WebhookSubscription\",\"topic\":[\"http://localhost/docs/\"],\"inbox\":\"http://h.example/\",\"expires\":\"1970-01-01T00:00:01Z\"}" == (400, 0)
#guard refused "not json" == (400, 0)
-- An inbox that is a container of this storage would make a loop: refused.
#guard refused "{\"type\":\"WebhookSubscription\",\"topic\":[\"http://localhost/docs/\"],\"inbox\":\"http://localhost/docs/\"}" == (400, 0)
#guard refused "{\"type\":\"WebhookSubscription\",\"topic\":[\"http://localhost/docs/\"],\"inbox\":\"http://localhost/\"}" == (400, 0)
-- Any inbox at this server's authority is refused (issue 915,
-- `InboxGuard.loops`), also one that is not a container.
#guard refused "{\"type\":\"WebhookSubscription\",\"topic\":[\"http://localhost/docs/\"],\"inbox\":\"http://localhost/.well-known/lws-storage\"}" == (400, 0)
-- This server under another name: `localhost` at another spelling, a loopback
-- address, IPv6 loopback, all at port 80 (the base IRI's).
#guard refused "{\"type\":\"WebhookSubscription\",\"topic\":[\"http://localhost/docs/\"],\"inbox\":\"http://LOCALHOST:80/in\"}" == (400, 0)
#guard refused "{\"type\":\"WebhookSubscription\",\"topic\":[\"http://localhost/docs/\"],\"inbox\":\"http://127.0.0.1/in\"}" == (400, 0)
#guard refused "{\"type\":\"WebhookSubscription\",\"topic\":[\"http://localhost/docs/\"],\"inbox\":\"http://[::1]/in\"}" == (400, 0)
-- Negative: another port of this machine is another server.
#guard refused "{\"type\":\"WebhookSubscription\",\"topic\":[\"http://localhost/docs/\"],\"inbox\":\"http://127.0.0.1:8080/in\"}" == (201, 1)
#guard refused subBody "text/plain" == (415, 0)

-- `expires` far in the future is accepted and echoed.
private def wExp : W := run1 w1 (subReq
  "{\"type\":\"WebhookSubscription\",\"topic\":[\"http://localhost/docs/\"],\"inbox\":\"http://h.example/\",\"expires\":\"2999-12-31T23:59:59Z\"}")
#guard wExp.resp.status == 201 && (respJ wExp).getString? "expires" == some "2999-12-31T23:59:59Z"

-- Subscribe-time authorization: an agent that cannot read a topic is refused
-- with 403, even when it can read the others.
private def canReadOnlyA : Option String → String → Bool := fun _ p => p == "/docs/a.txt"
private def subAuth (topics : String) : Nat :=
  (subscriptionsStep canReadOnlyA cfg 2000 (some "https://id.example/bob")
    (subReq ("{\"type\":\"WebhookSubscription\",\"topic\":" ++ topics ++ ",\"inbox\":\"http://h.example/\"}"))
    subscriptionsPath {}).1.status
#guard subAuth "[\"http://localhost/docs/a.txt\"]" == 201
#guard subAuth "[\"http://localhost/docs/a.txt\",\"http://localhost/docs/\"]" == 403
#guard subAuth "[\"http://localhost/docs/\"]" == 403

/-! ## Deliveries (LWS §Notification Data Model, §Activity Types) -/

private def w3 : W := run1 w2 (putText "/docs/b.txt" "two")
private def w4 : W := run1 w3 (putText "/docs/a.txt" "uno")
private def w5 : W := run1 w4 (req "DELETE" "/docs/a.txt")
private def w6 : W := run1 w5 (putText "/other.txt" "elsewhere")
private def w7 : W := run1 w6 (putText "/docs/sub/c.txt" "deep")

-- Create: one delivery, a Notification envelope with one Create activity.
#guard w3.resp.status == 201 && w3.ds.length == 1
#guard w3.ds.head?.map (·.url) == some "http://hook.example:8080/in/1/"
#guard w3.ds.head?.map (fun d => (bodyJ d).getString? "type") == some (some "Notification")
#guard w3.ds.head?.map (fun d => (bodyJ d).getString? "storage") ==
  some (some "http://localhost/.well-known/lws-storage")
#guard w3.ds.head?.map (fun d => (acts d).map actType) == some [some "Create"]
#guard w3.ds.head?.map (fun d => (acts d).map objId) == some [some "http://localhost/docs/b.txt"]
#guard w3.ds.head?.map (fun d => (acts d).map objType) == some [some "DataResource"]
#guard w3.ds.head?.map (fun d => (acts d).map (·.getString? "target")) == some [some "http://localhost/docs/"]
-- No actor ("The actor property SHOULD be omitted by default.").
#guard w3.ds.head?.map (fun d => (acts d).map (·.field? "actor")) == some [none]
-- id: a urn:uuid; published: an RFC 3339 date-time.
#guard w3.ds.head?.map (fun d => (acts d).map (fun a => ((a.getString? "id").getD "").startsWith "urn:uuid:")) == some [true]
#guard w3.ds.head?.map (fun d => (acts d).map (fun a => (a.getString? "published").bind parseRfc3339?)) ==
  some [some w2.st.clock]
#guard w3.ds.head?.map (fun d => d.headers.lookup "content-type") == some (some "application/lws+json")

-- Update and Delete (with origin).
#guard w4.ds.head?.map (fun d => (acts d).map actType) == some [some "Update"]
#guard w4.ds.head?.map (fun d => (acts d).map objId) == some [some "http://localhost/docs/a.txt"]
#guard w5.resp.status == 204
#guard w5.ds.head?.map (fun d => (acts d).map actType) == some [some "Delete"]
#guard w5.ds.head?.map (fun d => (acts d).map (·.getString? "origin")) == some [some "http://localhost/docs/"]
-- Negative: a change outside the topic is not delivered.
#guard w6.resp.status == 201 && w6.ds.isEmpty
-- Recursive scope and batching: one PUT created a subcontainer and a
-- resource in it; one envelope carries both Creates, in that order.
#guard w7.ds.length == 1
#guard w7.ds.head?.map (fun d => (acts d).map (fun a => (actType a, objId a, objType a))) ==
  some [ (some "Create", some "http://localhost/docs/sub/", some "Container")
       , (some "Create", some "http://localhost/docs/sub/c.txt", some "DataResource") ]
-- Activity identifiers are distinct.
#guard
  let ids := (w3.ds ++ w4.ds ++ w5.ds ++ w7.ds).flatMap (fun d => (acts d).filterMap (·.getString? "id"))
  ids.length == 5 && ids.eraseDups.length == 5

-- Negative: a failed request (412) changes nothing and delivers nothing.
#guard
  let w := run1 w3 (req "PUT" "/docs/b.txt" [("content-type", "text/plain"), ("if-match", "\"stale\"")] "x")
  w.resp.status == 412 && w.ds.isEmpty

-- A linkset change is an Update of its resource.
#guard
  let w := run1 w3 (req "PATCH" "/docs/b.txt?linkset" [("content-type", "application/json-patch+json")]
    "[{\"op\":\"add\",\"path\":\"/linkset/0/license\",\"value\":[{\"href\":\"https://example.org/l\"}]}]")
  w.resp.status == 204 && w.ds.head?.map (fun d => (acts d).map actType) == some [some "Update"]

-- A subscription to a data resource hears nothing about its siblings.
private def wData : W := run1 w1 (subReq
  "{\"type\":\"WebhookSubscription\",\"topic\":[\"http://localhost/docs/a.txt\"],\"inbox\":\"http://h.example/\"}")
#guard (run1 wData (putText "/docs/sibling.txt" "s")).ds.isEmpty
#guard ((run1 wData (putText "/docs/a.txt" "changed")).ds.map (fun d => (acts d).map objId)) ==
  [[some "http://localhost/docs/a.txt"]]

/-! ## Delivery-time authorization -/

-- A subscriber that may read the container but not a new member hears
-- nothing of that member, and does hear of a member it may read.
private def chs : List Change :=
  [ ⟨.create, "/docs/secret.txt", .dataResource⟩, ⟨.update, "/docs/visible.txt", .dataResource⟩ ]
private def bobSub : Subscription :=
  { id := "s", owner := some "bob", topics := ["/docs/"], inbox := "http://h.example/", created := 0 }
private def bobReads : Option String → MemState → String → Bool :=
  fun who _ p => who == some "bob" && p != "/docs/secret.txt"
#guard
  let (_, ds) := emit bobReads "http://localhost/" none 5000 st0 st0 chs { subs := [bobSub] }
  ds.length == 1 && ds.head?.map (fun d => (acts d).map objId) == some [some "http://localhost/docs/visible.txt"]
-- Negative: no readable resource, no delivery at all.
#guard (emit (fun _ _ _ => false) "http://localhost/" none 5000 st0 st0 chs { subs := [bobSub] }).2.isEmpty
-- An expired or deactivated subscription delivers nothing.
#guard (emit bobReads "http://localhost/" none 5000 st0 st0 chs
  { subs := [{ bobSub with expiresAt := some 4000 }] }).2.isEmpty
#guard (emit bobReads "http://localhost/" none 5000 st0 st0 chs
  { subs := [{ bobSub with active := false }] }).2.isEmpty

/-! ## Subscription management (webhook suite §Subscription Management) -/

private def wList : W := run1 w2 (req "GET" subscriptionsPath)
#guard wList.resp.status == 200
#guard (respJ wList).getString? "type" == some "Container"
#guard ((respJ wList).getArray? "items").map (·.map (·.getString? "id")) ==
  some [some "http://localhost/.well-known/lws-subscriptions/sub0"]
#guard (run1 w2 (req "GET" (subscriptionsPath ++ "sub0"))).resp.status == 200
#guard (j (run1 w2 (req "GET" (subscriptionsPath ++ "sub0"))).resp.body).field? "active" == some (.bool true)
private def wDel : W := run1 w2 (req "DELETE" (subscriptionsPath ++ "sub0"))
#guard wDel.resp.status == 204 && wDel.ns.subs.isEmpty
#guard (run1 wDel (req "GET" (subscriptionsPath ++ "sub0"))).resp.status == 404
#guard ((respJ (run1 wDel (req "GET" subscriptionsPath))).getArray? "items") == some []
-- Negative: after the DELETE, a change delivers nothing.
#guard (run1 wDel (putText "/docs/z.txt" "z")).ds.isEmpty
-- Negative: another agent sees neither the subscription nor a listing of it.
#guard (subscriptionsStep (fun _ _ => true) cfg 2000 (some "mallory")
  (req "GET" (subscriptionsPath ++ "sub0")) (subscriptionsPath ++ "sub0") w2.ns).1.status == 404
#guard (subscriptionsStep (fun _ _ => true) cfg 2000 (some "mallory")
  (req "DELETE" (subscriptionsPath ++ "sub0")) (subscriptionsPath ++ "sub0") w2.ns).2.subs.length == 1
#guard (run1 w2 (req "PUT" subscriptionsPath [("content-type", "text/plain")] "x")).resp.status == 405
#guard (run1 w2 (req "GET" (subscriptionsPath ++ "nothing"))).resp.status == 404

/-! ## Delivery outcomes: retry and deactivation -/

private def pendId (w : W) : String := (w.ds.head?.map (·.id)).getD ""
#guard
  let (ns, r) := deliveryResult none 3000 (pendId w3) 202 w3.ns
  r.isNone && ns.pending.isEmpty
#guard
  let (ns1, r1) := deliveryResult none 3000 (pendId w3) 503 w3.ns
  let (ns2, r2) := deliveryResult none 3001 (pendId w3) 503 ns1
  let (ns3, r3) := deliveryResult none 3003 (pendId w3) 503 ns2
  r1.map (·.2) == some 1 && r2.map (·.2) == some 2 && r3.isNone && ns3.pending.isEmpty &&
  ns3.subs.map (·.failures) == [1] && ns3.subs.map (·.active) == [true]
#guard
  let (ns, r) := deliveryResult none 3000 (pendId w3) 410 w3.ns
  r.isNone && ns.subs.map (·.active) == [false] && ns.revision == w3.ns.revision + 1
-- Three failed deliveries in a row deactivate the subscription.
#guard
  let ns := (List.range 3).foldl (fun ns _ =>
    let ns := { ns with pending := [{ id := "dx", subId := "sub0", inbox := "http://h.example/",
                                      body := "{}", attempt := maxAttempts }] }
    (deliveryResult none 3000 "dx" 404 ns).1) w3.ns
  ns.subs.map (·.active) == [false]
-- Negative: an unknown delivery id changes nothing.
#guard (deliveryResult none 3000 "nope" 503 w3.ns).2.isNone

/-! ## Signatures (webhook suite §Signature Requirements) -/

private def wSigned : W := run1 w2 (putText "/docs/s.txt" "signed") (signer := some stubSigner)
private def hdr (k : String) : Option String := wSigned.ds.head?.bind (·.headers.lookup k)
#guard hdr "content-digest" == wSigned.ds.head?.map (fun d => contentDigest d.body)
#guard (hdr "signature-input").map (fun v => v.startsWith
  "sig1=(\"@method\" \"@scheme\" \"@authority\" \"@path\" \"content-type\" \"content-digest\");created=") ==
  some true
#guard (hdr "signature-input").map (fun v => (v.splitOn ";keyid=\"http://localhost/.well-known/lws-storage#").length == 2) ==
  some true
-- The signature is over the RFC 9421 signature base of this request.
#guard
  match wSigned.ds.head? with
  | some d =>
      let params := signatureParams w2.st.clock stubSigner.keyId
      let b := signatureBase "http" "hook.example:8080" "/in/1/" (contentDigest d.body) params
      hdr "signature" == some ("sig1=:" ++ Base64.encode (L4Factoidal.Crypto.sha256 b.toUTF8) ++ ":")
  | none => false
-- Negative: with no signer the request carries no signature.
#guard w3.ds.head?.map (fun d => d.headers.lookup "signature") == some none

/-! ## Pieces -/

#guard parseRfc3339? "1970-01-01T00:00:00Z" == some 0
#guard parseRfc3339? "2026-03-26T10:30:00Z" >>= (fun t => some (isoDateTime t)) == some "2026-03-26T10:30:00Z"
#guard parseRfc3339? "2026-03-26T10:30:00.123+01:00" >>= (fun t => some (isoDateTime t)) == some "2026-03-26T09:30:00Z"
#guard parseRfc3339? "2024-02-29T00:00:00z" >>= (fun t => some (isoDateTime t)) == some "2024-02-29T00:00:00Z"
#guard parseRfc3339? "2023-02-29T00:00:00Z" == none
#guard parseRfc3339? "2026-13-01T00:00:00Z" == none
#guard parseRfc3339? "2026-03-26 10:30:00Z" == none
#guard parseRfc3339? "2026-03-26T10:30:00" == none
#guard parseRfc3339? "1969-12-31T23:59:59Z" == none

#guard urlParts? "https://Receiver.example:443/hooks/lws?x=1" == some ("https", "receiver.example", "/hooks/lws")
#guard urlParts? "http://127.0.0.1:8080" == some ("http", "127.0.0.1:8080", "/")
#guard urlParts? "http://h.example:80/a" == some ("http", "h.example", "/a")
#guard urlParts? "ftp://h.example/" == none
#guard urlParts? "http://user@h.example/" == none
#guard urlParts? "http://h.example/a b" == none

#guard (uuidOfDigest (L4Factoidal.Crypto.sha256 "x".toUTF8)).length == 36
#guard ((uuidOfDigest (L4Factoidal.Crypto.sha256 "x".toUTF8)).toList[14]?) == some '8'

-- classify: nothing at either time is no change; an auxiliary resource is
-- no change.
#guard classify MemStore st0 st0 "/nothing" == none
-- Two writes within one second (same modification time): the bytes decide.
#guard
  let e : Entry := { path := "/n.txt", kind := .dataResource, contentType := "text/plain",
                     body := "a".toUTF8, mtime := 7 }
  let s1 := memPut st0 e
  classify MemStore s1 (memPut s1 { e with body := "b".toUTF8 }) "/n.txt" ==
    some ⟨.update, "/n.txt", .dataResource⟩ &&
  classify MemStore s1 (memPut s1 e) "/n.txt" == none
#guard
  let acl : Entry := { path := "/.acl", kind := .metadataResource, contentType := "text/turtle",
                       body := .empty, mtime := 1 }
  classify MemStore st0 (memPut st0 acl) "/.acl" == none

/-! ## Delivery rate (issue 915; webhook suite §Security Considerations)

"Rate limiting and endpoint verification are suggested to prevent abuse of
the subscription mechanism." At most `deliveryLimit` deliveries per
subscription in a window of `deliveryWindow` seconds; the activities over
the limit wait and go in one batched envelope (core §Batching
Notifications). -/

private def cRate : Config := { cfg with deliveryLimit := 2, deliveryWindow := 60 }

/-- Subscribe, then `n` PUTs into the topic, each one engine second after
the last. -/
private def burst (c : Config) (n : Nat) : List W :=
  let w0' := run1 w1 (subReq subBody) (c := c)
  (List.range n).foldl (fun ws i =>
    let w := ws.getLast?.getD w0'
    ws ++ [run1 { w with ds := [] } (putText ("/docs/r" ++ toString i ++ ".txt") (toString i)) (c := c)])
    [w0']

private def bRate : List W := burst cRate 5
private def bOff : List W := burst { cRate with deliveryLimit := 0 } 5

-- Positive: 5 changes in one window give 2 deliveries; 3 activities wait.
#guard (bRate.flatMap (·.ds)).length == 2
#guard (bRate.getLast?.map (fun w => w.ns.held.length)) == some 3
#guard (bRate.getLast?.map (fun w => decide (w.ns.revision > w2.ns.revision))) == some true
-- The engine names when to flush: the end of the window.
#guard (bRate.getLast?.bind (fun w => nextWake w.st.clock cRate.rate w.ns)).isSome
-- Before the window ends a flush sends nothing ...
#guard (bRate.getLast?.map (fun w => (flush "http://localhost/" none w.st.clock cRate.rate w.ns).2.length)) == some 0
-- ... after it, ONE envelope with the three waiting activities, in order,
-- and nothing waits any more.
private def flushed : Option (NotifState × List Delivery) :=
  bRate.getLast?.map (fun w => flush "http://localhost/" none (w.st.clock + 60) cRate.rate w.ns)
#guard flushed.map (fun x => x.2.length) == some 1
#guard flushed.map (fun x => x.2.flatMap (fun d => (acts d).map objId)) ==
  some [some "http://localhost/docs/r2.txt", some "http://localhost/docs/r3.txt", some "http://localhost/docs/r4.txt"]
#guard flushed.map (fun x => x.1.held.isEmpty) == some true
#guard flushed.bind (fun x => nextWake 0 cRate.rate x.1) == none
-- A change in a later window carries the waiting activities first.
#guard
  match bRate.getLast? with
  | some w =>
      let w' := run1 { w with st := { w.st with clock := w.st.clock + 60 }, ds := [] }
        (putText "/docs/late.txt" "late") (c := cRate)
      w'.ds.length == 1 && w'.ns.held.isEmpty &&
      w'.ds.flatMap (fun d => (acts d).map objId) ==
        [some "http://localhost/docs/r2.txt", some "http://localhost/docs/r3.txt",
         some "http://localhost/docs/r4.txt", some "http://localhost/docs/late.txt"]
  | none => false
-- Negative: with the limit off every change is delivered at once.
#guard (bOff.flatMap (·.ds)).length == 5
#guard (bOff.getLast?.map (fun w => w.ns.held.isEmpty)) == some true
-- Negative: a cancelled subscription drops what waits for it.
#guard
  match bRate.getLast? with
  | some w => (run1 w (req "DELETE" (subscriptionsPath ++ "sub0")) (c := cRate)).ns.held.isEmpty
  | none => false
-- The default: 10 deliveries per subscription per 60 seconds.
#guard (({} : Config).rate.limit, ({} : Config).rate.window) == (10, 60)
-- `admit` itself: the third decision in one window is refused, the first of
-- the next window is admitted.
#guard
  let s : Subscription := { id := "s", owner := none, topics := ["/"], inbox := "http://h.example/", created := 0 }
  let r : Rate := ⟨2, 60⟩
  let (a1, s1) := admit r 100 s
  let (a2, s2) := admit r 101 s1
  let (a3, s3) := admit r 102 s2
  let (a4, _) := admit r 160 s3
  a1 && a2 && !a3 && a4

/-! ## An inbox that is this server under another name (issue 915)

The host resolves the inbox host name when the engine asks
(`resolveNeeded?`) and passes the addresses back (`Config.resolved`);
`InboxGuard.loops` decides. -/

#guard resolveNeeded? stubV MemStore cfg az 0 (subReq subBody) st0 == some "hook.example"
-- Negative: nothing to resolve for an unauthorized request, a resolved name,
-- an IP literal, or another request.
#guard resolveNeeded? stubV MemStore cfg {} 0 (subReq subBody) st0 == none
#guard resolveNeeded? stubV MemStore { cfg with resolved := [("hook.example", ["192.0.2.1"])] } az 0
  (subReq subBody) st0 == none
#guard resolveNeeded? stubV MemStore cfg az 0 (subReq
  "{\"type\":\"WebhookSubscription\",\"topic\":[\"http://localhost/docs/\"],\"inbox\":\"http://192.0.2.1/\"}") st0 == none
#guard resolveNeeded? stubV MemStore cfg az 0 (putText "/x.txt" "y") st0 == none

private def cListen (addrs : List String) : Config :=
  { cfg with listenAddress := some "127.0.0.1", listenPort := some 8080,
             resolved := [("hook.example", addrs)] }
-- Positive: the name resolves to the address and port this server listens on.
#guard (run1 w1 (subReq subBody) (c := cListen ["127.0.0.1"])).resp.status == 400
#guard (run1 w1 (subReq subBody) (c := cListen ["192.0.2.1", "::1"])).resp.status == 400
-- Negative: it resolves elsewhere, or not at all.
#guard (run1 w1 (subReq subBody) (c := cListen ["192.0.2.1"])).resp.status == 201
#guard (run1 w1 (subReq subBody) (c := cListen [])).resp.status == 201

/-! ## The registry check (`lws-core-16`) -/

/-- The check the conformance registry names for `lws-core-16`: a change in
a subscribed container is delivered as a Notification envelope whose
activity is a Create of the resource with the container as `target`, an
Update and a Delete follow, and a change outside the topic is not
delivered. `Harness/LwsProbe.lean` evaluates it. -/
def lwsGuardNotificationsDelivered : Bool :=
  w3.ds.head?.map (fun d => ((bodyJ d).getString? "type", (acts d).map actType,
    (acts d).map (·.getString? "target"))) ==
    some (some "Notification", [some "Create"], [some "http://localhost/docs/"]) &&
  w4.ds.head?.map (fun d => (acts d).map actType) == some [some "Update"] &&
  w5.ds.head?.map (fun d => (acts d).map actType) == some [some "Delete"] &&
  w6.ds.isEmpty

#guard lwsGuardNotificationsDelivered

end L4Factoidal.LWS.NotificationsTests
