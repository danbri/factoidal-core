/-
L4Factoidal.LWS.Tests — one build-time check per `guarded` row of
`L4Factoidal.LWS.Conformance.registry`, plus the theorems its `proved` rows
name.

Every `#guard` is evaluated during `lake build`: a wrong answer is a build
failure. Each check is a named `def` returning `Bool`, so the registry row
can name it and `Harness/LwsProbe.lean` can print the name beside the
statement it decides.
-/
import L4Factoidal.LWS.Operations
import L4Factoidal.LWS.Patch
import L4Factoidal.LWS.Conformance
import L4Factoidal.Syntax.Turtle

namespace L4Factoidal.LWS.Tests

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.HTTP (Request Response)
open L4Factoidal.LWS
open L4Factoidal.JSON
open L4Factoidal.Syntax

/-! ## Fixtures -/

def cfg : Config := { baseIri := "http://example.org/", owner := some "http://example.org/alice/card#me" }

/-- A storage holding only its root, at clock 0. -/
def emptyStorage : MemState :=
  { entries := [{ path := "/", kind := .storageRoot, contentType := "text/turtle",
                  body := "", mtime := 0 }], clock := 1 }

def req (method target : String) (headers : List (String × String) := [])
    (body : String := "") : Request :=
  { method, path := target, queryStr := "", headers, body }

def run (r : Request) (st : MemState) : Response × MemState :=
  step MemStore cfg r st

/-- Run a list of requests in order, keeping every response. -/
def runAll : List Request → MemState → List Response × MemState
  | [], st => ([], st)
  | r :: rest, st =>
      let (resp, st') := run r st
      let (resps, st'') := runAll rest st'
      (resp :: resps, st'')

def hdr (resp : Response) (name : String) : Option String :=
  (resp.headers.find? (fun (k, _) => k == name)).map (·.2)

def turtle : List (String × String) := [("content-type", "text/turtle")]

/-! ## The clock -/

-- Day zero of the Unix epoch is a Thursday.
#guard httpDate 0 == "Thu, 01 Jan 1970 00:00:00 GMT"
#guard httpDate 1000000000 == "Sun, 09 Sep 2001 01:46:40 GMT"

/-! ## lws-core-03 — Last-Modified on GET and HEAD -/

/-- "HTTP Server MUST generate a Last-Modified header field in response to
GET and HEAD requests." -/
def lwsGuardLastModifiedOnGet : Bool :=
  let (_, st) := run (req "PUT" "/alice/card" turtle "<#me> <http://example.org/p> \"v\" .") emptyStorage
  let (resp, _) := run (req "GET" "/alice/card") st
  resp.status == 200 && (hdr resp "last-modified").isSome

def lwsGuardLastModifiedOnHead : Bool :=
  let (_, st) := run (req "PUT" "/alice/card" turtle "x") emptyStorage
  let (resp, _) := run (req "HEAD" "/alice/card") st
  resp.status == 200 && (hdr resp "last-modified").isSome && resp.body == ""

#guard lwsGuardLastModifiedOnGet
#guard lwsGuardLastModifiedOnHead

/-! ## lws-core-04 — the ?insertions blank-node refusal -/

def exP : WfIri := ⟨"http://example.org/p", by rfl⟩

/-- "The PATCH ?insertions formulae MUST NOT contain blank nodes." -/
def lwsGuardInsertionsRefuseBlankNodes : Bool :=
  let p : Patch := { insertions := [{ s := .bnode "b0", p := .iri exP, o := .var "x" }]
                   , conditions := [{ s := .var "s", p := .iri exP, o := .var "x" }] }
  match wellFormed p with
  | some e => e == PatchError.blankNodeInInsertions && e.status == 422
  | none   => false

/-- A patch whose insertions carry no blank node and whose variables are
bound by the conditions is well formed, so the guard above is not passing
because every patch is refused. -/
def lwsGuardInsertionsAcceptWithoutBlankNodes : Bool :=
  let p : Patch := { insertions := [{ s := .var "s", p := .iri exP, o := .var "x" }]
                   , conditions := [{ s := .var "s", p := .iri exP, o := .var "x" }] }
  (wellFormed p).isNone

#guard lwsGuardInsertionsRefuseBlankNodes
#guard lwsGuardInsertionsAcceptWithoutBlankNodes

-- An unbound variable in the insertions is refused with 422 too.
#guard (wellFormed { insertions := [{ s := .var "y", p := .iri exP, o := .var "y" }] }
          == some (PatchError.unboundVariable "y"))

/-! ## lws-core-05 — a container enumerates its members -/

def populated : MemState :=
  (runAll [ req "PUT" "/alice/card" turtle "a"
          , req "PUT" "/alice/notes/" turtle ""
          , req "PUT" "/alice/notes/one" turtle "b" ] emptyStorage).2

/-- "container — an LWS resource that is able to enumerate a collection of
LWS resources". Direct containment only: `/alice/notes/one` is contained by
`/alice/notes/`, not by `/alice/`. -/
def lwsGuardContainerEnumerates : Bool :=
  let alice := containedPaths MemStore populated "/alice/"
  let notes := containedPaths MemStore populated "/alice/notes/"
  alice.contains "/alice/card" && alice.contains "/alice/notes/" &&
  !alice.contains "/alice/notes/one" && notes == ["/alice/notes/one"]

#guard lwsGuardContainerEnumerates

-- PUT created the intermediate container /alice/ that no request named.
#guard (memLookup populated "/alice/").isSome

/-! ## lws-core-08 — auxiliary resources are advertised as web links -/

/-- "Auxiliary resources are discovered using web links [RFC8288] of a
specific type." -/
def lwsGuardAuxiliaryLinksAdvertised : Bool :=
  let (resp, _) := run (req "GET" "/alice/card") populated
  match hdr resp "link" with
  | none => false
  | some v =>
      (v.splitOn "rel=\"acl\"").length > 1 &&
      (v.splitOn "rel=\"describedby\"").length > 1 &&
      (v.splitOn "solid/terms#storageDescription").length > 1

#guard lwsGuardAuxiliaryLinksAdvertised

-- The storage root, and only the storage root, advertises pim:Storage.
#guard advertisesStorage (discoveryLinks "http://example.org/" none "/" .storageRoot true)
#guard !advertisesStorage (discoveryLinks "http://example.org/" none "/a" .dataResource false)

/-! ## lws-core-11 — create, read, update, delete -/

/-- "An operation is any of the following actions that can be performed on
a served resource: create resource, read resource, update resource, delete
resource." One sequence exercising all four. -/
def lwsGuardCreateReadUpdateDelete : Bool :=
  let (rs, st) := runAll
    [ req "PUT" "/alice/card" turtle "one"      -- create
    , req "GET" "/alice/card"                   -- read
    , req "PUT" "/alice/card" turtle "two"      -- update
    , req "GET" "/alice/card"                   -- read again
    , req "DELETE" "/alice/card"                -- delete
    , req "GET" "/alice/card" ] emptyStorage    -- gone
  (rs.map (·.status)) == [201, 200, 204, 200, 204, 404] &&
  (rs[1]?.map (·.body)) == some "one" &&
  (rs[3]?.map (·.body)) == some "two" &&
  (memLookup st "/alice/card").isNone

#guard lwsGuardCreateReadUpdateDelete

/-! ## lws-core-12 — created is not success -/

/-- "A success response is not defined for the create resource operation.
See instead created." A PUT that creates answers 201 with a `Location`; a
PUT that replaces answers 204 with none. -/
def lwsGuardCreatedIsNotSuccess : Bool :=
  let (created, st) := run (req "PUT" "/alice/card" turtle "one") emptyStorage
  let (replaced, _) := run (req "PUT" "/alice/card" turtle "two") st
  created.status == 201 && hdr created "location" == some "/alice/card" &&
  replaced.status == 204 && (hdr replaced "location").isNone

#guard lwsGuardCreatedIsNotSuccess

/-! ## POST assigns a name, and refuses a target with no representation -/

#guard (run (req "POST" "/alice/" turtle "x") populated).1.status == 201
#guard (run (req "POST" "/nowhere/" turtle "x") populated).1.status == 404
#guard (run (req "POST" "/alice/card" turtle "x") populated).1.status == 405

-- Two POSTs to one container get two different names, because the clock
-- advanced between them.
#guard
  let (rs, _) := runAll [ req "POST" "/alice/" turtle "x"
                        , req "POST" "/alice/" turtle "y" ] populated
  (rs[0]?.bind (fun r => hdr r "location")) !=
    (rs[1]?.bind (fun r => hdr r "location"))

/-! ## DELETE refuses the storage root, and a non-empty container -/

#guard (run (req "DELETE" "/") populated).1.status == 405
#guard (run (req "DELETE" "/alice/notes/") populated).1.status == 409
#guard
  let allow := hdr (run (req "DELETE" "/") populated).1 "allow"
  match allow with
  | some v => (v.splitOn "DELETE").length == 1
  | none   => false

/-! ## lws-core-06 — the storage root has no parent -/

/-- "The storage root is the only LWS resource that does not have a parent
in the LWS containment hierarchy". -/
theorem rootHasNoParent : parent? rootPath = none := by
  simp [parent?, rootPath]

/-! ## LWS editor's draft 2026-10-19 (w3c/lws-protocol 9a08ff65): the HTTP binding

Rows `lws-ed-NN` of the registry. Each behaviour has a positive guard and a
negative guard, so an engine that answers yes to everything fails the build. -/

def json : List (String × String) := [("content-type", "application/json")]

def hasLink (resp : Response) (frag : String) : Bool :=
  match hdr resp "link" with
  | some v => (v.splitOn frag).length > 1
  | none => false

/-- lws-ed-01, §Read Resource: "Responses MUST include an `ETag` header". -/
def lwsGuardEtagOnRead : Bool :=
  let (_, st) := run (req "PUT" "/a" turtle "x") emptyStorage
  let (g, _) := run (req "GET" "/a") st
  let (h, _) := run (req "HEAD" "/a") st
  let (c, _) := run (req "GET" "/") st
  (hdr g "etag").isSome && hdr g "etag" == hdr h "etag" && (hdr c "etag").isSome
#guard lwsGuardEtagOnRead
-- A write changes the tag.
#guard
  let (rs, _) := runAll [req "PUT" "/a" turtle "x", req "GET" "/a",
                         req "PUT" "/a" turtle "y", req "GET" "/a"] emptyStorage
  (rs[1]?.bind (hdr · "etag")) != (rs[3]?.bind (hdr · "etag"))

/-- lws-ed-02, §Update Resource: a failed `If-Match` answers 412 and does
not write; a matching one writes. -/
def lwsGuardIfMatch : Bool :=
  let (_, st) := run (req "PUT" "/a" turtle "x") emptyStorage
  let tag := (hdr (run (req "GET" "/a") st).1 "etag").getD ""
  let (bad, st1) := run (req "PUT" "/a" (("if-match", "\"nope\"") :: turtle) "y") st
  let (good, st2) := run (req "PUT" "/a" (("if-match", tag) :: turtle) "z") st
  bad.status == 412 && (memLookup st1 "/a").map (·.body) == some "x" &&
  good.status == 204 && (memLookup st2 "/a").map (·.body) == some "z"
#guard lwsGuardIfMatch
-- If-Match on an absent resource fails; If-None-Match: * on an absent one writes.
#guard (run (req "PUT" "/b" (("if-match", "*") :: turtle) "y") emptyStorage).1.status == 412
#guard (run (req "PUT" "/b" (("if-none-match", "*") :: turtle) "y") emptyStorage).1.status == 201
#guard
  let (_, st) := run (req "PUT" "/b" turtle "y") emptyStorage
  (run (req "PUT" "/b" (("if-none-match", "*") :: turtle) "z") st).1.status == 412

/-- lws-ed-03, §Read Resource: "If the resource or container listing has
not changed, respond with `304 Not Modified`". -/
def lwsGuardNotModified : Bool :=
  let (_, st) := run (req "PUT" "/a" turtle "x") emptyStorage
  let (g, _) := run (req "GET" "/a") st
  let tag := (hdr g "etag").getD ""
  let lm := (hdr g "last-modified").getD ""
  let (n1, _) := run (req "GET" "/a" [("if-none-match", tag)]) st
  let (n2, _) := run (req "GET" "/a" [("if-modified-since", lm)]) st
  let (o, _) := run (req "GET" "/a" [("if-none-match", "\"other\"")]) st
  n1.status == 304 && n1.body == "" && n2.status == 304 && o.status == 200
#guard lwsGuardNotModified

/-- lws-ed-04, §Read Resource: "Servers MUST support range requests". -/
def lwsGuardRange : Bool :=
  let (_, st) := run (req "PUT" "/t" [("content-type", "text/plain")] "abcdefghij") emptyStorage
  let (r1, _) := run (req "GET" "/t" [("range", "bytes=2-4")]) st
  let (r2, _) := run (req "GET" "/t" [("range", "bytes=-3")]) st
  let (r3, _) := run (req "GET" "/t" [("range", "bytes=7-")]) st
  r1.status == 206 && r1.body == "cde" && hdr r1 "content-range" == some "bytes 2-4/10" &&
  r2.body == "hij" && r3.body == "hij" && hdr r1 "accept-ranges" == some "bytes"
#guard lwsGuardRange
-- Unsatisfiable: 416 with `bytes */len`; a syntax this server ignores: 200.
#guard
  let (_, st) := run (req "PUT" "/t" [("content-type", "text/plain")] "abc") emptyStorage
  let (r, _) := run (req "GET" "/t" [("range", "bytes=9-")]) st
  r.status == 416 && hdr r "content-range" == some "bytes */3"
#guard
  let (_, st) := run (req "PUT" "/t" [("content-type", "text/plain")] "abc") emptyStorage
  (run (req "GET" "/t" [("range", "items=0-1")]) st).1.status == 200

/-- lws-ed-05, §Container Representation and §LWS Media Type: the
`application/lws+json` listing with `id`, `type`, `totalItems`, `items`. -/
def lwsGuardContainerListing : Bool :=
  let (resp, _) := run (req "GET" "/alice/" [("accept", "application/lws+json")]) populated
  hdr resp "content-type" == some "application/lws+json" &&
  (match parseJson resp.body with
   | .ok j =>
       j.getString? "type" == some "Container" &&
       j.getString? "id" == some "http://example.org/alice/" &&
       (match j.field? "totalItems" with | some (.number "2") => true | _ => false) &&
       (match j.getArray? "items" with
        | some items =>
            items.length == 2 &&
            items.any (fun i => i.getString? "id" == some "http://example.org/alice/card" &&
                                i.getString? "type" == some "DataResource" &&
                                i.getString? "format" == some "text/turtle") &&
            items.any (fun i => i.getString? "type" == some "Container")
        | none => false)
   | .error _ => false)
#guard lwsGuardContainerListing
-- An empty container lists `items: []`; a data resource is never listed as one.
#guard
  let (_, st) := run (req "PUT" "/e/" turtle "") emptyStorage
  let (resp, _) := run (req "GET" "/e/") st
  (resp.body.splitOn "\"items\":[]").length > 1 && (resp.body.splitOn "\"totalItems\":0").length > 1
#guard ((run (req "GET" "/alice/card") populated).1.body.splitOn "totalItems").length == 1

/-- lws-ed-06, §Content Negotiation: the Turtle LWS profile on request,
with the profile in `Content-Type` and `Vary: Accept`. -/
def lwsGuardContainerTurtle : Bool :=
  let (resp, _) := run (req "GET" "/alice/" [("accept", "text/turtle")]) populated
  hdr resp "content-type" == some "text/turtle; profile=\"https://www.w3.org/ns/lws/v1\"" &&
  hdr resp "vary" == some "accept" &&
  (resp.body.splitOn "a lws:Container").length > 1 &&
  (match parseTurtle resp.body none .rdf11 with | .ok g => g.length > 4 | .error _ => false)
#guard lwsGuardContainerTurtle
-- The two representations carry different entity tags.
#guard
  hdr (run (req "GET" "/alice/" [("accept", "text/turtle")]) populated).1 "etag" !=
  hdr (run (req "GET" "/alice/" [("accept", "application/lws+json")]) populated).1 "etag"

/-- lws-ed-07, §Containment and §Discovery: `up` on every non-root
resource, `type`, `linkset`, and `lws#storage` on every read. -/
def lwsGuardLwsLinks : Bool :=
  let (d, _) := run (req "GET" "/alice/card") populated
  let (root, _) := run (req "HEAD" "/") populated
  hasLink d "</alice/>; rel=\"up\"" &&
  hasLink d "<https://www.w3.org/ns/lws#DataResource>; rel=\"type\"" &&
  hasLink d "</alice/card?linkset>; rel=\"linkset\"; type=\"application/linkset+json\"" &&
  hasLink d "rel=\"https://www.w3.org/ns/lws#storage\"" &&
  hasLink root "<https://www.w3.org/ns/lws#Container>; rel=\"type\"" &&
  !hasLink root "rel=\"up\""
#guard lwsGuardLwsLinks

/-- lws-ed-08, §Create Resource: 201 with `Location`, `up`, `linkset`,
`type`; a `Link` with `rel="type"` to lws:Container creates a container. -/
def lwsGuardPostCreates : Bool :=
  let (resp, st) := run (req "POST" "/alice/"
    [("content-type", "text/plain"), ("link", "<https://www.w3.org/ns/lws#Container>; rel=\"type\"")]
    "") populated
  let loc := (hdr resp "location").getD ""
  resp.status == 201 && loc.endsWith "/" && hasLink resp "rel=\"up\"" &&
  hasLink resp "rel=\"linkset\"" && hasLink resp "lws#Container" &&
  ((memLookup st loc).map (·.kind.isContainer)) == some true
#guard lwsGuardPostCreates
-- A Slug that names an existing resource does not overwrite it.
#guard
  let (resp, st) := run (req "POST" "/alice/" (("slug", "card") :: turtle) "new") populated
  hdr resp "location" != some "/alice/card" &&
  (memLookup st "/alice/card").map (·.body) == some "a"
-- A Slug with a slash is not used as a path.
#guard
  let (resp, _) := run (req "POST" "/alice/" (("slug", "../x") :: turtle) "new") populated
  match hdr resp "location" with
  | some l => l.startsWith "/alice/res" | none => false

/-- lws-ed-09, §Delete Resource: `Depth: infinity` deletes a non-empty
container and everything in it; without it the answer is 409. -/
def lwsGuardRecursiveDelete : Bool :=
  let (r1, st1) := run (req "DELETE" "/alice/" [("depth", "infinity")]) populated
  r1.status == 204 && (memLookup st1 "/alice/notes/one").isNone &&
  (memLookup st1 "/alice/").isNone && (memLookup st1 "/").isSome
#guard lwsGuardRecursiveDelete
#guard (run (req "DELETE" "/alice/") populated).1.status == 409

/-- lws-ed-10, §Update Resource: "LWS server MUST minimally support JSON
Patch (`application/json-patch+json`)". -/
def lwsGuardJsonPatch : Bool :=
  let (_, st) := run (req "PUT" "/d.json" json "{\"a\":1,\"b\":[1,2]}") emptyStorage
  let patch := "[{\"op\":\"replace\",\"path\":\"/a\",\"value\":5},{\"op\":\"add\",\"path\":\"/b/-\",\"value\":3},{\"op\":\"test\",\"path\":\"/b/0\",\"value\":1}]"
  let (resp, st') := run (req "PATCH" "/d.json" [("content-type", "application/json-patch+json")] patch) st
  resp.status == 204 &&
  (memLookup st' "/d.json").map (·.body) == some "{\"a\":5,\"b\":[1,2,3]}"
#guard lwsGuardJsonPatch
-- A failing `test` leaves the resource unchanged and answers 409.
#guard
  let (_, st) := run (req "PUT" "/d.json" json "{\"a\":1}") emptyStorage
  let patch := "[{\"op\":\"remove\",\"path\":\"/a\"},{\"op\":\"test\",\"path\":\"/z\",\"value\":1}]"
  let (resp, st') := run (req "PATCH" "/d.json" [("content-type", "application/json-patch+json")] patch) st
  resp.status == 409 && (memLookup st' "/d.json").map (·.body) == some "{\"a\":1}"
-- Another patch format is 415 with `Accept-Patch`.
#guard
  let (_, st) := run (req "PUT" "/d.json" json "{}") emptyStorage
  let (resp, _) := run (req "PATCH" "/d.json" [("content-type", "text/n3")] "x") st
  resp.status == 415 && hdr resp "accept-patch" == some "application/json-patch+json"

/-- lws-ed-11, §Metadata: the linkset resource is `application/linkset+json`,
advertises GET and PATCH in `Allow`, JSON Patch in `Accept-Patch`, and goes
away with its resource. -/
def lwsGuardLinkset : Bool :=
  let (resp, _) := run (req "GET" "/alice/card?linkset") populated
  let (_, gone) := run (req "DELETE" "/alice/card") populated
  resp.status == 200 && hdr resp "content-type" == some "application/linkset+json" &&
  ((hdr resp "allow").map (fun a => decide ((a.splitOn "PATCH").length > 1))) == some true &&
  hdr resp "accept-patch" == some "application/json-patch+json" &&
  (resp.body.splitOn "\"anchor\":\"http://example.org/alice/card\"").length > 1 &&
  (resp.body.splitOn "\"up\"").length > 1 &&
  (run (req "GET" "/alice/card?linkset") gone).1.status == 404
#guard lwsGuardLinkset
-- PUT on a linkset is 405; a PATCH that changes a server-managed link is 409;
-- a PATCH that only tests is 204.
#guard (run (req "PUT" "/alice/card?linkset" [("content-type", "application/linkset+json")] "{}") populated).1.status == 405
#guard (run (req "PATCH" "/alice/card?linkset" [("content-type", "application/json-patch+json")]
          "[{\"op\":\"remove\",\"path\":\"/linkset/0/up\"}]") populated).1.status == 409
#guard (run (req "PATCH" "/alice/card?linkset" [("content-type", "application/json-patch+json")]
          "[{\"op\":\"test\",\"path\":\"/linkset/0/anchor\",\"value\":\"http://example.org/alice/card\"}]") populated).1.status == 204

/-- lws-ed-12, §Discovery: the storage description is `application/lws+cid`
with `id`, `type: Storage` and a `StorageRoot` service. -/
def lwsGuardStorageDescription : Bool :=
  let (resp, _) := run (req "GET" "/.well-known/lws-storage") populated
  hdr resp "content-type" == some "application/lws+cid" &&
  (match parseJson resp.body with
   | .ok j => j.getString? "type" == some "Storage" &&
              j.getString? "id" == some "http://example.org/.well-known/lws-storage" &&
              (resp.body.splitOn "\"serviceEndpoint\":\"http://example.org/\"").length > 1 &&
              (resp.body.splitOn "\"@context\":[\"https://www.w3.org/ns/cid/v1\",\"https://www.w3.org/ns/lws/v1\"]").length > 1
   | .error _ => false)
#guard lwsGuardStorageDescription
#guard (run (req "PUT" "/.well-known/lws-storage" turtle "x") populated).1.status == 405

/-- lws-ed-13, §Summary of HTTP Status Mappings: RFC 9457 problem details. -/
def lwsGuardProblemDetails : Bool :=
  let (resp, _) := run (req "GET" "/nothing") populated
  resp.status == 404 && hdr resp "content-type" == some "application/problem+json" &&
  (match parseJson resp.body with
   | .ok j => j.getString? "title" == some "Not Found" && j.getString? "instance" == some "/nothing"
   | .error _ => false)
#guard lwsGuardProblemDetails
#guard hdr (run (req "GET" "/alice/card") populated).1 "content-type" == some "text/turtle"

/-- lws-ed-14: a request path with a dot segment or other traversal form is
refused with 400 and touches nothing. -/
def lwsGuardTraversalRefused : Bool :=
  ["/../etc/passwd", "/a/../b", "/./a", "/a/%2e%2e/b", "/a%2fb", "a", "/a//b", "/a\\b"].all
    (fun t =>
      let (resp, st) := run (req "PUT" t turtle "x") emptyStorage
      resp.status == 400 && st.entries.length == emptyStorage.entries.length)
#guard lwsGuardTraversalRefused
#guard (run (req "PUT" "/a/b..c" turtle "x") emptyStorage).1.status == 201
#guard validTarget "/" && validTarget "/a/b/" && !validTarget "" && !validTarget "/.."

/-! ## The registry's own arithmetic -/

#guard Conformance.registry.length == 18
#guard (Conformance.registry.map (·.id)).eraseDups.length == Conformance.registry.length

end L4Factoidal.LWS.Tests
