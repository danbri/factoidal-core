/-
L4Factoidal.LWS.SearchTests — `#guard`s for the Type Index and Type Search
services (`L4Factoidal.LWS.Search`, `L4Factoidal.LWS.TypeIndex`),
https://github.com/danbri/factoidal/issues/912.

Every check runs `Search.serverStep` on the indexed reference store, the
storage writes included, so the index is the one the store maintains. The
first part runs in the development mode with no authorization; the last part
has Web Access Control with tokens checked by a stub verifier (a signature
verifies exactly when its octets are `good`), as `AuthorizationTests` does.
Each behaviour has a positive and a negative check. Host checks:
`tests/lws/draft-binding.mjs` and `tests/lws/authorization.mjs`.
-/
import L4Factoidal.LWS.Search

namespace L4Factoidal.LWS.SearchTests

open L4Factoidal.JSON
open L4Factoidal.LWS
open L4Factoidal.LWS.Search
open L4Factoidal.HTTP (Request Response)

private def stubV : JOSE.Verifiers :=
  { es256 := fun _ _ sig => sig == "good".toUTF8
    rs256 := fun _ _ _ _ => false
    eddsa := fun _ _ _ => false }

private def B : String := "http://localhost/"
private def cfg : Config := { baseIri := B, typeIndex := true, moves := true }
private def az : Authorization.AuthzConfig := { insecureNoAuth := true }

private def st0 : IxState MemStore :=
  IxState.ofMem B { entries := [{ path := "/", kind := .storageRoot, contentType := "text/turtle",
                                   body := .empty, mtime := 1000 }], clock := 1001 }

private def req (m t : String) (hs : List (String × String) := []) (body : String := "") : Request :=
  { method := m, path := t, queryStr := "", headers := hs, body }

structure W where
  st : IxState MemStore
  resp : Response

private def run1 (w : W) (r : Request) (c : Config := cfg) (a : Authorization.AuthzConfig := az) : W :=
  match Search.serverStep stubV MemStore memStoreLaws c a none 1100 r w.st {} with
  | .inl _ => { w with resp := ⟨599, [], "", none⟩ }
  | .inr (resp, st', _, _) => ⟨st', resp⟩

private def runAll (w : W) (rs : List Request) : W := rs.foldl (fun w r => run1 w r) w

private def j (s : String) : Json := (parseJson? s).getD .null

private def post (slug : String) (ct body : String) (link : String := "") : Request :=
  req "POST" "/c/" ([("content-type", ct), ("slug", slug)] ++
    (if link == "" then [] else [("link", link)])) body

private def person : String := "https://schema.org/Person"
private def event : String := "https://schema.org/Event"
private def foafPerson : String := "http://xmlns.com/foaf/0.1/Person"

/-- A container `/c/` with three data resources:
`/c/a` (text, Link type Person), `/c/b` (Turtle stating Event, no link),
`/c/p` (Turtle stating foaf:Person, Link type Person and describedby a shape). -/
private def w1 : W := runAll ⟨st0, ⟨200, [], "", none⟩⟩
  [ req "POST" "/" [("slug", "c"), ("link", "<https://www.w3.org/ns/lws#Container>; rel=\"type\"")]
  , post "a" "text/plain" "typed by its Link header" ("<" ++ person ++ ">; rel=\"type\"")
  , post "b" "text/turtle" ("<> a <" ++ event ++ "> .")
  , post "p" "text/turtle" ("<> a <" ++ foafPerson ++ "> .")
      ("<" ++ person ++ ">; rel=\"type\", <https://ex.org/shape>; rel=\"describedby\"") ]

private def query (w : W) (body : String) (hs : List (String × String) := []) : W :=
  run1 w (req "QUERY" typeSearchPath ([("content-type", mediaLwsQuery)] ++ hs) body)

private def ids (w : W) : List String :=
  ((j w.resp.body).getArray? "items").getD [] |>.filterMap (·.getString? "id")

private def found (w : W) (body : String) : List String := ids (query w body)

private def L (s : String) : String := "http://localhost" ++ s

/-! ## Discovery (lws10-index §Discovery) -/

private def service (c : Config) (ty : String) : Option String :=
  (((j (run1 ⟨st0, ⟨200, [], "", none⟩⟩ (req "GET" storagePath) c).resp.body).getArray? "service").bind
    (·.find? (fun s => s.getString? "type" == some ty))).bind (·.getString? "serviceEndpoint")

#guard service cfg "TypeIndexService" == some (L typeIndexPath)
#guard service cfg "TypeSearchService" == some (L typeSearchPath)
-- Negative: a storage that does not offer the services advertises none.
#guard service { cfg with typeIndex := false } "TypeIndexService" == none
#guard service { cfg with typeIndex := false } "TypeSearchService" == none

/-! ## Type derivation and the CNF filter (lws10-index §QUERY) -/

#guard w1.resp.status == 201
-- A Link type on create, a type from Turtle content, both at once.
#guard found w1 ("{\"type\":[\"" ++ person ++ "\"]}") == [L "/c/a", L "/c/p"]
#guard found w1 ("{\"type\":[\"" ++ event ++ "\"]}") == [L "/c/b"]
#guard found w1 ("{\"type\":[\"" ++ foafPerson ++ "\"]}") == [L "/c/p"]
-- AND across groups, OR inside a group.
#guard found w1 ("{\"type\":[\"" ++ person ++ "\",\"" ++ foafPerson ++ "\"]}") == [L "/c/p"]
#guard found w1 ("{\"type\":[[\"" ++ event ++ "\",\"" ++ foafPerson ++ "\"]]}") == [L "/c/b", L "/c/p"]
#guard found w1 ("{\"type\":[[\"" ++ event ++ "\",\"" ++ foafPerson ++ "\"],\"" ++ person ++ "\"]}") ==
  [L "/c/p"]
-- Native classes: a resource's own class only.
#guard found w1 ("{\"type\":[\"" ++ person ++ "\",\"https://www.w3.org/ns/lws#DataResource\"]}") ==
  [L "/c/a", L "/c/p"]
#guard found w1 ("{\"type\":[\"" ++ person ++ "\",\"https://www.w3.org/ns/lws#Container\"]}") == []
#guard found w1 "{\"type\":[\"https://www.w3.org/ns/lws#Container\"]}" == [L "/", L "/c/"]
-- No constraint selects every resource; an empty key is no constraint; @ members are ignored.
#guard found w1 "{}" == [L "/", L "/c/", L "/c/a", L "/c/b", L "/c/p"]
#guard found w1 ("{\"type\":[\"" ++ event ++ "\"],\"describedby\":[]}") == [L "/c/b"]
#guard found w1 ("{\"@context\":\"https://www.w3.org/ns/lws/v1\",\"@type\":\"urn:x:y\",\"type\":[\"" ++
  event ++ "\"]}") == [L "/c/b"]
-- Duplicate groups are ignored.
#guard found w1 ("{\"type\":[\"" ++ event ++ "\",\"" ++ event ++ "\",[\"" ++ event ++ "\"]]}") ==
  [L "/c/b"]
-- An indexed relation; an unindexed one, a target nothing declares, and a
-- structural relation all give the same empty answer.
#guard found w1 ("{\"type\":[\"" ++ person ++ "\"],\"describedby\":[\"https://ex.org/shape\"]}") ==
  [L "/c/p"]
#guard found w1 ("{\"type\":[\"" ++ person ++ "\"],\"describedby\":[\"urn:x:none\"]}") == []
#guard found w1 ("{\"type\":[\"" ++ person ++ "\"],\"urn:x:unindexed\":[\"urn:x:x\"]}") == []
#guard found w1 ("{\"type\":[\"" ++ person ++ "\"],\"up\":[\"" ++ L "/c/" ++ "\"]}") == []
#guard (query w1 ("{\"type\":[\"" ++ person ++ "\"],\"urn:x:unindexed\":[\"urn:x:x\"]}")).resp.body ==
  (query w1 ("{\"type\":[\"" ++ person ++ "\"],\"describedby\":[\"urn:x:none\"]}")).resp.body
-- A type nothing bears: 200 with no items, not an error.
#guard (query w1 "{\"type\":[\"urn:x:nothing\"]}").resp.status == 200
#guard found w1 "{\"type\":[\"urn:x:nothing\"]}" == []

/-! ## The response (lws10-index §QUERY, §Security and Authorization) -/

private def q1 : W := query w1 ("{\"type\":[\"" ++ person ++ "\"]}")
#guard q1.resp.status == 200
#guard q1.resp.headers.lookup "content-type" == some "application/lws+json"
#guard q1.resp.headers.lookup "cache-control" == some "private"
#guard q1.resp.headers.lookup "vary" == some "accept, authorization"
#guard q1.resp.headers.lookup "accept-query" == some "application/lws-query+json"
#guard (j q1.resp.body).getString? "type" == some "ContainerPage"
#guard (j q1.resp.body).field? "id" == none
#guard (j q1.resp.body).field? "totalItems" == some (.number "2")
-- Each item carries its id and its types: the native class name and the declared type.
#guard (((j q1.resp.body).getArray? "items").bind (·.head?)).bind (·.field? "type") ==
  some (.array [.string "DataResource", .string person])
-- A search changes nothing.
#guard q1.st.base.clock == w1.st.base.clock && q1.st.base.entries.length == w1.st.base.entries.length
-- ld+json on request, 406 when nothing acceptable, lws+json at low weight.
#guard (query w1 "{}" [("accept", "application/ld+json")]).resp.headers.lookup "content-type" ==
  some "application/ld+json"
#guard (query w1 "{}" [("accept", "image/png")]).resp.status == 406
#guard (query w1 "{}" [("accept", "image/png, application/lws+json;q=0.1")]).resp.status == 200
-- OPTIONS advertises QUERY and the format.
#guard (run1 w1 (req "OPTIONS" typeSearchPath)).resp.headers.lookup "accept-query" ==
  some "application/lws-query+json"
#guard (run1 w1 (req "OPTIONS" typeSearchPath)).resp.headers.lookup "allow" == some "OPTIONS, QUERY"

/-! ## Errors (lws10-index §Errors) -/

private def status (w : W) (r : Request) : Nat := (run1 w r).resp.status
private def qStatus (body : String) : Nat := (query w1 body).resp.status

#guard status w1 (req "QUERY" typeSearchPath [] "{\"type\":[]}") == 400
#guard status w1 (req "QUERY" typeSearchPath [("content-type", "application/x-other")] "{}") == 415
#guard (run1 w1 (req "QUERY" typeSearchPath [("content-type", "application/x-other")] "{}")).resp.headers.lookup
  "accept-query" == some "application/lws-query+json"
#guard qStatus "{\"type\": [\"urn:x:a\"" == 400
#guard qStatus "[]" == 400
#guard qStatus "{\"type\":\"urn:x:a\"}" == 400
#guard qStatus "{\"type\":[42]}" == 400
#guard qStatus "{\"type\":[[\"urn:x:a\",7]]}" == 400
#guard qStatus "{\"type\":[{\"not\":\"urn:x:a\"}]}" == 400
#guard qStatus "{\"type\":[[]]}" == 400
#guard qStatus "{\"type\":[\"Person\"]}" == 400
#guard qStatus "{\"describedby\":[\"not an iri\"]}" == 400
#guard qStatus "{\"type\":[\"urn:x:a#b#c\"]}" == 400
-- Complexity: 64 IRIs are answered, 65 are refused with 422, never narrowed.
private def many (n : Nat) : String :=
  "{\"type\":[" ++ String.intercalate "," ((List.range n).map (fun i => "\"urn:x:" ++ toString i ++ "\"")) ++ "]}"
#guard qStatus (many 64) == 200
#guard qStatus (many 65) == 422
-- Other methods.
#guard status w1 (req "POST" typeSearchPath [("content-type", mediaLwsQuery)] "{}") == 405
#guard status w1 (req "GET" typeSearchPath) == 405
#guard status w1 (req "DELETE" typeIndexPath) == 405

/-! ## Pagination (lws10-index §QUERY; the core's LWS pagination) -/

private def c2 : Config := { cfg with pageSize := 2 }
private def p1 : W := run1 w1 (req "QUERY" typeSearchPath [("content-type", mediaLwsQuery)] "{}") c2

private def linkOf (r : Response) (rel : String) : Option String :=
  match parseLinkField ((r.headers.lookup "link").getD "") with
  | .ok ls => (ls.find? (·.rel == rel)).map (·.target)
  | .error _ => none

private def localTarget (u : String) : String := String.ofList (u.toList.drop "http://localhost".length)

#guard ids p1 == [L "/", L "/c/"]
#guard (j p1.resp.body).field? "totalItems" == some (.number "5")
#guard (linkOf p1.resp "first").isSome && (linkOf p1.resp "last").isSome
#guard (linkOf p1.resp "next").isSome && (linkOf p1.resp "prev").isNone
private def p2 : W := run1 w1 (req "GET" (localTarget ((linkOf p1.resp "next").getD ""))) c2
#guard p2.resp.status == 200 && ids p2 == [L "/c/a", L "/c/b"]
#guard (linkOf p2.resp "prev").isSome && (linkOf p2.resp "next").isSome
private def p3 : W := run1 w1 (req "GET" (localTarget ((linkOf p2.resp "next").getD ""))) c2
#guard ids p3 == [L "/c/p"] && (linkOf p3.resp "next").isNone
-- An altered page reference, and a page past the last, are 404.
#guard status w1 (req "GET" (localTarget ((linkOf p1.resp "first").getD "") ++ "-unrecognized")) == 404
#guard status w1 (req "GET" (typeSearchPath ++ "?q=e30&page=4")) == 404
#guard status w1 (req "GET" (typeSearchPath ++ "?q=%%%&page=1")) == 404
-- Empty answers still name their first page.
#guard (linkOf (query w1 "{\"type\":[\"urn:x:nothing\"]}").resp "first").isSome

/-! ## The type index (lws10-index §GET [TypeIndexService]) -/

private def tix (w : W) (c : Config := cfg) : W := run1 w (req "GET" typeIndexPath) c
private def tids (w : W) : List String := ids w

#guard (tix w1).resp.status == 200
#guard (j (tix w1).resp.body).getString? "type" == some "TypeIndex"
#guard (tix w1).resp.headers.lookup "cache-control" == some "private"
#guard tids (tix w1) == [foafPerson, event, person, lwsContainerType, lwsDataResourceType]
-- Negative: a type no resource bears is not listed.
#guard !(tids (tix w1)).contains "urn:x:nothing"
-- Pages of the type index.
#guard tids (tix w1 c2) == [foafPerson, event] && (linkOf (tix w1 c2).resp "next").isSome
#guard tids (run1 w1 (req "GET" (typeIndexPath ++ "?page=3")) c2) == [lwsDataResourceType]
#guard status w1 (req "GET" (typeIndexPath ++ "?page=4")) == 404
#guard status w1 (req "GET" (typeIndexPath ++ "?bogus")) == 404

/-! ## Changes are reflected at once (lws10-index §Type and Relation Derivation) -/

-- A combined update: content and Link headers with Prefer: set-linkset.
private def wu : W := run1 w1 (req "PUT" "/c/a" [("content-type", "text/plain"), ("prefer", "set-linkset"),
  ("link", "<" ++ event ++ ">; rel=\"type\"")] "now an event")
#guard wu.resp.status == 204
#guard wu.resp.headers.lookup "preference-applied" == some "set-linkset"
#guard found wu ("{\"type\":[\"" ++ person ++ "\"]}") == [L "/c/p"]
#guard found wu ("{\"type\":[\"" ++ event ++ "\"]}") == [L "/c/a", L "/c/b"]
-- Without the preference the links stay (a PUT changes content only).
private def wn : W := run1 w1 (req "PUT" "/c/a" [("content-type", "text/plain"),
  ("link", "<" ++ event ++ ">; rel=\"type\"")] "content only")
#guard wn.resp.headers.lookup "preference-applied" == none
#guard found wn ("{\"type\":[\"" ++ person ++ "\"]}") == [L "/c/a", L "/c/p"]
-- Turtle content replaced: the content type follows.
private def wt : W := run1 w1 (req "PUT" "/c/b" [("content-type", "text/turtle")] ("<> a <" ++ person ++ "> ."))
#guard found wt ("{\"type\":[\"" ++ event ++ "\"]}") == []
#guard found wt ("{\"type\":[\"" ++ person ++ "\"]}") == [L "/c/a", L "/c/b", L "/c/p"]
-- A delete.
private def wd : W := run1 w1 (req "DELETE" "/c/b")
#guard found wd ("{\"type\":[\"" ++ event ++ "\"]}") == []
#guard !(tids (tix wd)).contains event
-- A linkset PATCH adds an indexed relation.
private def wl : W := run1 w1 (req "PATCH" "/c/a?linkset" [("content-type", "application/json-patch+json")]
  "[{\"op\":\"add\",\"path\":\"/linkset/0/describedby\",\"value\":[{\"href\":\"https://ex.org/shape\"}]}]")
#guard wl.resp.status == 204
#guard found wl ("{\"describedby\":[\"https://ex.org/shape\"]}") == [L "/c/a", L "/c/p"]
#guard found w1 ("{\"describedby\":[\"https://ex.org/shape\"]}") == [L "/c/p"]
-- A recursive delete of the container empties the index of its members.
private def wr : W := run1 w1 (req "DELETE" "/c/" [("depth", "infinity")])
#guard found wr "{}" == [L "/"]
-- A move (LWS §Moving Resources, issue 914): the resource is found at its new path only.
private def wm : W := runAll w1
  [ req "PUT" "/d/x.txt" [("content-type", "text/plain")] "x"
  , req "PATCH" "/c/a?linkset" [("content-type", "application/json-patch+json")]
      "[{\"op\":\"replace\",\"path\":\"/linkset/0/up/0/href\",\"value\":\"http://localhost/d/\"}]" ]
#guard wm.resp.status == 200
#guard found wm ("{\"type\":[\"" ++ person ++ "\"]}") == [L "/c/p", L "/d/a"]
#guard !(found wm ("{\"type\":[\"" ++ person ++ "\"]}")).contains (L "/c/a")

-- In every state above the index answer is the filter over the store.
private def filters : List Filter :=
  [ [], [(typeRel, [person])], [(typeRel, [event, foafPerson])], [("describedby", ["https://ex.org/shape"])] ]
#guard [w1, wu, wn, wt, wd, wl, wr, wm].all (fun w => filters.all (fun gs =>
  ixSearch w.st.ix gs == specSearch MemStore w.st.baseIri gs w.st.base))

/-! ## Authorization (lws10-index §Security and Authorization) -/

private def alice : String := "https://id.example/alice"
private def bob : String := "https://id.example/bob"
private def zeros : ByteArray := ⟨Array.replicate 32 0⟩
private def acfg : Authorization.AuthzConfig :=
  { issuers := [{ issuer := "https://as.example", keys := [{ kid := some "k1", key := .ec zeros zeros }],
                  fetchedAt := some 1000 }] }
private def tok (sub : String) (sig : String := "good") : String :=
  JOSE.Base64Url.encodeUtf8 "{\"alg\":\"ES256\",\"typ\":\"at+jwt\",\"kid\":\"k1\"}" ++ "." ++
  JOSE.Base64Url.encodeUtf8 ("{\"iss\":\"https://as.example\",\"sub\":\"" ++ sub ++
    "\",\"aud\":\"http://localhost/.well-known/lws-storage\",\"exp\":1300,\"iat\":1000}") ++ "." ++
  JOSE.Base64Url.encode sig.toUTF8
private def as_ (who : String) : List (String × String) := [("authorization", "Bearer " ++ tok who)]

private def stA : IxState MemStore :=
  IxState.ofMem B { entries :=
    [ { path := "/", kind := .storageRoot, contentType := "text/turtle", body := .empty, mtime := 1000 }
    , { path := "/.acl", kind := .metadataResource, contentType := "text/turtle", mtime := 1000,
        body := textBytes ((Authorization.ownerRootAcl B alice).getD "") } ], clock := 1001 }

private def runA (w : W) (r : Request) : W := run1 w r cfg acfg

private def bobAcl : String :=
  "@prefix acl: <http://www.w3.org/ns/auth/acl#> .\n" ++
  "<http://localhost/c/a.acl#bob> a acl:Authorization; acl:agent <" ++ bob ++ ">; acl:accessTo <http://localhost/c/a>; acl:mode acl:Read .\n" ++
  "<http://localhost/c/a.acl#alice> a acl:Authorization; acl:agent <" ++ alice ++ ">; acl:accessTo <http://localhost/c/a>;" ++
  " acl:mode acl:Read, acl:Write, acl:Control .\n"

private def wA : W := [ req "PUT" "/c/a" ([("content-type", "text/plain"),
      ("link", "<" ++ person ++ ">; rel=\"type\""), ("prefer", "set-linkset")] ++ as_ alice) "a"
  , req "PUT" "/c/b" ([("content-type", "text/turtle")] ++ as_ alice) ("<> a <" ++ person ++ "> , <" ++ event ++ "> .")
  , req "PUT" "/c/a.acl" ([("content-type", "text/turtle")] ++ as_ alice) bobAcl ].foldl runA
  ⟨stA, ⟨200, [], "", none⟩⟩

private def queryAs (w : W) (hs : List (String × String)) (body : String) : W :=
  runA w (req "QUERY" typeSearchPath ([("content-type", mediaLwsQuery)] ++ hs) body)

#guard wA.resp.status == 201
-- alice may read both, bob one; the count is over bob's view.
#guard ids (queryAs wA (as_ alice) ("{\"type\":[\"" ++ person ++ "\"]}")) == [L "/c/a", L "/c/b"]
#guard ids (queryAs wA (as_ bob) ("{\"type\":[\"" ++ person ++ "\"]}")) == [L "/c/a"]
#guard (j (queryAs wA (as_ bob) ("{\"type\":[\"" ++ person ++ "\"]}")).resp.body).field? "totalItems" ==
  some (.number "1")
-- A type borne only by what bob may not read is not in his type index, nor found.
#guard ids (queryAs wA (as_ bob) ("{\"type\":[\"" ++ event ++ "\"]}")) == []
#guard ids (runA wA (req "GET" typeIndexPath (as_ bob))) == [person, lwsDataResourceType]
#guard (ids (runA wA (req "GET" typeIndexPath (as_ alice)))).contains event
-- The ACL resource itself is never an item.
#guard !(ids (queryAs wA (as_ alice) "{}")).contains (L "/c/a.acl")
-- Anonymous: answered, with what the public may read (nothing here).
#guard (queryAs wA [] "{}").resp.status == 200 && ids (queryAs wA [] "{}") == []
-- A refused credential is 401, not an empty answer.
#guard (queryAs wA [("authorization", "Basic Ym9iOmJvYg==")] "{}").resp.status == 401
-- Revoking bob's access takes effect on the next request.
private def wRev : W := runA wA (req "DELETE" "/c/a.acl" (as_ alice))
#guard wRev.resp.status == 204
#guard ids (queryAs wRev (as_ bob) ("{\"type\":[\"" ++ person ++ "\"]}")) == []
#guard ids (runA wRev (req "GET" typeIndexPath (as_ bob))) == []

/-! ## Named checks (the conformance registry rows `lws-index-NN`) -/

/-- §Discovery: both services advertised with an endpoint; none when off. -/
def lwsGuardIndexDiscovery : Bool :=
  service cfg "TypeIndexService" == some (L typeIndexPath) &&
  service cfg "TypeSearchService" == some (L typeSearchPath) &&
  service { cfg with typeIndex := false } "TypeSearchService" == none

/-- §QUERY: the CNF filter over types and an indexed relation, the native
classes, and the ContainerPage. -/
def lwsGuardTypeSearch : Bool :=
  found w1 ("{\"type\":[[\"" ++ event ++ "\",\"" ++ foafPerson ++ "\"],\"" ++ person ++ "\"]}") == [L "/c/p"] &&
  found w1 ("{\"type\":[\"" ++ person ++ "\"],\"describedby\":[\"https://ex.org/shape\"]}") == [L "/c/p"] &&
  found w1 ("{\"type\":[\"" ++ person ++ "\",\"https://www.w3.org/ns/lws#Container\"]}") == [] &&
  (j q1.resp.body).getString? "type" == some "ContainerPage"

/-- §Errors: 400, 415, 406, 422. -/
def lwsGuardSearchErrors : Bool :=
  status w1 (req "QUERY" typeSearchPath [] "{}") == 400 &&
  status w1 (req "QUERY" typeSearchPath [("content-type", "application/x-other")] "{}") == 415 &&
  (query w1 "{}" [("accept", "image/png")]).resp.status == 406 &&
  qStatus "{\"type\":[[]]}" == 400 && qStatus (many 65) == 422

/-- §Security and Authorization: results, counts and the type index are
filtered by the agent's current read access. -/
def lwsGuardSearchAuthorized : Bool :=
  ids (queryAs wA (as_ bob) ("{\"type\":[\"" ++ person ++ "\"]}")) == [L "/c/a"] &&
  ids (runA wA (req "GET" typeIndexPath (as_ bob))) == [person, lwsDataResourceType] &&
  ids (queryAs wRev (as_ bob) ("{\"type\":[\"" ++ person ++ "\"]}")) == [] &&
  q1.resp.headers.lookup "cache-control" == some "private"

#guard lwsGuardIndexDiscovery
#guard lwsGuardTypeSearch
#guard lwsGuardSearchErrors
#guard lwsGuardSearchAuthorized

end L4Factoidal.LWS.SearchTests
