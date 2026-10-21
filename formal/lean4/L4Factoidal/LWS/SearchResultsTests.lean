/-
L4Factoidal.LWS.SearchResultsTests — `#guard`s for the ANTICIPATORY AND
UNSTABLE search results resource (`L4Factoidal.LWS.SearchResults`),
https://github.com/danbri/factoidal/issues/922.

Every check runs `SearchResults.serverStep` first and, when it passes,
`Search.serverStep` on the indexed reference store, which is the order of
`Wasm.Ops.Lws.lwsStepWith`. Web Access Control is on, with tokens checked by
a stub verifier (a signature verifies exactly when its octets are `good`), as
in `SearchTests`. Each behaviour has a positive and a negative check. Host
checks: `tests/lws/draft-binding.mjs` and `tests/lws/authorization.mjs`.
-/
import L4Factoidal.LWS.SearchResults

namespace L4Factoidal.LWS.SearchResultsTests

open L4Factoidal.JSON
open L4Factoidal.LWS
open L4Factoidal.LWS.Search
open L4Factoidal.HTTP (Request Response)

private def stubV : JOSE.Verifiers :=
  { es256 := fun _ _ sig => sig == "good".toUTF8
    rs256 := fun _ _ _ _ => false
    eddsa := fun _ _ _ => false }

private def B : String := "http://localhost/"
private def L (s : String) : String := "http://localhost" ++ s
private def cfg : Config :=
  { baseIri := B, typeIndex := true, moves := true, searchResults := true }
private def cfgOff : Config := { cfg with searchResults := false }

private def alice : String := "https://alice.example/#me"
private def bob : String := "https://bob.example/#me"
private def person : String := "https://schema.org/Person"
private def event : String := "https://schema.org/Event"

private def zeros : ByteArray := ⟨Array.replicate 32 0⟩
private def acfg : Authorization.AuthzConfig :=
  { issuers := [{ issuer := "https://as.example", keys := [{ kid := some "k1", key := .ec zeros zeros }],
                  fetchedAt := some 1000 }] }
private def tok (sub : String) (client : String := "") (sig : String := "good") : String :=
  JOSE.Base64Url.encodeUtf8 "{\"alg\":\"ES256\",\"typ\":\"at+jwt\",\"kid\":\"k1\"}" ++ "." ++
  JOSE.Base64Url.encodeUtf8 ("{\"iss\":\"https://as.example\",\"sub\":\"" ++ sub ++
    "\",\"aud\":\"http://localhost/.well-known/lws-storage\",\"exp\":5000,\"iat\":1000" ++
    (if client == "" then "" else ",\"client_id\":\"" ++ client ++ "\"") ++ "}") ++ "." ++
  JOSE.Base64Url.encode sig.toUTF8
private def as_ (who : String) (client : String := "app1") : List (String × String) :=
  [("authorization", "Bearer " ++ tok who client)]

private def req (m t : String) (hs : List (String × String) := []) (body : String := "") : Request :=
  { method := m, path := t, queryStr := "", headers := hs, body }

/-- 16 random bytes, as a host passes them. -/
private def rnd (k : Nat) : ByteArray := ⟨Array.replicate 16 (UInt8.ofNat k)⟩

structure W where
  st : IxState MemStore
  rs : SearchResults.ResultsState := {}
  resp : Response := ⟨200, [], "", none⟩

private def run1 (w : W) (r : Request) (rand : Option ByteArray := some (rnd 7))
    (c : Config := cfg) (now : Nat := 1100) : W :=
  match SearchResults.serverStep stubV MemStore memStoreLaws c acfg now rand r w.st w.rs with
  | .fetch _ _ => { w with resp := ⟨599, [], "", none⟩ }
  | .handled resp rs' => { w with rs := rs', resp }
  | .pass =>
      match Search.serverStep stubV MemStore memStoreLaws c acfg none now r w.st {} with
      | .inl _ => { w with resp := ⟨599, [], "", none⟩ }
      | .inr (resp, st', _, _) => { w with st := st', resp }

private def j (s : String) : Json := (parseJson? s).getD .null

private def ids (w : W) : List String :=
  ((j w.resp.body).getArray? "items").getD [] |>.filterMap (·.getString? "id")

private def stA : IxState MemStore :=
  IxState.ofMem B { entries :=
    [ { path := "/", kind := .storageRoot, contentType := "text/turtle", body := .empty, mtime := 1000 }
    , { path := "/.acl", kind := .metadataResource, contentType := "text/turtle", mtime := 1000,
        body := textBytes ((Authorization.ownerRootAcl B alice).getD "") } ], clock := 1001 }

private def bobAcl : String :=
  "@prefix acl: <http://www.w3.org/ns/auth/acl#> .\n" ++
  "<http://localhost/c/a.acl#bob> a acl:Authorization; acl:agent <" ++ bob ++ ">; acl:accessTo <http://localhost/c/a>; acl:mode acl:Read .\n" ++
  "<http://localhost/c/a.acl#alice> a acl:Authorization; acl:agent <" ++ alice ++ ">; acl:accessTo <http://localhost/c/a>;" ++
  " acl:mode acl:Read, acl:Write, acl:Control .\n"

/-- alice owns the storage; `/c/a` (Person, bob may read it) and `/c/b`
(Person and Event, only alice). -/
private def wA : W := [ req "PUT" "/c/a" ([("content-type", "text/plain"),
      ("link", "<" ++ person ++ ">; rel=\"type\""), ("prefer", "set-linkset")] ++ as_ alice) "a"
  , req "PUT" "/c/b" ([("content-type", "text/turtle")] ++ as_ alice) ("<> a <" ++ person ++ "> , <" ++ event ++ "> .")
  , req "PUT" "/c/a.acl" ([("content-type", "text/turtle")] ++ as_ alice) bobAcl ].foldl
  (fun w r => run1 w r) { st := stA }

private def queryAs (w : W) (hs : List (String × String)) (body : String)
    (rand : Option ByteArray := some (rnd 7)) (c : Config := cfg) (now : Nat := 1100) : W :=
  run1 w (req "QUERY" typeSearchPath ([("content-type", mediaLwsQuery)] ++ hs) body) rand c now

private def personQ : String := "{\"type\":[\"" ++ person ++ "\"]}"

private def cl (w : W) : Option String := w.resp.headers.lookup "content-location"

/-- The path a Content-Location names. -/
private def pathOf (w : W) : String :=
  match cl w with
  | some u => String.ofList (u.toList.drop (B.length - 1))
  | none => ""

private def getAs (w : W) (target : String) (hs : List (String × String)) (now : Nat := 1100)
    (c : Config := cfg) : W :=
  run1 w (req "GET" target hs) none c now

/-! ## Discovery: an extension member, only when on -/

private def searchEntry (c : Config) : Option Json :=
  ((j (run1 { st := stA } (req "GET" storagePath) none c).resp.body).getArray? "service").bind
    (·.find? (fun s => s.getString? "type" == some "TypeSearchService"))

#guard ((searchEntry cfg).bind (·.getString? unstableResultsMember)).isSome
#guard ((searchEntry cfg).bind (·.getString? "serviceEndpoint")) == some (L typeSearchPath)
-- Negative: off by default, so no member.
#guard ((searchEntry cfgOff).bind (·.getString? unstableResultsMember)).isNone
#guard (({ baseIri := B, typeIndex := true } : Config).searchResults) == false

/-! ## A QUERY names a results resource -/

#guard wA.resp.status == 201
private def qA : W := queryAs wA (as_ alice) personQ
#guard qA.resp.status == 200
#guard ids qA == [L "/c/a", L "/c/b"]
#guard cl qA == some (L (searchResultsPath (JOSE.Base64Url.encode (rnd 7))))
#guard isSearchResultsPath (pathOf qA)
#guard qA.rs.records.length == 1
-- Negative: off, no Content-Location and no record.
#guard cl (queryAs wA (as_ alice) personQ (c := cfgOff)) == none
#guard (queryAs wA (as_ alice) personQ (c := cfgOff)).rs.records.isEmpty
-- Negative: an anonymous QUERY is answered and names nothing.
#guard (queryAs wA [] personQ).resp.status == 200 && cl (queryAs wA [] personQ) == none
#guard (queryAs wA [] personQ).rs.records.isEmpty
-- Negative: without 16 random bytes from the host, nothing is named.
#guard cl (queryAs wA (as_ alice) personQ none) == none
#guard cl (queryAs wA (as_ alice) personQ (some ⟨Array.replicate 8 1⟩)) == none
-- Negative: a refused QUERY names nothing.
#guard (queryAs wA (as_ alice) "{\"type\":[[]]}").resp.status == 400
#guard cl (queryAs wA (as_ alice) "{\"type\":[[]]}") == none
-- Negative: a name in use is not given again.
#guard cl (queryAs qA (as_ alice) personQ) == none

/-! ## Only the creating agent and client -/

private def resA : String := pathOf qA
#guard (getAs qA resA (as_ alice)).resp.status == 200
#guard ids (getAs qA resA (as_ alice)) == [L "/c/a", L "/c/b"]
#guard (getAs qA resA (as_ alice)).resp.headers.lookup "cache-control" == some "private"
-- bob, who may read /c/a, still gets 404: the resource is alice's.
#guard (getAs qA resA (as_ bob)).resp.status == 404
#guard ((getAs qA resA (as_ bob)).resp.body.splitOn "/c/").length == 1
-- alice through another client, and an anonymous request: 404.
#guard (getAs qA resA (as_ alice "app2")).resp.status == 404
#guard (getAs qA resA []).resp.status == 404
-- A refused credential (a scheme other than Bearer): 401.
#guard (getAs qA resA [("authorization", "Basic Ym9iOmJvYg==")]).resp.status == 401
-- An unknown name: 404, the same as another agent's.
#guard (getAs qA (searchResultsPath "AAAAAAAAAAAAAAAAAAAAAA") (as_ alice)).resp.status == 404
-- Methods.
#guard (run1 qA (req "DELETE" resA (as_ alice))).resp.status == 405
#guard (run1 qA (req "HEAD" resA (as_ alice))).resp.status == 200
#guard (run1 qA (req "HEAD" resA (as_ alice))).resp.body == ""
-- Off: the path is no results resource.
#guard (getAs qA resA (as_ alice) (c := cfgOff)).resp.status != 200

/-! ## The results of that QUERY, filtered again on every access -/

-- A Person made after the QUERY is not one of its results; a new QUERY finds it.
private def wNew : W := run1 qA (req "PUT" "/c/d" ([("content-type", "text/plain"),
  ("link", "<" ++ person ++ ">; rel=\"type\""), ("prefer", "set-linkset")] ++ as_ alice) "d")
#guard wNew.resp.status == 201
#guard ids (getAs wNew resA (as_ alice)) == [L "/c/a", L "/c/b"]
#guard ids (queryAs wNew (as_ alice) personQ (rnd 8)) == [L "/c/a", L "/c/b", L "/c/d"]
-- A deleted result disappears.
private def wDel : W := run1 qA (req "DELETE" "/c/b" (as_ alice))
#guard wDel.resp.status == 204
#guard ids (getAs wDel resA (as_ alice)) == [L "/c/a"]
-- A result that no longer matches the filter disappears.
private def wRetype : W := run1 qA (req "PUT" "/c/b" ([("content-type", "text/turtle")] ++ as_ alice)
  ("<> a <" ++ event ++ "> ."))
#guard ids (getAs wRetype resA (as_ alice)) == [L "/c/a"]
-- bob's own results hold only what he may read; when his access is revoked,
-- his results resource drops it on the next GET.
private def qB : W := queryAs wA (as_ bob) personQ (rnd 9)
#guard ids qB == [L "/c/a"]
#guard ids (getAs qB (pathOf qB) (as_ bob)) == [L "/c/a"]
#guard (getAs qB (pathOf qB) (as_ alice)).resp.status == 404
private def wRev : W := run1 qB (req "DELETE" "/c/a.acl" (as_ alice))
#guard wRev.resp.status == 204
#guard (getAs wRev (pathOf qB) (as_ bob)).resp.status == 200
#guard ids (getAs wRev (pathOf qB) (as_ bob)) == []

/-! ## Expiry -/

#guard (getAs qA resA (as_ alice) (now := 1100 + 599)).resp.status == 200
#guard (getAs qA resA (as_ alice) (now := 1100 + 600)).resp.status == 410
-- Negative: after expiry another agent still gets 404, not 410.
#guard (getAs qA resA (as_ bob) (now := 1100 + 600)).resp.status == 404
-- A shorter lifetime from the configuration.
#guard (getAs (queryAs wA (as_ alice) personQ (c := { cfg with searchResultsTtl := 5 }))
  resA (as_ alice) (now := 1105)).resp.status == 410

/-! ## Pages -/

private def cfgP : Config := { cfg with pageSize := 1 }
private def qP : W := queryAs wA (as_ alice) personQ (c := cfgP)
#guard ids (getAs qP resA (as_ alice) (c := cfgP)) == [L "/c/a"]
#guard ids (getAs qP (resA ++ "?page=2") (as_ alice) (c := cfgP)) == [L "/c/b"]
#guard (getAs qP (resA ++ "?page=3") (as_ alice) (c := cfgP)).resp.status == 404
#guard (getAs qP (resA ++ "?page=x") (as_ alice) (c := cfgP)).resp.status == 404
#guard ((getAs qP resA (as_ alice) (c := cfgP)).resp.headers.lookup "link").map
  (fun l => (l.splitOn (resA ++ "?page=2")).length != 1) == some true
#guard (j (getAs qP resA (as_ alice) (c := cfgP)).resp.body).field? "totalItems" == some (.number "2")

/-! ## A bound on the number of records, oldest removed first -/

private def cfgM : Config := { cfg with searchResultsMax := 2 }
private def w3 : W := [7, 8, 9].foldl (fun w k => queryAs w (as_ alice) personQ (rnd k) cfgM) wA
#guard w3.rs.records.length == 2
#guard (getAs w3 resA (as_ alice) (c := cfgM)).resp.status == 404
#guard (getAs w3 (searchResultsPath (JOSE.Base64Url.encode (rnd 9))) (as_ alice) (c := cfgM)).resp.status == 200
-- Negative: with no room at all, nothing is named.
#guard cl (queryAs wA (as_ alice) personQ (c := { cfg with searchResultsMax := 0 })) == none

/-! ## Snapshot -/

#guard (SearchResults.stateOfJson (SearchResults.stateJson w3.rs)).toOption.map (·.records) ==
  some w3.rs.records
#guard (SearchResults.stateOfJson (SearchResults.stateJson qB.rs)).toOption.map (·.records) ==
  some qB.rs.records
-- Negative: another format, a traversal path and a name that is not base64url are refused.
#guard (SearchResults.stateOfJson (j "{\"format\":\"x\",\"records\":[]}")).toOption.isNone
#guard (SearchResults.stateOfJson (j ("{\"format\":\"" ++ SearchResults.formatName ++
  "\",\"records\":[{\"id\":\"AAAA\",\"filter\":{},\"agent\":\"a\",\"client\":null,\"created\":1," ++
  "\"expires\":2,\"paths\":[\"/../x\"]}]}"))).toOption.isNone
#guard (SearchResults.stateOfJson (j ("{\"format\":\"" ++ SearchResults.formatName ++
  "\",\"records\":[{\"id\":\"a/b\",\"filter\":{},\"agent\":\"a\",\"client\":null,\"created\":1," ++
  "\"expires\":2,\"paths\":[]}]}"))).toOption.isNone

/-! ## Named checks -/

/-- lws10-index §QUERY: a results resource is subject to the same
authorization filtering on every access. -/
def lwsGuardResultsFiltered : Bool :=
  ids (getAs qA resA (as_ alice)) == [L "/c/a", L "/c/b"] &&
  ids (getAs wDel resA (as_ alice)) == [L "/c/a"] &&
  ids (getAs wRev (pathOf qB) (as_ bob)) == []

/-- lws10-index §QUERY: a results resource is not reused across clients. -/
def lwsGuardResultsNotReused : Bool :=
  (getAs qA resA (as_ bob)).resp.status == 404 &&
  (getAs qA resA (as_ alice "app2")).resp.status == 404 &&
  (getAs qA resA []).resp.status == 404 &&
  (getAs qA resA (as_ alice)).resp.status == 200

#guard lwsGuardResultsFiltered
#guard lwsGuardResultsNotReused

end L4Factoidal.LWS.SearchResultsTests
