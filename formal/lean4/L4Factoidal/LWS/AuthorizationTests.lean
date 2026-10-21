/-
L4Factoidal.LWS.AuthorizationTests — `#guard`s for the storage-server
authorization of the LWS editor's draft (section "Authorization"),
https://github.com/danbri/factoidal/issues/886.

The verifiers here are a stub: a signature verifies exactly when its
octets are `good`. Real signatures (HACL* P-256 through the wasm module)
are checked by `node tests/lws/authorization.mjs`.
-/
import L4Factoidal.LWS.Authorization

namespace L4Factoidal.LWS.AuthorizationTests

open L4Factoidal.LWS
open L4Factoidal.LWS.Authorization
open L4Factoidal.JOSE
open L4Factoidal.HTTP (Request Response)

private def stubV : Verifiers :=
  { es256 := fun _ _ sig => sig == "good".toUTF8
    rs256 := fun _ _ _ _ => false
    eddsa := fun _ _ _ => false }

private def zeros : ByteArray := ⟨Array.replicate 32 0⟩
private def key1 : KeyEntry := { kid := some "k1", key := .ec zeros zeros }

private def issuerA : String := "https://as.example"
private def alice : String := "https://id.example/alice"
private def bob : String := "https://id.example/bob"

private def cfg : Config := { baseIri := "http://localhost/" }

/-- Keys cached at clock 1000, so no refetch before 1060. -/
private def acfg : AuthzConfig :=
  { issuers := [{ issuer := issuerA, keys := [key1], fetchedAt := some 1000 }] }

private def b64 (s : String) : String := Base64Url.encodeUtf8 s

private def tok (claims : String) (kid : String := "k1") (sig : String := "good") : String :=
  b64 ("{\"alg\":\"ES256\",\"typ\":\"at+jwt\",\"kid\":\"" ++ kid ++ "\"}") ++ "." ++
  b64 claims ++ "." ++ Base64Url.encode sig.toUTF8

private def claimsWith (iss aud sub : String) (exp iat : Nat) (extra : String := "") : String :=
  "{\"iss\":\"" ++ iss ++ "\",\"sub\":\"" ++ sub ++ "\",\"aud\":\"" ++ aud ++
  "\",\"client_id\":\"https://app.example/id\",\"jti\":\"j1\",\"exp\":" ++ toString exp ++
  ",\"iat\":" ++ toString iat ++ extra ++ "}"

private def goodTok : String := tok (claimsWith issuerA "http://localhost/" alice 1300 1000)

/-! ## RFC 9728 §3.1 metadata URL -/

#guard metadataUrl "http://localhost/" == "http://localhost/.well-known/oauth-protected-resource"
#guard metadataUrl "https://storage.example/storage_1/photos/img.jpg" ==
  "https://storage.example/.well-known/oauth-protected-resource/storage_1/photos/img.jpg"
#guard resourceOfMetadataPath "http://localhost/" "/.well-known/oauth-protected-resource/a/b" ==
  "http://localhost/a/b"
#guard resourceOfMetadataPath "http://localhost/" "/.well-known/oauth-protected-resource" ==
  "http://localhost/"
#guard issuerMetadataUrl "https://as.example/" == "https://as.example/.well-known/lws-configuration"

/-! ## Token validation, one check at a time -/

#guard validateToken stubV cfg acfg 1100 goodTok == .valid alice issuerA
-- expired (exp 1300, leeway 60)
#guard validateToken stubV cfg acfg 1400 goodTok == .refused (.claims .expired)
-- within the skew allowance it is still valid
#guard validateToken stubV cfg acfg 1350 goodTok == .valid alice issuerA
-- wrong audience
#guard validateToken stubV cfg acfg 1100
    (tok (claimsWith issuerA "http://other.example/" alice 1300 1000)) ==
  .refused (.claims .audienceMismatch)
-- audience as an array that includes the storage
#guard validateToken stubV cfg acfg 1100
    (tok ("{\"iss\":\"https://as.example\",\"sub\":\"" ++ alice ++
      "\",\"aud\":[\"x\",\"http://localhost/\"],\"exp\":1300,\"iat\":1000}")) ==
  .valid alice issuerA
-- untrusted issuer
#guard validateToken stubV cfg acfg 1100
    (tok (claimsWith "https://evil.example" "http://localhost/" alice 1300 1000)) ==
  .refused (.untrustedIssuer (some "https://evil.example"))
-- bad signature, keys fetched recently: refused
#guard validateToken stubV cfg acfg 1010
    (tok (claimsWith issuerA "http://localhost/" alice 1300 1000) (sig := "evil")) ==
  .refused .badSignature
-- bad signature, refresh interval passed: fetch the keys again (rotation)
#guard validateToken stubV cfg acfg 1100
    (tok (claimsWith issuerA "http://localhost/" alice 1300 1000) (sig := "evil")) ==
  .needKeys issuerA
-- unknown kid, keys fetched recently: refused
#guard validateToken stubV cfg acfg 1010
    (tok (claimsWith issuerA "http://localhost/" alice 1300 1000) (kid := "k2")) ==
  .refused .noKey
-- refreshInterval 0 still never fetches twice in one instant
#guard validateToken stubV cfg
    { issuers := [{ issuer := issuerA, keys := [key1], fetchedAt := some 1100 }],
      refreshInterval := 0 } 1100
    (tok (claimsWith issuerA "http://localhost/" alice 1300 1000) (sig := "evil")) ==
  .refused .badSignature
#guard validateToken stubV cfg
    { issuers := [{ issuer := issuerA, keys := [key1], fetchedAt := some 1100 }],
      refreshInterval := 0 } 1101
    (tok (claimsWith issuerA "http://localhost/" alice 1300 1000) (sig := "evil")) ==
  .needKeys issuerA
-- iat in the future
#guard validateToken stubV cfg acfg 1100
    (tok (claimsWith issuerA "http://localhost/" alice 1300 1200)) ==
  .refused .issuedInFuture
-- nbf in the future
#guard validateToken stubV cfg acfg 1100
    (tok (claimsWith issuerA "http://localhost/" alice 1300 1000 ",\"nbf\":1250")) ==
  .refused (.claims .notYetValid)
-- iat absent
#guard validateToken stubV cfg acfg 1100
    (tok ("{\"iss\":\"https://as.example\",\"sub\":\"" ++ alice ++
      "\",\"aud\":\"http://localhost/\",\"exp\":1300}")) ==
  .refused .issuedAtMissing
-- not a JWS
#guard validateToken stubV cfg acfg 1100 "abc" == .refused .notJws
-- no trusted issuers: nothing is valid
#guard validateToken stubV cfg {} 1100 goodTok ==
  .refused (.untrustedIssuer (some issuerA))
-- an issuer whose keys were never fetched asks for them
#guard validateToken stubV cfg { issuers := [{ issuer := issuerA }] } 1100 goodTok ==
  .needKeys issuerA

/-! ## The request decision -/

private def aclBody : String :=
  "@prefix acl: <http://www.w3.org/ns/auth/acl#> .\n" ++
  "<http://localhost/.acl#owner> a acl:Authorization ; acl:agent <" ++ alice ++ "> ;\n" ++
  "  acl:accessTo <http://localhost/> ; acl:default <http://localhost/> ;\n" ++
  "  acl:mode acl:Read, acl:Write, acl:Control .\n"

/-- `/pub` has its own ACL resource (Web Access Control §5.1: the
effective ACL of `/pub` is then `/pub.acl`, not the root's). -/
private def pubAclBody : String :=
  "@prefix acl: <http://www.w3.org/ns/auth/acl#> .\n" ++
  "<http://localhost/pub.acl#owner> a acl:Authorization ; acl:agent <" ++ alice ++ "> ;\n" ++
  "  acl:accessTo <http://localhost/pub> ; acl:mode acl:Read, acl:Write, acl:Control .\n" ++
  "<http://localhost/pub.acl#public> a acl:Authorization ;\n" ++
  "  acl:agentClass <http://xmlns.com/foaf/0.1/Agent> ;\n" ++
  "  acl:accessTo <http://localhost/pub> ; acl:mode acl:Read .\n"

private def st : MemState :=
  { entries :=
      [ { path := "/", kind := .storageRoot, contentType := "text/turtle", body := ByteArray.empty, mtime := 1 }
      , { path := "/.acl", kind := .metadataResource, contentType := "text/turtle",
          body := textBytes aclBody, mtime := 1 }
      , { path := "/pub.acl", kind := .metadataResource, contentType := "text/turtle",
          body := textBytes pubAclBody, mtime := 1 }
      , { path := "/pub", kind := .dataResource, contentType := "text/plain", body := textBytes "hi",
          mtime := 1 } ]
    clock := 2 }

private def req (m p : String) (hs : List (String × String) := []) : Request :=
  { method := m, path := p, queryStr := "", headers := hs, body := "x" }

private def bearer (t : String) : List (String × String) := [("authorization", "Bearer " ++ t)]

private def statusOf : Decision → Nat
  | .respond r => r.status
  | .proceed _ => 0
  | .fetch _ _ => 1

private def headerOf (d : Decision) (n : String) : String :=
  match d with
  | .respond r => ((r.headers.find? (·.1 == n)).map (·.2)).getD ""
  | _ => ""

private def proceeds (d : Decision) (who : Option String) : Bool :=
  match d with
  | .proceed w => w == who
  | _ => false

-- Missing token: 401 with resource_metadata and the storage link, no error code.
#guard statusOf (decide stubV MemStore cfg acfg 1100 (req "PUT" "/private") st) == 401
#guard headerOf (decide stubV MemStore cfg acfg 1100 (req "PUT" "/private") st) "www-authenticate"
  == "Bearer resource_metadata=\"http://localhost/.well-known/oauth-protected-resource/private\""
#guard headerOf (decide stubV MemStore cfg acfg 1100 (req "PUT" "/private") st) "link"
  == "<http://localhost/>; rel=\"https://www.w3.org/ns/lws#storage\""
-- Public read granted by the ACL, no token.
#guard proceeds (decide stubV MemStore cfg acfg 1100 (req "GET" "/pub") st) none
-- Owner with a valid token may write.
#guard proceeds (decide stubV MemStore cfg acfg 1100 (req "PUT" "/private" (bearer goodTok)) st)
  (some alice)
-- Expired token: 401 invalid_token.
#guard headerOf (decide stubV MemStore cfg acfg 1400 (req "PUT" "/private" (bearer goodTok)) st)
  "www-authenticate" ==
  "Bearer resource_metadata=\"http://localhost/.well-known/oauth-protected-resource/private\", error=\"invalid_token\""
-- Another agent with a valid token: 403 insufficient_scope.
#guard statusOf (decide stubV MemStore cfg acfg 1100
  (req "PUT" "/private" (bearer (tok (claimsWith issuerA "http://localhost/" bob 1300 1000)))) st)
  == 403
-- Another agent may still read the public resource but not write it.
#guard proceeds (decide stubV MemStore cfg acfg 1100
  (req "GET" "/pub" (bearer (tok (claimsWith issuerA "http://localhost/" bob 1300 1000)))) st)
  (some bob)
#guard statusOf (decide stubV MemStore cfg acfg 1100
  (req "PUT" "/pub" (bearer (tok (claimsWith issuerA "http://localhost/" bob 1300 1000)))) st)
  == 403
-- Writing the ACL needs acl:Control; bob has none.
#guard statusOf (decide stubV MemStore cfg acfg 1100
  (req "PUT" "/.acl" (bearer (tok (claimsWith issuerA "http://localhost/" bob 1300 1000)))) st)
  == 403
-- A non-Bearer scheme: invalid_request.
#guard headerOf (decide stubV MemStore cfg acfg 1100
  (req "GET" "/pub" [("authorization", "Basic dXNlcjpwdw==")]) st) "www-authenticate" ==
  "Bearer resource_metadata=\"http://localhost/.well-known/oauth-protected-resource/pub\", error=\"invalid_request\""
-- A bad token on a public resource is still refused: a presented
-- credential that fails validation is never treated as anonymous.
#guard statusOf (decide stubV MemStore cfg acfg 1100 (req "GET" "/pub" (bearer "abc")) st) == 401
-- Keys needed: the decision names the issuer metadata URL.
#guard (match decide stubV MemStore cfg { issuers := [{ issuer := issuerA }] } 1100
    (req "GET" "/pub" (bearer goodTok)) st with
  | .fetch i u => i == issuerA && u == "https://as.example/.well-known/lws-configuration"
  | _ => false)
-- The metadata document.
#guard statusOf (decide stubV MemStore cfg acfg 1100
  (req "GET" "/.well-known/oauth-protected-resource/private") st) == 200
#guard (match decide stubV MemStore cfg acfg 1100
    (req "GET" "/.well-known/oauth-protected-resource/private") st with
  | .respond r => r.body == "{\"resource\":\"http://localhost/private\",\"authorization_servers\":[\"https://as.example\"],\"bearer_methods_supported\":[\"header\"]}"
  | _ => false)
#guard statusOf (decide stubV MemStore cfg acfg 1100
  (req "PUT" "/.well-known/oauth-protected-resource") st) == 405
-- The storage description is public.
#guard proceeds (decide stubV MemStore cfg acfg 1100 (req "GET" "/.well-known/lws-storage") st) none
-- No issuers and no opt-out: an anonymous write is refused.
#guard statusOf (decide stubV MemStore cfg {} 1100 (req "PUT" "/x") st) == 401
-- The explicit development mode proceeds as the configured agent.
#guard proceeds (decide stubV MemStore { cfg with agent := some bob } { insecureNoAuth := true }
  1100 (req "PUT" "/x") st) (some bob)

/-! ## The owner's root ACL -/

private def ownerSt : MemState :=
  { entries :=
      [ { path := "/", kind := .storageRoot, contentType := "text/turtle", body := ByteArray.empty, mtime := 1 }
      , { path := "/.acl", kind := .metadataResource, contentType := "text/turtle",
          body := textBytes ((ownerRootAcl "http://localhost/" alice).getD ""), mtime := 1 } ]
    clock := 2 }

#guard proceeds (decide stubV MemStore cfg acfg 1100 (req "PUT" "/a/b" (bearer goodTok)) ownerSt)
  (some alice)
#guard statusOf (decide stubV MemStore cfg acfg 1100 (req "GET" "/a/b") ownerSt) == 401
#guard statusOf (decide stubV MemStore cfg acfg 1100
  (req "GET" "/a/b" (bearer (tok (claimsWith issuerA "http://localhost/" bob 1300 1000)))) ownerSt)
  == 403
#guard ownerRootAcl "http://localhost/" "https://id.example/x> <y" == none

/-! ## Fetched documents -/

private def fresh : AuthzConfig := { issuers := [{ issuer := issuerA }] }

#guard (installFetched fresh issuerA "https://as.example/.well-known/lws-configuration" 200
    "{\"issuer\":\"https://as.example\",\"jwks_uri\":\"https://as.example/jwks\"}" 5).2 ==
  .next "https://as.example/jwks"
-- RFC 8414 §3.3: a metadata document naming another issuer is not used.
#guard (installFetched fresh issuerA "https://as.example/.well-known/lws-configuration" 200
    "{\"issuer\":\"https://evil.example\",\"jwks_uri\":\"https://evil.example/jwks\"}" 5).2 ==
  .refused "issuer metadata names a different issuer (RFC 8414 §3.3)"
-- A URL nobody asked for is refused.
#guard (installFetched fresh issuerA "https://as.example/jwks" 200 "{\"keys\":[]}" 5).2 ==
  .refused "this URL was not asked for"
-- An untrusted issuer is refused.
#guard (installFetched fresh "https://evil.example" "https://evil.example/x" 200 "{}" 5).2 ==
  .refused "not a trusted issuer"
-- The JWK Set after the metadata: one EC key installed (RFC 7517 §5).
#guard (let (a1, _) := installFetched fresh issuerA
          "https://as.example/.well-known/lws-configuration" 200
          "{\"issuer\":\"https://as.example\",\"jwks_uri\":\"https://as.example/jwks\"}" 5
        (installFetched a1 issuerA "https://as.example/jwks" 200
          ("{\"keys\":[{\"kty\":\"EC\",\"crv\":\"P-256\",\"kid\":\"k1\"," ++
           "\"x\":\"f83OJ3D2xF1Bg8vub9tLe1gHMzV76e8Tus9uPHvRVEU\"," ++
           "\"y\":\"x_FEzRu9m36HLN_tue659LNpXW6pCyStikYjKIWI5a0\"}," ++
           "{\"kty\":\"oct\",\"k\":\"AAAA\"}]}") 6).2) == .installed 1

end L4Factoidal.LWS.AuthorizationTests
