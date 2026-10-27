/-
L4Factoidal.Authz.Tests — `#guard`s for the authorization server component
(https://github.com/danbri/factoidal/issues/916), positive and negative.

The primitives are a STUB (`stub`): a "signature" is SHA-256 of the private
key and the message, and a "public key" is the private key written twice,
so a token verifies exactly when it was signed with the matching stub key.
An extern cannot run in the interpreter. Real ES256 and Ed25519 (HACL\*
through the wasm module) are checked by `node tests/authz/server.mjs`, and
the three P-256 externs by `lake exe l4crypto-probe`.

The controlled identifier documents below follow the shapes of Touchstone's
identities (`definitions/lws10/identities.yamlld`: `#cid`,
`#cid-document-id-mismatch`, `#cid-key-not-for-authentication`,
`#cid-key-revoked`, `#cid-foreign-controller`, `#cid-referenced-method`,
`#oidc`), written here from the CID 1.0 and lws10-authn-* rules, not copied.
-/
import L4Factoidal.Authz.Server

namespace L4Factoidal.Authz.Tests

open L4Factoidal.JSON
open L4Factoidal.JOSE
open L4Factoidal.Authz
open L4Factoidal.HTTP (Request Response)

/-! ## The stub primitives -/

def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

def stubSig (sk msg : ByteArray) : ByteArray :=
  L4Factoidal.Crypto.sha256 (sk ++ msg) ++ L4Factoidal.Crypto.sha256 (msg ++ sk)

def stub : Crypto :=
  { verifiers :=
      { es256 := fun pub msg sig => pub.size == 64 && sig == stubSig (pub.extract 0 32) msg
        rs256 := fun _ _ _ _ => false
        eddsa := fun pk msg sig => sig == stubSig pk msg }
    es256Sign := fun sk msg nonce =>
      if sk.size == 32 && nonce.size == 32 && nonce != zeros 32 then some (stubSig sk msg) else none
    es256Public := fun sk => if sk.size == 32 && sk != zeros 32 then some (sk ++ sk) else none
    eddsaSign := fun sk msg => stubSig sk msg
    eddsaPublic := fun sk => if sk.size == 32 then some sk else none
    p256Decompress := fun pk =>
      if pk.size == 33 && (pk.get! 0 == 2 || pk.get! 0 == 3) then
        some (pk.extract 1 33 ++ pk.extract 1 33) else none }

def bytesOf (n : Nat) (b : UInt8) : ByteArray := ⟨Array.replicate n b⟩

/-- 112 "random" bytes: nonces 0..64, key 64..96, jti 96..112. -/
def rnd : ByteArray := bytesOf 112 7

/-! ## Fixtures -/

def asIssuer : String := "https://as.example"
def storage : String := "https://storage.example/.well-known/lws-storage"
def now : Nat := 1761313600

def asKey : ByteArray := bytesOf 32 1
def cfg : AuthzConfig :=
  { issuer := asIssuer, resources := [storage, "https://storage.example/"] }
def keys0 : KeyStore := { keys := [(mkKey stub .es256 asKey now).get!] }
def st0 : AuthzState := { keys := keys0 }

/-- Sign a JWT with the stub. -/
def jwt (header claims : Json) (sk : ByteArray) : String :=
  let h := Base64Url.encode (toStringCompact header).toUTF8
  let p := Base64Url.encode (toStringCompact claims).toUTF8
  h ++ "." ++ p ++ "." ++ Base64Url.encode (stubSig sk (h ++ "." ++ p).toUTF8)

def num (n : Nat) : Json := .number (toString n)

/-- A did:key with a P-256 key: the stub's "compressed point" is 0x02 then
the 32-byte private key. -/
def subjKey : ByteArray := bytesOf 32 5
def didMb : String :=
  "z" ++ L4Factoidal.VC.Multibase.base58Encode ([0x80, 0x24, 2] ++ subjKey.data.toList)
def did : String := "did:key:" ++ didMb

def selfClaims (sub : String) (extra : List (String × Json) := []) (drop : List String := []) : Json :=
  .object ((([ ("sub", .string sub), ("iss", .string sub), ("client_id", .string sub)
             , ("aud", .array [.string asIssuer]), ("iat", num now), ("exp", num (now + 300)) ]
           ).filter (fun kv => !drop.contains kv.1)).map (fun kv =>
             match extra.lookup kv.1 with | some v => (kv.1, v) | none => kv) ++
           extra.filter (fun kv => !["sub", "iss", "client_id", "aud", "iat", "exp"].contains kv.1))

def es256Header (kid : String) : Json :=
  .object [("alg", .string "ES256"), ("typ", .string "JWT"), ("kid", .string kid)]

def didToken : String := jwt (es256Header didMb) (selfClaims did) subjKey

def form (ps : List (String × String)) : String :=
  "&".intercalate (ps.map fun (k, v) => k ++ "=" ++ v)

def baseForm (tok : String) (ty : String := tokenTypeJwt) : List (String × String) :=
  [ ("grant_type", tokenExchangeGrant), ("resource", storage)
  , ("subject_token", tok), ("subject_token_type", ty) ]

def tokenReq (body : String) : Request :=
  { method := "POST", path := "/token", queryStr := "",
    headers := [("content-type", "application/x-www-form-urlencoded")], body }

def ctx0 : Ctx := cfg.ctx stub st0 now

/-- The error code of an answer. -/
def errorOf (o : TokenOutcome) : Option String :=
  match o with
  | .refused r => (parseJson? r.body).bind (·.getString? "error")
  | _ => none

def _root_.L4Factoidal.Authz.TokenOutcome.isIssued : TokenOutcome → Bool
  | .issued .. => true
  | _ => false

def issued? (o : TokenOutcome) : Option String :=
  match o with
  | .issued _ t _ _ _ => some t
  | _ => none

def run (ps : List (String × String)) (st : AuthzState := st0) (c : AuthzConfig := cfg) :
    TokenOutcome :=
  tokenOutcome stub c st now rnd ps

/-! ## Metadata (lws10-core "Authorization Server Metadata") -/

#guard (metadataJson cfg).getString? "issuer" == some asIssuer
#guard (metadataJson cfg).getString? "token_endpoint" == some "https://as.example/token"
#guard (metadataJson cfg).getString? "jwks_uri" == some "https://as.example/jwks"
#guard (metadataJson cfg).getArray? "grant_types_supported" == some [.string tokenExchangeGrant]
#guard (metadataJson cfg).getArray? "subject_identifier_types_supported" ==
  some [.string "https", .string "did:key"]
-- SAML is not advertised: no XML Signature verifier (issue 926).
#guard !((metadataJson cfg).getArray? "subject_token_types_supported").get!.contains (.string tokenTypeSaml2)
#guard issuerPath "https://as.example" == ""
#guard issuerPath "https://as.example/tenant/" == "/tenant"
#guard lwsConfigurationPath "https://as.example/tenant" == "/.well-known/lws-configuration/tenant"
#guard tokenPath "https://as.example/tenant" == "/tenant/token"

/-! ## Endpoint paths: configurable, two forms (whole and issuer-relative) -/

-- An issuer that shares its path with a storage, its endpoints under the
-- storage's `.well-known/`, as `lws-serve --authz` sets it.
def cfgMounted : AuthzConfig :=
  { cfg with issuer := "https://h.example/targets/f"
             tokenPath := "/.well-known/lws-token", jwksPath := "/.well-known/lws-jwks" }
#guard (metadataJson cfgMounted).getString? "token_endpoint" ==
  some "https://h.example/targets/f/.well-known/lws-token"
#guard (metadataJson cfgMounted).getString? "jwks_uri" ==
  some "https://h.example/targets/f/.well-known/lws-jwks"
-- whole form
#guard endpointOf? cfgMounted "/.well-known/lws-configuration/targets/f" == some .metadata
#guard endpointOf? cfgMounted "/.well-known/oauth-authorization-server/targets/f" == some .metadata
#guard endpointOf? cfgMounted "/targets/f/.well-known/lws-token" == some .token
#guard endpointOf? cfgMounted "/targets/f/.well-known/lws-jwks" == some .jwks
-- issuer form (a proxy removed /targets/f)
#guard endpointOf? cfgMounted "/.well-known/lws-configuration" == some .metadata
#guard endpointOf? cfgMounted "/.well-known/lws-token" == some .token
#guard endpointOf? cfgMounted "/.well-known/lws-jwks" == some .jwks
-- storage paths are not this server's
#guard endpointOf? cfgMounted "/token" == none
#guard endpointOf? cfgMounted "/.well-known/lws-storage" == none
#guard endpointOf? cfgMounted "/.well-known/oauth-protected-resource/x" == none
#guard !owns cfgMounted "/notes/a.txt"
#guard owns cfgMounted "/.well-known/lws-token?x=1"
-- the default paths are unchanged
#guard endpointOf? cfg "/token" == some .token
#guard endpointOf? cfg "/jwks" == some .jwks
#guard endpointOf? cfg "/.well-known/lws-configuration" == some .metadata

/-! ## Keys and the JWK Set -/

#guard keys0.current?.isSome
#guard (keys0.current?.map (·.kid)) == some (thumbprint (keys0.current?.get!.jwk))
-- The published set holds no private member.
#guard ((jwksText keys0 now 360).splitOn "\"d\"").length == 1
#guard (publishedKeys cfg keys0 now).length == 1
-- A key the primitive refuses is not made.
#guard (mkKey stub .es256 (zeros 32) now).isNone
-- The key file reads back to the same kids.
#guard (match keyStoreOfDoc stub (keysDoc keys0) with
        | .ok s => s.keys.map (·.kid) == keys0.keys.map (·.kid)
        | .error _ => false)
-- A changed kid in the file is refused.
#guard (match keyStoreOfDoc stub (.object [("format", .string keysFormat),
          ("keys", .array [.object [("kid", .string "x"), ("alg", .string "ES256"),
            ("d", .string (Base64Url.encode asKey)), ("created", num now)]])]) with
        | .ok _ => false
        | .error _ => true)

/-! ## Rotation -/

def k2 : KeyRec := (mkKey stub .es256 (bytesOf 32 2) (now + 10)).get!
def keys1 : KeyStore := rotateWith keys0 k2 (now + 10) 360

#guard keys1.current?.map (·.kid) == some k2.kid
-- The old key stays published within the grace period, then goes.
#guard (published keys1 (now + 100) 360).length == 2
#guard (published keys1 (now + 10 + 360) 360).length == 1
#guard needsRotation keys0 (now + 5) 0 == false
#guard needsRotation keys0 (now + 5) 5 == true
#guard needsRotation {} now 0 == true

/-! ## Token exchange: the request (lws10-core "Token Exchange", "Request") -/

#guard errorOf (run [("resource", storage), ("subject_token", didToken),
  ("subject_token_type", tokenTypeJwt)]) == some "invalid_request"
#guard errorOf (run [("grant_type", "client_credentials"), ("resource", storage),
  ("subject_token", didToken), ("subject_token_type", tokenTypeJwt)]) == some "unsupported_grant_type"
#guard errorOf (run [("grant_type", tokenExchangeGrant), ("subject_token", didToken),
  ("subject_token_type", tokenTypeJwt)]) == some "invalid_request"
#guard errorOf (run [("grant_type", tokenExchangeGrant), ("resource", storage),
  ("subject_token_type", tokenTypeJwt)]) == some "invalid_request"
#guard errorOf (run [("grant_type", tokenExchangeGrant), ("resource", storage),
  ("subject_token", didToken)]) == some "invalid_request"
#guard errorOf (run (baseForm didToken ++ [("resource", storage)])) == some "invalid_request"
#guard errorOf (run [("grant_type", tokenExchangeGrant), ("resource", "https://unknown-storage.invalid/"),
  ("subject_token", didToken), ("subject_token_type", tokenTypeJwt)]) == some "invalid_target"
#guard errorOf (run (baseForm didToken ++ [("audience", "https://other.example/")])) == some "invalid_target"
#guard errorOf (run (baseForm didToken ++ [("actor_token", "x")])) == some "invalid_request"
#guard errorOf (run (baseForm didToken ++ [("requested_token_type", "urn:x")])) == some "invalid_request"
#guard errorOf (run (baseForm didToken "urn:ietf:params:oauth:token-type:refresh_token")) == some "invalid_request"

/-! ## did:key subject (lws10-authn-ssi-cid, DID subjects) -/

#guard (run (baseForm didToken)).isIssued
-- The issued token: header, claims, and the published key verifies it.
#guard (match issued? (run (baseForm didToken)) with
        | some t =>
            let c := (claimsOf? t).getD .null
            c.getString? "iss" == some asIssuer && c.getString? "sub" == some did &&
            c.getString? "client_id" == some did &&
            c.field? "aud" == some (.array [.string storage]) &&
            numClaim? c "exp" == some ((now : Int) + 300) && (c.getString? "jti").isSome &&
            headerKid? t == keys0.current?.map (·.kid) &&
            verifiesPublished stub cfg keys0 now t
        | none => false)
#guard (match parseJwt ((issued? (run (baseForm didToken))).get!) with
        | .ok p => p.header.getString? "typ" == some "at+jwt" && p.alg == .es256
        | .error _ => false)
-- The full kid form `did#mb` is accepted too.
#guard (run (baseForm (jwt (es256Header (did ++ "#" ++ didMb)) (selfClaims did) subjKey))).isIssued
-- Negative cases: each refused with invalid_request and no token.
#guard errorOf (run (baseForm (jwt (es256Header didMb) (selfClaims did) (bytesOf 32 6)))) == some "invalid_request"
#guard errorOf (run (baseForm (jwt (.object [("alg", .string "none"), ("kid", .string didMb)]) (selfClaims did) subjKey))) == some "invalid_request"
#guard errorOf (run (baseForm (jwt (es256Header didMb)
  (selfClaims did [("iat", num (now - 3900)), ("exp", num (now - 3600))]) subjKey))) == some "invalid_request"
#guard errorOf (run (baseForm (jwt (es256Header didMb) (selfClaims did [] ["exp"]) subjKey))) == some "invalid_request"
#guard errorOf (run (baseForm (jwt (es256Header didMb) (selfClaims did [] ["iat"]) subjKey))) == some "invalid_request"
#guard errorOf (run (baseForm (jwt (es256Header didMb)
  (selfClaims did [("iat", num (now + 3600)), ("exp", num (now + 3900))]) subjKey))) == some "invalid_request"
#guard errorOf (run (baseForm (jwt (es256Header didMb)
  (selfClaims did [("client_id", .string "https://other-client.invalid/")]) subjKey))) == some "invalid_request"
#guard errorOf (run (baseForm (jwt (es256Header didMb)
  (selfClaims did [("aud", .array [.string "https://not-the-authorization-server.invalid/"])]) subjKey))) == some "invalid_request"
#guard errorOf (run (baseForm (jwt (es256Header "zOther") (selfClaims did) subjKey))) == some "invalid_request"
#guard errorOf (run (baseForm (jwt (es256Header didMb) (selfClaims did [] ["sub"]) subjKey))) == some "invalid_request"
#guard errorOf (run (baseForm "not.a.jwt")) == some "invalid_request"
-- SAML 2.0: refused, the stated gap of issue 926.
#guard (match validateSubject ctx0 tokenTypeSaml2 "PHNhbWw+" with
        | .refused w => (w.splitOn "issues/926").length == 2
        | _ => false)
#guard errorOf (run (baseForm "PHNhbWw+" tokenTypeSaml2)) == some "invalid_request"

/-! ## CID subject with an HTTPS identifier -/

def alice : String := "https://id.example/alice"
def aliceKey : ByteArray := bytesOf 32 9
def aliceJwk : Json :=
  .object [ ("kty", .string "EC"), ("crv", .string "P-256")
          , ("x", .string (Base64Url.encode aliceKey)), ("y", .string (Base64Url.encode aliceKey)) ]
def method (ctrl : String := alice) (extra : List (String × Json) := []) : Json :=
  .object ([ ("id", .string (alice ++ "#k1")), ("type", .string "JsonWebKey")
           , ("controller", .string ctrl), ("publicKeyJwk", aliceJwk) ] ++ extra)
def cidDoc (fields : List (String × Json)) : String := toStringCompact (.object fields)

def withDoc (url body : String) (st : AuthzState := st0) : AuthzState :=
  recordFetched cfg st url 200 body now

def aliceToken (kid : String := "k1") (sk : ByteArray := aliceKey) : String :=
  jwt (es256Header kid) (selfClaims alice) sk

def docOk : String := cidDoc [("id", .string alice), ("authentication", .array [method])]

#guard (run (baseForm (aliceToken)) (withDoc alice docOk)).isIssued
#guard (match issued? (run (baseForm aliceToken) (withDoc alice docOk)) with
        | some t => ((claimsOf? t).bind (·.getString? "sub")) == some alice
        | none => false)
-- A referenced method (CID 1.0 §3.3, the reference form).
#guard (run (baseForm aliceToken) (withDoc alice (cidDoc
  [("id", .string alice), ("verificationMethod", .array [method]),
   ("authentication", .array [.string "#k1"])]))).isIssued
-- Negative: the document names another id.
#guard errorOf (run (baseForm aliceToken) (withDoc alice (cidDoc
  [("id", .string "https://id.example/someone-else"), ("authentication", .array [method])]))) == some "invalid_request"
-- Negative: the key is for assertion only.
#guard errorOf (run (baseForm aliceToken) (withDoc alice (cidDoc
  [("id", .string alice), ("verificationMethod", .array [method]),
   ("assertionMethod", .array [.string (alice ++ "#k1")])]))) == some "invalid_request"
-- Negative: revoked.
#guard errorOf (run (baseForm aliceToken) (withDoc alice (cidDoc
  [("id", .string alice), ("authentication", .array [method alice [("revoked", .string "2000-01-01T00:00:00Z")]])]))) == some "invalid_request"
-- A future expiry is still in force.
#guard (run (baseForm aliceToken) (withDoc alice (cidDoc
  [("id", .string alice), ("authentication", .array [method alice [("expires", .string "2100-01-01T00:00:00Z")]])]))).isIssued
-- Negative: another controller.
#guard errorOf (run (baseForm aliceToken) (withDoc alice (cidDoc
  [("id", .string alice), ("authentication", .array [method "https://id.example/someone-else"])]))) == some "invalid_request"
-- Negative: unknown kid, bad signature, missing kid.
#guard errorOf (run (baseForm (aliceToken "nope")) (withDoc alice docOk)) == some "invalid_request"
#guard errorOf (run (baseForm (aliceToken "k1" (bytesOf 32 3))) (withDoc alice docOk)) == some "invalid_request"
#guard errorOf (run (baseForm (jwt (.object [("alg", .string "ES256")]) (selfClaims alice) aliceKey)) (withDoc alice docOk)) == some "invalid_request"
-- A failed fetch is a refusal.
#guard errorOf (run (baseForm aliceToken) (recordFetched cfg st0 alice 404 "" now)) == some "invalid_request"

/-! ## Fetches and the private-address guard -/

-- No document yet: the host must resolve the name first.
#guard (match run (baseForm aliceToken) with
        | .need (.resolve h) => h == "id.example"
        | _ => false)
-- Resolved to a public address: fetch it from that address.
#guard (match run (baseForm aliceToken) (recordResolved cfg st0 "id.example" ["93.184.216.34"] now) with
        | .need (.fetch u _ a) => u == alice && a == "93.184.216.34"
        | _ => false)
-- Resolved to a private or loopback address: refused.
#guard errorOf (run (baseForm aliceToken) (recordResolved cfg st0 "id.example" ["10.1.2.3"] now)) == some "invalid_request"
#guard errorOf (run (baseForm aliceToken) (recordResolved cfg st0 "id.example" ["93.184.216.34", "::1"] now)) == some "invalid_request"
#guard errorOf (run (baseForm aliceToken) (recordResolved cfg st0 "id.example" ["fe80::1"] now)) == some "invalid_request"
#guard errorOf (run (baseForm aliceToken) (recordResolved cfg st0 "id.example" ["fd00::1"] now)) == some "invalid_request"
#guard errorOf (run (baseForm aliceToken) (recordResolved cfg st0 "id.example" ["169.254.169.254"] now)) == some "invalid_request"
#guard errorOf (run (baseForm aliceToken) (recordResolved cfg st0 "id.example" [] now)) == some "invalid_request"
-- With --allow-private-fetch the same address is used.
#guard (match run (baseForm aliceToken) (recordResolved cfg st0 "id.example" ["10.1.2.3"] now)
          { cfg with fetch := { allowPrivateFetch := true } } with
        | .need (.fetch _ _ a) => a == "10.1.2.3"
        | _ => false)
#guard privateAddr (.v4 [172, 16, 0, 1]) && privateAddr (.v4 [192, 168, 1, 1]) &&
  privateAddr (.v4 [127, 0, 0, 2]) && privateAddr (.v4 [0, 0, 0, 0]) && !privateAddr (.v4 [172, 32, 0, 1]) &&
  !privateAddr (.v4 [8, 8, 8, 8]) && privateAddr (.v6 [0xfc00, 0, 0, 0, 0, 0, 0, 1]) &&
  !privateAddr (.v6 [0x2001, 0xdb8, 0, 0, 0, 0, 0, 1])
-- http subjects: refused unless --allow-http; a localhost name is loopback.
def httpAlice : String := "http://localhost:8080/agents/alice"
#guard errorOf (run (baseForm (jwt (es256Header "k1") (selfClaims httpAlice) aliceKey))) == some "invalid_request"
#guard errorOf (run (baseForm (jwt (es256Header "k1") (selfClaims httpAlice) aliceKey)) st0
  { cfg with fetch := { allowHttp := true } }) == some "invalid_request"
#guard (match run (baseForm (jwt (es256Header "k1") (selfClaims httpAlice) aliceKey)) st0
          { cfg with fetch := { allowHttp := true, allowPrivateFetch := true } } with
        | .need (.fetch u _ a) => u == httpAlice && a == "127.0.0.1"
        | _ => false)

/-! ## OpenID Connect ID token (lws10-authn-openid) -/

def op : String := "https://op.example"
def opKey : ByteArray := bytesOf 32 11
def opJwks : String := toStringCompact (.object [("keys", .array [.object
  [ ("kty", .string "EC"), ("crv", .string "P-256"), ("kid", .string "op1")
  , ("x", .string (Base64Url.encode opKey)), ("y", .string (Base64Url.encode opKey)) ]])])
def bob : String := "https://id.example/bob"
def bobDoc (provider : String := op) : String := cidDoc [("id", .string bob), ("service", .array [.object
  [("type", .string lwsOpenIdProvider), ("serviceEndpoint", .string provider)]])]
def disc (iss : String := op) : String := toStringCompact (.object
  [("issuer", .string iss), ("jwks_uri", .string (op ++ "/jwks"))])
def oidcSt (doc : String := bobDoc) (d : String := disc) : AuthzState :=
  withDoc (op ++ "/jwks") opJwks (withDoc (discoveryUrl op) d (withDoc bob doc))
def idClaims (drop : List String := []) (iss : String := op) : Json :=
  .object (([ ("sub", .string bob), ("iss", .string iss), ("azp", .string "https://client.example/app")
            , ("aud", .array [.string "https://client.example/app", .string asIssuer])
            , ("iat", num now), ("exp", num (now + 300)) ]).filter (fun kv => !drop.contains kv.1))
def idToken (drop : List String := []) (sk : ByteArray := opKey) : String :=
  jwt (es256Header "op1") (idClaims drop) sk

#guard (run (baseForm idToken tokenTypeIdToken) (oidcSt)).isIssued
#guard (match issued? (run (baseForm idToken tokenTypeIdToken) oidcSt) with
        | some t => ((claimsOf? t).bind (·.getString? "client_id")) == some "https://client.example/app" &&
                    ((claimsOf? t).bind (·.getString? "sub")) == some bob
        | none => false)
-- Negative: the subject's document names another provider.
#guard errorOf (run (baseForm idToken tokenTypeIdToken) (oidcSt (bobDoc "https://rogue.example"))) == some "invalid_request"
-- Negative: no azp, bad signature, expired.
#guard errorOf (run (baseForm (idToken ["azp"]) tokenTypeIdToken) oidcSt) == some "invalid_request"
#guard errorOf (run (baseForm (idToken [] (bytesOf 32 12)) tokenTypeIdToken) oidcSt) == some "invalid_request"
#guard errorOf (run (baseForm (jwt (es256Header "op1") (.object
  [ ("sub", .string bob), ("iss", .string op), ("azp", .string "https://client.example/app")
  , ("aud", .array [.string asIssuer]), ("iat", num (now - 3900)), ("exp", num (now - 3600)) ]) opKey)
  tokenTypeIdToken) oidcSt) == some "invalid_request"
-- Negative: the discovery document names another issuer (OIDC Discovery §4.3).
#guard errorOf (run (baseForm idToken tokenTypeIdToken) (oidcSt bobDoc (disc "https://elsewhere.example"))) == some "invalid_request"
-- An ID token presented as a self-issued JWT is refused (sub ≠ iss).
#guard errorOf (run (baseForm idToken tokenTypeJwt) oidcSt) == some "invalid_request"

/-! ## The HTTP step -/

def get (p : String) : Request := { method := "GET", path := p, queryStr := "" }
def statusOf (r : StepResult × AuthzState × Bool) : Nat :=
  match r.1 with
  | .respond resp => resp.status
  | .need _ => 0

#guard statusOf (step stub cfg st0 now rnd (get "/.well-known/lws-configuration")) == 200
#guard statusOf (step stub cfg st0 now rnd (get "/.well-known/oauth-authorization-server")) == 200
#guard statusOf (step stub cfg st0 now rnd (get "/jwks")) == 200
#guard statusOf (step stub cfg st0 now rnd (get "/token")) == 405
#guard statusOf (step stub cfg st0 now rnd (get "/elsewhere")) == 404
#guard statusOf (step stub cfg st0 now rnd { tokenReq (form (baseForm didToken)) with headers := [] }) == 400
#guard statusOf (step stub cfg st0 now rnd (tokenReq (form (baseForm didToken)))) == 200
-- With no key, the first request makes one and says the keys changed.
#guard (step stub cfg {} now rnd (get "/jwks")).2.2 == true
#guard (step stub cfg st0 now rnd (get "/jwks")).2.2 == false

/-! ## CORS (https://github.com/danbri/factoidal/issues/923) -/

def page : String := "https://danbri.github.io"
def corsOn : AuthzConfig := { cfg with cors := .echo }
def hdrOf (r : StepResult × AuthzState × Bool) (k : String) : Option String :=
  match r.1 with
  | .respond resp => resp.headers.lookup k
  | .need _ => none
def preflightTo (p : String) : Request :=
  { method := "OPTIONS", path := p, queryStr := "",
    headers := [("origin", page), ("access-control-request-method", "POST"),
                ("access-control-request-headers", "content-type")] }

-- A preflight to the token endpoint: 204, the page's origin, POST allowed,
-- and no key made (state and `changed` as before, even with no key).
#guard statusOf (stepCors stub corsOn st0 now rnd (preflightTo "/token")) == 204
#guard hdrOf (stepCors stub corsOn st0 now rnd (preflightTo "/token")) "access-control-allow-origin" == some page
#guard hdrOf (stepCors stub corsOn st0 now rnd (preflightTo "/token")) "access-control-allow-methods" ==
  some "GET, HEAD, OPTIONS, POST"
#guard (stepCors stub corsOn {} now rnd (preflightTo "/token")).2.2 == false
-- Other answers carry the fields; status unchanged.
#guard statusOf (stepCors stub corsOn st0 now rnd { tokenReq (form (baseForm didToken)) with
    headers := (tokenReq (form (baseForm didToken))).headers ++ [("origin", page)] }) == 200
#guard hdrOf (stepCors stub corsOn st0 now rnd { get "/jwks" with headers := [("origin", page)] })
  "access-control-allow-origin" == some page
#guard hdrOf (stepCors stub corsOn st0 now rnd { get "/jwks" with headers := [("origin", page)] })
  "access-control-allow-credentials" == none
#guard hdrOf (stepCors stub corsOn st0 now rnd { get "/token" with headers := [("origin", page)] })
  "access-control-expose-headers" == some "Allow, WWW-Authenticate"
-- An origin not on the list gets no Access-Control-Allow-Origin.
#guard hdrOf (stepCors stub { cfg with cors := .allow [page] } st0 now rnd
    { get "/jwks" with headers := [("origin", "https://evil.example")] })
  "access-control-allow-origin" == none
-- CORS off: a preflight is an ordinary OPTIONS (404 here, as before).
#guard statusOf (stepCors stub cfg st0 now rnd (preflightTo "/elsewhere")) == 404
#guard hdrOf (stepCors stub cfg st0 now rnd { get "/jwks" with headers := [("origin", page)] })
  "access-control-allow-origin" == none

end L4Factoidal.Authz.Tests
