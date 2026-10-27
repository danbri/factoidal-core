/-
L4Factoidal.Authz.SubjectToken — validation of the subject token the
token endpoint receives (https://github.com/danbri/factoidal/issues/916).

lws10-core, "Authorization", "Token Exchange", "Request": "Before
returning an access token to the client, the authorization server MUST
successfully validate all presented tokens." lws10-core, "Authentication",
"Authentication Credential Validation": "An authentication credential MUST
be signed."

## The suites, in the order of the design record

1. OpenID Connect ID token, token type
   `urn:ietf:params:oauth:token-type:id_token` (lws10-authn-openid, "Token
   Type Identifier"). "Authentication Credential Serialization": no `none`,
   `sub`, `iss`, `azp` ("The ID Token MUST use the azp (authorized party)
   claim for the LWS client identifier"), audience in `aud`.
   "Authentication Credential Validation": "the validator MUST dereference
   the sub (subject) claim [...] The resulting resource MUST be formatted as
   a valid controlled identifier document [CID-1.0] with an id value equal
   to the subject identifier. The verifier MUST use the subject's controlled
   identifier document to locate a service object whose serviceEndpoint
   value is equal to the value of the iss claim [...] and whose type value
   is equal to https://www.w3.org/ns/lws#OpenIdProvider. The verifier MUST
   perform OpenID Connect Discovery to locate the public portion of the JSON
   Web Key". OpenID Connect Discovery §4.3: the `issuer` of the discovery
   document must equal the issuer. `oidcKey`.
2. Self-issued credential, HTTPS subject, token type
   `urn:ietf:params:oauth:token-type:jwt` (lws10-authn-ssi-cid).
   "Authentication Credential Serialization": "The claims sub, iss, and
   client_id MUST all use the same URI value", "The aud claim MUST include
   the target authorization server", `exp` and `iat` required.
   "Authentication Credential Validation": "the verifier MUST dereference
   the sub (subject) claim [...] with an id value equal to the subject
   identifier", "MUST use the kid (key ID) value from the signed JWT header
   to identify a verification method from the subject's controlled
   identifier document. This process is described in [CID-1.0] Section
   3.3." CID 1.0 §3.3: the method must be one the `authentication`
   relationship names (embedded, or referenced and defined under
   `verificationMethod`), and its `controller` must be the subject; §2.2: a
   method with a `revoked` or `expires` time at or before now is not used.
   `cidKey`.
3. Self-issued credential, `did:key` subject (lws10-authn-ssi-cid, which
   covers DID subjects; lws10-authn-ssi-did-key is discontinued in its
   favour). The DID document is derived from the identifier (did:key
   §3.1.3): multicodec `0x1200` (P-256, compressed point, decompressed by
   HACL\*) or `0xed` (Ed25519). The `kid` is `did:key:z…#z…` or `z…`.
   `didKeyJwk?`.
4. SAML 2.0 assertion, `urn:ietf:params:oauth:token-type:saml2`
   (lws10-authn-saml): "the signature of the credential MUST be validated
   as described in SAML Core, section 5". `L4Factoidal.SAML.validate`:
   base64url XML, `saml:Assertion` from an identity provider in
   `Ctx.samlIdps` (trust is out of band), its enveloped XML Signature
   (exclusive canonicalization, rsa-sha256) verified under that
   provider's key, `saml:Conditions` times and `saml:Audience` (this
   server's issuer), the subject `saml:NameID`, the client the bearer
   `Recipient`. With no trusted provider the token type is refused and not
   advertised. https://github.com/danbri/factoidal/issues/926.

Every JWT suite: `alg: none` and any algorithm outside ES256, RS256, EdDSA are
refused by `JOSE.preKey` before a key is chosen; the signature is checked
by `JOSE.verifyCompact`; `exp` (required), `iat` (required, not in the
future), `nbf` (if present) are checked with `leeway` seconds of skew; and
`aud` must contain this server's issuer identifier.
-/
import L4Factoidal.Authz.Keys
import L4Factoidal.Authz.Fetch
import L4Factoidal.JOSE.Jwt
import L4Factoidal.VC.Multibase
import L4Factoidal.LWS.AccessPolicy
import L4Factoidal.SAML.Assertion

namespace L4Factoidal.Authz

open L4Factoidal.JSON
open L4Factoidal.JOSE

/-! ## Token types -/

def tokenTypeJwt : String := "urn:ietf:params:oauth:token-type:jwt"
def tokenTypeIdToken : String := "urn:ietf:params:oauth:token-type:id_token"
def tokenTypeSaml2 : String := "urn:ietf:params:oauth:token-type:saml2"
def tokenTypeAccessToken : String := "urn:ietf:params:oauth:token-type:access_token"

def samlIssue : String := "https://github.com/danbri/factoidal/issues/926"

def lwsOpenIdProvider : String := "https://www.w3.org/ns/lws#OpenIdProvider"

/-! ## Context and results -/

/-- What validation may read: the primitives, this server's issuer
identifier (the audience a credential must name), the clock, the skew, the
fetch policy and the document cache. -/
structure Ctx where
  C : Crypto
  issuer : String
  now : Nat
  leeway : Nat := 60
  policy : FetchPolicy := {}
  fs : FetchState := {}
  /-- The SAML identity providers this server trusts (out of band). -/
  samlIdps : List L4Factoidal.SAML.Idp := []

inductive SubjectResult where
  /-- The subject token is valid: the agent and the client it names. -/
  | valid (subject client : String)
  | refused (why : String)
  | need (n : Need)
  deriving Repr, BEq, DecidableEq

/-- A key, or why there is none yet. -/
inductive KeyFound where
  | key (k : Jwk)
  | refused (why : String)
  | need (n : Need)

/-! ## The JWT -/

structure Parsed where
  token : String
  alg : Alg
  header : Json
  claims : Json

/-- Split, decode and parse a compact JWS (`JOSE.preKey`), then its claims.
Nothing is decided from the claims before a signature verifies; they only
choose which key to try. -/
def parseJwt (token : String) : Except String Parsed :=
  match preKey token with
  | .error (.algNotAllowed a) => .error s!"the algorithm {a} is refused"
  | .error r => .error s!"not a signed JWT ({repr r})"
  | .ok (c, h) =>
      match (Base64Url.decode c.payloadB64).bind String.fromUTF8? with
      | none => .error "the claims are not base64url UTF-8"
      | some text =>
          match parseJson? text with
          | some j =>
              if j matches .object _ then .ok { token, alg := h.alg, header := h.json, claims := j }
              else .error "the claims are not a JSON object"
          | none => .error "the claims are not a JSON object"

def numClaim? (j : Json) (n : String) : Option Int := (j.field? n).bind numericDate?

/-- `exp` required and not passed, `iat` required and not in the future,
`nbf` not in the future, each with `leeway`. -/
def timesOk (ctx : Ctx) (c : Json) : Except String Unit :=
  let now : Int := ctx.now
  match numClaim? c "exp", numClaim? c "iat" with
  | none, _ => .error "exp is required"
  | _, none => .error "iat is required"
  | some e, some i =>
      if e + ctx.leeway ≤ now then .error "the credential has expired"
      else if i > now + ctx.leeway then .error "iat lies in the future"
      else match numClaim? c "nbf" with
        | some n => if n > now + ctx.leeway then .error "the credential is not valid yet" else .ok ()
        | none => .ok ()

/-- Does `aud` (a string or an array of strings) contain this server? -/
def audienceHas (ctx : Ctx) (c : Json) : Bool :=
  match (c.field? "aud").bind audience? with
  | some auds => auds.contains ctx.issuer
  | none => false

/-- The signature check: the only way to `valid`. -/
def finish (ctx : Ctx) (p : Parsed) (k : Jwk) (subject client : String) : SubjectResult :=
  if verifyCompact ctx.C.verifiers k p.token = .verified then .valid subject client
  else .refused "the signature does not verify with the subject's key"

/-! ## Multikey and did:key -/

/-- A Multikey value (`z` base58btc): multicodec `0x1200` P-256 compressed
point (33 bytes, decompressed by the primitive) or `0xed` Ed25519 (32
bytes). -/
def multikeyJwk? (C : Crypto) (mb : String) : Option Jwk :=
  if !mb.startsWith "z" then none
  else match L4Factoidal.VC.Multibase.base58Decode? (mb.drop 1).toString with
    | some (a :: b :: rest) =>
        if a == 0x80 && b == 0x24 && rest.length == 33 then
          (C.p256Decompress ⟨rest.toArray⟩).map (fun raw => .ec (raw.extract 0 32) (raw.extract 32 64))
        else if a == 0xed && b == 0x01 && rest.length == 32 then some (.okp ⟨rest.toArray⟩)
        else none
    | _ => none

def didKeyPrefix : String := "did:key:"

/-- The key a `did:key` identifier names, and the multibase value (the
fragment of its one verification method). -/
def didKeyJwk? (C : Crypto) (did : String) : Option (Jwk × String) :=
  if !did.startsWith didKeyPrefix then none
  else
    let mb := (did.drop didKeyPrefix.length).toString
    (multikeyJwk? C mb).map (·, mb)

/-! ## Controlled identifier documents -/

/-- A `#fragment` reference resolved against the subject's document IRI;
anything else as written. -/
def resolveRef (sub ref : String) : String :=
  if ref.startsWith "#" then withoutFragment sub ++ ref else ref

def idOf (sub : String) (m : Json) : Option String := (m.getString? "id").map (resolveRef sub)

/-- The verification methods the `authentication` relationship names (CID
1.0 §3.3): embedded objects, and references to a `verificationMethod` of
the same document. A method listed only under `verificationMethod`, or only
for another relationship, is not among them. -/
def authenticationMethods (doc : Json) (sub : String) : List Json :=
  let defined := (doc.getArray? "verificationMethod").getD []
  ((doc.getArray? "authentication").getD []).filterMap fun e =>
    match e with
    | .string r =>
        let ref := resolveRef sub r
        defined.find? (fun m => idOf sub m == some ref)
    | .object _ => some e
    | _ => none

/-- Has the method been revoked or expired (CID 1.0 §2.2)? An unreadable
time counts as revoked. -/
def methodInForce (now : Nat) (m : Json) : Bool :=
  ["revoked", "expires"].all fun n =>
    match m.field? n with
    | none => true
    | some (.string t) =>
        match L4Factoidal.LWS.AccessPolicy.parseXsdDateTime? t with
        | some at_ => decide ((now : Int) < at_)
        | none => false
    | some _ => false

/-- The public key of a verification method: `publicKeyJwk` (public members
only), or a Multikey `publicKeyMultibase`. -/
def methodKey? (C : Crypto) (m : Json) : Option Jwk :=
  match m.field? "publicKeyJwk" with
  | some j => parsePublicJwk? j
  | none => (m.getString? "publicKeyMultibase").bind (multikeyJwk? C)

/-- The method `methodId` of the subject's document, if it may be used to
authenticate the subject. -/
def selectMethod (ctx : Ctx) (doc : Json) (sub methodId : String) : Except String Jwk :=
  if doc.getString? "id" != some sub then
    .error s!"the controlled identifier document at {sub} names another id"
  else match (authenticationMethods doc sub).find? (fun m => idOf sub m == some methodId) with
    | none => .error s!"the controlled identifier document names no authentication method {methodId}"
    | some m =>
        if (m.getString? "controller").map (resolveRef sub) != some sub then
          .error s!"verification method {methodId} is controlled by another identifier"
        else if !methodInForce ctx.now m then
          .error s!"verification method {methodId} is revoked or expired"
        else match methodKey? ctx.C m with
          | some k => .ok k
          | none => .error s!"verification method {methodId} carries no usable public key"

def cidAccept : String := "application/ld+json, application/cid+json, application/json"

/-- The key of a CID-suite credential with an HTTPS subject. -/
def methodIdOf (sub kid : String) : String :=
  if (kid.splitOn ":").length > 1 then kid else withoutFragment sub ++ "#" ++ kid

def cidKey (ctx : Ctx) (sub : String) (kid : String) : KeyFound :=
  match lookup ctx.policy ctx.fs ctx.now sub cidAccept with
  | .need n => .need n
  | .refused w => .refused w
  | .doc t =>
      match parseJson? t with
      | none => .refused s!"the document at {sub} is not JSON"
      | some doc =>
          match selectMethod ctx doc sub (methodIdOf sub kid) with
          | .ok k => .key k
          | .error w => .refused w

/-! ## OpenID Connect -/

/-- Does a service object have the given type (a string or an array)? -/
def hasType (s : Json) (t : String) : Bool :=
  match s.field? "type" with
  | some (.string x) => x == t
  | some (.array xs) => xs.contains (.string t)
  | _ => false

/-- Does the document name `iss` as an OpenID Provider service? -/
def namesProvider (doc : Json) (iss : String) : Bool :=
  ((doc.getArray? "service").getD []).any fun s =>
    hasType s lwsOpenIdProvider &&
      (match s.field? "serviceEndpoint" with
       | some (.string e) => e == iss
       | some (.array es) => es.contains (.string iss)
       | _ => false)

def trimSlash (s : String) : String := if s.endsWith "/" then (s.dropEnd 1).toString else s

def discoveryUrl (iss : String) : String := trimSlash iss ++ "/.well-known/openid-configuration"

/-- The keys of a JWK Set with their `kid`; members that are not usable
public keys are dropped (RFC 7517 §5). -/
def jwkSetKeys (text : String) : Option (List (Option String × Jwk)) :=
  (parseJson? text).bind fun j =>
    (j.getArray? "keys").map fun items =>
      items.filterMap fun it => (parsePublicJwk? it).map (it.getString? "kid", ·)

def keysForKid (kid : Option String) (ks : List (Option String × Jwk)) : List Jwk :=
  match kid with
  | some k => (ks.filter (fun e => e.1 == some k)).map (·.2)
  | none => if ks.length == 1 then ks.map (·.2) else []

/-- The key of an ID token: subject document, provider service, discovery,
JWK Set. -/
def oidcKey (ctx : Ctx) (iss sub : String) (kid : Option String) : KeyFound :=
  match lookup ctx.policy ctx.fs ctx.now sub cidAccept with
  | .need n => .need n
  | .refused w => .refused w
  | .doc t =>
      match parseJson? t with
      | none => .refused s!"the document at {sub} is not JSON"
      | some doc =>
          if doc.getString? "id" != some sub then
            .refused s!"the controlled identifier document at {sub} names another id"
          else if !namesProvider doc iss then
            .refused s!"the subject's controlled identifier document names no OpenID Provider {iss}"
          else
            match lookup ctx.policy ctx.fs ctx.now (discoveryUrl iss) "application/json" with
            | .need n => .need n
            | .refused w => .refused w
            | .doc dt =>
                match parseJson? dt with
                | none => .refused "the OpenID Provider's discovery document is not JSON"
                | some disc =>
                    if disc.getString? "issuer" != some iss then
                      .refused "the OpenID Provider's discovery document names another issuer"
                    else match disc.getString? "jwks_uri" with
                      | none => .refused "the OpenID Provider's discovery document has no jwks_uri"
                      | some ju =>
                          match lookup ctx.policy ctx.fs ctx.now ju "application/json" with
                          | .need n => .need n
                          | .refused w => .refused w
                          | .doc kt =>
                              match jwkSetKeys kt with
                              | none => .refused "the OpenID Provider's JWK Set does not parse"
                              | some ks =>
                                  match keysForKid kid ks with
                                  | k :: _ => .key k
                                  | [] =>
                                      -- A rotated provider key: fetch the
                                      -- set again, at most once a second.
                                      match lookup ctx.policy ctx.fs ctx.now ju "application/json" (some 1) with
                                      | .need n => .need n
                                      | _ => .refused s!"the OpenID Provider publishes no key {kid.getD "(none)"}"

/-! ## The suites -/

/-- The key a suite found, then the signature: the only path to `valid`. -/
def withKey (ctx : Ctx) (p : Parsed) (kf : KeyFound) (subject client : String) : SubjectResult :=
  match kf with
  | .need n => .need n
  | .refused w => .refused w
  | .key k => finish ctx p k subject client

/-- The claim checks of the CID suite: `sub` = `iss` = `client_id`, the
times, the audience. The subject. -/
def selfIssuedSubject (ctx : Ctx) (p : Parsed) : Except String String :=
  match p.claims.getString? "sub", p.claims.getString? "iss", p.claims.getString? "client_id" with
  | some sub, some iss, some cl =>
      if !(sub == iss && sub == cl) then .error "sub, iss and client_id must be the same identifier"
      else match timesOk ctx p.claims with
        | .error w => .error w
        | .ok () =>
            if !audienceHas ctx p.claims then .error "aud does not include this authorization server"
            else .ok sub
  | none, _, _ => .error "sub is required"
  | _, none, _ => .error "iss is required"
  | _, _, none => .error "client_id is required"

/-- The key of the CID suite: from the `did:key` identifier, or from the
subject's controlled identifier document. -/
def selfIssuedKey (ctx : Ctx) (p : Parsed) (sub : String) : KeyFound :=
  if sub.startsWith didKeyPrefix then
    match didKeyJwk? ctx.C sub with
    | none => .refused "the did:key names neither a P-256 nor an Ed25519 key"
    | some (k, mb) =>
        if p.header.getString? "kid" == some (sub ++ "#" ++ mb) || p.header.getString? "kid" == some mb
        then .key k
        else .refused "the kid names no verification method of the DID document the did:key derives"
  else match p.header.getString? "kid" with
    | none => .refused "a CID credential names its verification method in kid, and this one has none"
    | some kid => cidKey ctx sub kid

/-- The CID suite, for an HTTPS or a `did:key` subject. -/
def validateSelfIssued (ctx : Ctx) (p : Parsed) : SubjectResult :=
  match selfIssuedSubject ctx p with
  | .error w => .refused w
  | .ok sub => withKey ctx p (selfIssuedKey ctx p sub) sub sub

/-- The claim checks of the OpenID Connect suite: (`iss`, `sub`, `azp`). -/
def idTokenClaims (ctx : Ctx) (p : Parsed) : Except String (String × String × String) :=
  match p.claims.getString? "iss", p.claims.getString? "sub" with
  | some iss, some sub =>
      match p.claims.getString? "azp" with
      | none => .error "the ID Token names no azp, so the client it was issued to is unknown"
      | some azp =>
          match timesOk ctx p.claims with
          | .error w => .error w
          | .ok () =>
              if !audienceHas ctx p.claims then .error "aud does not include this authorization server"
              else .ok (iss, sub, azp)
  | _, _ => .error "an ID Token needs iss and sub"

/-- The OpenID Connect suite. -/
def validateIdToken (ctx : Ctx) (p : Parsed) : SubjectResult :=
  match idTokenClaims ctx p with
  | .error w => .refused w
  | .ok (iss, sub, azp) => withKey ctx p (oidcKey ctx iss sub (p.header.getString? "kid")) sub azp

/-- The SAML 2.0 suite. The audience is this server's issuer identifier. -/
def validateSaml (ctx : Ctx) (token : String) : SubjectResult :=
  if ctx.samlIdps.isEmpty then
    .refused "SAML 2.0 assertions are not accepted: this server trusts no SAML identity provider"
  else
    match L4Factoidal.SAML.validate ctx.C.verifiers.rs256
        { idps := ctx.samlIdps, audience := ctx.issuer, now := ctx.now, leeway := ctx.leeway } token with
    | .ok c => .valid c.nameId c.recipient
    | .error w => .refused w

/-- Validate a subject token of a token type. -/
def validateSubject (ctx : Ctx) (tokenType token : String) : SubjectResult :=
  if tokenType == tokenTypeSaml2 then validateSaml ctx token
  else if tokenType == tokenTypeJwt || tokenType == tokenTypeIdToken then
    match parseJwt token with
    | .error w => .refused w
    | .ok p => if tokenType == tokenTypeJwt then validateSelfIssued ctx p else validateIdToken ctx p
  else .refused s!"unsupported subject_token_type {tokenType}"

/-! ## Theorems -/

/-- `withKey` gives `valid` only through a key that verifies the token. -/
theorem withKey_valid {ctx : Ctx} {p : Parsed} {kf : KeyFound} {s c s' c' : String}
    (h : withKey ctx p kf s' c' = .valid s c) :
    ∃ k, kf = .key k ∧ verifyCompact ctx.C.verifiers k p.token = .verified ∧ s = s' ∧ c = c' := by
  unfold withKey at h
  split at h
  · simp at h
  · simp at h
  · rename_i k
    unfold finish at h
    split at h
    · rename_i hv
      simp at h
      exact ⟨k, rfl, hv, h.1.symm, h.2.symm⟩
    · simp at h

/-- `validateSaml` gives `valid` only for an assertion whose signature
verified under the key of a trusted identity provider of the context. -/
theorem validateSaml_valid {ctx : Ctx} {token s c : String}
    (h : validateSaml ctx token = .valid s c) :
    ∃ cl d idp, L4Factoidal.SAML.validate ctx.C.verifiers.rs256
        { idps := ctx.samlIdps, audience := ctx.issuer, now := ctx.now, leeway := ctx.leeway } token = .ok cl ∧
      cl.nameId = s ∧ cl.recipient = c ∧ idp ∈ ctx.samlIdps ∧ idp.entityId = cl.issuer ∧
      L4Factoidal.SAML.decodeToken token = .ok d ∧
      L4Factoidal.XML.DSig.verifyEnveloped ctx.C.verifiers.rs256 idp.n idp.e d = .ok () := by
  unfold validateSaml at h
  split at h
  · cases h
  · split at h
    · rename_i cl hv
      cases h
      obtain ⟨d, idp, hd, hm, he, hver⟩ := L4Factoidal.SAML.validate_ok hv
      exact ⟨cl, d, idp, hv, rfl, rfl, hm, he, hd, hver⟩
    · cases h

end L4Factoidal.Authz
