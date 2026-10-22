/-
L4Factoidal.Authz.Server — an OAuth 2.0 authorization server for Linked
Web Storage, as a component any resource server can use
(https://github.com/danbri/factoidal/issues/916). Design record:
`docs/designissues/2026-10-22-authorization-server.md`.

Owner, 2026-10-22, verbatim: "Do auth server (as a component other servers
might use too)."

## What lws10-core "Authorization" requires of it

* "Authorization Server Metadata": "An authorization server MUST provide a
  metadata resource to allow clients to discover endpoint locations and
  capabilities as described in [RFC8414]. This metadata resource MUST be
  available at a URL with the path /.well-known/lws-configuration." Plus
  `subject_token_types_supported` and `subject_identifier_types_supported`.
  `metadataJson`. RFC 8414 §3.1: an issuer with a path puts the path after
  the well-known segment. The document is also served at the RFC 8414
  default name `/.well-known/oauth-authorization-server`, for third-party
  resource servers.
* "Token Exchange", "Request": the token endpoint "MUST support the
  urn:ietf:params:oauth:grant-type:token-exchange grant type"; "The
  resource parameter is REQUIRED"; "The authorization server MUST reject
  any request in which the resource parameter identifies an unknown or
  untrusted storage"; "The subject_token parameter is REQUIRED"; "Before
  returning an access token to the client, the authorization server MUST
  successfully validate all presented tokens." `exchange`.
* "Token Exchange", "Response": RFC 6749 §5.1, an RFC 9068 access token
  with `sub`, `iss`, `client_id`, `aud` ("MUST include the URI supplied by
  the client in the resource parameter"), `exp` ("RECOMMENDED: 300 seconds
  or less"), `iat`, `jti`. "All invalid or unauthorized requests MUST
  result in an error response as described in Section 5.2". `issueToken`,
  `tokenOutcome`.
* "Protocol Flow": "The interaction between the authorization server and
  the storage server is out of scope". This server knows no storage: it
  issues tokens for the resource IRIs it is configured with
  (`AuthzConfig.resources`), and a resource server reads its metadata and
  JWK Set.

## The theorems hold by a run-time check

`issueToken` checks its own output before it answers: it parses the token,
finds the key with the token's `kid` in the JWK Set text this server
publishes, verifies the signature with `JOSE.verifyCompact` (the function
the LWS storage server uses), and checks that `aud` is exactly
`[resource]`, `iss` the issuer and `sub` the subject (`selfCheck`). When a
check fails the answer is 500 and no token. `issueToken_verifies_published`
and `issueToken_audience_exact` (`Authz/Theorems.lean`) therefore hold
BECAUSE OF THAT CHECK, for every token this server gives out; no theorem
here says the check never fails. The proof that removes the check (a JSON
print/parse and compact JWS round trip):
https://github.com/danbri/factoidal/issues/927.

## What the host does

Sockets, clock, random bytes, file I/O. Every request carries `now` and
112 random bytes (two ECDSA nonce candidates, a private key candidate for
a rotation, a `jti`). When a subject token needs a document the engine
answers `Need` (`Authz/Fetch.lean`) and the host steps again after it
passed the answer.
-/
import L4Factoidal.Authz.SubjectToken
import L4Factoidal.HTTP.Server
import L4Factoidal.SPARQL.Protocol

namespace L4Factoidal.Authz

open L4Factoidal.JSON
open L4Factoidal.JOSE
open L4Factoidal.HTTP (Request Response)

/-! ## Configuration and state -/

structure AuthzConfig where
  /-- The issuer identifier: an absolute `http(s)` IRI, no query, no
  fragment, no trailing slash. -/
  issuer : String
  /-- The resource IRIs (storages) tokens may be issued for. -/
  resources : List String := []
  alg : SigAlg := .es256
  /-- Access token lifetime, seconds; at most 300 (the draft's
  RECOMMENDED bound). -/
  tokenLifetime : Nat := 300
  leeway : Nat := 60
  /-- Make a new signing key when the current one is this old; 0: never. -/
  rotateAfter : Nat := 0
  fetch : FetchPolicy := {}

structure AuthzState where
  keys : KeyStore := {}
  fetch : FetchState := {}

def AuthzConfig.grace (cfg : AuthzConfig) : Nat := cfg.tokenLifetime + cfg.leeway

/-- The context subject-token validation reads. -/
def AuthzConfig.ctx (cfg : AuthzConfig) (C : Crypto) (st : AuthzState) (now : Nat) : Ctx :=
  { C, issuer := cfg.issuer, now, leeway := cfg.leeway, policy := cfg.fetch, fs := st.fetch }

/-! ## Endpoints and metadata -/

def tokenExchangeGrant : String := "urn:ietf:params:oauth:grant-type:token-exchange"

/-- The path of the issuer identifier (empty for an origin). -/
def issuerPath (issuer : String) : String :=
  match issuer.splitOn "://" with
  | [_, rest] =>
      match rest.splitOn "/" with
      | _ :: segs => trimSlash (if segs.isEmpty then "" else "/" ++ "/".intercalate segs)
      | [] => ""
  | _ => ""

def lwsConfigurationPath (issuer : String) : String :=
  "/.well-known/lws-configuration" ++ issuerPath issuer
def oauthMetadataPath (issuer : String) : String :=
  "/.well-known/oauth-authorization-server" ++ issuerPath issuer
def jwksPath (issuer : String) : String := issuerPath issuer ++ "/jwks"
def tokenPath (issuer : String) : String := issuerPath issuer ++ "/token"

def tokenEndpointUrl (issuer : String) : String := trimSlash issuer ++ "/token"
def jwksUrl (issuer : String) : String := trimSlash issuer ++ "/jwks"

def strs (l : List String) : Json := .array (l.map Json.string)

/-- The RFC 8414 §2 metadata, with the two LWS members. -/
def metadataJson (cfg : AuthzConfig) : Json :=
  .object [ ("issuer", .string cfg.issuer)
          , ("token_endpoint", .string (tokenEndpointUrl cfg.issuer))
          , ("jwks_uri", .string (jwksUrl cfg.issuer))
          , ("grant_types_supported", strs [tokenExchangeGrant])
          -- RFC 8414 §2 lists the response types of the authorization
          -- endpoint. This server has none, so the list is empty.
          , ("response_types_supported", strs [])
          , ("token_endpoint_auth_methods_supported", strs ["none"])
          , ("claims_supported", strs ["sub", "iss", "client_id", "aud", "exp", "iat", "jti"])
          , ("subject_token_types_supported", strs [tokenTypeJwt, tokenTypeIdToken])
          , ("subject_identifier_types_supported", strs ["https", "did:key"]) ]

/-! ## Responses -/

def jsonResponse (status : Nat) (j : Json) (extra : List (String × String) := []) : Response :=
  { status, headers := ("content-type", "application/json") :: extra, body := toStringCompact j }

/-- RFC 6749 §5.2: 400, the error code and a description, not cached. -/
def errorResponse (code desc : String) : Response :=
  jsonResponse 400 (.object [("error", .string code), ("error_description", .string desc)])
    [("cache-control", "no-store")]

/-- A failure of this server: no token. -/
def serverError (desc : String) : Response :=
  jsonResponse 500 (.object [("error", .string "server_error"), ("error_description", .string desc)])
    [("cache-control", "no-store")]

/-- RFC 6749 §5.1 and RFC 8693 §2.2.1. -/
def successResponse (token : String) (lifetime : Nat) : Response :=
  jsonResponse 200 (.object [ ("access_token", .string token)
                            , ("issued_token_type", .string tokenTypeAccessToken)
                            , ("token_type", .string "Bearer")
                            , ("expires_in", .number (toString lifetime)) ])
    [("cache-control", "no-store"), ("pragma", "no-cache")]

/-! ## The token request -/

open L4Factoidal.SPARQL.Protocol (parseQueryString collectValues)

/-- The value of a form parameter: none, one, or a refusal when it is
given more than once (RFC 6749 §3.2: "Request and response parameters
MUST NOT be included more than once"). -/
def formValue (form : List (String × String)) (k : String) : Except String (Option String) :=
  match collectValues k form with
  | [] => .ok none
  | [v] => .ok (some v)
  | _ => .error s!"the parameter {k} is given more than once"

/-- What the token endpoint decided before signing. -/
inductive Exchange where
  | error (code desc : String)
  | issue (subject client resource : String)
  | need (n : Need)
  deriving Repr, BEq, DecidableEq

/-- The parameters a token-exchange request reads. -/
structure TokenRequest where
  resource : String
  subjectToken : String
  subjectTokenType : String

/-- Read the parameters; `.error` is an RFC 6749 §5.2 error. -/
def readTokenRequest (form : List (String × String)) :
    Except (String × String) TokenRequest := do
  let one (k : String) : Except (String × String) (Option String) :=
    match formValue form k with
    | .ok v => .ok v
    | .error w => .error ("invalid_request", w)
  match ← one "grant_type" with
  | none => throw ("invalid_request", "grant_type is required")
  | some g => if g != tokenExchangeGrant then
      throw ("unsupported_grant_type", "only token exchange (RFC 8693) is supported")
  let some resource ← one "resource" | throw ("invalid_request", "resource is required")
  let some subjectToken ← one "subject_token" | throw ("invalid_request", "subject_token is required")
  if subjectToken.isEmpty then throw ("invalid_request", "subject_token is required")
  let some subjectTokenType ← one "subject_token_type"
    | throw ("invalid_request", "subject_token_type is required")
  if (← one "actor_token").isSome then
    throw ("invalid_request", "actor_token (delegation) is not supported")
  match ← one "requested_token_type" with
  | some t => if t != tokenTypeAccessToken && t != tokenTypeJwt then
      throw ("invalid_request", s!"requested_token_type {t} is not supported")
  | none => pure ()
  match ← one "audience" with
  | some a => if a != resource then
      throw ("invalid_target", "audience must be the resource")
  | none => pure ()
  pure { resource, subjectToken, subjectTokenType }

/-- lws10-core "Token Exchange", "Request": "The authorization server MUST
reject any request in which the resource parameter identifies an unknown or
untrusted storage." RFC 8693 §2.2.2: `invalid_target`. -/
def tokenRequest (cfg : AuthzConfig) (form : List (String × String)) :
    Except (String × String) TokenRequest :=
  match readTokenRequest form with
  | .error e => .error e
  | .ok tr =>
      if cfg.resources.contains tr.resource then .ok tr
      else .error ("invalid_target", s!"this server issues no tokens for {tr.resource}")

/-- The token endpoint's decision: the request, then the subject token. -/
def exchange (ctx : Ctx) (cfg : AuthzConfig) (form : List (String × String)) : Exchange :=
  match tokenRequest cfg form with
  | .error (c, d) => .error c d
  | .ok tr =>
      match validateSubject ctx tr.subjectTokenType tr.subjectToken with
      | .valid s c => .issue s c tr.resource
      | .refused w => .error "invalid_request" w
      | .need n => .need n

/-! ## Issuing -/

/-- The `kid` of a compact JWS header. -/
def headerKid? (token : String) : Option String :=
  match preKey token with
  | .ok (_, h) => h.json.getString? "kid"
  | .error _ => none

/-- The claims object of a compact JWS, unverified. -/
def claimsOf? (token : String) : Option Json :=
  match parseJwt token with
  | .ok p => some p.claims
  | .error _ => none

/-- The keys of the JWK Set this server publishes, read back from its own
text by the parser a resource server uses. -/
def publishedKeys (cfg : AuthzConfig) (ks : KeyStore) (now : Nat) : List (Option String × Jwk) :=
  (jwkSetKeys (jwksText ks now cfg.grace)).getD []

/-- The token verifies under the published key its `kid` names. -/
def verifiesPublished (C : Crypto) (cfg : AuthzConfig) (ks : KeyStore) (now : Nat) (t : String) : Bool :=
  match headerKid? t with
  | some kid => (publishedKeys cfg ks now).any fun e =>
      e.1 == some kid && decide (verifyCompact C.verifiers e.2 t = .verified)
  | none => false

/-- The token's claims name exactly this issuer, subject and audience. -/
def claimsExact (cfg : AuthzConfig) (t subject resource : String) : Bool :=
  match claimsOf? t with
  | some c =>
      decide (c.getString? "iss" = some cfg.issuer) &&
      decide (c.getString? "sub" = some subject) &&
      decide ((c.field? "aud").bind audience? = some [resource])
  | none => false

/-- The run-time check of every issued token (module header). -/
def selfCheck (C : Crypto) (cfg : AuthzConfig) (ks : KeyStore) (now : Nat)
    (t subject resource : String) : Bool :=
  verifiesPublished C cfg ks now t && claimsExact cfg t subject resource

/-- The access token: RFC 9068 header and claims, signed with the current
key, checked by `selfCheck`. `rnd`: bytes 0..64 two ECDSA nonce candidates,
96..112 the `jti`. -/
def issueToken (C : Crypto) (cfg : AuthzConfig) (ks : KeyStore) (now : Nat) (rnd : ByteArray)
    (subject client resource : String) : Except String String :=
  match ks.current? with
  | none => .error "no signing key"
  | some k =>
      let header := Json.object [ ("alg", .string k.alg.name), ("typ", .string "at+jwt")
                                , ("kid", .string k.kid) ]
      let claims := Json.object
        [ ("iss", .string cfg.issuer), ("sub", .string subject)
        , ("aud", .array [.string resource]), ("client_id", .string client)
        , ("iat", .number (toString now)), ("exp", .number (toString (now + cfg.tokenLifetime)))
        , ("jti", .string (L4Factoidal.Crypto.bytesToHex (rnd.extract 96 112))) ]
      let h64 := Base64Url.encode (toStringCompact header).toUTF8
      let p64 := Base64Url.encode (toStringCompact claims).toUTF8
      let input := (h64 ++ "." ++ p64).toUTF8
      let sig? : Option ByteArray := match k.alg with
        | .es256 => match C.es256Sign k.secret input (rnd.extract 0 32) with
          | some s => some s
          | none => C.es256Sign k.secret input (rnd.extract 32 64)
        | .eddsa => some (C.eddsaSign k.secret input)
      match sig? with
      | none => .error "the signing primitive refused both nonce candidates"
      | some sig =>
          let t := h64 ++ "." ++ p64 ++ "." ++ Base64Url.encode sig
          if selfCheck C cfg ks now t subject resource then .ok t
          else .error "the issued token failed its own check"

/-- The token endpoint's whole answer. -/
inductive TokenOutcome where
  | issued (resp : Response) (token subject client resource : String)
  | refused (resp : Response)
  | need (n : Need)

def tokenOutcome (C : Crypto) (cfg : AuthzConfig) (st : AuthzState) (now : Nat) (rnd : ByteArray)
    (form : List (String × String)) : TokenOutcome :=
  match exchange (cfg.ctx C st now) cfg form with
  | .need n => .need n
  | .error c d => .refused (errorResponse c d)
  | .issue s cl res =>
      match issueToken C cfg st.keys now rnd s cl res with
      | .ok t => .issued (successResponse t cfg.tokenLifetime) t s cl res
      | .error e => .refused (serverError e)

/-! ## One request -/

inductive StepResult where
  | respond (resp : Response)
  | need (n : Need)

/-- Is the content form-encoded (RFC 6749 §4.1.3, §3.2)? -/
def isFormContent (r : Request) : Bool :=
  match r.header? "content-type" with
  | some v => ((v.splitOn ";").headD "").trimAscii.toString.toLower == "application/x-www-form-urlencoded"
  | none => false

def notAllowed (allow : String) : Response :=
  { status := 405, headers := [("allow", allow), ("content-type", "application/json")],
    body := toStringCompact (.object [("error", .string "method not allowed")]) }

def notFound : Response :=
  { status := 404, headers := [("content-type", "application/json")],
    body := toStringCompact (.object [("error", .string "not found")]) }

/-- GET or HEAD of a JSON document. -/
def getJson (r : Request) (j : Json) : Response :=
  if r.method == "GET" then jsonResponse 200 j
  else if r.method == "HEAD" then { jsonResponse 200 j with body := "" }
  else notAllowed "GET, HEAD"

/-- Rotate when the current key is due (`needsRotation`): the new key from
bytes 64..96 of the request's random bytes. -/
def maybeRotate (C : Crypto) (cfg : AuthzConfig) (st : AuthzState) (now : Nat) (rnd : ByteArray) :
    AuthzState × Bool :=
  if needsRotation st.keys now cfg.rotateAfter then
    match mkKey C cfg.alg (rnd.extract 64 96) now with
    | some k => ({ st with keys := rotateWith st.keys k now cfg.grace }, true)
    | none => (st, false)
  else (st, false)

/-- One HTTP request: (answer, new state, whether the keys changed). -/
def step (C : Crypto) (cfg : AuthzConfig) (st0 : AuthzState) (now : Nat) (rnd : ByteArray)
    (r : Request) : StepResult × AuthzState × Bool :=
  let (st, changed) := maybeRotate C cfg st0 now rnd
  let path := r.path
  if path == lwsConfigurationPath cfg.issuer || path == oauthMetadataPath cfg.issuer then
    (.respond (getJson r (metadataJson cfg)), st, changed)
  else if path == jwksPath cfg.issuer then
    (.respond (getJson r (jwksJson st.keys now cfg.grace)), st, changed)
  else if path == tokenPath cfg.issuer then
    if r.method != "POST" then (.respond (notAllowed "POST"), st, changed)
    else if !isFormContent r then
      (.respond (errorResponse "invalid_request"
        "the token request must be application/x-www-form-urlencoded"), st, changed)
    else match tokenOutcome C cfg st now rnd (parseQueryString r.body) with
      | .need n => (.need n, st, changed)
      | .refused resp => (.respond resp, st, changed)
      | .issued resp _ _ _ _ => (.respond resp, st, changed)
  else (.respond notFound, st, changed)

/-- The answer of the host to a `Need`. -/
def recordFetched (cfg : AuthzConfig) (st : AuthzState) (url : String) (status : Nat) (body : String)
    (now : Nat) : AuthzState :=
  { st with fetch := recordDoc cfg.fetch st.fetch url status body now }

def recordResolved (cfg : AuthzConfig) (st : AuthzState) (host : String) (addresses : List String)
    (now : Nat) : AuthzState :=
  { st with fetch := recordHost cfg.fetch st.fetch host addresses now }

end L4Factoidal.Authz
