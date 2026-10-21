/-
L4Factoidal.LWS.Authorization — storage-server authorization of the LWS
1.0 editor's draft (w3c/lws-protocol 9a08ff65, 2026-10-19, section
"Authorization"), decided in Lean.
https://github.com/danbri/factoidal/issues/886

## What the draft requires of a storage server

  * Authorization Server Discovery: "A storage server generating a 401
    (Unauthorized) response MUST send a WWW-Authenticate header field
    containing at least one conforming challenge. A conforming challenge
    MUST include the resource_metadata parameter defined in Section 5.1 of
    [RFC9728] […]. The response MUST also include a Link header
    identifying the storage that contains the requested resource".
    `challenge`.
  * Protected Resource Metadata: the document "MUST conform to OAuth 2.0
    Protected Resource Metadata [RFC9728]", "the authorization_servers
    parameter is REQUIRED […] and its value MUST contain the issuer
    identifier of at least one authorization server", and "The resource
    value […] identifies the requested resource, not the storage".
    `metadataDocument`, `metadataUrl` (RFC 9728 §3.1 insertion rule).
  * Token Validation by a Storage Server: Bearer presentation (RFC 6750
    §2.1); "Verify the JWT signature using the authorization server's
    public key retrieved from the jwks_uri […] Storage servers SHOULD
    cache these keys and MUST support key rotation"; issuer, audience
    ("the aud claim includes the URI of the storage"), `exp`, `nbf` and
    "the iat (issued at) claim is not in the future", each with clock
    skew. "If validation fails, the storage server MUST return 401
    Unauthorized with a WWW-Authenticate header containing the
    resource_metadata parameter and an appropriate error parameter".
    "If the token is otherwise valid but an authorization policy does not
    allow the requested operation, the storage server MUST reject the
    request." `validateToken`, `decide`.

The draft names no DPoP binding; Bearer is the only scheme. The Solid
server keeps its DPoP-bound Solid-OIDC path (`Solid/Server/Auth.lean`).

## What the host does

Only I/O. The host holds the socket and the clock, and fetches the two
documents this module names (`Decision.fetch`): the authorization
server's `/.well-known/lws-configuration` metadata (RFC 8414) and the JWK
Set at its `jwks_uri`. `installFetched` decides what a fetched document
means. Which key verifies a token, whether a token is acceptable, which
status answers, and when keys may be fetched again are all decided here.

## The authorization policy

Web Access Control (`Solid/Server/WAC.lean`) over the ACL resources in the
storage, with the token's `sub` as the agent. The LWS draft leaves the
policy language to the server ("A compliant LWS server designates a
resource manager for each resource"); WAC is the one this project has.

## Off is explicit

`AuthzConfig.insecureNoAuth` is `false` by default. With no trusted issuer
and no opt-out, every request that the ACLs do not grant to the public
answers 401: a storage does not fall open (`validateToken_no_issuers`,
`validateToken_valid_verified`).
-/
import L4Factoidal.LWS.Operations
import L4Factoidal.Solid.Server.Methods
import L4Factoidal.JOSE.Jwt
import L4Factoidal.JOSE.Jws
import L4Factoidal.JOSE.Jwk

namespace L4Factoidal.LWS.Authorization

open L4Factoidal.JSON
open L4Factoidal.JOSE
open L4Factoidal.LWS
open L4Factoidal.HTTP (Request Response)
open L4Factoidal.Solid.Server (Requester allowed aclGraphOf requiredMode targetsAcl
  authorizationSubject)

/-! ## Configuration -/

/-- One key of a JWK Set, with its `kid` (RFC 7517 §4.5) when it has one. -/
structure KeyEntry where
  kid : Option String
  key : Jwk

/-- One trusted authorization server. `keys` is the cache the draft says a
storage server SHOULD keep; `fetchedAt` is when it was last filled. -/
structure TrustedIssuer where
  issuer : String
  jwksUri : Option String := none
  keys : List KeyEntry := []
  fetchedAt : Option Nat := none

/-- The storage server's authorization configuration. -/
structure AuthzConfig where
  /-- The development mode with no authorization at all. Off unless a
  deployment opts in (`--insecure-no-auth`). -/
  insecureNoAuth : Bool := false
  issuers : List TrustedIssuer := []
  /-- The storage IRI tokens must name in `aud`. `none`: the canonical URI
  of the storage, the storage description `<baseIri>.well-known/lws-storage`
  (`storageIri`). -/
  audience : Option String := none
  /-- Allowed clock skew, seconds. -/
  leeway : Nat := 60
  /-- The least time between two key fetches for one issuer, so that a
  token naming an unknown `kid` cannot make the server fetch on every
  request. -/
  refreshInterval : Nat := 60

instance : Inhabited AuthzConfig := ⟨{}⟩

/-! ## Discovery documents -/

def wellKnownPrm : String := "/.well-known/oauth-protected-resource"
def wellKnownLwsConfig : String := "/.well-known/lws-configuration"

/-- Split an absolute IRI into its origin (`scheme://authority`) and its
path (empty when there is none). -/
def splitOrigin (iri : String) : String × String :=
  match iri.splitOn "://" with
  | [scheme, rest] =>
      match rest.splitOn "/" with
      | [] => (iri, "")
      | auth :: segs =>
          (scheme ++ "://" ++ auth, if segs.isEmpty then "" else "/" ++ "/".intercalate segs)
  | _ => (iri, "")

/-- RFC 9728 §3.1: the metadata URL inserts `/.well-known/oauth-protected-
resource` between the host and the path, "any terminating slash (/)
following the host component" removed. -/
def metadataUrl (resource : String) : String :=
  let (o, p) := splitOrigin resource
  o ++ wellKnownPrm ++ (if p == "/" then "" else p)

/-- The resource a metadata path describes; the inverse of `metadataUrl`
for a storage whose root is an origin. -/
def resourceOfMetadataPath (baseIri path : String) : String :=
  let (o, _) := splitOrigin baseIri
  let rest := (path.drop wellKnownPrm.length).toString
  o ++ (if rest == "" then "/" else rest)

/-- The storage IRI: the audience a token must name, and the target of the
`lws#storage` link of a 401.

lws10-core `Discovery.html`: the storage description's "`id` ... MUST be the
canonical URI of the storage", "Requests for the storage URI MUST return a
document that conforms to the storage description resource data model", and
"All responses to GET and HEAD requests targeting storage resources MUST
include a Link header whose target is the canonical URI of the storage".
So the storage URI is the URI of the storage description
(`iriOfPath baseIri storagePath`); the storage root container (`baseIri`) is
a different resource, the `serviceEndpoint` of the `StorageRoot` service.
`Authorization.html`: the 401 "MUST also include a Link header identifying
the storage that contains the requested resource ... A client supplies this
URI as the resource parameter when requesting an access token", and the
token's `aud` "MUST include the URI supplied by the client in the resource
parameter, which is the URI of a storage". The 401 link, the default
audience and every other response's `lws#storage` link are therefore one
IRI (https://github.com/danbri/factoidal/issues/911, F4). `audience`
overrides it for a deployment whose storage has another canonical URI.

The protected resource metadata `resource` is NOT this IRI:
`Authorization.html`, "The resource value in a protected resource metadata
document identifies the requested resource, not the storage that contains
it" (`resourceOfMetadataPath`). -/
def storageIri (cfg : Config) (a : AuthzConfig) : String :=
  a.audience.getD (iriOfPath cfg.baseIri storagePath)

/-- The RFC 9728 §2 document. -/
def metadataDocument (a : AuthzConfig) (resource : String) : String :=
  toStringCompact (.object
    [ ("resource", .string resource)
    , ("authorization_servers", .array (a.issuers.map (fun i => Json.string i.issuer)))
    , ("bearer_methods_supported", .array [.string "header"]) ])

/-- Where an issuer's RFC 8414 metadata is: the draft fixes the path
`/.well-known/lws-configuration`. -/
def issuerMetadataUrl (issuer : String) : String :=
  let trimmed := if issuer.endsWith "/" then (issuer.dropEnd 1).toString else issuer
  trimmed ++ wellKnownLwsConfig

/-! ## Token validation -/

/-- Why a presented token was refused. -/
inductive Refusal where
  | malformedAuthorization
  | wrongScheme (scheme : String)
  | notJws
  | claimsUnreadable
  | untrustedIssuer (iss : Option String)
  | noKey
  | badSignature
  | claims (o : ClaimsOutcome)
  | issuedInFuture
  | issuedAtMissing
  deriving Repr, BEq, DecidableEq

/-- The RFC 6750 §3.1 error code for a refusal. -/
def Refusal.errorCode : Refusal → String
  | .malformedAuthorization => "invalid_request"
  | .wrongScheme _ => "invalid_request"
  | _ => "invalid_token"

/-- What token validation decided. -/
inductive TokenResult where
  | valid (sub iss : String)
  | refused (r : Refusal)
  /-- The issuer is trusted but no cached key can be tried; fetch its
  metadata first. -/
  | needKeys (issuer : String)
  deriving Repr, BEq, DecidableEq

/-- The unverified claims of a compact JWS. Read only to find which
trusted issuer's keys to try; nothing is decided from them before the
signature verifies. -/
def unverifiedClaims? (token : String) : Option Claims :=
  match preKey token with
  | .error _ => none
  | .ok (c, _) =>
      (Base64Url.decode c.payloadB64).bind fun b =>
        (String.fromUTF8? b).bind fun s => (parseJson? s).bind parseClaims?

/-- The `kid` of a compact JWS header, if any. -/
def headerKid? (token : String) : Option String :=
  match preKey token with
  | .error _ => none
  | .ok (_, h) => h.json.getString? "kid"

/-- The keys to try: those with the token's `kid`, or every key when the
token names none. -/
def candidateKeys (kid : Option String) (ks : List KeyEntry) : List Jwk :=
  match kid with
  | none => ks.map (·.key)
  | some k => (ks.filter (fun e => e.kid == some k)).map (·.key)

/-- May keys be fetched for this issuer now? -/
def mayFetch (a : AuthzConfig) (now : Nat) (i : TrustedIssuer) : Bool :=
  match i.fetchedAt with
  | none => true
  -- At least one second: within one instant a fetch is never repeated,
  -- so one request makes at most one metadata and one key-set fetch per
  -- issuer, whatever the configured interval.
  | some t => decide (t + max 1 a.refreshInterval ≤ now)

/-- The claims checks, once the signature has verified: issuer,
audience, `exp`, `nbf` (`Jwt.validate`), then `iat` not in the future. -/
def checkClaims (cfg : Config) (a : AuthzConfig) (now : Nat) (ti : TrustedIssuer)
    (c : Claims) : TokenResult :=
  let policy : Policy :=
    { now := now, leeway := a.leeway, issuer := ti.issuer, audience := storageIri cfg a }
  match validate policy c with
  | .ok =>
      match c.iat with
      | none => .refused .issuedAtMissing
      | some t =>
          if decide (t ≤ (now : Int) + a.leeway) then
            match c.sub with
            | some s => .valid s ti.issuer
            | none => .refused (.claims .subjectMissing)
          else .refused .issuedInFuture
  | o => .refused (.claims o)

/-- Does some candidate key verify the token? -/
def anyKeyVerifies (V : Verifiers) (ks : List Jwk) (token : String) : Bool :=
  ks.any (fun k => verifyCompact V k token == .verified)

/-- After the issuer is known: the keys, the signature, then the claims. -/
def validateWith (V : Verifiers) (cfg : Config) (a : AuthzConfig) (now : Nat)
    (token : String) (ti : TrustedIssuer) (c : Claims) : TokenResult :=
  let ks := candidateKeys (headerKid? token) ti.keys
  if ks.isEmpty then
    if mayFetch a now ti then .needKeys ti.issuer else .refused .noKey
  else if anyKeyVerifies V ks token then checkClaims cfg a now ti c
  -- A rotated key: a token signed by a key the cache does not hold yet.
  -- Fetch once per refresh interval, then refuse.
  else if mayFetch a now ti then .needKeys ti.issuer
  else .refused .badSignature

/-- The draft's validation, in its order: signature, issuer, audience,
then the three temporal checks. -/
def validateToken (V : Verifiers) (cfg : Config) (a : AuthzConfig) (now : Nat)
    (token : String) : TokenResult :=
  match unverifiedClaims? token with
  | none => .refused .notJws
  | some c =>
      match a.issuers.find? (fun i => c.iss == some i.issuer) with
      | none => .refused (.untrustedIssuer c.iss)
      | some ti => validateWith V cfg a now token ti c

/-! ## Authentication of one request -/

/-- What the request's credential established. -/
inductive Authn where
  | anonymous
  | authenticated (sub : String)
  | refused (r : Refusal)
  | needKeys (issuer : String)
  deriving Repr, BEq, DecidableEq

/-- RFC 6750 §2.1: `Authorization: Bearer <token>`; the scheme is case
insensitive (RFC 9110 §11.1). -/
def authenticate (V : Verifiers) (cfg : Config) (a : AuthzConfig) (now : Nat)
    (r : Request) : Authn :=
  match r.header? "authorization" with
  | none => .anonymous
  | some v =>
      match v.splitOn " " with
      | [scheme, token] =>
          if scheme.toLower != "bearer" then .refused (.wrongScheme scheme)
          else if token == "" then .refused .malformedAuthorization
          else match validateToken V cfg a now token with
            | .valid s _ => .authenticated s
            | .refused rf => .refused rf
            | .needKeys i => .needKeys i
      | _ => .refused .malformedAuthorization

/-! ## Responses -/

/-- The 401 of "Authorization Server Discovery". RFC 6750 §3.1: with no
credential the challenge carries no error code; with a refused one it
carries the code. -/
def challenge (cfg : Config) (a : AuthzConfig) (target : String) (err : Option String) :
    Response :=
  let resource := iriOfPath cfg.baseIri target
  let params := "Bearer resource_metadata=\"" ++ metadataUrl resource ++ "\"" ++
    (match err with | none => "" | some e => ", error=\"" ++ e ++ "\"")
  problem 401 "an access token is required" target
    [ ("www-authenticate", params)
    , ("link", renderLinks [{ target := storageIri cfg a, rel := lwsStorageRel }]) ]

/-- The answer when a valid token's agent is not allowed the operation:
RFC 6750 §3.1 `insufficient_scope` is 403. -/
def forbidden (cfg : Config) (target : String) : Response :=
  let resource := iriOfPath cfg.baseIri target
  problem 403 "the access policy does not allow this operation" target
    [ ("www-authenticate", "Bearer resource_metadata=\"" ++ metadataUrl resource ++
        "\", error=\"insufficient_scope\"") ]

/-! ## The decision -/

/-- What the storage server does with one request. -/
inductive Decision where
  /-- Run the storage operation as this agent. -/
  | proceed (agent : Option String)
  /-- Answer without touching the storage. -/
  | respond (resp : Response)
  /-- Fetch this URL for this issuer, give it to `installFetched`, and
  decide again. -/
  | fetch (issuer url : String)

variable {σ : Type}

/-- One request's authorization decision. -/
def decide (V : Verifiers) (S : Store σ) (cfg : Config) (a : AuthzConfig) (now : Nat)
    (r : Request) (st : σ) : Decision :=
  let (path, _) := splitTarget r.path
  if a.insecureNoAuth then .proceed cfg.agent
  else if path.startsWith wellKnownPrm then
    if r.method == "GET" || r.method == "HEAD" then
      .respond ⟨200, [("content-type", "application/json")],
        if r.method == "HEAD" then "" else
          metadataDocument a (resourceOfMetadataPath cfg.baseIri path), none⟩
    else .respond (problem 405 "the metadata document is read only" path
        [("allow", "GET, HEAD")])
  -- The storage description is what a client reads to validate the
  -- discovered values before it has a token ("Discovery Validation by a
  -- Client"), so it is public.
  else if path == storagePath then .proceed none
  -- The subscription endpoint (LWS §Subscriptions: "a subscriber creates a
  -- subscription by sending an authenticated POST request to the
  -- serviceEndpoint"). It needs an authenticated agent; which topics that
  -- agent may subscribe to, and which subscriptions it may see, are
  -- decided by `L4Factoidal.LWS.Notifications` against the access policy.
  else if cfg.notifications && isSubscriptionPath path then
    match authenticate V cfg a now r with
    | .needKeys i => .fetch i (issuerMetadataUrl i)
    | .refused rf => .respond (challenge cfg a path (some rf.errorCode))
    | .anonymous => .respond (challenge cfg a path none)
    | .authenticated s => .proceed (some s)
  -- The Type Index and Type Search services (lws10-index §Security and
  -- Authorization): every client may ask, and the answer holds only what
  -- that client may read (`L4Factoidal.LWS.Search`). An anonymous request
  -- is answered with what the public may read; a refused credential is 401.
  else if cfg.typeIndex && isIndexServicePath path then
    match authenticate V cfg a now r with
    | .needKeys i => .fetch i (issuerMetadataUrl i)
    | .refused rf => .respond (challenge cfg a path (some rf.errorCode))
    | .anonymous => .proceed none
    | .authenticated s => .proceed (some s)
  else
    let gate (who : Option String) : Decision :=
      let subject := authorizationSubject path
      let mode := requiredMode r.method (targetsAcl path)
      let may (p : String) (m : L4Factoidal.Solid.Server.Mode) : Bool :=
        allowed S aclGraphOf cfg.baseIri st (authorizationSubject p)
          { webId := who, origin := r.header? "origin" } m
      -- LWS §Moving Resources: a move needs the delete of every moved
      -- resource (the whole subtree of a container) and a create in the
      -- destination, evaluated before the move is applied.
      let moveOk : Bool := match movePlanOf? S cfg.baseIri cfg.moves r st with
        | none => true
        | some plan => plan.moves.all (fun m => may m.1 (requiredMode "DELETE" (targetsAcl m.1))) &&
            may plan.dest (requiredMode "POST" false)
      if may path mode && moveOk then
        .proceed who
      else match who with
        | none => .respond (challenge cfg a path none)
        | some _ => .respond (forbidden cfg path)
    match authenticate V cfg a now r with
    | .needKeys i => .fetch i (issuerMetadataUrl i)
    | .refused rf => .respond (challenge cfg a path (some rf.errorCode))
    | .anonymous => gate none
    | .authenticated s => gate (some s)

/-- One authorized LWS step: the decision, then `LWS.step` as the agent it
names. A `fetch` decision is returned to the host unchanged. -/
def authorizedStep (V : Verifiers) (S : Store σ) (cfg : Config) (a : AuthzConfig)
    (now : Nat) (r : Request) (st : σ) : Sum (String × String) (Response × σ) :=
  match decide V S cfg a now r st with
  | .fetch i u => .inl (i, u)
  | .respond resp => .inr (resp, st)
  | .proceed agent => .inr (step S { cfg with agent := agent } r st)

/-! ## Fetched documents -/

/-- Read a JWK Set (RFC 7517 §5). Members that are not usable public keys
are dropped, as §5 allows ("Implementations SHOULD ignore JWKs within a
JWK Set that use "kty" (key type) values that are not understood"). -/
def parseJwks? (body : String) : Option (List KeyEntry) :=
  match parseJson? body with
  | none => none
  | some j =>
      match j.getArray? "keys" with
      | none => none
      | some items =>
          some (items.filterMap (fun it =>
            (parsePublicJwk? it).map (fun k => { kid := it.getString? "kid", key := k })))

/-- What a fetched document did. -/
inductive Fetched where
  /-- The issuer metadata named this `jwks_uri`; fetch it next. -/
  | next (url : String)
  /-- Keys installed. -/
  | installed (count : Nat)
  | refused (why : String)
  deriving Repr, BEq

private def updateIssuer (a : AuthzConfig) (iss : String)
    (f : TrustedIssuer → TrustedIssuer) : AuthzConfig :=
  { a with issuers := a.issuers.map (fun i => if i.issuer == iss then f i else i) }

/-- Interpret one fetched document for one trusted issuer.

RFC 8414 §3.3: "The "issuer" value returned MUST be identical to the
authorization server's issuer identifier value into which the well-known
URI string was inserted to create the URL used to retrieve the metadata.
If these values are not identical, the data contained in the response
MUST NOT be used." A failed fetch still stamps `fetchedAt`, so a broken
issuer is not fetched on every request. -/
def installFetched (a : AuthzConfig) (issuer url : String) (status : Nat) (body : String)
    (now : Nat) : AuthzConfig × Fetched :=
  match a.issuers.find? (fun i => i.issuer == issuer) with
  | none => (a, .refused "not a trusted issuer")
  | some ti =>
      let stamp := updateIssuer a issuer (fun i => { i with fetchedAt := some now })
      if status != 200 then (stamp, .refused s!"{url} answered {status}")
      else if url == issuerMetadataUrl issuer then
        match parseJson? body with
        | none => (stamp, .refused "issuer metadata is not JSON")
        | some j =>
            if j.getString? "issuer" != some issuer then
              (stamp, .refused "issuer metadata names a different issuer (RFC 8414 §3.3)")
            else match j.getString? "jwks_uri" with
              | none => (stamp, .refused "issuer metadata has no jwks_uri")
              | some u =>
                  (updateIssuer a issuer (fun i => { i with jwksUri := some u }), .next u)
      else if ti.jwksUri == some url then
        match parseJwks? body with
        | none => (stamp, .refused "not a JWK Set")
        | some ks =>
            (updateIssuer a issuer (fun i => { i with keys := ks, fetchedAt := some now }),
             .installed ks.length)
      else (a, .refused "this URL was not asked for")

/-! ## The owner's root ACL -/

/-- Characters an IRI reference may not hold in a Turtle `IRIREF`
(Turtle §6.5, production [18]). -/
def iriRefSafe (s : String) : Bool :=
  s != "" && !s.toList.any (fun (c : Char) => c.toNat ≤ 0x20 || "<>\"{}|^`\\".toList.contains c)

/-- The root ACL resource of a new storage whose owner is configured: the
owner has `acl:Read`, `acl:Write` and `acl:Control` on the root and, by
`acl:default`, on everything below it. Web Access Control §3.2: "The ACL
resource of the root container MUST include an Authorization allowing the
acl:Control access privilege." `none` when the owner is not a safe
`IRIREF`. -/
def ownerRootAcl (baseIri owner : String) : Option String :=
  if iriRefSafe baseIri && iriRefSafe owner then
    some ("@prefix acl: <http://www.w3.org/ns/auth/acl#> .\n" ++
      "<" ++ baseIri ++ ".acl#owner> a acl:Authorization ;\n" ++
      "  acl:agent <" ++ owner ++ "> ;\n" ++
      "  acl:accessTo <" ++ baseIri ++ "> ;\n" ++
      "  acl:default <" ++ baseIri ++ "> ;\n" ++
      "  acl:mode acl:Read, acl:Write, acl:Control .\n")
  else none

/-! ## Configuration from JSON -/

/-- `{"issuers":[{"issuer":…, "jwks":{"keys":[…]}?}], "audience"?, "leeway"?}`.
Inline `jwks` fills the cache with no fetch. -/
def authzConfigOfJson (j : Json) (now : Nat) : Except String AuthzConfig := do
  let issuers ← match j.getArray? "issuers" with
    | none => .ok []
    | some items => items.mapM (fun it =>
        match it.getString? "issuer" with
        | none => .error "auth.issuers: member \"issuer\" is required"
        | some iss =>
            match it.field? "jwks" with
            | none => .ok { issuer := iss }
            | some jw =>
                match parseJwks? (toStringCompact jw) with
                | none => .error "auth.issuers: \"jwks\" is not a JWK Set"
                | some ks => .ok { issuer := iss, keys := ks, fetchedAt := some now })
  let num (n : String) (d : Nat) : Nat :=
    match j.field? n with
    | some (.number s) => (s.toNat?).getD d
    | _ => d
  .ok { issuers, audience := j.getString? "audience",
        leeway := num "leeway" 60, refreshInterval := num "refreshInterval" 60 }

/-! ## Theorems -/

/-- **Off is explicit.** Only the opt-in skips the decision. -/
theorem decide_insecure (V : Verifiers) (S : Store σ) (cfg : Config) (a : AuthzConfig)
    (now : Nat) (r : Request) (st : σ) (h : a.insecureNoAuth = true) :
    decide V S cfg a now r st = .proceed cfg.agent := by
  simp [decide, h]

/-- The default configuration is not the insecure mode. -/
theorem default_not_insecure : (default : AuthzConfig).insecureNoAuth = false := rfl

/-- **With no trusted issuer, no token is valid.** -/
theorem validateToken_no_issuers (V : Verifiers) (cfg : Config) (a : AuthzConfig) (now : Nat)
    (token : String) (h : a.issuers = []) (s i : String) :
    validateToken V cfg a now token ≠ .valid s i := by
  unfold validateToken
  split
  · simp
  · simp [h]

/-- **A valid token came from a trusted issuer, and a key of that issuer
verified its signature.** There is no path to `valid` that skips the
signature. -/
theorem validateToken_valid_verified {V : Verifiers} {cfg : Config} {a : AuthzConfig}
    {now : Nat} {token s i : String} (h : validateToken V cfg a now token = .valid s i) :
    ∃ c ti, unverifiedClaims? token = some c ∧
      a.issuers.find? (fun i => c.iss == some i.issuer) = some ti ∧
      anyKeyVerifies V (candidateKeys (headerKid? token) ti.keys) token = true ∧
      checkClaims cfg a now ti c = .valid s i := by
  unfold validateToken at h
  split at h
  · simp at h
  · rename_i c hc
    split at h
    · simp at h
    · rename_i ti hti
      refine ⟨c, ti, hc, hti, ?_⟩
      unfold validateWith at h
      dsimp only at h
      by_cases he : (candidateKeys (headerKid? token) ti.keys).isEmpty = true
      · simp only [he, if_true] at h
        split at h <;> simp at h
      · by_cases hv : anyKeyVerifies V (candidateKeys (headerKid? token) ti.keys) token = true
        · simp only [he, hv, if_true, if_false, Bool.false_eq_true] at h
          exact ⟨hv, h⟩
        · simp only [he, hv, if_false, Bool.false_eq_true] at h
          split at h <;> simp at h

/-- **A valid token passed the claims policy**: its issuer is the trusted
one, its audience contains the storage, and it had not expired. -/
theorem checkClaims_valid {cfg : Config} {a : AuthzConfig} {now : Nat} {ti : TrustedIssuer}
    {c : Claims} {s i : String} (h : checkClaims cfg a now ti c = .valid s i) :
    validate { now := now, leeway := a.leeway, issuer := ti.issuer,
               audience := storageIri cfg a } c = .ok ∧ i = ti.issuer ∧ c.sub = some s := by
  unfold checkClaims at h
  dsimp only at h
  split at h
  · rename_i hv
    split at h
    · simp at h
    · split at h
      · split at h
        · rename_i hs
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hv, rfl, hs⟩
        · simp at h
      · simp at h
  · simp at h

/-- **No credential, no issuers, no public grant: 401.** A storage with no
trusted issuer does not fall open: an anonymous request is decided by the
ACLs alone. -/
theorem authenticate_anonymous (V : Verifiers) (cfg : Config) (a : AuthzConfig) (now : Nat)
    (r : Request) (h : r.header? "authorization" = none) :
    authenticate V cfg a now r = .anonymous := by
  simp [authenticate, h]

end L4Factoidal.LWS.Authorization
