/-
L4Factoidal.Solid.Server.Oidc — Solid-OIDC access-token verification for
the Solid server, with DPoP proofs, decided in Lean.
https://github.com/danbri/factoidal/issues/899

## What the specifications require

Solid-OIDC (W3C Solid CG report, https://solidproject.org/TR/oidc):

  * §8.1: the token's `aud` "MUST include ... the string `solid`"; the
    `webid` claim "MUST be the user's WebID"; `iss` is the URL of the OP.
  * §8.1.1: "the verifying party MUST follow OpenID Connect Discovery 1.0
    to find an OP's signing keys (JWK)", and "MUST perform §6.1 OIDC
    Issuer Discovery using the value of the `webid` claim to dereference
    the WebID Profile Document": the profile must list the token's issuer
    with `solid:oidcIssuer`.
  * §9.3: a DPoP proof "valid according to [RFC 9449] Section 4.3 ... MUST
    be present", and the DPoP-bound token "MUST be validated according to
    [RFC 9449] Section 6".

OpenID Connect Discovery 1.0 §4: the metadata is at the issuer with
`/.well-known/openid-configuration` appended; §4.3: "The issuer value
returned MUST be identical to the Issuer URL that was used as the prefix
to /.well-known/openid-configuration to retrieve the configuration
information".

RFC 9449 §4.3 (`htm`, `htu`, `iat`, `jti`, signature by the `jwk`
header), §6 (`cnf.jkt` is the thumbprint of the proof key), §7.1 (`ath`,
the `DPoP` scheme), §11.1 (a `jti` seen before is a replay).

## What is decided where

The token, signature, claims, binding and proof checks are
`Auth.checkCredential`, unchanged. This module adds what a running server
needs around it: the trusted-issuer key cache filled by OpenID Connect
Discovery, the WebID profile check of §8.1.1, the `jti` replay cache, and
the RFC 9449 §7.1 challenge on a 401. The host fetches only the URLs a
`Decision.fetch` names, and `installFetched` decides what each fetched
document means.

## Off is explicit

`OidcConfig.insecureNoAuth` turns authentication off; the requester is
then the handle configuration's agent (`Methods.requesterOf`), as before.
With it off and no trusted issuer, no credential authenticates
(`authConfigFor_no_issuer_keys`).
-/
import L4Factoidal.Solid.Server.Auth
import L4Factoidal.LWS.Authorization
import L4Factoidal.Solid.Client.Profile

namespace L4Factoidal.Solid.Server.Oidc

open L4Factoidal.JSON
open L4Factoidal.JOSE
open L4Factoidal.LWS
open L4Factoidal.HTTP (Request Response)
open L4Factoidal.LWS.Authorization (TrustedIssuer KeyEntry parseJwks? candidateKeys headerKid?
  unverifiedClaims?)
open L4Factoidal.Solid.Server (ServerConfig Requester AuthConfig AuthResult AuthRefusal
  authenticate requesterOf stepAs)

/-! ## Configuration and state -/

/-- One WebID profile read for §8.1.1: the `solid:oidcIssuer` values. -/
structure ProfileEntry where
  webId : String
  issuers : List String
  fetchedAt : Nat
  deriving Repr, BEq

/-- The Solid-OIDC configuration of one storage, with the caches the
server keeps between requests. -/
structure OidcConfig where
  /-- The development mode with no authentication. -/
  insecureNoAuth : Bool := false
  issuers : List TrustedIssuer := []
  /-- Allowed clock skew for `exp`, seconds. -/
  leeway : Nat := 60
  /-- RFC 9449 §4.3 `iat` window, seconds. -/
  iatWindow : Nat := 60
  /-- Least time between two fetches of one document. -/
  refreshInterval : Nat := 60
  /-- Check §8.1.1: the WebID profile lists the token issuer. -/
  checkProfileIssuer : Bool := true
  profiles : List ProfileEntry := []
  /-- The `jti` values of accepted proofs, with their `iat`. -/
  seenJti : List (String × Int) := []

instance : Inhabited OidcConfig := ⟨{}⟩

/-- The audience Solid-OIDC §8.1 requires. -/
def solidAudience : String := "solid"

/-- OpenID Connect Discovery 1.0 §4 metadata URL. -/
def discoveryUrl (issuer : String) : String :=
  let trimmed := if issuer.endsWith "/" then (issuer.dropEnd 1).toString else issuer
  trimmed ++ "/.well-known/openid-configuration"

/-- The document a WebID names: the WebID with its fragment removed. -/
def profileDocument (webId : String) : String :=
  (webId.splitOn "#").headD webId

/-- Issuer identifiers compared with and without one trailing slash,
because a profile writes `<https://idp.example/>` for the issuer
`https://idp.example/` and some issuers omit the slash in one place. -/
def sameIssuer (a b : String) : Bool :=
  let t (s : String) := if s.endsWith "/" then (s.dropEnd 1).toString else s
  t a == t b

/-- Time gate for one cached document. -/
def mayFetchAt (oc : OidcConfig) (now : Nat) : Option Nat → Bool
  | none => true
  | some t => decide (t + max 1 oc.refreshInterval ≤ now)

/-! ## Reading the presented credential -/

/-- The `Authorization: DPoP <token>` value and the `DPoP` proof. -/
def credential? (r : Request) : Option (String × String) :=
  match r.header? "authorization" with
  | none => none
  | some a =>
      match Solid.Server.splitScheme a with
      | some (s, tok) => if s.toLower == "dpop" then (r.header? "dpop").map (tok, ·) else none
      | none => none

/-- The `jti` and `iat` of a DPoP proof, read to record it in the replay
cache once the proof has been accepted. -/
def proofJtiIat? (proof : String) : Option (String × Int) :=
  match preKey proof with
  | .error _ => none
  | .ok (c, _) =>
      match payloadClaims? c with
      | some { jti := some j, iat := some i, .. } => some (j, i)
      | _ => none

/-- The per-request authentication configuration `Auth.authenticate`
reads: the trusted issuer's cached keys, the claims policy with audience
`solid`, and the proof policy whose replay oracle is the `jti` cache. -/
def authConfigFor (_V : Verifiers) (oc : OidcConfig) (now : Nat) (ti : TrustedIssuer)
    (token : String) : AuthConfig :=
  { enforceAuth := true
    idpKeys := candidateKeys (headerKid? token) ti.keys
    policy := { now := now, leeway := oc.leeway, issuer := ti.issuer, audience := solidAudience }
    proofPolicy := { now := now, iatWindow := oc.iatWindow,
                     jtiFresh := fun j => !(oc.seenJti.any (·.1 == j)) }
    subjectIsWebId := false }

/-! ## The decision -/

/-- Why a credential was refused, beyond the reasons `Auth` names. -/
inductive Refusal where
  | auth (r : AuthRefusal)
  | untrustedIssuer (iss : Option String)
  | notJws
  | issuerNotInProfile (webId issuer : String)
  deriving Repr, BEq

/-- RFC 9449 §7.1 and RFC 6750 §3.1 error code. -/
def Refusal.errorCode : Refusal → String
  | .auth .missingProof => "invalid_dpop_proof"
  | .auth (.proofRefused _) => "invalid_dpop_proof"
  | .auth .malformedAuthorization => "invalid_request"
  | .auth (.wrongScheme _) => "invalid_request"
  | _ => "invalid_token"

/-- What to fetch. -/
inductive FetchKind where
  | issuer
  | profile
  deriving Repr, BEq, DecidableEq

def FetchKind.name : FetchKind → String
  | .issuer => "issuer"
  | .profile => "profile"

/-- What the server does with one request. -/
inductive Decision where
  /-- Run the request as this requester; record this proof `jti`. -/
  | proceed (who : Requester) (jti : Option (String × Int))
  | refuse (r : Refusal)
  /-- Fetch `url` (for the issuer or the WebID `key`), give it to
  `installFetched`, and decide again. -/
  | fetch (kind : FetchKind) (key url : String)
  deriving Inhabited

/-- The access token of the request, or the empty string. -/
def tokenOf (r : Request) : String := ((credential? r).map (·.1)).getD ""

/-- The trusted issuer the unverified `iss` names. The issuer is read
from the unverified token only to choose which trusted issuer's keys to
try; nothing is accepted before `Auth.checkCredential` verifies the
signature under those keys. -/
def pickIssuer (oc : OidcConfig) (token : String) : Option TrustedIssuer :=
  (unverifiedClaims? token).bind fun c => oc.issuers.find? (fun i => c.iss == some i.issuer)

/-- The server configuration `Auth.authenticate` runs under for `r`. -/
def requestConfig (V : Verifiers) (cfg : ServerConfig) (oc : OidcConfig) (now : Nat)
    (r : Request) : ServerConfig :=
  let ti : TrustedIssuer := (pickIssuer oc (tokenOf r)).getD { issuer := "" }
  { cfg with auth := authConfigFor V oc now ti (tokenOf r) }

/-- The decision once `Auth.authenticate` has answered `res`. -/
def afterAuth (oc : OidcConfig) (now : Nat) (r : Request) (res : AuthResult) : Decision :=
  let ti : TrustedIssuer := (pickIssuer oc (tokenOf r)).getD { issuer := "" }
  match res with
  | .refused (.noTrustedKey _) =>
      match (credential? r), unverifiedClaims? (tokenOf r), pickIssuer oc (tokenOf r) with
      | none, _, _ => .refuse (.auth .malformedAuthorization)
      | some _, none, _ => .refuse .notJws
      | some _, some c, none => .refuse (.untrustedIssuer c.iss)
      | some _, some _, some t =>
          -- No cached key verifies: an empty cache or a rotated key.
          if mayFetchAt oc now t.fetchedAt then .fetch .issuer t.issuer (discoveryUrl t.issuer)
          else .refuse (.auth (.noTrustedKey []))
  | .refused rf => .refuse (.auth rf)
  | .anonymous | .disabled => .proceed { webId := none, origin := r.header? "origin" } none
  | .authenticated w _ =>
      let ok := Decision.proceed { webId := some w, origin := r.header? "origin" }
                  (proofJtiIat? (((credential? r).map (·.2)).getD ""))
      if !oc.checkProfileIssuer then ok
      else match oc.profiles.find? (·.webId == w) with
        | some p =>
            if p.issuers.any (sameIssuer ti.issuer) then ok
            else if mayFetchAt oc now (some p.fetchedAt) then
              .fetch .profile w (profileDocument w)
            else .refuse (.issuerNotInProfile w ti.issuer)
        | none => .fetch .profile w (profileDocument w)

/-- Authentication of one request. -/
def authDecision (V : Verifiers) (cfg : ServerConfig) (oc : OidcConfig) (now : Nat)
    (r : Request) : Decision :=
  if oc.insecureNoAuth then .proceed (requesterOf cfg r) none
  else match r.header? "authorization" with
    | none => .proceed { webId := none, origin := r.header? "origin" } none
    | some _ => afterAuth oc now r (authenticate V (requestConfig V cfg oc now r) r)

/-- Record an accepted proof, and forget proofs whose `iat` is outside the
window, which `DPoP.validateProof` refuses anyway. -/
def remember (oc : OidcConfig) (now : Nat) (j : Option (String × Int)) : OidcConfig :=
  let keep := oc.seenJti.filter (fun (_, i) => decide ((now : Int) - oc.iatWindow ≤ i))
  { oc with seenJti := match j with | some e => e :: keep | none => keep }

/-- The RFC 9449 §7.1 challenge. -/
def challengeValue (err : Option String) : String :=
  "DPoP algs=\"ES256 RS256 EdDSA\"" ++
    (match err with | none => "" | some e => ", error=\"" ++ e ++ "\"")

/-- Add the challenge to a 401 answer. -/
def withChallenge (err : Option String) (resp : Response) : Response :=
  if resp.status == 401 then
    { resp with headers := resp.headers ++ [("www-authenticate", challengeValue err)] }
  else resp

variable {σ : Type}

/-- One authenticated Solid step: the decision, then `Methods.stepAs` as
the requester it names. A `fetch` decision is returned to the host. -/
def authenticatedStep (V : Verifiers) (S : Store σ) (cfg : ServerConfig) (oc : OidcConfig)
    (now : Nat) (r : Request) (st : σ) :
    Sum (FetchKind × String × String) (Response × σ × OidcConfig) :=
  match authDecision V cfg oc now r with
  | .fetch k key url => .inl (k, key, url)
  | .refuse rf =>
      .inr (Solid.Server.withCors r
              (withChallenge (some rf.errorCode)
                 ⟨401, [("content-type", "text/plain")], "Unauthorized"⟩), st, oc)
  | .proceed who j =>
      let (resp, st') := stepAs S cfg who r st
      .inr ((if oc.insecureNoAuth then resp else withChallenge none resp), st',
            remember oc now j)

/-! ## Fetched documents -/

private def updateIssuer (oc : OidcConfig) (iss : String)
    (f : TrustedIssuer → TrustedIssuer) : OidcConfig :=
  { oc with issuers := oc.issuers.map (fun i => if i.issuer == iss then f i else i) }

/-- What a fetched document did. -/
inductive Fetched where
  | next (url : String)
  | installed (count : Nat)
  | refused (why : String)
  deriving Repr, BEq

/-- Interpret one fetched document. For an issuer: its OpenID Connect
Discovery metadata (§4.3 issuer identity check), then its JWK Set. For a
WebID: its profile document, read for `solid:oidcIssuer`. A URL that no
decision named is refused. A failed fetch stamps the time, so a broken
document is not fetched on every request. -/
def installFetched (oc : OidcConfig) (kind : FetchKind) (key url : String) (status : Nat)
    (body : String) (now : Nat) : OidcConfig × Fetched :=
  match kind with
  | .profile =>
      if url != profileDocument key then (oc, .refused "this URL was not asked for")
      else
        let issuers := if status == 200 then
            (L4Factoidal.Solid.Client.readProfile key url body).oidcIssuers else []
        let others := oc.profiles.filter (·.webId != key)
        ({ oc with profiles := { webId := key, issuers, fetchedAt := now } :: others },
         if status == 200 then .installed issuers.length
         else .refused s!"{url} answered {status}")
  | .issuer =>
      match oc.issuers.find? (fun i => i.issuer == key) with
      | none => (oc, .refused "not a trusted issuer")
      | some ti =>
          let stamp := updateIssuer oc key (fun i => { i with fetchedAt := some now })
          if status != 200 then (stamp, .refused s!"{url} answered {status}")
          else if url == discoveryUrl key then
            match parseJson? body with
            | none => (stamp, .refused "issuer metadata is not JSON")
            | some j =>
                if j.getString? "issuer" != some key then
                  (stamp, .refused "issuer metadata names a different issuer (OpenID Connect Discovery 1.0 §4.3)")
                else match j.getString? "jwks_uri" with
                  | none => (stamp, .refused "issuer metadata has no jwks_uri")
                  | some u => (updateIssuer oc key (fun i => { i with jwksUri := some u }), .next u)
          else if ti.jwksUri == some url then
            match parseJwks? body with
            | none => (stamp, .refused "not a JWK Set")
            | some ks =>
                (updateIssuer oc key (fun i => { i with keys := ks, fetchedAt := some now }),
                 .installed ks.length)
          else (oc, .refused "this URL was not asked for")

/-! ## Configuration from JSON -/

/-- `{"issuers":[{"issuer":…, "jwks":{…}?}], "leeway"?, "iatWindow"?,
"refreshInterval"?, "checkProfileIssuer"?}`; the issuer list is read by
`LWS.Authorization.authzConfigOfJson`. -/
def oidcConfigOfJson (j : Json) (now : Nat) : Except String OidcConfig := do
  let a ← L4Factoidal.LWS.Authorization.authzConfigOfJson j now
  let iw := match j.field? "iatWindow" with
    | some (.number s) => (s.toNat?).getD 60
    | _ => 60
  .ok { issuers := a.issuers, leeway := a.leeway, refreshInterval := a.refreshInterval,
        iatWindow := iw, checkProfileIssuer := (j.getBool? "checkProfileIssuer").getD true }

/-! ## Theorems -/

/-- **Off is explicit**: only the opt-in takes the handle's requester. -/
theorem decide_insecure (V : Verifiers) (cfg : ServerConfig) (oc : OidcConfig) (now : Nat)
    (r : Request) (h : oc.insecureNoAuth = true) :
    authDecision V cfg oc now r = .proceed (requesterOf cfg r) none := by
  simp [authDecision, h]

/-- **No credential, no WebID.** -/
theorem decide_anonymous (V : Verifiers) (cfg : ServerConfig) (oc : OidcConfig) (now : Nat)
    (r : Request) (h0 : oc.insecureNoAuth = false) (h : r.header? "authorization" = none) :
    authDecision V cfg oc now r = .proceed { webId := none, origin := r.header? "origin" } none := by
  simp [authDecision, h0, h]

/-- Only an authenticated result names a WebID. -/
theorem afterAuth_webId {oc : OidcConfig} {now : Nat} {r : Request} {res : AuthResult}
    {w : String} {o : Option String} {j : Option (String × Int)}
    (h : afterAuth oc now r res = .proceed { webId := some w, origin := o } j) :
    ∃ jkt, res = .authenticated w jkt := by
  unfold afterAuth at h
  cases res with
  | disabled => simp at h
  | anonymous => simp at h
  | refused rf =>
      cases rf
      all_goals simp at h
      all_goals (repeat' split at h) <;> simp at h
  | authenticated w' jkt =>
      refine ⟨jkt, ?_⟩
      simp only at h
      repeat' split at h
      all_goals simp_all

/-- **A WebID comes only from an authenticated credential.** If the
decision names a WebID with authentication on, `Auth.authenticate`
authenticated the request under the trusted issuer's keys, the `solid`
audience and the replay oracle, so every check of
`Auth.checkCredential` passed (`checkCredential_authenticated_proof_ok`,
`_claims_ok`, `_bound`, `_webid`). -/
theorem authDecision_webId_authenticated {V : Verifiers} {cfg : ServerConfig}
    {oc : OidcConfig} {now : Nat} {r : Request} {w : String} {o : Option String}
    {j : Option (String × Int)} (h0 : oc.insecureNoAuth = false)
    (h : authDecision V cfg oc now r = .proceed { webId := some w, origin := o } j) :
    ∃ jkt, authenticate V (requestConfig V cfg oc now r) r = .authenticated w jkt := by
  unfold authDecision at h
  simp only [h0, Bool.false_eq_true, if_false] at h
  split at h
  · simp at h
  · exact afterAuth_webId h

/-- The configuration `authDecision` authenticates under requires the
audience `solid` (Solid-OIDC §8.1) and pins the trusted issuer. -/
theorem requestConfig_audience (V : Verifiers) (cfg : ServerConfig) (oc : OidcConfig)
    (now : Nat) (r : Request) :
    (requestConfig V cfg oc now r).auth.policy.audience = solidAudience ∧
    (requestConfig V cfg oc now r).auth.enforceAuth = true := by
  simp [requestConfig, authConfigFor]

/-- **With no trusted issuer and authentication on, no request is
authenticated**: the key list `authConfigFor` builds is empty, and
`Auth.checkCredential_no_keys` refuses every credential. -/
theorem authConfigFor_no_issuer_keys (V : Verifiers) (oc : OidcConfig) (now : Nat)
    (token : String) :
    (authConfigFor V oc now { issuer := "" } token).idpKeys = [] := by
  simp [authConfigFor, candidateKeys]
  split <;> simp

/-- **The replay cache holds every accepted `jti`** whose `iat` is inside
the window, so a second presentation of the same proof meets
`jtiFresh = false`. -/
theorem remember_holds (oc : OidcConfig) (now : Nat) (ji : String) (i : Int) :
    ((remember oc now (some (ji, i))).seenJti.any (·.1 == ji)) = true := by
  simp [remember]

theorem remember_refuses_replay (V : Verifiers) (oc : OidcConfig) (now now' : Nat)
    (ji : String) (i : Int) (ti : TrustedIssuer) (token : String) :
    (authConfigFor V (remember oc now (some (ji, i))) now' ti token).proofPolicy.jtiFresh ji
      = false := by
  simp [authConfigFor, remember]

/-! ## Fixtures (header reading; signatures are exercised by the host
suite `tests/solid/server/oidc.mjs`) -/

private def req (headers : List (String × String)) : Request :=
  { method := "GET", path := "/r", queryStr := "", headers := headers }

private def stubV : Verifiers :=
  { es256 := fun _ _ _ => true, rs256 := fun _ _ _ _ => true, eddsa := fun _ _ _ => true }

private def isRefuse : Decision → Bool
  | .refuse _ => true
  | _ => false

private def isAnon : Decision → Bool
  | .proceed { webId := none, .. } none => true
  | _ => false

#guard isAnon (authDecision stubV {} {} 0 (req []))
#guard isRefuse (authDecision stubV {} {} 0 (req [("authorization", "Bearer abc")]))
#guard isRefuse (authDecision stubV {} {} 0 (req [("authorization", "DPoP abc")]))
#guard isRefuse (authDecision stubV {} {} 0 (req [("authorization", "DPoP abc"), ("dpop", "x")]))
#guard match authDecision stubV { lws := { agent := some "https://a/#me" } }
          { insecureNoAuth := true } 0 (req [("authorization", "DPoP abc")]) with
        | .proceed { webId := some "https://a/#me", .. } none => true
        | _ => false
#guard discoveryUrl "https://idp.example/" == "https://idp.example/.well-known/openid-configuration"
#guard discoveryUrl "https://idp.example" == "https://idp.example/.well-known/openid-configuration"
#guard profileDocument "https://a.example/profile/card#me" == "https://a.example/profile/card"
#guard sameIssuer "https://idp.example/" "https://idp.example"
#guard !sameIssuer "https://idp.example/" "https://evil.example/"
-- A URL no decision named is refused.
#guard ((installFetched { issuers := [{ issuer := "https://i/" }] } .issuer "https://i/"
          "https://elsewhere/" 200 "{}" 0).2 == .refused "this URL was not asked for")
#guard ((installFetched {} .profile "https://a/card#me" "https://b/card" 200 "" 0).2
          == .refused "this URL was not asked for")
-- Discovery: the issuer named in the metadata must be the one asked.
#guard ((installFetched { issuers := [{ issuer := "https://i/" }] } .issuer "https://i/"
          "https://i/.well-known/openid-configuration" 200
          "{\"issuer\":\"https://j/\",\"jwks_uri\":\"https://i/jwks\"}" 0).2
        == .refused "issuer metadata names a different issuer (OpenID Connect Discovery 1.0 §4.3)")
#guard ((installFetched { issuers := [{ issuer := "https://i/" }] } .issuer "https://i/"
          "https://i/.well-known/openid-configuration" 200
          "{\"issuer\":\"https://i/\",\"jwks_uri\":\"https://i/jwks\"}" 0).2
        == .next "https://i/jwks")
-- A profile listing the issuer.
#guard ((installFetched {} .profile "https://a/card#me" "https://a/card" 200
          "<#me> <http://www.w3.org/ns/solid/terms#oidcIssuer> <https://i/> ." 0).1.profiles
        == [{ webId := "https://a/card#me", issuers := ["https://i/"], fetchedAt := 0 }])
-- The replay window forgets old proofs and keeps fresh ones.
#guard (remember { seenJti := [("old", 0), ("new", 100)] } 120 none).seenJti == [("new", 100)]

end L4Factoidal.Solid.Server.Oidc
