/-
L4Factoidal.Authz.Theorems — what the authorization server component
guarantees (https://github.com/danbri/factoidal/issues/916).

Every theorem holds for EVERY `Crypto` record: nothing here depends on what
the HACL\* primitives compute.

The two theorems about an issued token (`issueToken_verifies_published`,
`issueToken_audience_exact`, and their token-endpoint forms) hold BECAUSE
OF THE RUN-TIME CHECK `selfCheck` in `issueToken`: the server answers 500
and gives no token when its own token does not verify under its published
key or does not carry exactly the requested audience. No theorem here says
that the check never fails; that proof (a JSON print/parse and compact JWS
round trip) is https://github.com/danbri/factoidal/issues/927.

The theorems about subject tokens are structural: a token is issued only
after `validateSubject` answered `valid`, which only `finish` can answer,
and only after `JOSE.verifyCompact` verified the subject token under the
key its suite selected.
-/
import L4Factoidal.Authz.Server

namespace L4Factoidal.Authz

open L4Factoidal.JSON
open L4Factoidal.JOSE

/-! ## Issued tokens (by the run-time check) -/

theorem issueToken_selfCheck {C : Crypto} {cfg : AuthzConfig} {ks : KeyStore} {now : Nat}
    {rnd : ByteArray} {s cl res t : String}
    (h : issueToken C cfg ks now rnd s cl res = .ok t) :
    selfCheck C cfg ks now t s res = true := by
  unfold issueToken at h
  split at h
  · simp at h
  · simp only at h
    split at h
    · simp at h
    · split at h
      · rename_i hc
        simp only [Except.ok.injEq] at h
        subst h
        exact hc
      · simp at h

/-- **An issued token verifies under a key of the published JWK Set**: the
key with the token's `kid`, read back from the JWK Set text this server
serves, with `JOSE.verifyCompact`. By the run-time check (issue 927). -/
theorem issueToken_verifies_published {C : Crypto} {cfg : AuthzConfig} {ks : KeyStore}
    {now : Nat} {rnd : ByteArray} {s cl res t : String}
    (h : issueToken C cfg ks now rnd s cl res = .ok t) :
    ∃ kid jwk, headerKid? t = some kid ∧ (some kid, jwk) ∈ publishedKeys cfg ks now ∧
      verifyCompact C.verifiers jwk t = .verified := by
  have hc := issueToken_selfCheck h
  unfold selfCheck at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hv, _⟩ := hc
  unfold verifiesPublished at hv
  split at hv
  · rename_i kid hk
    obtain ⟨e, he, hb⟩ := List.any_eq_true.mp hv
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
    obtain ⟨h1, h2⟩ := hb
    refine ⟨kid, e.2, hk, ?_, h2⟩
    have : e = (some kid, e.2) := by cases e; simp_all
    rw [this] at he
    exact he
  · simp at hv

/-- **An issued token carries exactly the requested audience**, this
issuer and the validated subject. By the run-time check (issue 927). -/
theorem issueToken_audience_exact {C : Crypto} {cfg : AuthzConfig} {ks : KeyStore}
    {now : Nat} {rnd : ByteArray} {s cl res t : String}
    (h : issueToken C cfg ks now rnd s cl res = .ok t) :
    ∃ c, claimsOf? t = some c ∧ c.getString? "iss" = some cfg.issuer ∧
      c.getString? "sub" = some s ∧ (c.field? "aud").bind audience? = some [res] := by
  have hc := issueToken_selfCheck h
  unfold selfCheck at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨_, hx⟩ := hc
  unfold claimsExact at hx
  split at hx
  · rename_i c hcl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    exact ⟨c, hcl, hx.1.1, hx.1.2, hx.2⟩
  · simp at hx

/-! ## The token endpoint -/

/-- The token request names a configured resource. -/
theorem tokenRequest_resource {cfg : AuthzConfig} {form : List (String × String)}
    {tr : TokenRequest} (h : tokenRequest cfg form = .ok tr) :
    cfg.resources.contains tr.resource = true := by
  unfold tokenRequest at h
  split at h
  · simp at h
  · split at h
    · rename_i tr' _ hc
      simp only [Except.ok.injEq] at h
      subst h
      exact hc
    · simp at h

/-- `exchange` answers `issue` only for a subject token that validated. -/
theorem exchange_issue_valid {ctx : Ctx} {cfg : AuthzConfig} {form : List (String × String)}
    {s c res : String} (h : exchange ctx cfg form = .issue s c res) :
    ∃ tr, tokenRequest cfg form = .ok tr ∧ tr.resource = res ∧
      validateSubject ctx tr.subjectTokenType tr.subjectToken = .valid s c := by
  unfold exchange at h
  split at h
  · simp at h
  · rename_i tr htr
    split at h
    · rename_i s' c' hv
      simp only [Exchange.issue.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨tr, htr, rfl, hv⟩
    · simp at h
    · simp at h

/-- **A token is issued only after the subject token validated**, for a
configured resource the request named, and the token is the one
`issueToken` checked. -/
theorem tokenOutcome_issued {C : Crypto} {cfg : AuthzConfig} {st : AuthzState} {now : Nat}
    {rnd : ByteArray} {form : List (String × String)} {resp : L4Factoidal.HTTP.Response} {t s cl res : String}
    (h : tokenOutcome C cfg st now rnd form = .issued resp t s cl res) :
    (∃ tr, tokenRequest cfg form = .ok tr ∧ tr.resource = res ∧
      cfg.resources.contains res = true ∧
      validateSubject (cfg.ctx C st now) tr.subjectTokenType tr.subjectToken = .valid s cl) ∧
    issueToken C cfg st.keys now rnd s cl res = .ok t := by
  unfold tokenOutcome at h
  split at h
  · simp at h
  · simp at h
  · rename_i s' cl' res' hx
    split at h
    · rename_i t' ht
      simp only [TokenOutcome.issued.injEq] at h
      obtain ⟨_, rfl, rfl, rfl, rfl⟩ := h
      obtain ⟨tr, htr, hres, hv⟩ := exchange_issue_valid hx
      refine ⟨⟨tr, htr, hres, ?_, hv⟩, ht⟩
      rw [← hres]; exact tokenRequest_resource htr
    · simp at h

/-- **A subject token that fails validation never yields an access token.** -/
theorem exchange_refused_no_token {C : Crypto} {cfg : AuthzConfig} {st : AuthzState} {now : Nat}
    {rnd : ByteArray} {form : List (String × String)} {tr : TokenRequest} {w : String}
    (htr : tokenRequest cfg form = .ok tr)
    (hv : validateSubject (cfg.ctx C st now) tr.subjectTokenType tr.subjectToken = .refused w)
    (resp : L4Factoidal.HTTP.Response) (t s cl res : String) :
    tokenOutcome C cfg st now rnd form ≠ .issued resp t s cl res := by
  intro h
  obtain ⟨⟨tr', htr', _, _, hv'⟩, _⟩ := tokenOutcome_issued h
  rw [htr] at htr'
  simp only [Except.ok.injEq] at htr'
  subst htr'
  rw [hv] at hv'
  simp at hv'

/-- The endpoint form of `issueToken_verifies_published`. -/
theorem tokenOutcome_issued_verifies_published {C : Crypto} {cfg : AuthzConfig}
    {st : AuthzState} {now : Nat} {rnd : ByteArray} {form : List (String × String)}
    {resp : L4Factoidal.HTTP.Response} {t s cl res : String}
    (h : tokenOutcome C cfg st now rnd form = .issued resp t s cl res) :
    ∃ kid jwk, headerKid? t = some kid ∧ (some kid, jwk) ∈ publishedKeys cfg st.keys now ∧
      verifyCompact C.verifiers jwk t = .verified :=
  issueToken_verifies_published (tokenOutcome_issued h).2

/-- The endpoint form of `issueToken_audience_exact`: `aud` is exactly the
resource the request named, which is a configured resource. -/
theorem tokenOutcome_issued_audience_exact {C : Crypto} {cfg : AuthzConfig}
    {st : AuthzState} {now : Nat} {rnd : ByteArray} {form : List (String × String)}
    {resp : L4Factoidal.HTTP.Response} {t s cl res : String}
    (h : tokenOutcome C cfg st now rnd form = .issued resp t s cl res) :
    ∃ tr c, tokenRequest cfg form = .ok tr ∧ tr.resource = res ∧
      cfg.resources.contains res = true ∧ claimsOf? t = some c ∧
      (c.field? "aud").bind audience? = some [res] ∧ c.getString? "sub" = some s := by
  obtain ⟨⟨tr, htr, hres, hin, _⟩, hi⟩ := tokenOutcome_issued h
  obtain ⟨c, hc, _, hs, ha⟩ := issueToken_audience_exact hi
  exact ⟨tr, c, htr, hres, hin, hc, ha, hs⟩

/-! ## Subject tokens, per suite -/

theorem parseJwt_token {tok : String} {p : Parsed} (h : parseJwt tok = .ok p) : p.token = tok := by
  unfold parseJwt at h
  split at h
  · simp at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · split at h
        · simp only [ite_true, Except.ok.injEq] at h; subst h; rfl
        · simp at h
      · simp at h

/-- The CID suite answers `valid` only through its key and the signature. -/
theorem validateSelfIssued_valid {ctx : Ctx} {p : Parsed} {s c : String}
    (h : validateSelfIssued ctx p = .valid s c) :
    ∃ k, selfIssuedSubject ctx p = .ok s ∧ selfIssuedKey ctx p s = .key k ∧
      verifyCompact ctx.C.verifiers k p.token = .verified ∧ c = s := by
  unfold validateSelfIssued at h
  split at h
  · simp at h
  · rename_i sub hs
    obtain ⟨k, hk, hv, rfl, rfl⟩ := withKey_valid h
    exact ⟨k, hs, hk, hv, rfl⟩

/-- The OpenID Connect suite answers `valid` only through its key and the
signature. -/
theorem validateIdToken_valid {ctx : Ctx} {p : Parsed} {s c : String}
    (h : validateIdToken ctx p = .valid s c) :
    ∃ iss k, idTokenClaims ctx p = .ok (iss, s, c) ∧
      oidcKey ctx iss s (p.header.getString? "kid") = .key k ∧
      verifyCompact ctx.C.verifiers k p.token = .verified := by
  unfold validateIdToken at h
  split at h
  · simp at h
  · rename_i iss sub azp hs
    obtain ⟨k, hk, hv, rfl, rfl⟩ := withKey_valid h
    exact ⟨iss, k, hs, hk, hv⟩

/-- **Every valid subject token verified under the key its suite chose.** -/
theorem validateSubject_valid_verified {ctx : Ctx} {tt tok s c : String}
    (h : validateSubject ctx tt tok = .valid s c) :
    ∃ p k, parseJwt tok = .ok p ∧ verifyCompact ctx.C.verifiers k tok = .verified := by
  unfold validateSubject at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp at h
      · rename_i p hp
        have ht := parseJwt_token hp
        split at h
        · obtain ⟨k, _, _, hv, _⟩ := validateSelfIssued_valid h
          exact ⟨p, k, hp, ht ▸ hv⟩
        · obtain ⟨_, k, _, _, hv⟩ := validateIdToken_valid h
          exact ⟨p, k, hp, ht ▸ hv⟩
    · simp at h

/-- **did:key subject**: the key is the one the identifier encodes, the
`kid` names its one verification method, and the client is the subject. -/
theorem didKey_valid_verified {ctx : Ctx} {p : Parsed} {s c : String}
    (h : validateSelfIssued ctx p = .valid s c) (hd : s.startsWith didKeyPrefix = true) :
    ∃ k mb, didKeyJwk? ctx.C s = some (k, mb) ∧
      (p.header.getString? "kid" = some (s ++ "#" ++ mb) ∨ p.header.getString? "kid" = some mb) ∧
      verifyCompact ctx.C.verifiers k p.token = .verified ∧ c = s := by
  obtain ⟨k, _, hk, hv, rfl⟩ := validateSelfIssued_valid h
  unfold selfIssuedKey at hk
  rw [if_pos hd] at hk
  split at hk
  · simp at hk
  · rename_i k' mb hj
    split at hk
    · rename_i hkid
      simp only [KeyFound.key.injEq] at hk
      subst hk
      simp only [Bool.or_eq_true, beq_iff_eq] at hkid
      exact ⟨k', mb, hj, hkid, hv, rfl⟩
    · simp at hk

/-- **CID subject with an HTTPS identifier**: the key came from `cidKey`
with the token's `kid`. -/
theorem cid_valid_verified {ctx : Ctx} {p : Parsed} {s c : String}
    (h : validateSelfIssued ctx p = .valid s c) (hd : s.startsWith didKeyPrefix = false) :
    ∃ kid k, p.header.getString? "kid" = some kid ∧ cidKey ctx s kid = .key k ∧
      verifyCompact ctx.C.verifiers k p.token = .verified ∧ c = s := by
  obtain ⟨k, _, hk, hv, rfl⟩ := validateSelfIssued_valid h
  unfold selfIssuedKey at hk
  rw [if_neg (by simp [hd])] at hk
  split at hk
  · simp at hk
  · rename_i kid hkid
    exact ⟨kid, k, hkid, hk, hv, rfl⟩

/-- **What `cidKey` established** (CID 1.0 §3.3): the subject's document
names the subject as its `id`, the method is one `authentication` names, its
`controller` is the subject, it is in force, and the key is its key. -/
theorem cidKey_method {ctx : Ctx} {sub kid : String} {k : Jwk}
    (h : cidKey ctx sub kid = .key k) :
    ∃ text doc m, lookup ctx.policy ctx.fs ctx.now sub cidAccept = .doc text ∧
      parseJson? text = some doc ∧ doc.getString? "id" = some sub ∧
      m ∈ authenticationMethods doc sub ∧ idOf sub m = some (methodIdOf sub kid) ∧
      (m.getString? "controller").map (resolveRef sub) = some sub ∧
      methodInForce ctx.now m = true ∧ methodKey? ctx.C m = some k := by
  unfold cidKey at h
  split at h
  · simp at h
  · simp at h
  · rename_i text hl
    split at h
    · simp at h
    · rename_i doc hdoc
      split at h
      · rename_i k' hs
        simp only [KeyFound.key.injEq] at h
        subst h
        unfold selectMethod at hs
        split at hs
        · simp at hs
        · rename_i hid
          split at hs
          · simp at hs
          · rename_i m hm
            have hmem := List.mem_of_find?_eq_some hm
            have hid' : idOf sub m = some (methodIdOf sub kid) := by
              simpa using List.find?_some hm
            split at hs
            · simp at hs
            · rename_i hctl
              split at hs
              · simp at hs
              · rename_i hin
                split at hs
                · rename_i k'' hk
                  simp only [Except.ok.injEq] at hs
                  subst hs
                  refine ⟨text, doc, m, hl, hdoc, ?_, hmem, hid', ?_, ?_, hk⟩
                  · simpa using hid
                  · simpa using hctl
                  · simpa using hin
                · simp at hs
      · simp at h

/-- **What `oidcKey` established** (lws10-authn-openid, "Authentication
Credential Validation"): the subject's document has the subject as `id` and
names `iss` as an `lws#OpenIdProvider` service. -/
theorem oidcKey_named_provider {ctx : Ctx} {iss sub : String} {kid : Option String} {k : Jwk}
    (h : oidcKey ctx iss sub kid = .key k) :
    ∃ text doc, lookup ctx.policy ctx.fs ctx.now sub cidAccept = .doc text ∧
      parseJson? text = some doc ∧ doc.getString? "id" = some sub ∧
      namesProvider doc iss = true := by
  unfold oidcKey at h
  split at h
  · simp at h
  · simp at h
  · rename_i text hl
    split at h
    · simp at h
    · rename_i doc hdoc
      split at h
      · simp at h
      · rename_i hid
        split at h
        · simp at h
        · rename_i hn
          refine ⟨text, doc, hl, hdoc, ?_, ?_⟩
          · simpa using hid
          · simpa using hn

/-- **OpenID Connect**: the key came from `oidcKey` for the token's `iss`,
and the client is `azp`. -/
theorem oidc_valid_named_provider {ctx : Ctx} {p : Parsed} {s c : String}
    (h : validateIdToken ctx p = .valid s c) :
    ∃ iss k text doc, idTokenClaims ctx p = .ok (iss, s, c) ∧
      oidcKey ctx iss s (p.header.getString? "kid") = .key k ∧
      verifyCompact ctx.C.verifiers k p.token = .verified ∧
      lookup ctx.policy ctx.fs ctx.now s cidAccept = .doc text ∧
      parseJson? text = some doc ∧ doc.getString? "id" = some s ∧ namesProvider doc iss = true := by
  obtain ⟨iss, k, hc, hk, hv⟩ := validateIdToken_valid h
  obtain ⟨text, doc, hl, hd, hid, hn⟩ := oidcKey_named_provider hk
  exact ⟨iss, k, text, doc, hc, hk, hv, hl, hd, hid, hn⟩

/-! ## Keys and metadata -/

/-- **The JWK Set holds no private member** (RFC 7517 §5; `d` of RFC 7518
§6.2.2.1 and RFC 8037 §2 never leaves the key file). -/
theorem publicJson_no_private_member (k : KeyRec) : hasPrivateMember (publicJson k) = false := by
  cases h : k.alg <;>
    simp [publicJson, h, hasPrivateMember, privateMemberNames, Json.field?, List.find?]

theorem jwks_no_private_member (s : KeyStore) (now grace : Nat) :
    ∀ j ∈ (published s now grace).map publicJson, hasPrivateMember j = false := by
  intro j hj
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hj
  exact publicJson_no_private_member k

/-- RFC 8414 §3.3: the metadata's `issuer` is the issuer identifier. -/
theorem metadata_issuer_eq (cfg : AuthzConfig) :
    (metadataJson cfg).getString? "issuer" = some cfg.issuer := by
  simp [metadataJson, Json.getString?, Json.field?, List.find?, Json.asString?]

/-- **Rotation keeps the previous key published** until `now + grace`, so
a token it signed still validates (lws10-core "Token Validation by a
Storage Server": "MUST support key rotation"). -/
theorem rotate_keeps_previous {s : KeyStore} {k x : KeyRec} {now grace t : Nat}
    (hx : x ∈ s.keys) (hr : x.retired = none) (ht : t < now + grace) (htn : now ≤ t) :
    { x with retired := some now } ∈ published (rotateWith s k now grace) t grace := by
  unfold published rotateWith
  simp only [List.mem_filter, List.mem_cons, List.mem_map]
  refine ⟨Or.inr ⟨?_, ?_⟩, ?_⟩
  · exact ⟨x, hx, by simp [hr]⟩
  · simp [stillPublished]; omega
  · simp [stillPublished]; omega

end L4Factoidal.Authz
