/-
L4Factoidal.Authz.CredentialMatch — access for "a holder of a credential of
type X from an issuer on trust list Y, not revoked".

Draft, theorem first. The theorems below are the specification; the
definitions are the smallest that make them true. Read the theorems' doc
comments first.

## The use case

An access rule says: the folder `MedicalData/` may be read by anyone who
presents a current credential of type `MedicalLicence` from an issuer that
the pod owner trusts for that type, with the claim `standing` equal to
`full`. Nobody is named in advance. A person's AI agent may act for them
under a delegation that can only narrow what they may do.

## What is decided here, and what is not

Decided here, from records the host hands over:

* Which credentials satisfy a matcher (`credMatches`), and whether a
  presentation does (`satisfies`).
* Which modes an access rule list allows (`allowed`), directly or through a
  delegation (`delegatedAllowed`).

Not decided here (each has its own module and its own theorems):

* Signatures. A `Credential` is what a format verifier returns after the
  issuer's proof checked: VC Data Integrity (`VC/Cryptosuite.lean`),
  VC-JOSE, or a selective-disclosure format. A `Presentation` is what is
  left after the holder's proof over (audience, nonce, credentials) checked.
* Status lists. `Ctx.status` is the result of `VC/StatusList.lean`'s
  `validate` on a list the host fetched, with the time it was fetched.
* Who the requester is. `Ctx.bound` is `Identity.Binding.bound`, mapped to
  agent IRIs.
* The clock. `Ctx.now` is the host's.

## What this cannot do (by design, stated so nobody assumes otherwise)

* It does not know the world. "MedicalLicence from issuer I" means only
  that I signed it. Whether I is the right authority is the trust list,
  which is the owner's policy decision. A wrong trust list is a wrong
  policy, and no theorem here can catch it.
* It cannot stop a holder sharing their key, their device or the data
  they read. Access is not control of use.
* Revocation is not instant. A revoked credential still satisfies ends the
  status answer in hand is older than `maxStatusAge`, or a fresh fetch
  says revoked; then any token issued on it lasts ends it expires.
* No deny rules. As in WAC, rules only add access; "everyone except
  suspended doctors" is written as "doctors whose status is valid".
* No equivalence across issuers' vocabularies. Two regulators' type IRIs
  are two types unless the matcher lists both (as two rules).
* No privacy from the server: the server sees the credentials presented.
  `ignores_unnamed_claims` shows that only the named claims matter, so a
  selective-disclosure format can reveal only those; unlinkable proofs are
  out of scope.

No `sorry`, no `axiom`, no `partial`. Core Lean only.
-/

namespace L4Factoidal.Authz.CredentialMatch

/-- A credential whose issuer proof has been verified. `claims` are the
disclosed claims as (path, value), e.g. ("standing", "full"). `statusRef`
names its status list entry, if it has one. Times are seconds. -/
structure Credential where
  id : String
  issuer : String
  types : List String
  subject : String
  claims : List (String × String)
  validFrom : Nat
  validUntil : Option Nat
  statusRef : Option String
deriving DecidableEq, Repr

inductive Status where
  | valid | revoked | suspended | unknown
deriving DecidableEq, Repr

/-- A status list answer for one entry, and when the list was fetched. -/
structure StatusAnswer where
  status : Status
  fetchedAt : Nat
deriving DecidableEq, Repr

/-- One trust list entry: this issuer may vouch for these credential types,
between these times. -/
structure TrustEntry where
  issuer : String
  types : List String
  since : Nat
  ends : Option Nat
deriving DecidableEq, Repr

/-- The matcher of an access rule. Every type in `types` is required; each
`claims` entry requires the credential to disclose that path with one of
the allowed values. -/
structure Matcher where
  types : List String
  trust : List TrustEntry
  claims : List (String × List String)
  /-- How old a status answer may be. -/
  maxStatusAge : Nat
  /-- A credential with no status entry is accepted only if its whole
  validity is at most this long (a short-lived credential). -/
  maxLifeWithoutStatus : Nat
deriving Repr

/-- A presentation whose holder proof has been verified. -/
structure Presentation where
  holder : String
  audience : String
  nonce : String
  credentials : List Credential
deriving Repr

/-- What the host hands over for one decision. -/
structure Ctx where
  now : Nat
  server : String
  /-- Nonces this server issued and has not seen used. -/
  nonces : List String
  /-- The requester's bound agent IRIs (`Identity.Binding.bound`). -/
  bound : List String
  status : String → Option StatusAnswer

/-! ## The decision -/

def allIn (xs ys : List String) : Bool := xs.all (fun x => ys.contains x)

def entryActive (t : TrustEntry) (now : Nat) : Bool :=
  decide (t.since ≤ now) && t.ends.all (fun u => decide (now ≤ u))

/-- The issuer is on the list, active now, for every required type. -/
def trusted (m : Matcher) (c : Credential) (now : Nat) : Bool :=
  m.trust.any (fun t => t.issuer == c.issuer && allIn m.types t.types && entryActive t now)

def timely (c : Credential) (now : Nat) : Bool :=
  decide (c.validFrom ≤ now) && c.validUntil.all (fun u => decide (now ≤ u))

def freshValid (m : Matcher) (now : Nat) : Option StatusAnswer → Bool
  | some a => a.status == .valid && decide (a.fetchedAt ≤ now) && decide (now - a.fetchedAt ≤ m.maxStatusAge)
  | none => false

def statusOk (m : Matcher) (ctx : Ctx) (c : Credential) : Bool :=
  match c.statusRef with
  | some r => freshValid m ctx.now (ctx.status r)
  | none =>
    match c.validUntil with
    | some u => decide (u - c.validFrom ≤ m.maxLifeWithoutStatus)
    | none => false

def claimOk (c : Credential) (k : String × List String) : Bool :=
  c.claims.any (fun cv => cv.1 == k.1 && k.2.contains cv.2)

def claimsOk (m : Matcher) (c : Credential) : Bool := m.claims.all (claimOk c)

def holderOk (ctx : Ctx) (p : Presentation) (c : Credential) : Bool :=
  c.subject == p.holder && ctx.bound.contains p.holder

def freshOk (ctx : Ctx) (p : Presentation) : Bool :=
  p.audience == ctx.server && ctx.nonces.contains p.nonce

def credMatches (m : Matcher) (ctx : Ctx) (p : Presentation) (c : Credential) : Bool :=
  allIn m.types c.types && trusted m c ctx.now && timely c ctx.now &&
  statusOk m ctx c && claimsOk m c && holderOk ctx p c

def satisfies (m : Matcher) (ctx : Ctx) (p : Presentation) : Bool :=
  !m.types.isEmpty && freshOk ctx p && p.credentials.any (credMatches m ctx p)

/-- After a decision the server forgets the nonce. -/
def consume (ctx : Ctx) (p : Presentation) : Ctx :=
  { ctx with nonces := ctx.nonces.erase p.nonce }

/-! ## Theorems: what a match means -/

/-- **Soundness.** A match means: the matcher names at least one type; the
presentation was made for this server with a nonce it issued; and one
presented credential has every required type, comes from an issuer the
list trusts now for all of them, is within its validity, has a fresh
`valid` status (or is short-lived), discloses the required claims, and is
about the very key that signed the presentation, which is one of the
requester's bound identifiers. -/
theorem matches_sound {m ctx p} (h : satisfies m ctx p = true) :
    m.types ≠ [] ∧ p.audience = ctx.server ∧ p.nonce ∈ ctx.nonces ∧
    ∃ c ∈ p.credentials,
      (∀ ty ∈ m.types, ty ∈ c.types) ∧
      (∃ t ∈ m.trust, t.issuer = c.issuer ∧ (∀ ty ∈ m.types, ty ∈ t.types) ∧ entryActive t ctx.now = true) ∧
      timely c ctx.now = true ∧ statusOk m ctx c = true ∧ claimsOk m c = true ∧
      c.subject = p.holder ∧ p.holder ∈ ctx.bound := by
  simp only [satisfies, freshOk, credMatches, trusted, holderOk, allIn, Bool.and_eq_true,
    Bool.not_eq_true', List.isEmpty_eq_false_iff, beq_iff_eq, List.contains_iff_mem,
    List.any_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hne, ha, hn⟩, c, hc, ⟨⟨⟨⟨hty, t, ht, ⟨hti, htt⟩, hta⟩, htm⟩, hst⟩, hcl⟩, hs, hb⟩ := h
  exact ⟨hne, ha, hn, c, hc, hty, ⟨t, ht, hti, htt, hta⟩, htm, hst, hcl, hs, hb⟩

/-- **An empty matcher satisfies nobody.** A rule that names no type is not
"any credential": it is refused. -/
theorem empty_types_denies {m ctx p} (h : m.types = []) : satisfies m ctx p = false := by
  simp [satisfies, h]

/-- **Issuers are trusted per type.** An issuer on the list only for
`Degree` cannot satisfy a matcher that requires `MedicalLicence`. -/
theorem issuer_scope {m ctx p c} (h : credMatches m ctx p c = true) :
    ∃ t ∈ m.trust, t.issuer = c.issuer ∧ ∀ ty ∈ m.types, ty ∈ t.types := by
  simp only [credMatches, trusted, allIn, Bool.and_eq_true, List.any_eq_true, beq_iff_eq,
    List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨_, t, ht, ⟨hi, hty⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  exact ⟨t, ht, hi, hty⟩

/-- **No transfer.** A credential about someone else does not match, even
if presented with a valid proof by the presenter's own key: the
credential's subject must be the presentation's signer, and the signer must
be one of the requester's bound identifiers. A copied credential file is
not enough. -/
theorem no_transfer {m ctx p c} (h : credMatches m ctx p c = true) :
    c.subject = p.holder ∧ p.holder ∈ ctx.bound := by
  simp only [credMatches, holderOk, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  exact h.2

/-! ## Theorems: fail closed -/

/-- **Status fails closed.** If the credential has a status entry and the
host has no answer for it, or the answer is anything but `valid`, or it is
older than `maxStatusAge`, the credential does not match. An unreachable
status list denies; it does not allow. -/
theorem status_fail_closed {m ctx p c r} (hr : c.statusRef = some r)
    (h : ctx.status r = none ∨
      (∃ a, ctx.status r = some a ∧ (a.status ≠ .valid ∨ ctx.now - a.fetchedAt > m.maxStatusAge))) :
    credMatches m ctx p c = false := by
  have : statusOk m ctx c = false := by
    simp only [statusOk, hr]
    rcases h with h | ⟨a, ha, hbad⟩
    · simp [h, freshValid]
    · rw [ha]; simp only [freshValid]
      rcases hbad with hs | hs
      · simp [hs]
      · have : ¬ (ctx.now - a.fetchedAt ≤ m.maxStatusAge) := by omega
        simp [this]
  simp [credMatches, this]

/-- **No status, no long life.** A credential with no status entry and no
end date never satisfies: it could never be revoked. -/
theorem unrevocable_denies {m ctx p c} (hs : c.statusRef = none) (hu : c.validUntil = none) :
    credMatches m ctx p c = false := by
  simp [credMatches, statusOk, hs, hu]

/-- **Expired or not yet valid denies.** -/
theorem untimely_denies {m ctx p c}
    (h : ctx.now < c.validFrom ∨ ∃ u, c.validUntil = some u ∧ u < ctx.now) :
    credMatches m ctx p c = false := by
  have : timely c ctx.now = false := by
    rcases h with h | ⟨u, hu, hlt⟩
    · simp [timely]; omega
    · simp [timely, hu]; omega
  simp [credMatches, this]

/-- **Wrong audience or unknown nonce denies.** A presentation made for
another server, or with a nonce this server did not issue, satisfies nothing. -/
theorem foreign_presentation_denies {m ctx p}
    (h : p.audience ≠ ctx.server ∨ p.nonce ∉ ctx.nonces) : satisfies m ctx p = false := by
  rcases h with h | h <;> simp [satisfies, freshOk, h]

/-- **No replay.** Once a nonce is consumed, the same presentation satisfies
nothing (when the server never issued a nonce twice). -/
theorem replay_denies {m ctx p} (hnd : ctx.nonces.Nodup) :
    satisfies m (consume ctx p) p = false := by
  apply foreign_presentation_denies
  exact Or.inr (hnd.not_mem_erase)

/-! ## Theorems: changes in the right direction -/

/-- **Removing trust never grants.** Matching under a smaller trust list
implies matching under the larger one; equivalently, taking an issuer off
the list can only remove access. -/
theorem trust_antitone {m ctx p} {trust' : List TrustEntry} (hsub : ∀ t ∈ trust', t ∈ m.trust)
    (h : satisfies { m with trust := trust' } ctx p = true) : satisfies m ctx p = true := by
  simp only [satisfies, credMatches, trusted, Bool.and_eq_true, List.any_eq_true] at h ⊢
  obtain ⟨hf, c, hc, ⟨⟨⟨⟨⟨hty, t, ht, htt⟩, hti⟩, hst⟩, hcl⟩, hh⟩⟩ := h
  exact ⟨hf, c, hc, ⟨⟨⟨⟨⟨hty, t, hsub t ht, htt⟩, hti⟩, hst⟩, hcl⟩, hh⟩⟩

/-- **Worse status never grants.** If every status answer in `ctx'` that
counts as fresh and valid also does in `ctx` (for instance `ctx'` is `ctx`
after a revocation), then a match in `ctx'` is a match in `ctx`. -/
theorem status_antitone {m ctx p} {status' : String → Option StatusAnswer}
    (hw : ∀ r, freshValid m ctx.now (status' r) = true → freshValid m ctx.now (ctx.status r) = true)
    (h : satisfies m { ctx with status := status' } p = true) : satisfies m ctx p = true := by
  simp only [satisfies, freshOk, Bool.and_eq_true, List.any_eq_true] at h ⊢
  obtain ⟨hf, c, hc, hm⟩ := h
  refine ⟨hf, c, hc, ?_⟩
  simp only [credMatches, Bool.and_eq_true] at hm ⊢
  obtain ⟨⟨⟨⟨⟨hty, htr⟩, hti⟩, hst⟩, hcl⟩, hh⟩ := hm
  refine ⟨⟨⟨⟨⟨hty, htr⟩, hti⟩, ?_⟩, hcl⟩, hh⟩
  simp only [statusOk] at hst ⊢
  cases hr : c.statusRef with
  | none => simpa [hr] using hst
  | some r => simp only [hr] at hst ⊢; exact hw r hst

/-- **Presenting more never hurts.** -/
theorem more_credentials_mono {m ctx p} {extra : List Credential}
    (h : satisfies m ctx p = true) : satisfies m ctx { p with credentials := p.credentials ++ extra } = true := by
  simp only [satisfies, freshOk, credMatches, holderOk, Bool.and_eq_true, List.any_eq_true,
    List.mem_append] at h ⊢
  obtain ⟨hf, c, hc, hm⟩ := h
  exact ⟨hf, c, Or.inl hc, hm⟩

/-! ## Theorem: data minimisation -/

/-- The claims the matcher looks at. -/
def named (m : Matcher) (c : Credential) : Credential :=
  { c with claims := c.claims.filter (fun cv => m.claims.any (fun k => k.1 == cv.1)) }

/-- **Only named claims matter.** Hiding every claim the matcher does not
name changes nothing, so a selective-disclosure presentation that reveals
only those claims gets the same answer. -/
theorem ignores_unnamed_claims (m : Matcher) (c : Credential) :
    claimsOk m (named m c) = claimsOk m c := by
  unfold claimsOk named
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor
  · intro h k hk
    have := h k hk
    simp only [claimOk, List.any_eq_true, List.mem_filter, Bool.and_eq_true, beq_iff_eq,
      List.contains_iff_mem] at this ⊢
    obtain ⟨cv, ⟨hcv, _⟩, he, hv⟩ := this
    exact ⟨cv, hcv, he, hv⟩
  · intro h k hk
    have := h k hk
    simp only [claimOk, List.any_eq_true, List.mem_filter, Bool.and_eq_true, beq_iff_eq,
      List.contains_iff_mem] at this ⊢
    obtain ⟨cv, hcv, he, hv⟩ := this
    exact ⟨cv, ⟨hcv, k, hk, he.symm⟩, he, hv⟩

/-! ## Access rules and delegation -/

inductive Mode where
  | read | append | write | control
deriving DecidableEq, Repr

/-- An access rule: these modes for whoever satisfies this matcher. -/
structure Rule where
  matcher : Matcher
  modes : List Mode

def allowed (rules : List Rule) (ctx : Ctx) (p : Presentation) (mode : Mode) : Bool :=
  rules.any (fun r => r.modes.contains mode && satisfies r.matcher ctx p)

/-- **No rule, no access**, and an allowed mode is one some rule lists
and whose matcher holds. -/
theorem allowed_sound {rules ctx p mode} (h : allowed rules ctx p mode = true) :
    ∃ r ∈ rules, mode ∈ r.modes ∧ satisfies r.matcher ctx p = true := by
  simp only [allowed, List.any_eq_true, Bool.and_eq_true, List.contains_iff_mem] at h
  obtain ⟨r, hr, hm, hx⟩ := h
  exact ⟨r, hr, hm, hx⟩

/-- A delegation, already verified: the holder `delegator` lets `agent`
use these modes ends `ends`. -/
structure Delegation where
  delegator : String
  agent : String
  modes : List Mode
  ends : Nat
deriving DecidableEq, Repr

/-- An agent acting for a credential holder: the holder's presentation
must match (made for this server, with a nonce), the delegation must come
from that holder, name the requester, be current, and list the mode. -/
def delegatedAllowed (rules : List Rule) (ctx : Ctx) (p : Presentation) (d : Delegation)
    (requester : String) (mode : Mode) : Bool :=
  d.delegator == p.holder && d.agent == requester && decide (ctx.now ≤ d.ends) &&
  d.modes.contains mode && allowed rules { ctx with bound := [p.holder] } p mode

/-- **Delegation only narrows.** What an agent may do is what the holder
may do AND what the delegation lists: never more than either. -/
theorem delegation_attenuates {rules ctx p d requester mode}
    (h : delegatedAllowed rules ctx p d requester mode = true) :
    mode ∈ d.modes ∧ allowed rules { ctx with bound := [p.holder] } p mode = true ∧
    d.delegator = p.holder ∧ d.agent = requester ∧ ctx.now ≤ d.ends := by
  simp only [delegatedAllowed, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h4, h5, h1, h2, h3⟩

/-! ## Worked cases -/

def regulator : TrustEntry := { issuer := "https://regulator.example", types := ["MedicalLicence"], since := 0, ends := none }
def university : TrustEntry := { issuer := "https://uni.example", types := ["Degree"], since := 0, ends := none }

def doctors : Matcher :=
  { types := ["MedicalLicence"], trust := [regulator, university], claims := [("standing", ["full"])],
    maxStatusAge := 600, maxLifeWithoutStatus := 86400 }

def licence (issuer subject : String) (statusRef : Option String := some "list#7") : Credential :=
  { id := "urn:c1", issuer, types := ["VerifiableCredential", "MedicalLicence"], subject,
    claims := [("standing", "full"), ("name", "J. Doe")], validFrom := 0, validUntil := some 10000000,
    statusRef }

def ctx0 (st : Status) : Ctx :=
  { now := 1000, server := "https://alice.pod", nonces := ["n1"], bound := ["did:key:zJ"],
    status := fun r => if r == "list#7" then some { status := st, fetchedAt := 900 } else none }

def pres (c : Credential) (holder := "did:key:zJ") : Presentation :=
  { holder, audience := "https://alice.pod", nonce := "n1", credentials := [c] }

-- A current, valid licence from the regulator, presented by its subject.
#guard satisfies doctors (ctx0 .valid) (pres (licence "https://regulator.example" "did:key:zJ"))
-- Revoked or suspended: no.
#guard !satisfies doctors (ctx0 .revoked) (pres (licence "https://regulator.example" "did:key:zJ"))
#guard !satisfies doctors (ctx0 .suspended) (pres (licence "https://regulator.example" "did:key:zJ"))
-- The university is trusted, but not for licences.
#guard !satisfies doctors (ctx0 .valid) (pres (licence "https://uni.example" "did:key:zJ"))
-- Someone else's licence, presented with the presenter's own key.
#guard !satisfies doctors { ctx0 .valid with bound := ["did:key:zEve"] }
  (pres (licence "https://regulator.example" "did:key:zJ") "did:key:zEve")
-- Status list unreachable.
#guard !satisfies doctors { ctx0 .valid with status := fun _ => none }
  (pres (licence "https://regulator.example" "did:key:zJ"))
-- Replay after the nonce was used.
#guard !satisfies doctors (consume (ctx0 .valid) (pres (licence "https://regulator.example" "did:key:zJ")))
  (pres (licence "https://regulator.example" "did:key:zJ"))
-- An AI agent may read for the doctor, and may not write, under a read-only delegation.
#guard delegatedAllowed [{ matcher := doctors, modes := [.read, .write] }] (ctx0 .valid)
  (pres (licence "https://regulator.example" "did:key:zJ"))
  { delegator := "did:key:zJ", agent := "did:key:zAgent", modes := [.read], ends := 2000 } "did:key:zAgent" .read
#guard !delegatedAllowed [{ matcher := doctors, modes := [.read, .write] }] (ctx0 .valid)
  (pres (licence "https://regulator.example" "did:key:zJ"))
  { delegator := "did:key:zJ", agent := "did:key:zAgent", modes := [.read], ends := 2000 } "did:key:zAgent" .write

end L4Factoidal.Authz.CredentialMatch
