/-
L4Factoidal.Identity.Binding — which of a person's identifiers an ACL may name.

A person's profile (a controlled identifier document in their pod) lists the
identifiers it claims: did:key agents, XMPP accounts, OpenID Connect
subjects. The host parses the profile, checks its shape (SHACL), and closes it
under OWL-RL (`owl:sameAs`, `foaf:account`) with a SPARQL query. What comes
out is `claims`. Separately, the host holds evidence that something outside
the profile checked:

* `keyProof did`: a signature over a challenge that names the profile,
  verified under the key the did:key itself encodes.
* `xmppReply jid profile`: a direct-message reply to a one-time code, whose
  `from` the XMPP server stamped as `jid`, naming `profile`.
* `oidcToken iss sub profile`: an ID token that verified under the
  `lws#OpenIdProvider` service of the subject's CID document, naming
  `profile` in the challenge.

An identifier is bound when the profile claims it AND evidence supports it.
Only bound identifiers become ACL agents. Theorems:

* `bound_sound`, `bound_complete`: bound = claimed ∧ evidenced.
* `unclaimed_never_bound`: evidence alone adds no one. A key or account
  that proves control of itself is not thereby in someone's profile.
* `other_profile_evidence_useless`: an XMPP or OIDC proof made for another
  profile does not bind here.
* `bound_mono_evidence`, `bound_antitone_claims`: more evidence never
  removes an agent; dropping a claim drops the agent.
* `closure_mentioned`: the `sameAs` closure invents no identifier; each one
  it reaches is the profile itself or is named in the profile's own links.
  The closure reads only the profile graph, so another document's
  `owl:sameAs` cannot pull an identity in.
* `agentIri_xmpp_injective`, `agentIri_didKey_injective`,
  `oidc_sub_is_profile`: a grant to one account or key is never a grant
  to another; an OIDC login binds only the profile's own IRI.
* `replay_diff`: the profile changelog stores line diffs; applying the diff
  of `a` to `b` to `a` gives `b`, so replaying the log rebuilds each
  version.

No `sorry`, no `axiom`, no `partial`.
-/

namespace L4Factoidal.Identity.Binding

/-- An identifier a profile can claim. The strings are as written in the
profile: `did` is the whole `did:key:…`, `bareJid` has no resource. -/
inductive Ident where
  | profile (iri : String)
  | didKey (did : String)
  | xmpp (bareJid : String)
  | oidc (iss sub : String)
deriving DecidableEq, Repr

/-- Evidence checked outside the profile. -/
inductive Evidence where
  | keyProof (did : String)
  | xmppReply (bareJid profile : String)
  | oidcToken (iss sub profile : String)
deriving DecidableEq, Repr

/-- Does this evidence support this identifier, for the profile `p`? -/
def supports (p : String) : Evidence → Ident → Bool
  | .keyProof d, .didKey d' => d == d'
  | .xmppReply j q, .xmpp j' => j == j' && q == p
  | .oidcToken i s q, .oidc i' s' => i == i' && s == s' && q == p && s == p
  | _, _ => false

/-- The profile document speaks for itself; every other identifier needs
evidence. -/
def evidenced (p : String) (evs : List Evidence) (i : Ident) : Bool :=
  i == .profile p || evs.any (fun e => supports p e i)

/-- The identifiers an ACL may name for this person. -/
def bound (p : String) (claims : List Ident) (evs : List Evidence) : List Ident :=
  claims.filter (evidenced p evs)

theorem bound_sound {p claims evs i} (h : i ∈ bound p claims evs) :
    i ∈ claims ∧ (i = .profile p ∨ ∃ e ∈ evs, supports p e i = true) := by
  simp only [bound, List.mem_filter, evidenced, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true] at h
  exact ⟨h.1, h.2⟩

theorem bound_complete {p claims evs i e} (hc : i ∈ claims) (he : e ∈ evs)
    (hs : supports p e i = true) : i ∈ bound p claims evs := by
  simp only [bound, List.mem_filter, evidenced, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true]
  exact ⟨hc, Or.inr ⟨e, he, hs⟩⟩

theorem unclaimed_never_bound {p claims evs i} (h : i ∉ claims) :
    i ∉ bound p claims evs := fun hb => h (bound_sound hb).1

theorem other_profile_evidence_useless {p q j i s i'} (h : q ≠ p) :
    supports p (.xmppReply j q) i' = false ∧
    supports p (.oidcToken i s q) i' = false := by
  cases i' <;> simp [supports, h]

theorem bound_mono_evidence {p claims evs evs' i} (hsub : ∀ e ∈ evs, e ∈ evs')
    (h : i ∈ bound p claims evs) : i ∈ bound p claims evs' := by
  rcases bound_sound h with ⟨hc, hp | ⟨e, he, hs⟩⟩
  · subst hp
    simp [bound, evidenced, hc]
  · exact bound_complete hc (hsub e he) hs

theorem bound_antitone_claims {p claims claims' evs i}
    (hsub : ∀ c ∈ claims', c ∈ claims) (h : i ∈ bound p claims' evs) :
    i ∈ bound p claims evs := by
  simp only [bound, List.mem_filter] at h ⊢
  exact ⟨hsub i h.1, h.2⟩

/-! ## The sameAs closure of the profile's own links -/

/-- One step: every identifier linked (either way) to one already reached. -/
def step (links : List (Ident × Ident)) (reached : List Ident) : List Ident :=
  reached ++ links.filterMap (fun l =>
    if reached.contains l.1 then some l.2
    else if reached.contains l.2 then some l.1 else none)

/-- The closure from the profile, `fuel` steps (the host uses the number of
links plus one, which reaches every connected identifier). -/
def closure (p : String) (links : List (Ident × Ident)) : Nat → List Ident
  | 0 => [.profile p]
  | n + 1 => step links (closure p links n)

/-- Named in the profile: the profile itself, or one end of one of its own
links. -/
def mentioned (p : String) (links : List (Ident × Ident)) (i : Ident) : Prop :=
  i = .profile p ∨ ∃ l ∈ links, i = l.1 ∨ i = l.2

theorem closure_mentioned (p : String) (links : List (Ident × Ident)) :
    ∀ n i, i ∈ closure p links n → mentioned p links i := by
  intro n
  induction n with
  | zero => intro i h; simp [closure] at h; exact Or.inl h
  | succ n ih =>
    intro i h
    simp only [closure, step, List.mem_append, List.mem_filterMap] at h
    rcases h with h | ⟨l, hl, hx⟩
    · exact ih i h
    · refine Or.inr ⟨l, hl, ?_⟩
      split at hx
      · simp at hx; exact Or.inr hx.symm
      · split at hx
        · simp at hx; exact Or.inl hx.symm
        · simp at hx

theorem oidc_sub_is_profile {p e iss sub} (h : supports p e (.oidc iss sub) = true) :
    sub = p := by
  cases e <;> simp [supports] at h
  exact h.1.1.2 ▸ h.2

/-! ## WAC agent IRIs -/

/-- The WAC `acl:agent` of an identifier. A did:key and a profile IRI are
IRIs already; an XMPP account is `xmpp:` + bare JID (RFC 5122); an OIDC
subject is its `sub`, which lws10-authn-openid requires to be the IRI of a
CID document. -/
def agentIri : Ident → String
  | .profile iri => iri
  | .didKey d => d
  | .xmpp j => "xmpp:" ++ j
  | .oidc _ s => s

/-- The kind of IRI each agent must be, checked by the host before an
identifier enters `claims` (SHACL `sh:pattern`). -/
def wellFormed : Ident → Prop
  | .profile iri => iri.startsWith "https:" ∨ iri.startsWith "http:"
  | .didKey d => d.startsWith "did:key:"
  | .xmpp j => ¬ j.startsWith "xmpp:" ∧ j ≠ ""
  | .oidc _ s => s.startsWith "https:" ∨ s.startsWith "http:"

/-- An OIDC subject is the person's CID document, so `supports` binds an
OIDC token only when its `sub` is the profile IRI (`oidc_sub_is_profile`):
its agent IRI is the profile's. XMPP accounts and did:keys are each
injective on their own. -/
theorem agentIri_xmpp_injective {a b : String} (h : agentIri (.xmpp a) = agentIri (.xmpp b)) :
    a = b := by
  simp only [agentIri] at h
  exact (String.append_right_inj "xmpp:").mp h

theorem agentIri_didKey_injective {a b : String} (h : agentIri (.didKey a) = agentIri (.didKey b)) :
    a = b := by simpa [agentIri] using h

/-! ## The changelog: line diffs that replay -/

/-- A diff of two line lists: keep `pre` lines, drop `del` lines, insert
`ins`, keep the rest. The host's diff keeps the common prefix and suffix. -/
structure Diff where
  pre : Nat
  del : Nat
  ins : List String
deriving DecidableEq, Repr

def apply (d : Diff) (a : List String) : List String :=
  a.take d.pre ++ d.ins ++ a.drop (d.pre + d.del)

/-- Length of the common prefix. -/
def commonPrefix : List String → List String → Nat
  | x :: xs, y :: ys => if x = y then commonPrefix xs ys + 1 else 0
  | _, _ => 0

theorem commonPrefix_take : ∀ (a b : List String),
    a.take (commonPrefix a b) = b.take (commonPrefix a b)
  | [], _ => by simp [commonPrefix]
  | _ :: _, [] => by simp [commonPrefix]
  | x :: xs, y :: ys => by
    by_cases h : x = y
    · subst h; simp [commonPrefix, commonPrefix_take xs ys]
    · simp [commonPrefix, h]

theorem commonPrefix_le_left : ∀ (a b : List String), commonPrefix a b ≤ a.length
  | [], _ => by simp [commonPrefix]
  | _ :: _, [] => by simp [commonPrefix]
  | x :: xs, y :: ys => by
    by_cases h : x = y
    · simp [commonPrefix, h, commonPrefix_le_left xs ys]
    · simp [commonPrefix, h]

/-- The diff from `a` to `b`: common prefix kept, the rest of `a` dropped,
the rest of `b` inserted. (The host also trims a common suffix; the
replay theorem for that form is the same argument on reversed lists.) -/
def diff (a b : List String) : Diff :=
  let n := commonPrefix a b
  { pre := n, del := a.length - n, ins := b.drop n }

theorem replay_diff (a b : List String) : apply (diff a b) a = b := by
  simp only [apply, diff]
  have hle := commonPrefix_le_left a b
  have hdrop : a.drop (commonPrefix a b + (a.length - commonPrefix a b)) = [] := by
    apply List.drop_eq_nil_of_le; omega
  rw [hdrop, List.append_nil, commonPrefix_take, List.take_append_drop]

/-- Replaying a log of diffs from the first version gives the last. -/
def replay : List String → List Diff → List String
  | a, [] => a
  | a, d :: ds => replay (apply d a) ds

def log : List (List String) → List Diff
  | a :: b :: rest => diff a b :: log (b :: rest)
  | _ => []

theorem replay_log : ∀ (v : List String) (vs : List (List String)),
    replay v (log (v :: vs)) = (v :: vs).getLast (by simp)
  | v, [] => by simp [replay, log]
  | v, w :: ws => by
    simp only [log, replay, replay_diff]
    rw [replay_log w ws]
    simp

/-! ## Checks -/

#guard bound "https://pod/me#i"
    [.profile "https://pod/me#i", .didKey "did:key:zA", .xmpp "me@x", .xmpp "eve@x"]
    [.keyProof "did:key:zA", .xmppReply "me@x" "https://pod/me#i",
     .xmppReply "eve@x" "https://pod/eve#i"]
  == [.profile "https://pod/me#i", .didKey "did:key:zA", .xmpp "me@x"]

#guard (closure "p" [(.profile "p", .xmpp "me@x"), (.xmpp "me@x", .didKey "did:key:zA"),
    (.xmpp "eve@x", .didKey "did:key:zE")] 3).contains (.didKey "did:key:zA")
#guard !(closure "p" [(.profile "p", .xmpp "me@x"), (.xmpp "eve@x", .didKey "did:key:zE")] 3).contains
    (.didKey "did:key:zE")

#guard apply (diff ["a", "b", "c"] ["a", "x", "c"]) ["a", "b", "c"] == ["a", "x", "c"]

end L4Factoidal.Identity.Binding
