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
* Email (`Ident.email`, a plain canonical address, never a mailto: URI):
  `normalize_idem` and `canonEmail_idem` (canonicalizing twice changes
  nothing; the domain is lower-cased, googlemail.com is gmail.com, and only
  at gmail.com do case, dots and a `+tag` of the local part not matter);
  `email_needs_authority` (an issuer the owner has not listed for the
  address's domain vouches for nothing); `email_pin_holds` (once an
  address is pinned to an issuer and subject, another subject gets
  nothing: a reassigned address does not inherit access).
* `replay_diffPS`, `replay_log`: the profile changelog stores line diffs
  (common prefix and suffix kept); applying the diff of `a` to `b` to `a`
  gives `b`, so replaying the log rebuilds each version.

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
  /-- A canonical email address (`canonEmail`), the string, not a mailto: IRI. -/
  | email (addr : String)
deriving DecidableEq, Repr

/-- Evidence checked outside the profile. -/
inductive Evidence where
  | keyProof (did : String)
  | xmppReply (bareJid profile : String)
  | oidcToken (iss sub profile : String)
  /-- An ID token from `iss` with `email_verified`, for `email` (already
  canonical), subject `sub`, made for the challenge that names `profile`. -/
  | oidcEmail (iss email sub profile : String)
deriving DecidableEq, Repr

/-- The owner's trust settings for email evidence. `authority` lists
(issuer, domain): which issuer may vouch for addresses in which domain
(Google's issuer for gmail.com, a company's issuer for its own domain).
`pins` lists (email, issuer, sub) recorded at first use. -/
structure Trust where
  authority : List (String × String) := []
  pins : List (String × String × String) := []
deriving Repr

/-- The domain of a canonical address: what follows its last `@`. -/
def domainOf (addr : String) : String := (addr.splitOn "@").getLast!

/-- The issuer may vouch for this address, and the address is either not
pinned, or pinned to this very issuer and subject. -/
def emailOk (t : Trust) (iss addr sub : String) : Bool :=
  t.authority.contains (iss, domainOf addr) &&
  t.pins.all (fun pin => pin.1 != addr || (pin.2.1 == iss && pin.2.2 == sub))

/-- Does this evidence support this identifier, for the profile `p`? -/
def supports (t : Trust) (p : String) : Evidence → Ident → Bool
  | .keyProof d, .didKey d' => d == d'
  | .xmppReply j q, .xmpp j' => j == j' && q == p
  | .oidcToken i s q, .oidc i' s' => i == i' && s == s' && q == p && s == p
  | .oidcEmail i e s q, .email e' => e == e' && q == p && emailOk t i e s
  | _, _ => false

/-- The profile document speaks for itself; every other identifier needs
evidence. -/
def evidenced (t : Trust) (p : String) (evs : List Evidence) (i : Ident) : Bool :=
  i == .profile p || evs.any (fun e => supports t p e i)

/-- The identifiers an ACL may name for this person. -/
def bound (t : Trust) (p : String) (claims : List Ident) (evs : List Evidence) : List Ident :=
  claims.filter (evidenced t p evs)

theorem bound_sound {t p claims evs i} (h : i ∈ bound t p claims evs) :
    i ∈ claims ∧ (i = .profile p ∨ ∃ e ∈ evs, supports t p e i = true) := by
  simp only [bound, List.mem_filter, evidenced, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true] at h
  exact ⟨h.1, h.2⟩

theorem bound_complete {t p claims evs i e} (hc : i ∈ claims) (he : e ∈ evs)
    (hs : supports t p e i = true) : i ∈ bound t p claims evs := by
  simp only [bound, List.mem_filter, evidenced, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true]
  exact ⟨hc, Or.inr ⟨e, he, hs⟩⟩

theorem unclaimed_never_bound {t p claims evs i} (h : i ∉ claims) :
    i ∉ bound t p claims evs := fun hb => h (bound_sound hb).1

theorem other_profile_evidence_useless {t p q j i s e i'} (h : q ≠ p) :
    supports t p (.xmppReply j q) i' = false ∧
    supports t p (.oidcToken i s q) i' = false ∧
    supports t p (.oidcEmail i e s q) i' = false := by
  cases i' <;> simp [supports, h]

theorem bound_mono_evidence {t p claims evs evs' i} (hsub : ∀ e ∈ evs, e ∈ evs')
    (h : i ∈ bound t p claims evs) : i ∈ bound t p claims evs' := by
  rcases bound_sound h with ⟨hc, hp | ⟨e, he, hs⟩⟩
  · subst hp
    simp [bound, evidenced, hc]
  · exact bound_complete hc (hsub e he) hs

theorem bound_antitone_claims {t p claims claims' evs i}
    (hsub : ∀ c ∈ claims', c ∈ claims) (h : i ∈ bound t p claims' evs) :
    i ∈ bound t p claims evs := by
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

theorem oidc_sub_is_profile {t p e iss sub} (h : supports t p e (.oidc iss sub) = true) :
    sub = p := by
  cases e <;> simp [supports] at h
  exact h.1.1.2 ▸ h.2

/-! ## Email addresses -/

theorem toLower_idem (c : Char) : c.toLower.toLower = c.toLower := by
  unfold Char.toLower
  split <;> rename_i h
  · simp at *
    intro h1
    have hv := c.valid
    rcases h with ⟨h2, h3⟩
    simp only [UInt32.le_iff_toNat_le, UInt32.lt_iff_toNat_lt, UInt32.toNat_add] at *
    simp at *
    omega
  · simp

/-- Lower-casing changes only A–Z, so it never makes or removes `@`, `+` or `.`. -/
theorem toLower_eq_self_of_not_upper (c : Char) (h : ¬ ('A' ≤ c ∧ c ≤ 'Z')) : c.toLower = c := by
  unfold Char.toLower
  split <;> rename_i h'
  · exfalso; apply h; simp only [Char.le_def] at *; exact ⟨h'.1, h'.2⟩
  · rfl

theorem toLower_eq_punct {c d : Char} (hd : ¬ ('A' ≤ d ∧ d ≤ 'Z')) (hd2 : ¬ ('a' ≤ d ∧ d ≤ 'z'))
    (h : c.toLower = d) : c = d := by
  revert h; unfold Char.toLower; split <;> rename_i h'
  · intro h1; exfalso; apply hd2; subst h1
    simp only [Char.le_def] at *
    simp only [UInt32.le_iff_toNat_le, UInt32.toNat_add] at *
    simp at *; omega
  · exact id

theorem lower_ne {c d : Char} (hd : ¬ ('A' ≤ d ∧ d ≤ 'Z')) (hd2 : ¬ ('a' ≤ d ∧ d ≤ 'z'))
    (hc : c ≠ d) : c.toLower ≠ d := fun h => hc (toLower_eq_punct hd hd2 h)

theorem map_lower_idem (l : List Char) : (l.map Char.toLower).map Char.toLower = l.map Char.toLower := by
  simp [List.map_map, Function.comp_def, toLower_idem]

theorem lower_ne_at {c : Char} (h : c ≠ '@') : c.toLower ≠ '@' := lower_ne (by decide) (by decide) h
theorem lower_ne_plus {c : Char} (h : c ≠ '+') : c.toLower ≠ '+' := lower_ne (by decide) (by decide) h
theorem lower_ne_dot {c : Char} (h : c ≠ '.') : c.toLower ≠ '.' := lower_ne (by decide) (by decide) h

/-! ## Splitting at the last `@` -/

def splitLast : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs =>
    match splitLast cs with
    | some (l, d) => some (c :: l, d)
    | none => if c = '@' then some ([], cs) else none

theorem splitLast_none : ∀ {d : List Char}, '@' ∉ d → splitLast d = none
  | [], _ => rfl
  | c :: cs, h => by
    have hc : c ≠ '@' := fun e => h (e ▸ List.mem_cons_self)
    have hcs : '@' ∉ cs := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitLast, splitLast_none hcs, hc]

theorem splitLast_join {d : List Char} (hd : '@' ∉ d) :
    ∀ l : List Char, splitLast (l ++ '@' :: d) = some (l, d)
  | [] => by simp [splitLast, splitLast_none hd]
  | c :: l => by simp [splitLast, splitLast_join hd l]

theorem splitLast_noat : ∀ {s l d : List Char}, splitLast s = some (l, d) → '@' ∉ d
  | [], _, _, h => by simp [splitLast] at h
  | c :: cs, l, d, h => by
    simp only [splitLast] at h
    split at h
    · rename_i l' d' heq; simp at h; rw [← h.2]; exact splitLast_noat heq
    · rename_i heq
      split at h
      · simp at h; rw [← h.2]; intro m
        -- cs has no '@', else splitLast cs would be some
        exact absurd heq (by
          intro hn
          have : ∀ {t : List Char}, '@' ∈ t → splitLast t ≠ none := by
            intro t
            induction t with
            | nil => intro m; simp at m
            | cons x xs ih =>
              intro m
              simp only [splitLast]
              cases hx : splitLast xs with
              | some p => simp
              | none =>
                rcases List.mem_cons.mp m with e | m'
                · simp [← e]
                · exact absurd hx (ih m')
          exact this m hn)
      · simp at h

/-! ## The canonical form -/

def gmail : List Char := "gmail.com".toList
def googlemail : List Char := "googlemail.com".toList

/-- The domain: lower case; googlemail.com is gmail.com. -/
def normDomain (d : List Char) : List Char :=
  if d.map Char.toLower = googlemail then gmail else d.map Char.toLower

/-- The local part: exact, except at gmail.com, Google's rule: case, dots and
a `+tag` do not matter. -/
def normLocal (d l : List Char) : List Char :=
  if d = gmail then ((l.takeWhile (· ≠ '+')).filter (· ≠ '.')).map Char.toLower else l

def normalize (s : List Char) : Option (List Char) :=
  match splitLast s with
  | none => none
  | some (l, d) => let d' := normDomain d; some (normLocal d' l ++ '@' :: d')

theorem normDomain_idem (d : List Char) : normDomain (normDomain d) = normDomain d := by
  unfold normDomain
  by_cases h : d.map Char.toLower = googlemail
  · simp only [h, if_true]; decide
  · simp only [h, if_false, map_lower_idem]

theorem normDomain_noat {d : List Char} (h : '@' ∉ d) : '@' ∉ normDomain d := by
  unfold normDomain
  split
  · decide
  · intro m
    obtain ⟨c, hc, he⟩ := List.mem_map.mp m
    exact lower_ne_at (fun e => h (e ▸ hc)) he

theorem takeWhile_self {p : Char → Bool} : ∀ {l : List Char}, (∀ x ∈ l, p x = true) → l.takeWhile p = l
  | [], _ => rfl
  | x :: xs, h => by
    simp [List.takeWhile, h x List.mem_cons_self, takeWhile_self (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem mem_takeWhile {p : Char → Bool} : ∀ {l : List Char} {x}, x ∈ l.takeWhile p → p x = true
  | [], _, h => by simp at h
  | y :: ys, x, h => by
    simp only [List.takeWhile] at h
    split at h
    · rename_i hy
      rcases List.mem_cons.mp h with e | m
      · subst e; exact hy
      · exact mem_takeWhile m
    · simp at h

theorem normLocal_idem (d l : List Char) : normLocal d (normLocal d l) = normLocal d l := by
  unfold normLocal
  split
  · rename_i hg
    generalize hm : ((l.takeWhile (· ≠ '+')).filter (· ≠ '.')) = m
    have hall : ∀ y ∈ m, y ≠ '+' ∧ y ≠ '.' := by
      intro y hy; rw [← hm] at hy
      obtain ⟨hy1, hy2⟩ := List.mem_filter.mp hy
      exact ⟨by simpa using mem_takeWhile hy1, by simpa using hy2⟩
    have hlow : ∀ x ∈ m.map Char.toLower, x ≠ '+' ∧ x ≠ '.' := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact ⟨lower_ne_plus (hall y hy).1, lower_ne_dot (hall y hy).2⟩
    rw [takeWhile_self (fun x hx => by simpa using (hlow x hx).1)]
    rw [List.filter_eq_self.mpr (fun x hx => by simpa using (hlow x hx).2)]
    exact map_lower_idem m
  · rfl

/-- **Normalizing twice changes nothing.** -/
theorem normalize_idem {s n : List Char} (h : normalize s = some n) : normalize n = some n := by
  unfold normalize at h
  split at h
  · simp at h
  · rename_i l d hs
    simp only [Option.some.injEq] at h
    subst h
    have hd := normDomain_noat (splitLast_noat hs)
    unfold normalize
    rw [splitLast_join hd]
    simp only [normDomain_idem, normLocal_idem]

/-- The canonical form of an address, as a string, or none. -/
def canonEmail (a : String) : Option String := (normalize a.toList).map String.ofList

theorem canonEmail_idem {a c : String} (h : canonEmail a = some c) : canonEmail c = some c := by
  unfold canonEmail at h ⊢
  cases hn : normalize a.toList with
  | none => simp [hn] at h
  | some n =>
    simp only [hn, Option.map_some, Option.some.injEq] at h
    subst h
    simp [String.toList_ofList, normalize_idem hn]

/-- **Only the domain's issuer can vouch for an address.** Email evidence
from an issuer that the owner has not listed for that address's domain
supports nothing, however well signed. -/
theorem email_needs_authority {t p i e s q i'} (h : (i, domainOf e) ∉ t.authority) :
    supports t p (.oidcEmail i e s q) i' = false := by
  cases i' <;> simp [supports, emailOk, List.contains_iff_mem, h]

/-- **A pinned address stays with its first subject.** Once (address,
issuer, subject) is pinned, a token for the same address with another
issuer or subject supports nothing: a reassigned or recycled address does
not inherit access. -/
theorem email_pin_holds {t p i e s q i' i0 s0} (hp : (e, i0, s0) ∈ t.pins) (hd : i ≠ i0 ∨ s ≠ s0) :
    supports t p (.oidcEmail i e s q) i' = false := by
  cases i' <;> simp only [supports, Bool.false_eq_true] <;> try rfl
  rename_i e'
  simp only [emailOk, Bool.and_eq_false_iff, List.all_eq_false]
  right; right
  refine ⟨_, hp, ?_⟩
  intro h
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h
  rcases hd with hd | hd
  · exact hd h.1.symm
  · exact hd h.2.symm

#guard canonEmail "John.Doe+lunch@GoogleMail.com" == some "johndoe@gmail.com"
#guard canonEmail "John.Doe+lunch@Example.COM" == some "John.Doe+lunch@example.com"
#guard canonEmail "no-at-sign" == none
#guard supports { authority := [("https://accounts.google.com", "gmail.com")] } "p"
  (.oidcEmail "https://accounts.google.com" "johndoe@gmail.com" "1234" "p") (.email "johndoe@gmail.com")
#guard !supports { authority := [("https://accounts.google.com", "gmail.com")] } "p"
  (.oidcEmail "https://evil.example" "johndoe@gmail.com" "1234" "p") (.email "johndoe@gmail.com")
def pinned : Trust := { authority := [("https://accounts.google.com", "gmail.com")], pins := [("johndoe@gmail.com", "https://accounts.google.com", "1234")] }
#guard !supports pinned "p"
  (.oidcEmail "https://accounts.google.com" "johndoe@gmail.com" "9999" "p") (.email "johndoe@gmail.com")

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
  | .email a => "mailto:" ++ a

/-- The kind of IRI each agent must be, checked by the host before an
identifier enters `claims` (SHACL `sh:pattern`). -/
def wellFormed : Ident → Prop
  | .profile iri => iri.startsWith "https:" ∨ iri.startsWith "http:"
  | .didKey d => d.startsWith "did:key:"
  | .xmpp j => ¬ j.startsWith "xmpp:" ∧ j ≠ ""
  | .oidc _ s => s.startsWith "https:" ∨ s.startsWith "http:"
  | .email a => canonEmail a = some a

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

/-- The diff from `a` to `b` with the common prefix kept, the rest of `a`
dropped, the rest of `b` inserted. -/
def diff (a b : List String) : Diff :=
  let n := commonPrefix a b
  { pre := n, del := a.length - n, ins := b.drop n }

theorem replay_diff (a b : List String) : apply (diff a b) a = b := by
  simp only [apply, diff]
  have hle := commonPrefix_le_left a b
  have hdrop : a.drop (commonPrefix a b + (a.length - commonPrefix a b)) = [] := by
    apply List.drop_eq_nil_of_le; omega
  rw [hdrop, List.append_nil, commonPrefix_take, List.take_append_drop]

/-- The host's diff (`lineDiff` in Foafos `profile.mjs`): the common prefix,
then the common suffix of what is left, both kept. -/
def diffPS (a b : List String) : Diff :=
  let n := commonPrefix a b
  let s := commonPrefix (a.drop n).reverse (b.drop n).reverse
  { pre := n, del := (a.drop n).length - s, ins := (b.drop n).take ((b.drop n).length - s) }

theorem tail_eq (a' b' : List String) :
    a'.drop (a'.length - commonPrefix a'.reverse b'.reverse) =
    b'.drop (b'.length - commonPrefix a'.reverse b'.reverse) := by
  have h := commonPrefix_take a'.reverse b'.reverse
  rw [List.take_reverse, List.take_reverse] at h
  simpa using congrArg List.reverse h

theorem replay_diffPS (a b : List String) : apply (diffPS a b) a = b := by
  simp only [apply, diffPS]
  generalize hn : commonPrefix a b = n
  have hpre := commonPrefix_take a b
  rw [hn] at hpre
  rw [← List.drop_drop, tail_eq, hpre, List.append_assoc, List.take_append_drop, List.take_append_drop]

/-- Replaying a log of diffs from the first version gives the last. -/
def replay : List String → List Diff → List String
  | a, [] => a
  | a, d :: ds => replay (apply d a) ds

def log : List (List String) → List Diff
  | a :: b :: rest => diffPS a b :: log (b :: rest)
  | _ => []

theorem replay_log : ∀ (v : List String) (vs : List (List String)),
    replay v (log (v :: vs)) = (v :: vs).getLast (by simp)
  | v, [] => by simp [replay, log]
  | v, w :: ws => by
    simp only [log, replay, replay_diffPS]
    rw [replay_log w ws]
    simp

/-! ## Checks -/

#guard bound {} "https://pod/me#i"
    [.profile "https://pod/me#i", .didKey "did:key:zA", .xmpp "me@x", .xmpp "eve@x"]
    [.keyProof "did:key:zA", .xmppReply "me@x" "https://pod/me#i",
     .xmppReply "eve@x" "https://pod/eve#i"]
  == [.profile "https://pod/me#i", .didKey "did:key:zA", .xmpp "me@x"]

#guard (closure "p" [(.profile "p", .xmpp "me@x"), (.xmpp "me@x", .didKey "did:key:zA"),
    (.xmpp "eve@x", .didKey "did:key:zE")] 3).contains (.didKey "did:key:zA")
#guard !(closure "p" [(.profile "p", .xmpp "me@x"), (.xmpp "eve@x", .didKey "did:key:zE")] 3).contains
    (.didKey "did:key:zE")

#guard apply (diff ["a", "b", "c"] ["a", "x", "c"]) ["a", "b", "c"] == ["a", "x", "c"]
#guard diffPS ["a", "b", "c"] ["a", "x", "c"] == { pre := 1, del := 1, ins := ["x"] }

end L4Factoidal.Identity.Binding
