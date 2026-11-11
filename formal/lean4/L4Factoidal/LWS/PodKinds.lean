/-
L4Factoidal.LWS.PodKinds — kinds of pod: storage policies and what each one
guarantees.

A pod owner picks a storage policy when the pod is made. This module states
four kinds and the theorems that hold for each, and for their combinations.
It is a specification: it says what a pod of each kind must do, and the
theorems prove that the definitions here do it. A server satisfies a kind
when its behaviour refines these definitions; that refinement is a separate
proof or a differential test, and is not in this file.

## The kinds

1. **Retention: wiped after a period** (`Policy.retainFor`, for example 90
   days). The pod has no clock that it can trust. It receives *time
   evidence*: claims of the form "source `s` says that the time now is at
   least `t`" (`TimeClaim`). The owner's trust policy (`TimeTrust`) names a
   set of time sources and a quorum `k`. A resource is *expired* when `k`
   distinct trusted sources each attest a time at or after its creation
   time plus the period. An expired resource is never served, and a sweep
   removes it, with all of its versions, from the pod's state.
2. **Encrypted at rest.** Storage holds only sealed records (`Sealed`): a
   key identifier and a ciphertext. The content key is held by a key holder
   outside storage (`KeyHolder`, the owner's device or a key service).
   Reading needs the key. Destroying the key (`shred`) makes every record
   sealed under it unreadable, wherever a copy of that record is.
3. **Versioning except binaries** (`Policy.versionText`). A write to a
   textual resource keeps the previous version; a write to a binary
   resource replaces it. Textual means `text/*`, or
   `application/(…+)?(json|xml|turtle|n-triples|n-quads|trig)`, compared
   without case and without parameters (`isTextual`). A delete hides the
   current version and keeps the history of a textual resource; `purge`
   removes the resource and its history. A binary resource has no history,
   so a delete removes it.
4. **Combinations.** The kinds compose: expiry removes every version, not
   only the current one; an encrypted versioned pod keeps every version
   sealed, and the key holder can read back the complete history; one key
   destruction makes the complete history unreadable.

## What is proved

Retention: `expired_has_quorum` (an expiry always has `k` distinct trusted
witnesses), `expired_mono` (more evidence never cancels an expiry),
`untrusted_irrelevant` (claims from sources outside the trust policy change
nothing, in either direction), `few_speakers_no_expiry` (fewer than `k`
trusted sources speaking cannot expire anything), `no_evidence_no_expiry`,
`no_early_wipe` (if fewer than `k` trusted sources are faulty, no resource
expires before its time), `keep_forever_never_expires`,
`serve_expired_none`, `history_expired_empty`, `sweep_no_expired`,
`expired_not_in_sweep`, `sweep_keeps_live`.

Encryption: `seal_opens` (the key holder reads back what was written),
`open_needs_key` (no key in the holder, no plaintext), `open_wrong_key`
(a different key reads nothing), `shred_unreadable`, `shred_backup_unreadable`
(a backup made at any time is unreadable after the key is destroyed),
`shred_spares_other_keys`, `encWrite_sealed` (every stored version is
ciphertext under the pod key).

Versioning: `isTextual` checks, `write_text_keeps_previous`,
`write_binary_replaces`, `writes_history_complete` (replaying the history
gives every body in write order), `binary_at_most_one_version`,
`unversioned_at_most_one_version`, `delete_hides_current`,
`delete_text_keeps_history`, `delete_binary_removes`,
`write_after_delete_serves`.

Combinations: `sweep_drops_every_version`, `encrypted_history_complete`,
`encWrites_all_sealed`, `shred_unreadable_every_version`.

## What is not proved, and cannot be proved here

* **Physical erasure.** The retention theorems prove that the pod refuses to
  serve an expired resource and drops it from its state. They do not and
  cannot prove that disk blocks, file-system journals, snapshots, replicas
  or backups are overwritten. That is why kind 2 exists: if the data was
  only ever stored sealed, destroying the key reaches every copy
  (crypto-shredding). This needs a key per scope that expires together, for
  example one key per resource or one key per month of writes; this file
  proves the per-key step (`shred_*`), not a key-rotation schedule.
* **The cipher.** Encryption is an abstract structure (`Cipher`) with two
  stated properties: decryption with the right key returns the plaintext
  (`dec_enc`), and decryption with a different key fails (`dec_wrong`).
  The second is an idealisation of authenticated encryption (AES-GCM,
  ChaCha20-Poly1305): in reality it fails with negligible probability, and
  this file has no probabilities. That a ciphertext reveals nothing about
  the plaintext or the key (confidentiality) is an assumption about the
  real cipher and is not stated as a theorem. Nonces are not modelled.
* **Key custody.** `shred` removes the key from the one key holder modelled.
  If a copy of the key exists elsewhere (an escrow, a key backup, a memory
  dump), the data stays readable there. The theorems assume the key holder
  is the only place the key is.
* **Metadata.** Only bodies are sealed. Paths, content types, creation
  times and the number of versions are stored in plaintext in this model,
  so an observer of storage learns them.
* **Time sources.** Signature checks on time claims happen before the claims
  reach these definitions (for example an RFC 3161 timestamp token, a
  Roughtime response, or a signed time statement). A forged signature is
  out of scope. `no_early_wipe` holds only under its stated assumption:
  fewer than `k` of the trusted sources ever overstate the time. With `k`
  or more faulty sources, a resource can expire early, and no proof can
  prevent that.
* **Liveness.** No theorem says that an expiry happens. If no time
  evidence arrives (the sources are unreachable), nothing expires; the pod
  keeps data past its period. A legal deletion duty therefore also needs
  the time sources to be reachable, which is an operational matter.

## Conflicts between kinds, and the choices made

* **Versioning against retention.** Retention counts from the resource's
  creation time, not from each version. A textual resource made 91 days ago
  and edited yesterday expires as a whole, with yesterday's edit. A
  per-version period is a different kind and is not specified here.
* **Versioning against delete.** A delete of a textual resource keeps its
  history (so a mistaken delete can be undone), which an owner who deletes
  for privacy may not expect. `purge` removes the history; expiry always
  acts as a purge. On an encrypted pod with a key per resource, a purge
  followed by `shred` also reaches backups.
* **Encryption against versioning.** No conflict in content: every version
  is sealed (`encWrites_all_sealed`). The number and timing of versions is
  visible (see Metadata).

No `sorry`, no `axiom`, no `partial`. Lean core only (no Mathlib).
-/

namespace L4Factoidal.LWS.PodKinds

/-! ## Shared definitions -/

/-- A list with each string once, in order of last occurrence. Used to count
*distinct* time sources, so that one source listed twice, or speaking twice,
counts once. -/
def dedup : List String → List String
  | [] => []
  | x :: xs => if x ∈ xs then dedup xs else x :: dedup xs

/-- The same list as `dedup`, built with an accumulator so that the compiled
code is a loop (`dedup_eq_dedupTR` makes the compiler use it). -/
def dedupTR (acc : List String) : List String → List String
  | [] => acc.reverse
  | x :: xs => dedupTR (if x ∈ xs then acc else x :: acc) xs

theorem dedupTR_eq : ∀ (acc l : List String), dedupTR acc l = acc.reverse ++ dedup l
  | acc, [] => by simp [dedupTR, dedup]
  | acc, x :: xs => by
      unfold dedupTR dedup
      split
      · exact dedupTR_eq acc xs
      · rw [dedupTR_eq]; simp

/-- `dedup` run through the accumulator form. -/
def dedupFast (l : List String) : List String := dedupTR [] l

@[csimp] theorem dedup_eq_dedupTR : @dedup = @dedupFast := by
  funext l; simp [dedupFast, dedupTR_eq]

theorem mem_dedup {x : String} : ∀ {l : List String}, x ∈ dedup l ↔ x ∈ l
  | [] => by simp [dedup]
  | y :: ys => by
      have ih := @mem_dedup x ys
      unfold dedup
      split
      · rw [ih, List.mem_cons]
        constructor
        · exact Or.inr
        · rintro (rfl | h) <;> assumption
      · rw [List.mem_cons, ih, List.mem_cons]

theorem nodup_dedup : ∀ (l : List String), (dedup l).Nodup
  | [] => by simp [dedup]
  | y :: ys => by
      unfold dedup
      split
      · exact nodup_dedup ys
      · rename_i h
        exact List.nodup_cons.mpr ⟨fun hm => h (mem_dedup.mp hm), nodup_dedup ys⟩

/-- Filtering by a weaker test keeps at least as many elements. -/
theorem length_filter_mono {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = true → q a = true) →
      (l.filter p).length ≤ (l.filter q).length
  | [], _ => by simp
  | a :: as, h => by
      have ih := @length_filter_mono α p q as (fun x hx => h x (List.mem_cons_of_mem a hx))
      have ha := h a (List.mem_cons_self ..)
      simp only [List.filter_cons]
      cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

/-! ## Kind 1: retention with time evidence -/

/-- One signed time claim, after its signature has been checked: the source
`source` says that the time now is at least `atLeast` (seconds since the Unix
epoch). For a Roughtime response this is midpoint minus radius. -/
structure TimeClaim where
  source : String
  atLeast : Nat
deriving DecidableEq, Repr

/-- The owner's trust policy for time: the sources the owner accepts, and how
many distinct ones must agree. -/
structure TimeTrust where
  sources : List String
  quorum : Nat
deriving Repr

/-- Does trusted source `s` attest that the time is at least `t`? -/
def attests (evs : List TimeClaim) (t : Nat) (s : String) : Bool :=
  evs.any (fun c => c.source == s && decide (t ≤ c.atLeast))

/-- The distinct trusted sources that attest time `t`. -/
def attestors (tr : TimeTrust) (evs : List TimeClaim) (t : Nat) : List String :=
  (dedup tr.sources).filter (attests evs t)

/-- The distinct trusted sources that said anything at all. -/
def speakers (tr : TimeTrust) (evs : List TimeClaim) : List String :=
  (dedup tr.sources).filter (fun s => evs.any (fun c => c.source == s))

/-- A quorum of distinct trusted sources attests that time `t` has come. -/
def timeReached (tr : TimeTrust) (evs : List TimeClaim) (t : Nat) : Bool :=
  decide (tr.quorum ≤ (attestors tr evs t).length)

/-- A storage policy: the kinds a pod has. -/
structure Policy where
  /-- Retention period in seconds; `none` keeps data until it is deleted. -/
  retainFor : Option Nat
  /-- Keep the history of textual resources. -/
  versionText : Bool
deriving Repr

/-- One resource. `B` is what storage holds for a body: plaintext bytes for a
plain pod, a `Sealed` record for an encrypted pod. `versions` is newest
first. `deleted` marks a delete that kept the history. -/
structure Res (B : Type) where
  path : String
  contentType : String
  /-- Creation time in seconds, from the time evidence when the resource was
  made. -/
  created : Nat
  versions : List B
  deleted : Bool := false
deriving Repr

/-- A pod's state: its resources. -/
abbrev Pod (B : Type) := List (Res B)

variable {B : Type}

/-- The resource's deadline, if the policy has a retention period. -/
def deadline (pol : Policy) (r : Res B) : Option Nat :=
  pol.retainFor.map (r.created + ·)

/-- The resource is expired: the policy has a period, and a quorum of trusted
sources attests a time at or after creation plus the period. -/
def expired (pol : Policy) (tr : TimeTrust) (evs : List TimeClaim) (r : Res B) : Bool :=
  match deadline pol r with
  | some d => timeReached tr evs d
  | none => false

/-- What a GET returns: nothing for an expired or deleted resource, otherwise
the newest version. -/
def serve (pol : Policy) (tr : TimeTrust) (evs : List TimeClaim) (r : Res B) : Option B :=
  if expired pol tr evs r then none
  else if r.deleted then none
  else r.versions.head?

/-- What a history read (the owner's version list, newest first) returns:
nothing for an expired resource, otherwise every version kept. -/
def history (pol : Policy) (tr : TimeTrust) (evs : List TimeClaim) (r : Res B) : List B :=
  if expired pol tr evs r then [] else r.versions

/-- The sweep: drop every expired resource, with all its versions, from the
pod's state. -/
def sweep (pol : Policy) (tr : TimeTrust) (evs : List TimeClaim) (p : Pod B) : Pod B :=
  p.filter (fun r => !expired pol tr evs r)

/-- An expiry always rests on a quorum: there is a list of `quorum` or more
distinct sources, each in the owner's trust policy, and each with a claim in
the evidence that the deadline has passed. One source cannot expire a
resource by itself when the quorum is two or more, however many claims it
sends. -/
theorem expired_has_quorum {pol tr evs} {r : Res B} (h : expired pol tr evs r = true) :
    ∃ (d : Nat) (l : List String), deadline pol r = some d ∧ l.Nodup ∧ tr.quorum ≤ l.length ∧
      ∀ s ∈ l, s ∈ tr.sources ∧ ∃ c ∈ evs, c.source = s ∧ d ≤ c.atLeast := by
  unfold expired at h
  split at h
  · rename_i d hd
    refine ⟨d, attestors tr evs d, hd, ?_, ?_, ?_⟩
    · exact (nodup_dedup _).sublist List.filter_sublist
    · simpa [timeReached] using h
    · intro s hs
      simp only [attestors, List.mem_filter, attests, List.any_eq_true, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq] at hs
      exact ⟨mem_dedup.mp hs.1, hs.2⟩
  · simp at h

/-- More evidence never cancels an expiry. If a resource is expired on some
claims, it stays expired when more claims arrive (from any source, trusted or
not, true or false), so an attacker cannot stop an expiry by sending claims of
an earlier time. -/
theorem expired_mono {pol tr evs evs'} {r : Res B}
    (hsub : ∀ c ∈ evs, c ∈ evs') (h : expired pol tr evs r = true) :
    expired pol tr evs' r = true := by
  unfold expired at *
  split at h
  · rename_i d hd
    simp only [timeReached, decide_eq_true_eq] at *
    refine Nat.le_trans h (length_filter_mono ?_)
    intro s _ hs
    simp only [attests, List.any_eq_true] at *
    obtain ⟨c, hc, hc'⟩ := hs
    exact ⟨c, hsub c hc, hc'⟩
  · simp at h

/-- Claims from sources outside the trust policy change nothing: adding any
number of them neither expires a resource nor stops an expiry. -/
theorem untrusted_irrelevant {pol tr evs} (extra : List TimeClaim) {r : Res B}
    (hx : ∀ c ∈ extra, c.source ∉ tr.sources) :
    expired pol tr (evs ++ extra) r = expired pol tr evs r := by
  unfold expired
  split
  · rename_i d _
    simp only [timeReached, attestors]
    congr 3
    apply List.filter_congr
    intro s hs
    have hs' := mem_dedup.mp hs
    simp only [attests, List.any_append]
    have : extra.any (fun c => c.source == s && decide (d ≤ c.atLeast)) = false := by
      rw [List.any_eq_false]
      intro c hc
      have hne : c.source ≠ s := fun he => hx c hc (he ▸ hs')
      simp [hne]
    rw [this, Bool.or_false]
  · rfl

/-- If fewer than `quorum` distinct trusted sources have said anything at all,
no resource expires, whatever they said. -/
theorem few_speakers_no_expiry {pol tr evs} {r : Res B}
    (h : (speakers tr evs).length < tr.quorum) : expired pol tr evs r = false := by
  unfold expired
  split
  · rename_i d _
    simp only [timeReached, decide_eq_false_iff_not, Nat.not_le]
    refine Nat.lt_of_le_of_lt (length_filter_mono ?_) h
    intro s _ hs
    simp only [attests, List.any_eq_true, Bool.and_eq_true] at *
    obtain ⟨c, hc, hc1, _⟩ := hs
    exact ⟨c, hc, hc1⟩
  · rfl

/-- With a quorum of one or more, no evidence means no expiry: a pod that
cannot reach any time source keeps its data. -/
theorem no_evidence_no_expiry {pol tr} {r : Res B} (hq : 1 ≤ tr.quorum) :
    expired pol tr [] r = false := by
  apply few_speakers_no_expiry
  have : speakers tr [] = [] := by simp [speakers]
  rw [this]; exact hq

/-- No early wipe, under a stated assumption about the sources. Let `now` be
the true time and `correct s` say that source `s` never claims a time later
than `now`. If fewer than `quorum` of the trusted sources are not correct,
then an expired resource's deadline is not later than `now`: the pod never
wipes a resource before its period ends. With `quorum` or more faulty sources
this theorem does not apply, and an early wipe is possible. -/
theorem no_early_wipe {pol tr evs} {r : Res B} (now : Nat) (correct : String → Bool)
    (hcorrect : ∀ c ∈ evs, correct c.source = true → c.atLeast ≤ now)
    (hfaulty : ((dedup tr.sources).filter (fun s => !correct s)).length < tr.quorum)
    (h : expired pol tr evs r = true) :
    ∃ d, deadline pol r = some d ∧ d ≤ now := by
  unfold expired at h
  split at h
  · rename_i d hd
    refine ⟨d, hd, ?_⟩
    refine Nat.le_of_not_lt (fun hlt => ?_)
    simp only [timeReached, decide_eq_true_eq] at h
    have : (attestors tr evs d).length ≤
        ((dedup tr.sources).filter (fun s => !correct s)).length := by
      apply length_filter_mono
      intro s _ hs
      simp only [attests, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hs
      obtain ⟨c, hc, hsrc, hle⟩ := hs
      cases hcs : correct s
      · rfl
      · have := hcorrect c hc (hsrc ▸ hcs)
        omega
    omega
  · simp at h

/-- A pod with no retention period never expires anything. -/
theorem keep_forever_never_expires {pol tr evs} {r : Res B} (h : pol.retainFor = none) :
    expired pol tr evs r = false := by
  simp [expired, deadline, h]

/-- An expired resource is never served. -/
theorem serve_expired_none {pol tr evs} {r : Res B} (h : expired pol tr evs r = true) :
    serve pol tr evs r = none := by
  simp [serve, h]

/-- An expired resource has no readable history: no old version can be read
through the history API either. -/
theorem history_expired_empty {pol tr evs} {r : Res B} (h : expired pol tr evs r = true) :
    history pol tr evs r = [] := by
  simp [history, h]

/-- After a sweep, no resource left in the pod's state is expired. -/
theorem sweep_no_expired {pol tr evs} {p : Pod B} :
    ∀ r ∈ sweep pol tr evs p, expired pol tr evs r = false := by
  intro r hr
  simp only [sweep, List.mem_filter, Bool.not_eq_true'] at hr
  exact hr.2

/-- A resource that is expired is not in the pod's state after a sweep. -/
theorem expired_not_in_sweep {pol tr evs} {p : Pod B} {r : Res B}
    (h : expired pol tr evs r = true) : r ∉ sweep pol tr evs p := by
  intro hr
  have := sweep_no_expired r hr
  simp_all

/-- A sweep keeps every resource that is not expired: the retention kind does
not lose live data. -/
theorem sweep_keeps_live {pol tr evs} {p : Pod B} {r : Res B}
    (hr : r ∈ p) (h : expired pol tr evs r = false) : r ∈ sweep pol tr evs p := by
  simp [sweep, hr, h]

/-! ## Kind 2: encrypted at rest -/

/-- An abstract authenticated cipher. `K` keys, `P` plaintexts, `C`
ciphertexts. The two fields are the assumptions this file makes about it; see
the module docstring for what they leave out. -/
structure Cipher (K P C : Type) where
  enc : K → P → C
  dec : K → C → Option P
  /-- The right key decrypts. -/
  dec_enc : ∀ k p, dec k (enc k p) = some p
  /-- A different key decrypts nothing (authenticated decryption fails). -/
  dec_wrong : ∀ k k' p, k ≠ k' → dec k' (enc k p) = none

/-- What encrypted storage holds for a body: the identifier of the key it is
sealed under, and the ciphertext. No key and no plaintext. -/
structure Sealed (C : Type) where
  keyId : String
  ct : C

/-- The key holder, outside storage: key identifiers and keys. -/
abbrev KeyHolder (K : Type) := List (String × K)

variable {K P C : Type}

/-- Seal a plaintext under a key. -/
def sealWith (cph : Cipher K P C) (kid : String) (k : K) (p : P) : Sealed C :=
  { keyId := kid, ct := cph.enc k p }

/-- Read a sealed record: ask the key holder for its key, then decrypt. -/
def openSealed (cph : Cipher K P C) (kh : KeyHolder K) (s : Sealed C) : Option P :=
  match kh.lookup s.keyId with
  | some k => cph.dec k s.ct
  | none => none

/-- Destroy a key: remove it from the key holder. -/
def shred (kh : KeyHolder K) (kid : String) : KeyHolder K :=
  kh.filter (fun e => e.1 != kid)

theorem lookup_shred_self (kh : KeyHolder K) (kid : String) :
    (shred kh kid).lookup kid = none := by
  induction kh with
  | nil => rfl
  | cons e es ih =>
      obtain ⟨a, b⟩ := e
      by_cases h : a = kid
      · subst h; simp [shred] at ih ⊢; exact ih
      · simp only [shred, List.filter_cons, bne_iff_ne, ne_eq, h, not_false_eq_true,
          ite_true, List.lookup_cons] at ih ⊢
        have : (kid == a) = false := by simp; exact Ne.symm h
        simp [this, ih]

theorem lookup_shred_other (kh : KeyHolder K) {kid kid' : String} (hne : kid' ≠ kid) :
    (shred kh kid).lookup kid' = kh.lookup kid' := by
  induction kh with
  | nil => rfl
  | cons e es ih =>
      obtain ⟨a, b⟩ := e
      by_cases h : a = kid
      · subst h
        have : (kid' == a) = false := by simpa using hne
        simp [shred, List.lookup_cons, this] at ih ⊢; exact ih
      · simp only [shred, List.filter_cons, bne_iff_ne, ne_eq, h, not_false_eq_true,
          ite_true, List.lookup_cons] at ih ⊢
        split <;> simp_all

/-- The key holder reads back what was sealed, when it holds the key. -/
theorem seal_opens (cph : Cipher K P C) {kh : KeyHolder K} {kid k} (p : P)
    (hk : kh.lookup kid = some k) : openSealed cph kh (sealWith cph kid k p) = some p := by
  simp [openSealed, sealWith, hk, cph.dec_enc]

/-- Reading needs the key: if the key holder has no key for the record, the
record yields no plaintext. -/
theorem open_needs_key (cph : Cipher K P C) {kh : KeyHolder K} {s : Sealed C}
    (h : kh.lookup s.keyId = none) : openSealed cph kh s = none := by
  simp [openSealed, h]

/-- A different key reads nothing: a key holder with a different key under
the same identifier (a wrong or substituted key) gets no plaintext. -/
theorem open_wrong_key (cph : Cipher K P C) {kh : KeyHolder K} {kid k k'} (p : P)
    (hk : kh.lookup kid = some k') (hne : k ≠ k') :
    openSealed cph kh (sealWith cph kid k p) = none := by
  simp [openSealed, sealWith, hk, cph.dec_wrong k k' p hne]

/-- Destroying a key makes every record sealed under it unreadable. -/
theorem shred_unreadable (cph : Cipher K P C) (kh : KeyHolder K) {s : Sealed C} :
    openSealed cph (shred kh s.keyId) s = none :=
  open_needs_key cph (lookup_shred_self kh s.keyId)

/-- Crypto-shredding reaches backups. A backup is any list of sealed records
copied out of storage at any time, before or after the key was destroyed.
After the key is destroyed, no record in it that was sealed under that key can
be read through the key holder. (This assumes, as the module docstring says,
that no other copy of the key exists and that the cipher is sound.) -/
theorem shred_backup_unreadable (cph : Cipher K P C) (kh : KeyHolder K) (kid : String)
    (backup : List (Sealed C)) :
    ∀ s ∈ backup, s.keyId = kid → openSealed cph (shred kh kid) s = none := by
  intro s _ hs
  subst hs
  exact shred_unreadable cph kh

/-- Destroying one key does not affect records sealed under other keys. -/
theorem shred_spares_other_keys (cph : Cipher K P C) (kh : KeyHolder K) {kid : String}
    {s : Sealed C} (hne : s.keyId ≠ kid) :
    openSealed cph (shred kh kid) s = openSealed cph kh s := by
  simp [openSealed, lookup_shred_other kh hne]

/-! ## Kind 3: versioning except binaries -/

/-- The media type without parameters and surrounding space, in lower case. -/
def essence (ct : String) : String :=
  (((ct.splitOn ";").headD "").trimAscii.toString).toLower

/-- The structured-syntax suffixes and subtypes that count as text under
`application/`. -/
def textualAppTypes : List String :=
  ["json", "xml", "turtle", "n-triples", "n-quads", "trig"]

/-- Textual content types: `text/*`, or `application/(…+)?(json|xml|turtle|
n-triples|n-quads|trig)`, as the shell decides. Everything else is binary. -/
def isTextual (ct : String) : Bool :=
  let e := essence ct
  if e.startsWith "text/" then true
  else if e.startsWith "application/" then
    let sub := e.drop "application/".length |>.toString
    textualAppTypes.any (fun t => sub == t || sub.endsWith ("+" ++ t))
  else false

/-- Write a new body. A textual resource on a pod that versions text keeps
its previous versions; any other write replaces. A write clears `deleted`. -/
def write (pol : Policy) (r : Res B) (b : B) : Res B :=
  if pol.versionText && isTextual r.contentType then
    { r with versions := b :: r.versions, deleted := false }
  else
    { r with versions := [b], deleted := false }

/-- A run of writes, in order. -/
def writeAll (pol : Policy) (r : Res B) (bs : List B) : Res B :=
  bs.foldl (write pol) r

/-- Does the policy keep history for this resource? -/
def keepsHistory (pol : Policy) (r : Res B) : Bool :=
  pol.versionText && isTextual r.contentType

/-- Delete. A resource with history is kept, marked deleted, so its history
can be read and restored; any other resource is removed. -/
def delete (pol : Policy) (r : Res B) : Option (Res B) :=
  if keepsHistory pol r then some { r with deleted := true } else none

/-- Purge: remove a resource and its history from the pod. -/
def purge (p : Pod B) (path : String) : Pod B :=
  p.filter (fun r => r.path != path)

/-- On a pod that versions text, a write of a textual resource keeps the
previous version: the new body goes on top of the old ones. -/
theorem write_text_keeps_previous {pol} {r : Res B} (b : B)
    (hv : pol.versionText = true) (ht : isTextual r.contentType = true) :
    (write pol r b).versions = b :: r.versions := by
  simp [write, hv, ht]

/-- A write of a binary resource replaces it: after the write it has exactly
one version, the new one. -/
theorem write_binary_replaces {pol} {r : Res B} (b : B)
    (ht : isTextual r.contentType = false) :
    (write pol r b).versions = [b] := by
  simp [write, ht]

theorem write_contentType {pol} {r : Res B} {b : B} :
    (write pol r b).contentType = r.contentType := by
  unfold write; split <;> rfl

/-- History is complete for text. After any run of writes, reading the
versions oldest first gives the versions that were there before, then every
body written, in the order written. Nothing is lost or reordered. -/
theorem writes_history_complete {pol} (bs : List B) {r : Res B}
    (hv : pol.versionText = true) (ht : isTextual r.contentType = true) :
    (writeAll pol r bs).versions.reverse = r.versions.reverse ++ bs := by
  induction bs generalizing r with
  | nil => simp [writeAll]
  | cons b bs ih =>
      simp only [writeAll, List.foldl_cons] at ih ⊢
      rw [ih (by rw [write_contentType]; exact ht), write_text_keeps_previous b hv ht]
      simp

/-- A binary resource has at most one version, whatever writes are made. -/
theorem binary_at_most_one_version {pol} (bs : List B) {r : Res B}
    (ht : isTextual r.contentType = false) (h1 : r.versions.length ≤ 1) :
    (writeAll pol r bs).versions.length ≤ 1 := by
  induction bs generalizing r with
  | nil => simpa [writeAll] using h1
  | cons b bs ih =>
      simp only [writeAll, List.foldl_cons] at ih ⊢
      exact ih (by rw [write_contentType]; exact ht) (by rw [write_binary_replaces b ht]; simp)

/-- On a pod that does not version, no resource ever has more than one
version. -/
theorem unversioned_at_most_one_version {pol} (bs : List B) {r : Res B}
    (hv : pol.versionText = false) (h1 : r.versions.length ≤ 1) :
    (writeAll pol r bs).versions.length ≤ 1 := by
  induction bs generalizing r with
  | nil => simpa [writeAll] using h1
  | cons b bs ih =>
      simp only [writeAll, List.foldl_cons] at ih ⊢
      exact ih (by simp [write, hv])

/-- After a delete, the resource is not served: either it is gone, or it is
kept only for its history and GET returns nothing. -/
theorem delete_hides_current {pol tr evs} {r : Res B} :
    ∀ r' ∈ delete pol r, serve pol tr evs r' = none := by
  intro r' h
  unfold delete at h
  split at h
  · simp only [Option.mem_def, Option.some.injEq] at h
    subst h
    simp only [serve]
    split <;> rfl
  · simp at h

/-- A delete of a textual resource on a versioning pod keeps every version
for the owner's history read (until expiry or a purge). -/
theorem delete_text_keeps_history {pol} {r : Res B}
    (hv : pol.versionText = true) (ht : isTextual r.contentType = true) :
    ∃ r', delete pol r = some r' ∧ r'.versions = r.versions ∧ r'.deleted = true := by
  simp [delete, keepsHistory, hv, ht]

/-- A delete of a binary resource removes it: no version is kept. -/
theorem delete_binary_removes {pol} {r : Res B} (ht : isTextual r.contentType = false) :
    delete pol r = none := by
  simp [delete, keepsHistory, ht]

/-- A write after a delete serves the new body (when not expired). -/
theorem write_after_delete_serves {pol tr evs} {r : Res B} (b : B)
    (hx : expired pol tr evs (write pol r b) = false) :
    serve pol tr evs (write pol r b) = some b := by
  unfold write at *
  split <;> simp_all [serve]

/-- A purge removes every resource at that path, with its history. -/
theorem purge_removes {p : Pod B} {path : String} : ∀ r ∈ purge p path, r.path ≠ path := by
  intro r hr
  simp only [purge, List.mem_filter, bne_iff_ne, ne_eq] at hr
  exact hr.2

/-! ## Kind 4: combinations -/

/-- Retention covers history. Expiry depends only on a resource's creation
time, so every resource left after a sweep is unexpired, and every version
left in the pod (current or historical) belongs to an unexpired resource. No
old version of an expired resource survives in the pod's state. -/
theorem sweep_drops_every_version {pol tr evs} {p : Pod B} :
    ∀ r ∈ sweep pol tr evs p, ∀ _v ∈ r.versions, expired pol tr evs r = false := by
  intro r hr _ _
  exact sweep_no_expired r hr

/-- Write a plaintext body to an encrypted pod: seal it under the pod key,
then write the sealed record with the pod's versioning rule. -/
def encWrite (cph : Cipher K P C) (pol : Policy) (kid : String) (k : K)
    (r : Res (Sealed C)) (p : P) : Res (Sealed C) :=
  write pol r (sealWith cph kid k p)

/-- Every version is a ciphertext sealed under key `kid`. -/
def AllSealed (cph : Cipher K P C) (kid : String) (r : Res (Sealed C)) : Prop :=
  ∀ v ∈ r.versions, ∃ k p, v = sealWith cph kid k p

/-- An encrypted write keeps the invariant: no stored version, new or old, is
anything but a ciphertext under the pod key. -/
theorem encWrite_sealed (cph : Cipher K P C) (pol : Policy) (kid : String) (k : K)
    {r : Res (Sealed C)} (p : P) (h : AllSealed cph kid r) :
    AllSealed cph kid (encWrite cph pol kid k r p) := by
  intro v hv
  unfold encWrite write at hv
  split at hv
  · simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ⟨k, p, rfl⟩
    · exact h v hv
  · simp only [List.mem_singleton] at hv
    exact ⟨k, p, hv⟩

/-- Encrypted and versioned: after any run of encrypted writes, every version
in the history is sealed under the pod key. -/
theorem encWrites_all_sealed (cph : Cipher K P C) (pol : Policy) (kid : String) (k : K)
    (ps : List P) {r : Res (Sealed C)} (h : AllSealed cph kid r) :
    AllSealed cph kid (ps.foldl (encWrite cph pol kid k) r) := by
  induction ps generalizing r with
  | nil => exact h
  | cons p ps ih => exact ih (encWrite_sealed cph pol kid k p h)

theorem encWrite_contentType {cph : Cipher K P C} {pol kid k} {r : Res (Sealed C)} {p : P} :
    (encWrite cph pol kid k r p).contentType = r.contentType := write_contentType

/-- Encrypted and versioned: the key holder can read back the complete history
of a textual resource. Opening the versions oldest first gives what could be
read before, then every plaintext written, in order. -/
theorem encrypted_history_complete (cph : Cipher K P C) {pol} {kh : KeyHolder K} {kid k}
    (ps : List P) {r : Res (Sealed C)}
    (hv : pol.versionText = true) (ht : isTextual r.contentType = true)
    (hk : kh.lookup kid = some k) :
    ((ps.foldl (encWrite cph pol kid k) r).versions.reverse.map (openSealed cph kh)) =
      r.versions.reverse.map (openSealed cph kh) ++ ps.map some := by
  induction ps generalizing r with
  | nil => simp
  | cons p ps ih =>
      simp only [List.foldl_cons]
      rw [ih (by rw [encWrite_contentType]; exact ht)]
      simp [encWrite, write_text_keeps_previous _ hv ht, seal_opens cph p hk]

/-- One key destruction reaches the complete history: on an encrypted pod,
after the pod key is destroyed, no version of any resource (current or old)
can be read. -/
theorem shred_unreadable_every_version (cph : Cipher K P C) (kh : KeyHolder K) (kid : String)
    {p : Pod (Sealed C)} (h : ∀ r ∈ p, AllSealed cph kid r) :
    ∀ r ∈ p, ∀ v ∈ r.versions, openSealed cph (shred kh kid) v = none := by
  intro r hr v hv
  obtain ⟨k, q, rfl⟩ := h r hr v hv
  exact shred_unreadable cph kh

/-! ## Examples -/

/-- Seconds in a day. -/
def day : Nat := 86400

/-- A pod that keeps 90 days and versions text. -/
def pod90 : Policy := { retainFor := some (90 * day), versionText := true }

/-- Trust three time sources, two must agree. -/
def twoOfThree : TimeTrust := { sources := ["roughtime-a", "roughtime-b", "tsa-c"], quorum := 2 }

/-- A note made at time 0. -/
def note : Res String :=
  { path := "/notes/a.txt", contentType := "text/plain; charset=utf-8", created := 0,
    versions := ["v1"] }

/-- A photo made at time 0. -/
def photo : Res String :=
  { path := "/photos/p.png", contentType := "image/png", created := 0, versions := ["png1"] }

-- 91 days, one trusted source: not enough.
#guard expired pod90 twoOfThree [⟨"roughtime-a", 91 * day⟩] note == false
-- 91 days, the same source twice: still one source.
#guard expired pod90 twoOfThree [⟨"roughtime-a", 91 * day⟩, ⟨"roughtime-a", 92 * day⟩] note == false
-- 91 days from two untrusted sources and one trusted: not enough.
#guard expired pod90 twoOfThree
  [⟨"evil-1", 91 * day⟩, ⟨"evil-2", 91 * day⟩, ⟨"tsa-c", 91 * day⟩] note == false
-- Two trusted sources at 91 days: expired; not served; swept.
#guard expired pod90 twoOfThree [⟨"roughtime-a", 91 * day⟩, ⟨"tsa-c", 91 * day⟩] note == true
#guard serve pod90 twoOfThree [⟨"roughtime-a", 91 * day⟩, ⟨"tsa-c", 91 * day⟩] note == none
#guard (sweep pod90 twoOfThree [⟨"roughtime-a", 91 * day⟩, ⟨"tsa-c", 91 * day⟩]
  [note, { photo with created := 50 * day }]).map (·.path) == ["/photos/p.png"]
-- Two trusted sources at 89 days: not yet.
#guard expired pod90 twoOfThree [⟨"roughtime-a", 89 * day⟩, ⟨"tsa-c", 89 * day⟩] note == false

-- A text file edited twice keeps all three versions, oldest first.
#guard (writeAll pod90 note ["v2", "v3"]).versions.reverse == ["v1", "v2", "v3"]
-- A PNG replaced twice has one version.
#guard (writeAll pod90 photo ["png2", "png3"]).versions == ["png3"]
-- Delete: the note keeps history and is not served; the photo is gone.
#guard ((delete pod90 note).map (·.versions)) == some ["v1"]
#guard ((delete pod90 note).bind (serve pod90 twoOfThree [])) == none
#guard (delete pod90 photo).isNone

-- The textual rule.
#guard isTextual "text/html"
#guard isTextual "Text/Turtle; charset=UTF-8"
#guard isTextual "application/ld+json"
#guard isTextual "application/n-quads"
#guard isTextual "application/sparql-results+xml"
#guard isTextual "application/trig"
#guard !isTextual "image/png"
#guard !isTextual "application/octet-stream"
#guard !isTextual "application/pdf"
#guard !isTextual "application/jsonx"

/-- A toy cipher for the examples only: XOR-free tagging, so it decrypts with
the right key and fails with any other. It has no secrecy. -/
def toyCipher : Cipher Nat String (Nat × String) where
  enc k p := (k, p)
  dec k c := if c.1 = k then some c.2 else none
  dec_enc k p := by simp
  dec_wrong k k' p h := by simp [h]

example : openSealed toyCipher [("pod", 7)] (sealWith toyCipher "pod" 7 "hello") = some "hello" :=
  seal_opens toyCipher "hello" rfl

example : openSealed toyCipher (shred [("pod", 7)] "pod") (sealWith toyCipher "pod" 7 "hello") = none :=
  shred_unreadable (s := sealWith toyCipher "pod" 7 "hello") toyCipher _

#guard openSealed toyCipher (shred [("pod", 7)] "pod") (sealWith toyCipher "pod" 7 "hello") == none

end L4Factoidal.LWS.PodKinds
