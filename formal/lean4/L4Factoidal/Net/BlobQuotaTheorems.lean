import L4Factoidal.Net.BlobUrls

namespace L4Factoidal.Net.BlobUrls

private theorem foldl_payload_add (entries : List Entry) (n : Nat) :
    entries.foldl (fun acc e => acc + e.body.size) n =
      n + entries.foldl (fun acc e => acc + e.body.size) 0 := by
  induction entries generalizing n with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (n + e.body.size), ih e.body.size]
    omega

private theorem foldl_payload_cons (e : Entry) (es : List Entry) :
    (e :: es).foldl (fun n x => n + x.body.size) 0 =
      e.body.size + es.foldl (fun n x => n + x.body.size) 0 := by
  simpa only [List.foldl_cons, Nat.zero_add] using foldl_payload_add es e.body.size

private theorem foldl_payload_filter_le (entries : List Entry) (keep : Entry → Bool) :
    (entries.filter keep).foldl (fun n e => n + e.body.size) 0 ≤
      entries.foldl (fun n e => n + e.body.size) 0 := by
  induction entries with
  | nil => simp
  | cons e es ih =>
    cases hp : keep e with
    | false =>
      rw [List.filter_cons, if_neg (by simp [hp]), foldl_payload_cons]
      omega
    | true =>
      rw [List.filter_cons, if_pos (by simp [hp]), foldl_payload_cons, foldl_payload_cons]
      omega

/-- Kind: resource invariant.
Says: the default store has exact payload accounting and meets both quotas.
Does not say: that arbitrary stores built with the public constructor meet the quotas. -/
theorem default_payload_quota :
    ({} : Store).held = ({} : Store).entries.foldl (fun n e => n + e.body.size) 0 ∧
      ({} : Store).entries.foldl (fun n e => n + e.body.size) 0 ≤ maxHeld ∧
      ({} : Store).entries.length ≤ maxEntries :=
  ⟨rfl, Nat.zero_le _, Nat.zero_le _⟩

/-- Kind: resource invariant.
Says: a successful addition to a correctly counted store adds exactly the new
body's bytes to the logical payload, counts them in `held`, and meets both quotas.
Does not say: that the quotas bound temporary copies, metadata, or process memory. -/
theorem add_payload_quota (s s' : Store) (origin uuid type url : String) (body : ByteArray)
    (hcount : s.held = s.entries.foldl (fun n e => n + e.body.size) 0)
    (ha : add s origin uuid type body = some (s', url)) :
    s'.held = s'.entries.foldl (fun n e => n + e.body.size) 0 ∧
      s'.entries.foldl (fun n e => n + e.body.size) 0 =
        s.entries.foldl (fun n e => n + e.body.size) 0 + body.size ∧
      s'.entries.foldl (fun n e => n + e.body.size) 0 ≤ maxHeld ∧
      s'.entries.length ≤ maxEntries := by
  obtain ⟨hentries, hheld, hcap⟩ := add_bounds s s' origin uuid type url body ha
  have hpayload : s'.entries.foldl (fun n e => n + e.body.size) 0 =
      s.entries.foldl (fun n e => n + e.body.size) 0 + body.size := by
    unfold add at ha
    split at ha
    · simp at ha
    · simp only [Option.some.injEq, Prod.mk.injEq] at ha
      rw [← ha.1]
      change ({ url := urlFor origin uuid, origin, type, body } :: s.entries : List Entry).foldl
        (fun n e => n + e.body.size) 0 = _
      rw [foldl_payload_cons]
      exact Nat.add_comm _ _
  have hexact : s'.held = s'.entries.foldl (fun n e => n + e.body.size) 0 :=
    calc
      s'.held = s.held + body.size := hheld
      _ = s'.entries.foldl (fun n e => n + e.body.size) 0 := by rw [hcount, hpayload]
  exact ⟨hexact, hpayload, by simpa only [← hexact] using hcap, hentries⟩

/-- Kind: resource invariant.
Says: revocation recomputes the payload counter and can only decrease the
logical payload and entry count, even if the old counter was stale.
Does not say: that revocation must release bytes for a particular URL. -/
theorem revoke_payload (s : Store) (origin url : String) :
    let s' := revoke s origin url
    s'.held = s'.entries.foldl (fun n e => n + e.body.size) 0 ∧
      s'.entries.foldl (fun n e => n + e.body.size) 0 ≤
        s.entries.foldl (fun n e => n + e.body.size) 0 ∧
      s'.entries.length ≤ s.entries.length := by
  unfold revoke
  exact ⟨rfl, foldl_payload_filter_le _ _, List.length_filter_le _ _⟩

/-- Kind: resource invariant.
Says: revoking from a store whose logical payload and entry count satisfy
the quotas yields exact accounting and preserves those quotas.
Does not say: that revocation enforces a quota for each origin. -/
theorem revoke_payload_quota (s : Store) (origin url : String)
    (hcap : s.entries.foldl (fun n e => n + e.body.size) 0 ≤ maxHeld)
    (hentries : s.entries.length ≤ maxEntries) :
    let s' := revoke s origin url
    s'.held = s'.entries.foldl (fun n e => n + e.body.size) 0 ∧
      s'.entries.foldl (fun n e => n + e.body.size) 0 ≤ maxHeld ∧
      s'.entries.length ≤ maxEntries := by
  obtain ⟨hcount, hbytes, hlength⟩ := revoke_payload s origin url
  exact ⟨hcount, Nat.le_trans hbytes hcap, Nat.le_trans hlength hentries⟩

#print axioms default_payload_quota
#print axioms add_payload_quota
#print axioms revoke_payload
#print axioms revoke_payload_quota

end L4Factoidal.Net.BlobUrls
