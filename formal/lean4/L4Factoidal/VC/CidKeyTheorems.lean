import L4Factoidal.CID.Retrieve
import L4Factoidal.VC.Cryptosuite

namespace L4Factoidal.VC.Cryptosuite

open L4Factoidal.VC.DataIntegrity (inForceAt)

private theorem resolvePublicKey_cid_method {docs : List (String × String)}
    {now : Option Int} {vm purpose : String} {pk : PublicKey}
    (h : resolvePublicKey docs now vm purpose = .ok pk)
    (hd : publicKeyOfDidKey? vm = none) :
    ∃ rel m, CID.Relationship.ofName? purpose = some rel ∧
      CID.retrieveWith docs vm rel = .ok m ∧
      publicKeyOfMethod? m = some pk ∧ inForceAt now m = true := by
  unfold resolvePublicKey at h
  rw [hd] at h
  simp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i rel hrel
      split at h
      · simp at h
      · simp at h
      · rename_i m hm
        split at h
        · simp at h
        · rename_i hforce
          split at h
          · rename_i pk' hk
            simp only [Except.ok.injEq] at h
            subst h
            exact ⟨rel, m, hrel, hm, hk, by simpa using hforce⟩
          · simp at h

/-- Kind: adapter soundness.
Says: successful CID resolution supplies the cryptosuite key of a method
authorised for the requested purpose in a parsed controller document from the
supplied table. When a verification time is given, the method is in force then.
Does not say: that the caller obtained authentic bytes, trusts the issuer, or
verified a signature. The did:key path has separate rules. -/
theorem resolvePublicKey_cid_document {docs : List (String × String)}
    {now : Option Int} {vm purpose : String} {pk : PublicKey}
    (h : resolvePublicKey docs now vm purpose = .ok pk)
    (hd : publicKeyOfDidKey? vm = none) :
    ∃ rel m url frag text j d,
      CID.Relationship.ofName? purpose = some rel ∧
      CID.documentUrlOf vm = .ok (url, frag) ∧
      (url, text) ∈ docs ∧ JSON.parseJson? text = some j ∧
      CID.parseDocument j = .ok d ∧ d.id = url ∧
      CID.absolute d.id m.id = vm ∧ CID.absolute d.id m.controller = url ∧
      d.associated rel vm = true ∧ publicKeyOfMethod? m = some pk ∧
      ∀ t, now = some t → CID.methodInForce t m = true := by
  obtain ⟨rel, m, hrel, hm, hk, hforce⟩ := resolvePublicKey_cid_method h hd
  obtain ⟨url, frag, text, j, hu, hmem, hj, hr⟩ := CID.retrieveWith_ok hm
  obtain ⟨url', frag', d, hu', hdoc, hid, _, hmid, hctl, hassoc, _⟩ :=
    CID.retrieveFromDocument_sound hr
  rw [hu] at hu'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hu'
  obtain ⟨rfl, rfl⟩ := hu'
  refine ⟨rel, m, url, frag, text, j, d, hrel, hu, hmem, hj, hdoc, hid,
    hmid, hctl, hassoc, hk, ?_⟩
  intro t ht
  simpa only [ht, inForceAt] using hforce

#print axioms resolvePublicKey_cid_document

end L4Factoidal.VC.Cryptosuite
