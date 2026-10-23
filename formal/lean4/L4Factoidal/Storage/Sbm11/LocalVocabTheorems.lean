/-
L4Factoidal.Storage.Sbm11.LocalVocabTheorems — the query-local vocabulary of
the nested evaluator (https://github.com/danbri/factoidal/issues/776; lemma
L5w of docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

A term with no id in the store (a VALUES term, a BIND value, a value of a
sub-SELECT) gets a query-local id: `IdQuery.localIdOf` gives it
`localId k = 15 · 2^60 + k`, `k` its index in the vocabulary of the run state
(`IdGroup.NSt.vocab`, indexed by `NSt.localIdx`), and `Store.withLocal`
decodes it. So the decoder of a row depends on the state. This file states
the invariant of that vocabulary and the decoder of a state:

* `decV dec voc`: a local id `localId k` decodes to entry `k` of `voc`, any
  other id as `dec` (the store's `termOf`); `okV ok voc`: the ids in `ok`
  and the local ids of `voc`.
* `VocInv cid voc ix`: at most `2^60` entries; `ix` is the index of `voc`
  (`ix[key]? = some k` exactly when entry `k` is `key`, so no entry twice);
  each entry has no id in the store (`cid` is `none`), is its own
  `normalizeTerm` and holds no `rdf:XMLLiteral` (`IdQuery.hasXmlLit`).
* `hdecV`: `Term.eqb` of two decoded ids in `okV ok voc` is id equality,
  from `hdec` on `ok` and the invariant (`eqb_norm_eq`: two terms that are
  their own `normalizeTerm` and hold no `rdf:XMLLiteral` are `Term.eqb`
  exactly when they are equal).
* `decV_mono`, `okV_mono`: the state only grows (the vocabulary of a later
  state has the earlier one as a prefix), and an id decodes the same in the
  later state.
* `termIdM_spec`: `IdQuery.termIdM` keeps the invariant and gives an id in
  `okV` of the new state that decodes to `normalizeTerm t`; or it refuses
  (`LocalRefusal`: an `rdf:XMLLiteral` with no store id, or a vocabulary of
  `2^60` terms; the harness then runs the reference evaluator).
* `valueIdM_spec`: `IdQuery.valueIdM`, the id of a VALUES, BIND or
  sub-SELECT value, as `termIdM`, or the refusal `langCaseMsg` for a value
  that is not its own `normalizeTerm`; an id it gives decodes to the value
  itself.
* `Ends`: a run of the nested evaluator ends with such a refusal or with a
  result, and `ends_bind` composes it.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.FilterIdTheorems

namespace L4Factoidal.Storage.Sbm11.LocalVocab

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.IdGroup (NSt NM)
open L4Factoidal.Storage.Sbm11.IdLeaf (CidOk)
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow decRow RowIds)
open L4Factoidal.Storage.Sbm11.FilterIdTheorems (eqb_normalize normalize_idem)

/-! ## Local ids -/

theorem localId_toNat (k : Nat) (hk : k < two60) : (localId k).toNat = tagLocal * two60 + k := by
  unfold localId
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  unfold tagLocal two60 at *
  omega

theorem tag_localId (k : Nat) (hk : k < two60) : tagOf (localId k) = tagLocal := by
  unfold tagOf
  rw [UInt64.toNat_shiftRight, localId_toNat k hk]
  have : (UInt64.toNat 60 % 64) = 60 := rfl
  rw [this, Nat.shiftRight_eq_div_pow]
  unfold tagLocal two60 at *
  omega

theorem mod_localId (k : Nat) (hk : k < two60) : (localId k).toNat % two60 = k := by
  rw [localId_toNat k hk]; unfold tagLocal two60 at *; omega

/-- No local id is 0 (`OptJoin.unbound`). -/
theorem localId_ne_zero {k : Nat} (hk : k < two60) : localId k ≠ 0 := by
  intro e
  have := tag_localId k hk
  rw [e] at this
  cases this

theorem localId_inj {k k' : Nat} (hk : k < two60) (hk' : k' < two60) (h : localId k = localId k') : k = k' := by
  have := congrArg (fun x : UInt64 => x.toNat % two60) h
  simp only [mod_localId k hk, mod_localId k' hk'] at this
  exact this

/-! ## Terms that are their own normal form -/

theorem normalizeLit_self (l : WfLiteral) (h : normalizeLit l = .literal l) :
    ∀ tag, l.val.langTag = some tag → tag.toLower = tag := by
  intro tag ht
  unfold normalizeLit at h
  rw [ht] at h
  simp only at h
  split at h
  · simp only [Term.literal.injEq] at h
    have := congrArg (fun x : WfLiteral => x.val.langTag) h
    simp only at this
    simpa [ht] using this
  · next hn =>
    exfalso; apply hn
    have := l.property
    unfold literalWf at this ⊢
    rw [ht] at this
    dsimp only
    revert this
    cases l.val.direction <;> simp

/-- Two terms that are their own `normalizeTerm`, the first with no
    `rdf:XMLLiteral`, are `Term.eqb` only when they are equal: `Term.eqb`
    compares language tags without case (both are lower case here) and
    `rdf:XMLLiteral` lexical forms by canonical XML (none here). -/
theorem eqb_norm_eq : ∀ (t s : Term), normalizeTerm t = t → normalizeTerm s = s → hasXmlLit t = false →
    t.eqb s = true → t = s
  | .iri i, .iri j, _, _, _, h => by simp [Term.eqb] at h; exact congrArg Term.iri (Subtype.ext h)
  | .bnode i, .bnode j, _, _, _, h => by simp [Term.eqb] at h; rw [h]
  | .literal l1, .literal l2, h1, h2, hx, h => by
    simp only [normalizeTerm] at h1 h2
    have t1 := normalizeLit_self l1 h1
    have t2 := normalizeLit_self l2 h2
    simp only [hasXmlLit, beq_eq_false_iff_ne, ne_eq] at hx
    simp only [Term.eqb, Literal.eqb, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hlex, hdt⟩, hlang⟩, hdir⟩ := h
    rw [if_neg (fun hh => hx hh.1), beq_iff_eq] at hlex
    congr 1
    apply Subtype.ext
    obtain ⟨⟨a1, d1, g1, r1⟩, _⟩ := l1
    obtain ⟨⟨a2, d2, g2, r2⟩, _⟩ := l2
    simp only at hlex hdt hlang hdir t1 t2 ⊢
    subst hlex hdt hdir
    congr 1
    cases g1 with
    | none => cases g2 with
      | none => rfl
      | some _ => simp [langTagOptionEq] at hlang
    | some a => cases g2 with
      | none => simp [langTagOptionEq] at hlang
      | some b =>
        simp only [langTagOptionEq, langTagEq, beq_iff_eq] at hlang
        rw [t1 a rfl, t2 b rfl] at hlang
        rw [hlang]
  | .tripleTerm s1 p1 o1, .tripleTerm s2 p2 o2, h1, h2, hx, h => by
    simp only [normalizeTerm, Term.tripleTerm.injEq, true_and] at h1 h2
    simp only [hasXmlLit] at hx
    simp only [Term.eqb, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hs, hp⟩, ho⟩ := h
    have := eqb_norm_eq o1 o2 h1 h2 hx ho
    subst this hp
    cases s1 <;> cases s2 <;> simp_all [Subject.eqb]
    exact Subtype.ext hs
  | .iri _, .bnode _, _, _, _, h | .iri _, .literal _, _, _, _, h | .iri _, .tripleTerm _ _ _, _, _, _, h
  | .bnode _, .iri _, _, _, _, h | .bnode _, .literal _, _, _, _, h | .bnode _, .tripleTerm _ _ _, _, _, _, h
  | .literal _, .iri _, _, _, _, h | .literal _, .bnode _, _, _, _, h | .literal _, .tripleTerm _ _ _, _, _, _, h
  | .tripleTerm _ _ _, .iri _, _, _, _, h | .tripleTerm _ _ _, .bnode _, _, _, _, h
  | .tripleTerm _ _ _, .literal _, _, _, _, h => by simp [Term.eqb] at h

/-! ## The decoder of a state -/

/-- The decoder of a state whose vocabulary is `voc`: `Store.withLocal`'s
    `termOf` (`IdQuery.localTermOf`) as a function. -/
def decV (dec : UInt64 → Term) (voc : Array Term) (x : UInt64) : Term :=
  if tagOf x == tagLocal then
    match voc[x.toNat % two60]? with
    | some t => t
    | none => dec x
  else dec x

/-- The ids of a state whose vocabulary is `voc`: those in `ok` and its
    local ids. -/
def okV (ok : UInt64 → Prop) (voc : Array Term) (x : UInt64) : Prop :=
  ok x ∨ ∃ k, k < voc.size ∧ x = localId k

/-- The invariant of the query-local vocabulary `voc` and its index `ix`. -/
structure VocInv (cid : Term → Option UInt64) (voc : Array Term) (ix : Std.HashMap Term Nat) : Prop where
  size : voc.size ≤ two60
  idx : ∀ (key : Term) (k : Nat), ix[key]? = some k ↔ voc[k]? = some key
  entry : ∀ k (h : k < voc.size), cid voc[k] = none ∧ normalizeTerm voc[k] = voc[k] ∧ hasXmlLit voc[k] = false

/-- The invariant of a run state. -/
def Inv (cid : Term → Option UInt64) (s : NSt) : Prop := VocInv cid s.vocab s.localIdx

theorem vocInv_empty (cid : Term → Option UInt64) : VocInv cid #[] {} := by
  refine ⟨by simp, fun key k => ?_, fun k h => absurd h (by simp)⟩
  simp

theorem inv_empty (cid : Term → Option UInt64) : Inv cid {} := vocInv_empty cid

theorem ok_okV {ok : UInt64 → Prop} {voc : Array Term} {x : UInt64} (h : ok x) : okV ok voc x := Or.inl h

theorem prefix_get {voc1 voc2 : Array Term} (hp : voc1.toList <+: voc2.toList) {k : Nat} (hk : k < voc1.size) :
    voc2[k]? = voc1[k]? := by
  obtain ⟨ext, he⟩ := hp
  rw [← Array.getElem?_toList, ← Array.getElem?_toList, ← he, List.getElem?_append_left (by simpa using hk)]

theorem prefix_size {voc1 voc2 : Array Term} (hp : voc1.toList <+: voc2.toList) : voc1.size ≤ voc2.size := by
  have := hp.length_le
  simpa using this

theorem okV_mono {ok : UInt64 → Prop} {voc1 voc2 : Array Term} (hp : voc1.toList <+: voc2.toList) {x : UInt64}
    (h : okV ok voc1 x) : okV ok voc2 x := by
  rcases h with h | ⟨k, hk, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, by have := prefix_size hp; omega, rfl⟩

theorem decV_ok (dec : UInt64 → Term) {ok : UInt64 → Prop} (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    (voc : Array Term) {x : UInt64} (hx : ok x) : decV dec voc x = dec x := by
  unfold decV
  rw [if_neg (by simpa using hloc x hx)]

theorem decV_local (dec : UInt64 → Term) (voc : Array Term) (hsz : voc.size ≤ two60) {k : Nat} (hk : k < voc.size) :
    decV dec voc (localId k) = voc[k] := by
  have hk' : k < two60 := by omega
  unfold decV
  rw [if_pos (by simp [tag_localId k hk']), mod_localId k hk', Array.getElem?_eq_getElem hk]

theorem decV_mono (dec : UInt64 → Term) {ok : UInt64 → Prop} (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    {voc1 voc2 : Array Term} (hp : voc1.toList <+: voc2.toList) (hsz : voc2.size ≤ two60) {x : UInt64}
    (h : okV ok voc1 x) : decV dec voc2 x = decV dec voc1 x := by
  rcases h with h | ⟨k, hk, rfl⟩
  · rw [decV_ok dec hloc voc2 h, decV_ok dec hloc voc1 h]
  · have h2 : k < voc2.size := by have := prefix_size hp; omega
    rw [decV_local dec voc2 hsz h2, decV_local dec voc1 (by have := prefix_size hp; omega) hk]
    have := prefix_get hp hk
    rw [Array.getElem?_eq_getElem h2, Array.getElem?_eq_getElem hk] at this
    exact Option.some.inj this

theorem rowIds_mono {ok : UInt64 → Prop} {voc1 voc2 : Array Term} (hp : voc1.toList <+: voc2.toList) {r : IdRow}
    (h : RowIds (okV ok voc1) r) : RowIds (okV ok voc2) r := fun a ha => okV_mono hp (h a ha)

theorem decRow_mono (dec : UInt64 → Term) {ok : UInt64 → Prop} (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    {voc1 voc2 : Array Term} (hp : voc1.toList <+: voc2.toList) (hsz : voc2.size ≤ two60) :
    ∀ (r : IdRow), RowIds (okV ok voc1) r → decRow (decV dec voc2) r = decRow (decV dec voc1) r := by
  intro r hr
  unfold decRow
  apply List.map_congr_left
  intro p hp'
  obtain ⟨v, x⟩ := p
  simp only [decV_mono dec hloc hp hsz (hr (v, x) hp')]

theorem rows_mono (dec : UInt64 → Term) {ok : UInt64 → Prop} (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    {voc1 voc2 : Array Term} (hp : voc1.toList <+: voc2.toList) (hsz : voc2.size ≤ two60) (L : List IdRow)
    (hL : ∀ r ∈ L, RowIds (okV ok voc1) r) : L.map (decRow (decV dec voc2)) = L.map (decRow (decV dec voc1)) :=
  List.map_congr_left fun r hr => decRow_mono dec hloc hp hsz r (hL r hr)

/-- No local id is in `ok`. -/
theorem local_not_ok {ok : UInt64 → Prop} (hloc : ∀ x, ok x → tagOf x ≠ tagLocal) {k : Nat} (hk : k < two60) :
    ¬ ok (localId k) := fun h => hloc _ h (tag_localId k hk)

/-- **`Term.eqb` of decoded ids is id equality** on the ids of a state. -/
theorem hdecV (cid : Term → Option UInt64) (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hcid : ∀ c, CidOk dec ok c (cid c))
    (hloc : ∀ x, ok x → tagOf x ≠ tagLocal) {voc : Array Term} {ix : Std.HashMap Term Nat}
    (hinv : VocInv cid voc ix) :
    ∀ x y, okV ok voc x → okV ok voc y → (decV dec voc x).eqb (decV dec voc y) = (x == y) := by
  -- a stored id and a local id
  have mixed : ∀ x k, ok x → (hk : k < voc.size) → (dec x).eqb voc[k] = false ∧ (x == localId k) = false := by
    intro x k hx hk
    have hc := hcid voc[k]
    rw [(hinv.entry k hk).1] at hc
    refine ⟨?_, ?_⟩
    · rw [Term.eqb_symm]; exact hc x hx
    · rw [beq_eq_false_iff_ne]
      intro e; subst e
      exact local_not_ok hloc (by have := hinv.size; omega) hx
  intro x y hx hy
  rcases hx with hx | ⟨k, hk, rfl⟩ <;> rcases hy with hy | ⟨k', hk', rfl⟩
  · rw [decV_ok dec hloc voc hx, decV_ok dec hloc voc hy]; exact hdec x y hx hy
  · rw [decV_ok dec hloc voc hx, decV_local dec voc hinv.size hk']
    rw [(mixed x k' hx hk').1, (mixed x k' hx hk').2]
  · rw [decV_ok dec hloc voc hy, decV_local dec voc hinv.size hk, Term.eqb_symm, (mixed y k hy hk).1,
      BEq.comm, (mixed y k hy hk).2]
  · rw [decV_local dec voc hinv.size hk, decV_local dec voc hinv.size hk']
    by_cases e : k = k'
    · subst e; simp
    · have hne : (localId k == localId k') = false := by
        rw [beq_eq_false_iff_ne]
        intro h
        exact e (localId_inj (by have := hinv.size; omega) (by have := hinv.size; omega) h)
      rw [hne]
      cases hb : voc[k].eqb voc[k'] with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨_, hn1, hx1⟩ := hinv.entry k hk
        obtain ⟨_, hn2, _⟩ := hinv.entry k' hk'
        have heq := eqb_norm_eq _ _ hn1 hn2 hx1 hb
        have i1 := (hinv.idx voc[k] k).mpr (Array.getElem?_eq_getElem hk)
        have i2 := (hinv.idx voc[k] k').mpr (by rw [Array.getElem?_eq_getElem hk', heq])
        rw [i1] at i2
        exact e (Option.some.inj i2)

/-- The decoded ids in `ok` are their own `normalizeTerm` (the dictionary
    lookup is exact on them and answers the folded term, `hcidN`). -/
theorem dec_normal (cid : Term → Option UInt64) (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hcid : ∀ c, CidOk dec ok c (cid c)) (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (x : UInt64) (hx : ok x) : normalizeTerm (dec x) = dec x := by
  have h := hcid (dec x)
  cases e : cid (dec x) with
  | none =>
    rw [e] at h
    have := h x hx
    rw [Term.eqb_refl] at this
    cases this
  | some z =>
    rw [e] at h
    have := h x hx
    rw [Term.eqb_refl] at this
    have hz : z = x := by simpa using this.symm
    subst hz
    exact (hcidN _ _ e).symm

theorem decV_normal (cid : Term → Option UInt64) (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hcid : ∀ c, CidOk dec ok c (cid c)) (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (hloc : ∀ x, ok x → tagOf x ≠ tagLocal) {voc : Array Term} {ix : Std.HashMap Term Nat}
    (hinv : VocInv cid voc ix) (x : UInt64) (hx : okV ok voc x) : normalizeTerm (decV dec voc x) = decV dec voc x := by
  rcases hx with hx | ⟨k, hk, rfl⟩
  · rw [decV_ok dec hloc voc hx]; exact dec_normal cid dec ok hcid hcidN x hx
  · rw [decV_local dec voc hinv.size hk]; exact (hinv.entry k hk).2.1

/-- The dictionary lookup is exact on the ids of a state for a term with an
    id: a local id decodes to a term with no id, so to no term `Term.eqb` to
    one with an id. -/
theorem cidOkV_some (cid : Term → Option UInt64) (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hcid : ∀ c, CidOk dec ok c (cid c)) (hcidok : ∀ t x, cid t = some x → ok x)
    (hloc : ∀ x, ok x → tagOf x ≠ tagLocal) {voc : Array Term} {ix : Std.HashMap Term Nat}
    (hinv : VocInv cid voc ix) (c : Term) (x : UInt64) (hc : cid c = some x) :
    CidOk (decV dec voc) (okV ok voc) c (some x) := by
  intro y hy
  have h := hcid c
  rw [hc] at h
  rcases hy with hy | ⟨k, hk, rfl⟩
  · rw [decV_ok dec hloc voc hy]; exact h y hy
  · rw [decV_local dec voc hinv.size hk]
    have hxk : (x == localId k) = false := by
      rw [beq_eq_false_iff_ne]
      intro e; subst e
      exact local_not_ok hloc (by have := hinv.size; omega) (hcidok c _ hc)
    rw [hxk]
    cases hb : c.eqb voc[k] with
    | false => rfl
    | true =>
      exfalso
      have hk2 := hcid voc[k]
      rw [(hinv.entry k hk).1] at hk2
      have h1 := hk2 x (hcidok c x hc)
      have h2 := h x (hcidok c x hc)
      rw [beq_self_eq_true] at h2
      have := Term.eqb_trans (by rw [Term.eqb_symm]; exact hb) h2
      rw [h1] at this
      cases this

/-- `Store.withLocal` decodes the ids of a state as `decV` does. -/
theorem termOf_withLocal (st : Store Id) (cid : Term → Option UInt64) (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (htermOf : ∀ x, ok x → st.termOf x = pure (dec x)) (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    {voc : Array Term} {ix : Std.HashMap Term Nat} (hinv : VocInv cid voc ix) (x : UInt64) (hx : okV ok voc x) :
    (st.withLocal voc).termOf x = pure (decV dec voc x) := by
  unfold Store.withLocal
  split
  · next he =>
    rcases hx with hx | ⟨k, hk, rfl⟩
    · rw [decV_ok dec hloc voc hx]; exact htermOf x hx
    · simp at he; subst he; simp at hk
  · show localTermOf st voc x = _
    unfold localTermOf decV
    rcases hx with hx | ⟨k, hk, rfl⟩
    · rw [if_neg (by simpa using hloc x hx), if_neg (by simpa using hloc x hx)]
      exact htermOf x hx
    · have hk' : k < two60 := by have := hinv.size; omega
      simp only [tag_localId k hk', beq_self_eq_true, if_true, mod_localId k hk', Array.getElem?_eq_getElem hk]

/-! ## `termIdM` -/

/-- The refusals of the query-local vocabulary, and of a value whose language
    tag is not in lower case (`IdQuery.valueIdM`). -/
def LocalRefusal (e : String) : Prop := e = localFullMsg ∨ e = localXmlMsg ∨ e = langCaseMsg

/-- A term with no id whose folded form has an id would contradict `CidOk`. -/
theorem cid_normalize_none (cid : Term → Option UInt64) (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hcid : ∀ c, CidOk dec ok c (cid c)) (hcidok : ∀ t x, cid t = some x → ok x)
    (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t) (t : Term) (ht : cid t = none) :
    cid (normalizeTerm t) = none := by
  cases e : cid (normalizeTerm t) with
  | none => rfl
  | some z =>
    exfalso
    have h := hcid t
    rw [ht] at h
    have := h z (hcidok _ _ e)
    rw [hcidN _ _ e, normalize_idem, Term.eqb_symm, eqb_normalize, Term.eqb_refl] at this
    cases this

theorem localIdOf_spec (cid : Term → Option UInt64) (voc : Array Term) (ix : Std.HashMap Term Nat)
    (hinv : VocInv cid voc ix) (t : Term) (hnone : cid (normalizeTerm t) = none) (dec : UInt64 → Term)
    (ok : UInt64 → Prop) :
    (∃ e, localIdOf voc ix t = .error e ∧ LocalRefusal e) ∨
      ∃ y voc' ix', localIdOf voc ix t = .ok (y, voc', ix') ∧ VocInv cid voc' ix' ∧ voc.toList <+: voc'.toList ∧
        okV ok voc' y ∧ y ≠ 0 ∧ decV dec voc' y = normalizeTerm t := by
  unfold localIdOf
  simp only []
  rw [Std.HashMap.get?_eq_getElem?]
  cases hk : ix[normalizeTerm t]? with
  | some k =>
    have hv := (hinv.idx _ k).mp hk
    have hkl : k < voc.size := by
      rcases Nat.lt_or_ge k voc.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hv; cases hv
    right
    refine ⟨localId k, voc, ix, rfl, hinv, List.prefix_refl _, Or.inr ⟨k, hkl, rfl⟩,
      localId_ne_zero (by have := hinv.size; omega), ?_⟩
    rw [decV_local dec voc hinv.size hkl]
    rw [Array.getElem?_eq_getElem hkl] at hv
    exact Option.some.inj hv
  | none =>
    simp only []
    by_cases hx : hasXmlLit (normalizeTerm t) = true
    · left; exact ⟨_, by rw [if_pos hx], Or.inr (Or.inl rfl)⟩
    · rw [if_neg hx]
      by_cases hs : voc.size < two60
      · rw [if_pos hs]
        right
        have hnot : ∀ k : Nat, voc[k]? ≠ some (normalizeTerm t) := by
          intro k h
          rw [(hinv.idx _ k).mpr h] at hk
          cases hk
        refine ⟨localId voc.size, voc.push (normalizeTerm t), ix.insert (normalizeTerm t) voc.size, rfl,
          ⟨by simp; omega, ?_, ?_⟩, ⟨[normalizeTerm t], by simp⟩, Or.inr ⟨voc.size, by simp, rfl⟩,
          localId_ne_zero hs, ?_⟩
        · intro key k
          rw [Std.HashMap.getElem?_insert]
          by_cases e : (normalizeTerm t == key) = true
          · have e' : normalizeTerm t = key := by simpa using e
            subst e'
            rw [if_pos e]
            constructor
            · intro h; cases h
              simp
            · intro h
              rw [Array.getElem?_push] at h
              split at h
              · next he => rw [he]
              · exact absurd h (hnot k)
          · rw [if_neg e]
            have e' : normalizeTerm t ≠ key := by simpa using e
            rw [hinv.idx key k, Array.getElem?_push]
            split
            · next he =>
              subst he
              constructor
              · intro h
                rw [Array.getElem?_eq_none (Nat.le_refl _)] at h; cases h
              · intro h; exact absurd (Option.some.inj h) e'
            · exact Iff.rfl
        · intro k hk
          rw [Array.getElem_push]
          split
          · exact hinv.entry k (by assumption)
          · refine ⟨hnone, normalize_idem t, by simpa using hx⟩
        · rw [decV_local dec _ (by simp; omega) (by simp), Array.getElem_push_eq]
      · rw [if_neg hs]
        left; exact ⟨_, rfl, Or.inl rfl⟩

/-- **`termIdM` on a state.** Over a store whose dictionary lookup is `cid`,
    `IdQuery.termIdM` refuses (`LocalRefusal`), or gives an id in `okV` of
    the new vocabulary that decodes to `normalizeTerm t`; the new vocabulary
    keeps the invariant and extends the old one. -/
theorem termIdM_spec (st : Store Id) (cid : Term → Option UInt64) (hid : ∀ t, st.idOf t = pure (cid t))
    (dec : UInt64 → Term) (ok : UInt64 → Prop) (hcid : ∀ c, CidOk dec ok c (cid c))
    (hcidok : ∀ t x, cid t = some x → ok x) (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (hloc : ∀ x, ok x → tagOf x ≠ tagLocal) (hcid0 : ∀ t x, cid t = some x → x ≠ 0)
    (voc : Array Term) (ix : Std.HashMap Term Nat)
    (hinv : VocInv cid voc ix) (t : Term) :
    (∃ e, termIdM st voc ix t = throw e ∧ LocalRefusal e) ∨
      ∃ y voc' ix', termIdM st voc ix t = pure (y, voc', ix') ∧ VocInv cid voc' ix' ∧
        voc.toList <+: voc'.toList ∧ okV ok voc' y ∧ y ≠ 0 ∧ decV dec voc' y = normalizeTerm t := by
  unfold termIdM
  rw [hid t]
  cases hc : cid t with
  | some y =>
    right
    refine ⟨y, voc, ix, rfl, hinv, List.prefix_refl _, Or.inl (hcidok t y hc), hcid0 t y hc, ?_⟩
    rw [decV_ok dec hloc voc (hcidok t y hc)]
    exact hcidN t y hc
  | none =>
    have hn := cid_normalize_none cid dec ok hcid hcidok hcidN t hc
    rcases localIdOf_spec cid voc ix hinv t hn dec ok with ⟨e, he, hr⟩ | ⟨y, voc', ix', he, h⟩
    · left
      refine ⟨e, ?_, hr⟩
      show (match localIdOf voc ix t with | .ok r => pure r | .error e => throw e : ExceptT String Id _) = _
      rw [he]
    · right
      refine ⟨y, voc', ix', ?_, h⟩
      show (match localIdOf voc ix t with | .ok r => pure r | .error e => throw e : ExceptT String Id _) = _
      rw [he]

/-- **`valueIdM` on a state.** As `termIdM_spec`, and an id it gives decodes
    to the value itself: it refuses (`langCaseMsg`) a value that is not its
    own `normalizeTerm`. -/
theorem valueIdM_spec (st : Store Id) (cid : Term → Option UInt64) (hid : ∀ t, st.idOf t = pure (cid t))
    (dec : UInt64 → Term) (ok : UInt64 → Prop) (hcid : ∀ c, CidOk dec ok c (cid c))
    (hcidok : ∀ t x, cid t = some x → ok x) (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (hloc : ∀ x, ok x → tagOf x ≠ tagLocal) (hcid0 : ∀ t x, cid t = some x → x ≠ 0)
    (voc : Array Term) (ix : Std.HashMap Term Nat)
    (hinv : VocInv cid voc ix) (t : Term) :
    (∃ e, valueIdM st voc ix t = throw e ∧ LocalRefusal e) ∨
      ∃ y voc' ix', valueIdM st voc ix t = pure (y, voc', ix') ∧ VocInv cid voc' ix' ∧
        voc.toList <+: voc'.toList ∧ okV ok voc' y ∧ y ≠ 0 ∧ decV dec voc' y = t := by
  unfold valueIdM
  by_cases hn : normalizeTerm t = t
  · rw [if_pos hn]
    rcases termIdM_spec st cid hid dec ok hcid hcidok hcidN hloc hcid0 voc ix hinv t with h | ⟨y, voc', ix', h1, h2, h3, h4, h5, h6⟩
    · exact Or.inl h
    · exact Or.inr ⟨y, voc', ix', h1, h2, h3, h4, h5, by rw [h6, hn]⟩
  · rw [if_neg hn]
    exact Or.inl ⟨_, rfl, Or.inr (Or.inr rfl)⟩

/-! ## Runs that end with a refusal or a result -/

/-- A run of the nested evaluator from a state ends with a refusal of the
    query-local vocabulary, or with a result `a` and a state `s` with
    `P a s`. -/
def Ends {α : Type} (r : ExceptT String Id (α × NSt)) (P : α → NSt → Prop) : Prop :=
  (∃ e, r = throw e ∧ LocalRefusal e) ∨ ∃ a s, r = pure (a, s) ∧ P a s

theorem ends_bind {α β : Type} {x : NM Id α} {k : α → NM Id β} {s : NSt} {P : α → NSt → Prop}
    {Q : β → NSt → Prop} (hx : Ends (x.run s) P) (hk : ∀ a s', P a s' → Ends ((k a).run s') Q) :
    Ends ((x >>= k).run s) Q := by
  rw [StateT.run_bind]
  rcases hx with ⟨e, he, hr⟩ | ⟨a, s', he, hP⟩
  · left; exact ⟨e, by rw [he]; rfl, hr⟩
  · rw [he, pure_bind]
    exact hk a s' hP

theorem ends_pure {α : Type} {r : ExceptT String Id (α × NSt)} {P : α → NSt → Prop} {a : α} {s : NSt}
    (h : r = pure (a, s)) (hP : P a s) : Ends r P := Or.inr ⟨a, s, h, hP⟩

theorem ends_mono {α : Type} {r : ExceptT String Id (α × NSt)} {P Q : α → NSt → Prop}
    (h : Ends r P) (hPQ : ∀ a s, P a s → Q a s) : Ends r Q := by
  rcases h with h | ⟨a, s, he, hP⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, s, he, hPQ a s hP⟩

end L4Factoidal.Storage.Sbm11.LocalVocab

#print axioms L4Factoidal.Storage.Sbm11.LocalVocab.eqb_norm_eq
#print axioms L4Factoidal.Storage.Sbm11.LocalVocab.hdecV
#print axioms L4Factoidal.Storage.Sbm11.LocalVocab.termIdM_spec
#print axioms L4Factoidal.Storage.Sbm11.LocalVocab.valueIdM_spec
#print axioms L4Factoidal.Storage.Sbm11.LocalVocab.cidOkV_some
#print axioms L4Factoidal.Storage.Sbm11.LocalVocab.termOf_withLocal
