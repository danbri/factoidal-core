/-
L4Factoidal.Storage.Sbm11.DictInjectiveTheorems — the SBM11 term dictionary
satisfies `RDF.DictInjective` (https://github.com/danbri/factoidal/issues/975,
step 2).

The base generation (`MemGen`):

* `memGen_dictInjective`: for a generation `G` with `G.check = true`, the
  codes `toCode? G.keys` and `ofCode? G.keys` are a `DictInjective` dictionary
  on the ids of the rows and the named graph ids (`MemGen.idUsed`). The
  check is the `Bool` test of `MemGenStoreTheorems` (`idOkB` of every row id
  and every named graph id); `PackSpecTheorems.packSpec_check` proves it for
  every generation that `packSpec` makes. `TermIdTheorems.toCode?_injective`
  and `ofCode?_toCode?` hold for every key list, with no check.
* Term equality. The dictionary holds terms with language tags in lower case
  (`keysOk`, part of the check). The lookup `MemGen.cid` folds the tag first
  (`normalizeTerm`, RDF 1.1 Concepts section 3.3). `cid_eq_iff_eqb`: two terms
  with ids have the same id exactly when they are `Term.eqb`-equal, the RDF
  term equality of the engine (tags without case; lexical form, datatype and
  base direction exactly). So `"x"@EN` and `"x"@en` have one id. The raw code
  `toCode?` of a term with an upper-case tag is `none` in such a dictionary.
* Inline ids: `inline_dict_disjoint`: an inline code (tag 4 or 5) is never a
  dictionary code (tags 1, 2, 3, 9) of a rank below `2^60`.

The delta overlay (`OverlayDict`):

* `overlay_dictInjective`: under `vocabOk` (a `Bool`: no duplicate entry, no
  entry with a base id, at most `2^60` entries), base ids and overlay ids
  together are a `DictInjective` dictionary on the base ids in use and the
  overlay ids.
* `ovEnc_injective`: two terms with one id are one term (all terms, no
  check). `ovEnc_base_ne_delta`: a base id is never an overlay id.
* `vocabOk_add`, `vocabOk_addAll`: the replay step keeps `vocabOk`, while the
  vocabulary has fewer than `2^60` entries. `idOrNew_isSome`: after the step,
  the term has an id. `ovEnc_vocabAdd`: the step changes no id that a term
  already had.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.DictInjective
import L4Factoidal.Storage.Sbm11.OverlayDict
import L4Factoidal.Storage.Sbm11.PackSpecTheorems

namespace L4Factoidal.Storage.Sbm11.MemGen

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11.Block

/-- The ids in use of a generation: the subject, predicate and object ids of
    the rows of the four permutations, and the named graph ids. -/
def MemGen.idUsed (G : MemGen) (n : Nat) : Prop :=
  (∃ k, k < 4 ∧ ∃ r ∈ G.rows k, n = r.c0 ∨ n = r.c1 ∨ n = r.c2) ∨ ∃ x ∈ G.named.toList, n = x.toNat

/-- The terms a generation holds: the terms of its ids in use. -/
def MemGen.termHeld (G : MemGen) (t : Term) : Prop :=
  ∃ n, G.idUsed n ∧ ofCode? G.keys n = some t

/-- An id that passes `idOkB` decodes to a term whose code is that id. -/
theorem idOkB_spec (keys : List Key) (n : Nat) (h : idOkB keys n = true) :
    ∃ t, ofCode? keys n = some t ∧ toCode? keys t = some n := by
  unfold idOkB at h
  split at h
  · rename_i t ht
    exact ⟨t, ht, by simpa using h⟩
  · cases h

variable (G : MemGen)

/-- Every id in use of a checked generation passes `idOkB`. -/
theorem idUsed_idOkB (h : G.check = true) : ∀ n, G.idUsed n → idOkB G.keys n = true := by
  intro n hu
  rcases hu with ⟨k, hk, r, hr, he⟩ | ⟨x, hx, rfl⟩
  · have hrows := (check_perm G h k hk).2.1
    unfold MemGen.rowsOk at hrows
    have hall := List.all_eq_true.mp hrows r hr
    simp only [Bool.and_eq_true] at hall
    rcases he with rfl | rfl | rfl
    · exact hall.1.1.1
    · exact hall.1.1.2
    · exact hall.1.2
  · have hn := check_named G h
    unfold MemGen.namedOk at hn
    simp only [Bool.and_eq_true] at hn
    have hall := List.all_eq_true.mp hn.2 x hx
    simp only [Bool.and_eq_true] at hall
    exact hall.1

/-- The SBM11 dictionary of a checked generation is injective on its ids in
    use, with `ofCode?` the inverse of `toCode?`. -/
theorem memGen_dictInjective (h : G.check = true) :
    DictInjective (toCode? G.keys) (ofCode? G.keys) G.termHeld G.idUsed := by
  have hed : ∀ n, G.idUsed n → ∃ t, G.termHeld t ∧ ofCode? G.keys n = some t ∧ toCode? G.keys t = some n := by
    intro n hu
    obtain ⟨t, hd, he⟩ := idOkB_spec G.keys n (idUsed_idOkB G h n hu)
    exact ⟨t, ⟨n, hu, hd⟩, hd, he⟩
  refine DictInjective.ofRoundTrip ?_ (fun t n _ he => ofCode?_toCode? G.keys t n he) hed
  intro t ⟨n, hu, hd⟩
  obtain ⟨t', _, hd', he'⟩ := hed n hu
  rw [hd] at hd'
  cases Option.some.inj hd'
  exact ⟨n, hu, he'⟩

/-- Two terms with ids in a generation whose keys pass `keysOk` have the same
    id exactly when they are the same RDF term (`Term.eqb`: language tags
    without case). -/
theorem cid_eq_iff_eqb (hk : keysOk G.keys = true) (t u : Term) (x y : UInt64)
    (hx : G.cid t = some x) (hy : G.cid u = some y) : x = y ↔ t.eqb u = true := by
  have h1 := mem_hcid G hk t
  rw [hx] at h1
  have h2 := h1 y (mem_hcidok G u y hy)
  rw [mem_hcidN G u y hy] at h2
  have hn : u.eqb (normalizeTerm u) = true := eqb_normalize u
  have hn' : (normalizeTerm u).eqb u = true := by rw [Term.eqb_symm]; exact hn
  constructor
  · intro e
    subst e
    have : t.eqb (normalizeTerm u) = true := by rw [h2]; simp
    exact Term.eqb_trans this hn'
  · intro e
    have : t.eqb (normalizeTerm u) = true := Term.eqb_trans e hn
    rw [h2] at this
    exact beq_iff_eq.mp this

end L4Factoidal.Storage.Sbm11.MemGen

namespace L4Factoidal.Storage.Sbm11

open L4Factoidal.RDF

/-- An inline code (tag 4 or 5) is never a dictionary code (tag 1, 2, 3 or
    9) of a rank below `2^60`. -/
theorem inline_dict_disjoint (t : Term) (n : Nat) (hn : inlineCode? t = some n) (k : Key) (r : Nat)
    (hr : r < two60) : dictCode k r ≠ n := by
  intro e
  have ht := inlineCode?_tag t n hn
  have hc := classTag_cases k
  have hdiv : dictCode k r / two60 = classTag k := by
    unfold dictCode; rw [two60_eq] at hr ⊢; omega
  rw [e] at hdiv
  simp only [tagInt, tagBool, tagBnode, tagIri, tagLit, tagTriple] at ht hc
  omega

end L4Factoidal.Storage.Sbm11

namespace L4Factoidal.Storage.Sbm11.OverlayDict

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11.MemGen (idOkB idOkB_spec)

theorem tagDelta_eq : Overlay.tagDelta = 14 := rfl

/-- A base id is below `10 · 2^60`; its tag is not `tagDelta`. -/
theorem base_tag_ne (keys : List Key) (t : Term) (n : Nat) (h : toCode? keys t = some n) :
    n / two60 ≠ Overlay.tagDelta := by
  have := (toCode?_range keys t n h).2
  rw [tagDelta_eq]
  rw [two60_eq] at this ⊢
  omega

theorem ovDec_base (keys : List Key) (ov : List Term) (t : Term) (n : Nat) (h : toCode? keys t = some n) :
    ovDec keys ov n = ofCode? keys n := by
  unfold ovDec
  rw [if_neg (base_tag_ne keys t n h)]

/-- An overlay id: tag 14 and the index of the term. -/
theorem ovEnc_delta (keys : List Key) (ov : List Term) (t : Term) (n : Nat) (h : ovEnc keys ov t = some n)
    (hc : toCode? keys t = none) :
    t ∈ ov ∧ ov.idxOf t < two60 ∧ n = Overlay.tagDelta * two60 + ov.idxOf t := by
  unfold ovEnc at h
  rw [hc] at h
  simp only at h
  split at h
  · rename_i hm
    exact ⟨hm.1, hm.2, (Option.some.inj h).symm⟩
  · cases h

/-- The term of the id of a term is that term (every term, no check). -/
theorem ovDec_ovEnc (keys : List Key) (ov : List Term) (t : Term) (n : Nat) (h : ovEnc keys ov t = some n) :
    ovDec keys ov n = some t := by
  cases hc : toCode? keys t with
  | some m =>
    have hm : m = n := by
      unfold ovEnc at h; rw [hc] at h; exact Option.some.inj h
    subst hm
    rw [ovDec_base keys ov t m hc]
    exact ofCode?_toCode? keys t m hc
  | none =>
    obtain ⟨hmem, hlt, rfl⟩ := ovEnc_delta keys ov t n h hc
    unfold ovDec
    have hdiv : (Overlay.tagDelta * two60 + ov.idxOf t) / two60 = Overlay.tagDelta := by
      rw [tagDelta_eq]; rw [two60_eq] at hlt ⊢; omega
    have hmod : (Overlay.tagDelta * two60 + ov.idxOf t) % two60 = ov.idxOf t := by
      rw [tagDelta_eq]; rw [two60_eq] at hlt ⊢; omega
    rw [if_pos hdiv, hmod]
    have hl : ov.idxOf t < ov.length := List.idxOf_lt_length_iff.mpr hmem
    rw [List.getElem?_eq_getElem hl, List.getElem_idxOf hl]

/-- Two terms with one id are one term (every term, no check). -/
theorem ovEnc_injective (keys : List Key) (ov : List Term) (t u : Term) (n : Nat)
    (h1 : ovEnc keys ov t = some n) (h2 : ovEnc keys ov u = some n) : t = u := by
  have e1 := ovDec_ovEnc keys ov t n h1
  have e2 := ovDec_ovEnc keys ov u n h2
  rw [e1] at e2
  exact Option.some.inj e2

/-- A base id is never an overlay id. -/
theorem ovEnc_base_ne_delta (keys : List Key) (ov : List Term) (t u : Term) (n m : Nat)
    (ht : toCode? keys t = some n) (hu : toCode? keys u = none) (hm : ovEnc keys ov u = some m) : n ≠ m := by
  obtain ⟨_, hlt, rfl⟩ := ovEnc_delta keys ov u m hm hu
  have := base_tag_ne keys t n ht
  intro e
  apply this
  rw [e, tagDelta_eq]
  rw [tagDelta_eq, two60_eq] at *
  omega

/-- Under `vocabOk`, the ids of a generation with its overlay are a
    `DictInjective` dictionary on the base ids in use (each passing `idOkB`,
    which `MemGen.check` gives) and the overlay ids. -/
theorem overlay_dictInjective (keys : List Key) (ov : List Term) (baseUsed : Nat → Prop)
    (hv : vocabOk keys ov = true) (hb : ∀ n, baseUsed n → idOkB keys n = true) :
    DictInjective (ovEnc keys ov) (ovDec keys ov) (ovHeld keys baseUsed ov) (ovUsed baseUsed ov) := by
  unfold vocabOk at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨hnd, hall⟩, hlen⟩ := hv
  have hed : ∀ n, ovUsed baseUsed ov n →
      ∃ t, ovHeld keys baseUsed ov t ∧ ovDec keys ov n = some t ∧ ovEnc keys ov t = some n := by
    intro n hu
    rcases hu with hbu | ⟨h14, hlt⟩
    · obtain ⟨t, hd, he⟩ := idOkB_spec keys n (hb n hbu)
      have hd' : ovDec keys ov n = some t := by rw [ovDec_base keys ov t n he]; exact hd
      refine ⟨t, ⟨n, Or.inl hbu, hd'⟩, hd', ?_⟩
      unfold ovEnc; rw [he]
    · have hd' : ovDec keys ov n = some ov[n % two60] := by
        unfold ovDec; rw [if_pos h14, List.getElem?_eq_getElem hlt]
      refine ⟨ov[n % two60], ⟨n, Or.inr ⟨h14, hlt⟩, hd'⟩, hd', ?_⟩
      have hnone : toCode? keys ov[n % two60] = none := by
        have := List.all_eq_true.mp hall _ (List.getElem_mem hlt)
        simpa using this
      have hidx := L4Factoidal.RDF.idxOf_getElem_of_nodup ov (n % two60) hlt hnd
      unfold ovEnc
      rw [hnone]
      simp only
      rw [hidx, if_pos ⟨List.getElem_mem hlt, by omega⟩]
      have := Nat.div_add_mod n two60
      rw [h14] at this
      rw [tagDelta_eq] at this ⊢
      congr 1
  refine DictInjective.ofRoundTrip ?_ (fun t n _ he => ovDec_ovEnc keys ov t n he) hed
  intro t ⟨n, hu, hd⟩
  obtain ⟨t', _, hd', he'⟩ := hed n hu
  rw [hd] at hd'
  cases Option.some.inj hd'
  exact ⟨n, hu, he'⟩

/-- An id that a term had before the step is its id after the step. -/
theorem ovEnc_vocabAdd (keys : List Key) (ov : List Term) (t s : Term) (n : Nat)
    (h : ovEnc keys ov s = some n) : ovEnc keys (vocabAdd keys ov t) s = some n := by
  unfold vocabAdd
  dsimp only
  split
  · exact h
  · cases hc : toCode? keys s with
    | some m => unfold ovEnc at h ⊢; rw [hc] at h ⊢; exact h
    | none =>
      obtain ⟨hmem, hlt, rfl⟩ := ovEnc_delta keys ov s n h hc
      have hidx : (ov ++ [normalizeTerm t]).idxOf s = ov.idxOf s := by
        rw [List.idxOf_append, if_pos hmem]
      unfold ovEnc
      rw [hc]
      simp only
      rw [hidx, if_pos ⟨List.mem_append_left _ hmem, hlt⟩]

/-- The step keeps `vocabOk` while the vocabulary has fewer than `2^60`
    entries. -/
theorem vocabOk_add (keys : List Key) (ov : List Term) (t : Term) (hv : vocabOk keys ov = true)
    (hlen : ov.length < two60) : vocabOk keys (vocabAdd keys ov t) = true := by
  unfold vocabAdd
  dsimp only
  split
  · exact hv
  · rename_i hnot
    have hnone : ovEnc keys ov (normalizeTerm t) = none := by simpa using hnot
    unfold ovEnc at hnone
    cases hc : toCode? keys (normalizeTerm t) with
    | some m => rw [hc] at hnone; cases hnone
    | none =>
      rw [hc] at hnone
      simp only at hnone
      have hnm : normalizeTerm t ∉ ov := by
        intro hm
        have hl := List.idxOf_lt_length_iff.mpr hm
        rw [if_pos ⟨hm, by omega⟩] at hnone
        cases hnone
      unfold vocabOk at hv ⊢
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hv ⊢
      obtain ⟨⟨hnd, hall⟩, _⟩ := hv
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hnd, by simp, ?_⟩
        intro a ha b hb e
        simp only [List.mem_singleton] at hb
        subst hb; subst e
        exact hnm ha
      · rw [List.all_append]
        simp only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true]
        exact ⟨hall, by simp [hc]⟩
      · simp only [List.length_append, List.length_singleton]
        omega

theorem length_vocabAdd (keys : List Key) (ov : List Term) (t : Term) :
    (vocabAdd keys ov t).length ≤ ov.length + 1 := by
  unfold vocabAdd
  dsimp only
  split <;> simp

/-- The replay of a list of terms keeps `vocabOk` while the vocabulary and
    the terms together are at most `2^60`. -/
theorem vocabOk_addAll (keys : List Key) : ∀ (ts : List Term) (ov : List Term),
    vocabOk keys ov = true → ov.length + ts.length ≤ two60 → vocabOk keys (vocabAddAll keys ov ts) = true
  | [], ov, hv, _ => hv
  | t :: ts, ov, hv, hlen => by
    unfold vocabAddAll
    simp only [List.foldl_cons]
    have h1 := vocabOk_add keys ov t hv (by simp at hlen; omega)
    have h2 := length_vocabAdd keys ov t
    exact vocabOk_addAll keys ts _ h1 (by simp at hlen; omega)

/-- After the step, the folded term has an id. -/
theorem idOrNew_isSome (keys : List Key) (ov : List Term) (t : Term) (hlen : ov.length < two60) :
    (idOrNew keys ov t).isSome = true := by
  unfold idOrNew vocabAdd
  dsimp only
  split
  · assumption
  · cases hc : toCode? keys (normalizeTerm t) with
    | some m => unfold ovEnc; rw [hc]; rfl
    | none =>
      have hm : normalizeTerm t ∈ ov ++ [normalizeTerm t] := List.mem_append_right _ (List.mem_singleton_self _)
      have hl : (ov ++ [normalizeTerm t]).idxOf (normalizeTerm t) < two60 := by
        have := List.idxOf_le_length (l := ov ++ [normalizeTerm t]) (a := normalizeTerm t)
        simp only [List.length_append, List.length_singleton] at this
        have h' : (ov ++ [normalizeTerm t]).idxOf (normalizeTerm t) < (ov ++ [normalizeTerm t]).length :=
          List.idxOf_lt_length_iff.mpr hm
        simp only [List.length_append, List.length_singleton] at h'
        omega
      unfold ovEnc
      rw [hc]
      simp only
      rw [if_pos ⟨hm, hl⟩]
      rfl

end L4Factoidal.Storage.Sbm11.OverlayDict

#print axioms L4Factoidal.Storage.Sbm11.MemGen.memGen_dictInjective
#print axioms L4Factoidal.Storage.Sbm11.MemGen.cid_eq_iff_eqb
#print axioms L4Factoidal.Storage.Sbm11.inline_dict_disjoint
#print axioms L4Factoidal.Storage.Sbm11.OverlayDict.overlay_dictInjective
#print axioms L4Factoidal.Storage.Sbm11.OverlayDict.ovEnc_injective
#print axioms L4Factoidal.Storage.Sbm11.OverlayDict.ovEnc_base_ne_delta
#print axioms L4Factoidal.Storage.Sbm11.OverlayDict.ovEnc_vocabAdd
#print axioms L4Factoidal.Storage.Sbm11.OverlayDict.vocabOk_addAll
#print axioms L4Factoidal.Storage.Sbm11.OverlayDict.idOrNew_isSome
