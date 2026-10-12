/-
L4Factoidal.Storage.Sbm11.TermIdTheorems — the SBM11 term id round trip.

* `ofInlineCode?_inlineCode?`: an inline id decodes to the term it was
  made from.
* `ofCode?_toCode?`: `toCode? d t = some n → ofCode? d n = some t`, for
  every dictionary `d` (a list of keys in rank order).
* `toCode?_injective`, `toId?_eq_iff`: two terms with ids in the same
  dictionary have the same id if and only if they are the same term.
* `toCode?_pos`: no term id is 0, so `GraphId.ofName` never names the
  default graph.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.TermId
import L4Factoidal.Storage.Sbm11.TermKeyTheorems

namespace L4Factoidal.Storage.Sbm11

open L4Factoidal.RDF

theorem findIntTypeGo_some (dt : WfIri) :
    ∀ (l : List IntType) (i j : Nat) (e : IntType),
      findIntTypeGo dt i l = some (j, e) → i ≤ j ∧ l[j - i]? = some e ∧ e.iri = dt := by
  intro l
  induction l with
  | nil => intro i j e h; simp [findIntTypeGo] at h
  | cons x xs ih =>
    intro i j e h
    by_cases hx : (x.iri == dt) = true
    · simp only [findIntTypeGo, hx, if_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Nat.le_refl _, by simp, Subtype.ext (by simpa using hx)⟩
    · simp only [findIntTypeGo, hx, Bool.false_eq_true, if_false] at h
      obtain ⟨hle, hget, hiri⟩ := ih (i + 1) j e h
      refine ⟨by omega, ?_, hiri⟩
      have : j - i = (j - (i + 1)) + 1 := by omega
      rw [this]
      simpa using hget

theorem findIntType?_some {dt : WfIri} {j : Nat} {e : IntType}
    (h : findIntType? dt = some (j, e)) :
    intTypesList[j]? = some e ∧ e.iri = dt ∧ j < 16 := by
  obtain ⟨_, hget, hiri⟩ := findIntTypeGo_some dt intTypesList 0 j e h
  simp only [Nat.sub_zero] at hget
  refine ⟨hget, hiri, ?_⟩
  have hlt : j < intTypesList.length := by
    rcases Nat.lt_or_ge j intTypesList.length with hl | hl
    · exact hl
    · rw [List.getElem?_eq_none hl] at hget; cases hget
  have : intTypesList.length = 13 := rfl
  omega

private theorem wfIri_eq_of_beq {a b : WfIri} (h : (a == b) = true) : a = b :=
  Subtype.ext (by simpa using h)

/-- `ofInlineCode?` on a tag-4 id. -/
theorem ofInlineCode?_int (n : Nat) (h4 : n / two60 = 4) :
    ofInlineCode? n =
      (match intTypesList[(n / two56) % 16]? with
       | none => none
       | some e =>
         if e.admits (((n % two56 : Nat) : Int) - two55Int) then
           mkLit (toString (((n % two56 : Nat) : Int) - two55Int)) e.iri.val none none
         else none) := by
  unfold ofInlineCode?
  rw [h4]
  rfl

/-- An inline id decodes to the term it was made from. -/
theorem ofInlineCode?_inlineCode? (t : Term) (n : Nat) (h : inlineCode? t = some n) :
    ofInlineCode? n = some t := by
  cases t with
  | literal l =>
    obtain ⟨⟨lex, dt, tag, dir⟩, hw⟩ := l
    have hself := mkLit_self ⟨⟨lex, dt, tag, dir⟩, hw⟩
    simp only at hself
    cases tag with
    | some _ => simp [inlineCode?] at h
    | none =>
      cases dir with
      | some _ => simp [inlineCode?] at h
      | none =>
        simp only [inlineCode?, Option.isNone_none, Bool.and_self, if_true] at h
        by_cases hb : (dt == xsdBoolean) = true
        · simp only [hb, if_true] at h
          have hdt : dt = xsdBoolean := wfIri_eq_of_beq hb
          subst hdt
          unfold boolCode? at h
          by_cases ht : lex = "true"
          · subst ht
            simp only [beq_self_eq_true, if_true, Option.some.injEq] at h
            subst h
            simp [ofInlineCode?, two60_eq, tagBool, hself]
          · by_cases hf : lex = "false"
            · subst hf
              simp only [beq_iff_eq, ht, if_false, if_true, Option.some.injEq] at h
              subst h
              simp [ofInlineCode?, two60_eq, tagBool, hself]
            · simp [ht, hf] at h
        · have hb' : (dt == xsdBoolean) = false := by simpa using hb
          simp only [hb', Bool.false_eq_true, if_false] at h
          cases hfind : findIntType? dt with
          | none => rw [hfind] at h; cases h
          | some ie =>
            obtain ⟨i, e⟩ := ie
            rw [hfind] at h
            obtain ⟨hget, hiri, hlt⟩ := findIntType?_some hfind
            unfold intCode? at h
            cases hv : lex.toInt? with
            | none => rw [hv] at h; cases h
            | some v =>
              rw [hv] at h
              dsimp only at h
              by_cases hc : (toString v == lex && e.admits v && decide (-two55Int ≤ v) &&
                  decide (v < two55Int)) = true
              · rw [if_pos hc] at h
                simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
                obtain ⟨⟨⟨hs, ha⟩, hlo⟩, hhi⟩ := hc
                simp only [Option.some.injEq] at h
                subst h
                rw [two55Int_eq] at hlo hhi
                have hpv : (((v + two55Int).toNat : Nat) : Int) = v + two55Int :=
                  Int.toNat_of_nonneg (by rw [two55Int_eq]; omega)
                rw [two55Int_eq] at hpv
                generalize hp : (v + two55Int).toNat = p at hpv
                have hplt : p < 72057594037927936 := by omega
                have hdiv : (tagInt * two60 + i * two56 + p) / two60 = 4 := by
                  rw [two60_eq, two56_eq]; simp only [tagInt]; omega
                have hsub : (tagInt * two60 + i * two56 + p) / two56 % 16 = i := by
                  rw [two60_eq, two56_eq]; simp only [tagInt]; omega
                have hmod : (tagInt * two60 + i * two56 + p) % two56 = p := by
                  rw [two60_eq, two56_eq]; simp only [tagInt]; omega
                have hval : ((p : Int) - two55Int) = v := by rw [two55Int_eq]; omega
                rw [ofInlineCode?_int _ hdiv, hsub, hmod, hget]
                dsimp only
                rw [hval, if_pos ha, hs, hiri]
                exact hself
              · rw [if_neg hc] at h; cases h
  | iri _ => simp [inlineCode?] at h
  | bnode _ => simp [inlineCode?] at h
  | tripleTerm _ _ _ => simp [inlineCode?] at h

/-- Inline ids carry tag 4 or tag 5. -/
theorem inlineCode?_tag (t : Term) (n : Nat) (h : inlineCode? t = some n) :
    n / two60 = tagInt ∨ n / two60 = tagBool := by
  cases t with
  | literal l =>
    simp only [inlineCode?] at h
    split at h
    · split at h
      · unfold boolCode? at h
        split at h
        · simp only [Option.some.injEq] at h; subst h
          right; rw [two60_eq]; simp only [tagBool]; try omega
        · split at h
          · simp only [Option.some.injEq] at h; subst h
            right; rw [two60_eq]; simp only [tagBool]; try omega
          · cases h
      · split at h
        · rename_i i e hfind
          obtain ⟨_, _, hlt⟩ := findIntType?_some hfind
          unfold intCode? at h
          split at h
          · cases h
          · rename_i v _
            split at h
            · rename_i hc
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
              obtain ⟨⟨_, hlo⟩, hhi⟩ := hc
              simp only [Option.some.injEq] at h; subst h
              left
              have hpv : (((v + two55Int).toNat : Nat) : Int) = v + two55Int :=
                Int.toNat_of_nonneg (by omega)
              rw [two55Int_eq] at hpv hlo hhi
              generalize (v + two55Int).toNat = p at hpv
              rw [two60_eq, two56_eq]; simp only [tagInt]; omega
            · cases h
        · cases h
    · cases h
  | iri _ => simp [inlineCode?] at h
  | bnode _ => simp [inlineCode?] at h
  | tripleTerm _ _ _ => simp [inlineCode?] at h

theorem classTag_cases (k : Key) :
    classTag k = tagBnode ∨ classTag k = tagIri ∨ classTag k = tagLit := by
  unfold classTag
  split
  · split
    · left; rfl
    · split
      · right; left; rfl
      · right; right; rfl
  · right; right; rfl

/-- The id round trip over a dictionary. -/
theorem ofCode?_toCode? (d : List Key) (t : Term) (n : Nat) (h : toCode? d t = some n) :
    ofCode? d n = some t := by
  unfold toCode? at h
  cases hin : inlineCode? t with
  | some c =>
    rw [hin] at h
    simp only [Option.some.injEq] at h
    subst h
    have htag := inlineCode?_tag t c hin
    have hdec := ofInlineCode?_inlineCode? t c hin
    unfold ofCode?
    rcases htag with ht | ht <;> simp [ht, tagInt, tagBool, hdec]
  | none =>
    rw [hin] at h
    cases hk : termKey? t with
    | none => rw [hk] at h; cases h
    | some k =>
      rw [hk] at h
      simp only at h
      by_cases hc : (d.idxOf k < d.length && decide (d.idxOf k < two60)) = true
      · rw [if_pos hc] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨hlen, hlt⟩ := hc
        have hlen' : d.idxOf k < d.length := by simpa using hlen
        have hget : d[d.idxOf k]? = some k := by
          rw [List.getElem?_eq_getElem hlen', List.getElem_idxOf hlen']
        have hdiv : dictCode k (d.idxOf k) / two60 = classTag k := by
          unfold dictCode; rw [two60_eq] at hlt ⊢; omega
        have hmod : dictCode k (d.idxOf k) % two60 = d.idxOf k := by
          unfold dictCode; rw [two60_eq] at hlt ⊢; omega
        have hdec := decodeKey?_termKey? t k hk
        unfold ofCode?
        rcases classTag_cases k with hct | hct | hct <;>
          simp [hdiv, hmod, hget, hct, hdec, tagBnode, tagIri, tagLit, tagInt, tagBool]
      · rw [if_neg hc] at h; cases h

/-- Two terms with ids in one dictionary have the same id only if they are
    the same term. -/
theorem toCode?_injective (d : List Key) (t₁ t₂ : Term) (n : Nat)
    (h₁ : toCode? d t₁ = some n) (h₂ : toCode? d t₂ = some n) : t₁ = t₂ := by
  have e₁ := ofCode?_toCode? d t₁ n h₁
  have e₂ := ofCode?_toCode? d t₂ n h₂
  rw [e₁] at e₂
  exact Option.some.inj e₂

/-- Every id is at least `2 ^ 60` (tag at least 1) and below `6 * 2 ^ 60`. -/
theorem toCode?_range (d : List Key) (t : Term) (n : Nat) (h : toCode? d t = some n) :
    two60 ≤ n ∧ n < 6 * two60 := by
  unfold toCode? at h
  cases hin : inlineCode? t with
  | some c =>
    rw [hin] at h
    simp only [Option.some.injEq] at h
    subst h
    have := inlineCode?_tag t c hin
    rw [two60_eq] at this ⊢
    simp only [tagInt, tagBool] at this
    omega
  | none =>
    rw [hin] at h
    cases hk : termKey? t with
    | none => rw [hk] at h; cases h
    | some k =>
      rw [hk] at h
      simp only at h
      by_cases hc : (d.idxOf k < d.length && decide (d.idxOf k < two60)) = true
      · rw [if_pos hc] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        unfold dictCode
        have := classTag_cases k
        simp only [tagBnode, tagIri, tagLit] at this
        rw [two60_eq] at hc ⊢
        rcases this with h' | h' | h' <;> rw [h'] <;> omega
      · rw [if_neg hc] at h; cases h

theorem toCode?_pos (d : List Key) (t : Term) (n : Nat) (h : toCode? d t = some n) : 0 < n := by
  have := (toCode?_range d t n h).1
  rw [two60_eq] at this
  omega

private theorem code_toNat (d : List Key) (t : Term) (n : Nat) (h : toCode? d t = some n) :
    (UInt64.ofNat n).toNat = n := by
  apply UInt64.toNat_ofNat_of_lt'
  have := (toCode?_range d t n h).2
  rw [two60_eq] at this
  show n < 18446744073709551616
  omega

/-- The 64-bit id round trip. -/
theorem ofId?_toId? (d : List Key) (t : Term) (i : TermId) (h : toId? d t = some i) :
    ofId? d i = some t := by
  unfold toId? at h
  cases hc : toCode? d t with
  | none => rw [hc] at h; cases h
  | some n =>
    rw [hc] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    unfold ofId?
    simp only
    rw [code_toNat d t n hc]
    exact ofCode?_toCode? d t n hc

/-- Two terms with ids in one dictionary: same id if and only if same term
    (RDF 1.1 Concepts section 3, term equality). -/
theorem toId?_eq_iff (d : List Key) (t₁ t₂ : Term) (i₁ i₂ : TermId)
    (h₁ : toId? d t₁ = some i₁) (h₂ : toId? d t₂ = some i₂) : i₁ = i₂ ↔ t₁ = t₂ := by
  constructor
  · intro he
    subst he
    have e₁ := ofId?_toId? d t₁ i₁ h₁
    have e₂ := ofId?_toId? d t₂ i₁ h₂
    rw [e₁] at e₂
    exact Option.some.inj e₂
  · intro he
    subst he
    rw [h₁] at h₂
    exact Option.some.inj h₂

/-- A named graph's id is never the default graph's. -/
theorem graphId_ofName_ne_default (d : List Key) (t : Term) (i : TermId) (h : toId? d t = some i) :
    GraphId.ofName i ≠ GraphId.default := by
  unfold toId? at h
  cases hc : toCode? d t with
  | none => rw [hc] at h; cases h
  | some n =>
    rw [hc] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    intro heq
    have hb : (UInt64.ofNat n) = 0 := by
      simpa [GraphId.ofName, GraphId.default] using heq
    have h1 := code_toNat d t n hc
    rw [hb] at h1
    have := toCode?_pos d t n hc
    simp at h1
    omega

end L4Factoidal.Storage.Sbm11
