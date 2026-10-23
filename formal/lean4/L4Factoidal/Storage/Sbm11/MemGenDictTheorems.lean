/-
L4Factoidal.Storage.Sbm11.MemGenDictTheorems — the dictionary hypotheses of
`HarnessWhereTheorems.harness_where_allowed` for the store of a generation in
memory (https://github.com/danbri/factoidal/issues/776; rows E0 and L4e of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

For `G : MemGen` whose keys pass `keysOk` (every key decodes to a term with
its language tags in lower case and with no `rdf:XMLLiteral` literal), with
`cid := G.cid`, `dec := G.dec`, `sok = ok := G.ok`, `idv := G.idv`, the
hypotheses `hid`, `hdec`, `hsok`, `hcid`, `hidv`, `hcid0`, `htag`, `hcidN`,
`htermOf`, `hloc`, `hcidok` and `htagk` hold (`dict_hyps`).

Why `keysOk` excludes `rdf:XMLLiteral`: `Term.eqb` compares two
`rdf:XMLLiteral` literals by their canonical XML (`XmlCanon.xmlCanonEq`), so
for the literals `"<x></x>"^^rdf:XMLLiteral` and `"<x/>"^^rdf:XMLLiteral`,
two keys and two ids, `(dec x).eqb (dec y) = true` with `x ≠ y`, and `hdec`
is false; for any `rdf:XMLLiteral` key, `hcid` is false at a term with
another lexical form and the same canonical XML. RDF 1.1 Concepts section
3.3 makes two literals the same term only when the lexical forms are the
same character by character; the id path follows that, the reference
evaluator does not (tests/sbm11/xmlliteral: the id path gives 2 rows, the
reference 4).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.MemGen
import L4Factoidal.Storage.Sbm11.TermIdTheorems
import L4Factoidal.Storage.Sbm11.TermKeyTheorems
import L4Factoidal.Storage.Sbm11.IdPathEvalTheorems
import L4Factoidal.Storage.Sbm11.ExistsTableTheorems

namespace L4Factoidal.Storage.Sbm11.MemGen

open L4Factoidal.RDF
open L4Factoidal.SPARQL (isNotLiteral)
open L4Factoidal.Storage.Sbm11.IdQuery (tagOf tagLocal)
open L4Factoidal.Storage.Sbm11.IdLeaf (CidOk)
open L4Factoidal.Storage.Sbm11.ExistsTableTheorems (TagKind)

/-! ## Lower case -/

theorem char_toLower_toLower (c : Char) : c.toLower.toLower = c.toLower := by
  unfold Char.toLower
  split <;> rename_i h
  · rw [dif_neg]
    intro h2
    simp only [ge_iff_le, UInt32.le_iff_toNat_le] at h h2
    simp only [UInt32.toNat_add] at h2
    have : ('A'.val).toNat = 65 := rfl
    have : ('Z'.val).toNat = 90 := rfl
    have : ('a'.val - 'A'.val).toNat = 32 := rfl
    omega
  · rfl

theorem string_toLower_toLower (s : String) : s.toLower.toLower = s.toLower := by
  rw [← String.toList_inj]
  simp only [String.toLower, String.toList_map, List.map_map]
  congr 1
  funext c
  exact char_toLower_toLower c

/-! ## `Term.eqb` against a term in lower case with no `rdf:XMLLiteral` -/

theorem wf_lower (l : Literal) (a b : String) (h : l.langTag = some a) (hw : literalWf l = true) :
    literalWf { l with langTag := some b } = true := by
  obtain ⟨lex, dt, tag, dir⟩ := l
  simp only at h
  subst h
  cases dir <;> exact hw

theorem normalizeLit_tag (l : WfLiteral) (a : String) (h : l.val.langTag = some a) :
    normalizeLit l = .literal ⟨{ l.val with langTag := some a.toLower }, wf_lower l.val a _ h l.property⟩ := by
  unfold normalizeLit
  split
  · rename_i hn; rw [h] at hn; cases hn
  · rename_i tag hn
    rw [h] at hn
    cases hn
    rw [dif_pos (wf_lower l.val a _ h l.property)]

/-- A literal in lower case keeps its language tag. -/
theorem tag_lower (l : WfLiteral) (b : String) (h : l.val.langTag = some b)
    (hn : normalizeLit l = .literal l) : b.toLower = b := by
  rw [normalizeLit_tag l b h] at hn
  simp only [Term.literal.injEq] at hn
  have := congrArg (fun v : WfLiteral => v.val.langTag) hn
  simp only [h, Option.some.injEq] at this
  exact this

/-- A term that is `Term.eqb` to a term in lower case with no
    `rdf:XMLLiteral` literal is that term once its tags are in lower case. -/
theorem eqb_norm : ∀ (c t : Term), normalizeTerm t = t → noXml t = true → c.eqb t = true →
    normalizeTerm c = t
  | .iri i, .iri j, _, _, h => by
    simp only [Term.eqb, beq_iff_eq] at h
    subst h; rfl
  | .bnode i, .bnode j, _, _, h => by
    simp only [Term.eqb, beq_iff_eq] at h
    subst h; rfl
  | .literal l1, .literal l2, hn, hx, h => by
    obtain ⟨⟨lex1, dt1, tag1, dir1⟩, w1⟩ := l1
    obtain ⟨⟨lex2, dt2, tag2, dir2⟩, w2⟩ := l2
    simp only [noXml, bne_iff_ne, ne_eq] at hx
    simp only [Term.eqb, Literal.eqb] at h
    have h1 : (dt2 == rdfXMLLiteral) = false := beq_eq_false_iff_ne.mpr hx
    have hif : (dt1 == rdfXMLLiteral && dt2 == rdfXMLLiteral) = false := by
      rw [h1, Bool.and_false]
    rw [hif] at h
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hlex, hdt⟩, htag⟩, hdir⟩ := h
    subst hlex hdt hdir
    cases tag1 with
    | none =>
      cases tag2 with
      | none => rfl
      | some b => simp [langTagOptionEq] at htag
    | some a =>
      cases tag2 with
      | none => simp [langTagOptionEq] at htag
      | some b =>
        simp only [langTagOptionEq, langTagEq, beq_iff_eq] at htag
        have hb := tag_lower _ b rfl hn
        show normalizeLit _ = _
        rw [normalizeLit_tag _ a rfl]
        simp only [Term.literal.injEq]
        apply Subtype.ext
        simp only [htag, hb]
  | .tripleTerm s p o, .tripleTerm s' p' o', hn, hx, h => by
    simp only [Term.eqb, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hs, hp⟩, ho⟩ := h
    have hs' : s = s' := by
      cases s <;> cases s' <;> simp only [Subject.eqb, beq_iff_eq, Bool.false_eq_true] at hs <;>
        first | (subst hs; rfl) | cases hs
    subst hs' hp
    simp only [normalizeTerm, Term.tripleTerm.injEq, true_and] at hn ⊢
    exact eqb_norm o o' hn hx ho
  | .iri _, .bnode _, _, _, h | .iri _, .literal _, _, _, h | .iri _, .tripleTerm _ _ _, _, _, h
  | .bnode _, .iri _, _, _, h | .bnode _, .literal _, _, _, h | .bnode _, .tripleTerm _ _ _, _, _, h
  | .literal _, .iri _, _, _, h | .literal _, .bnode _, _, _, h | .literal _, .tripleTerm _ _ _, _, _, h
  | .tripleTerm _ _ _, .iri _, _, _, h | .tripleTerm _ _ _, .bnode _, _, _, h
  | .tripleTerm _ _ _, .literal _, _, _, h => by simp [Term.eqb] at h

/-- A term is `Term.eqb` to itself with its tags in lower case. -/
theorem eqb_normalize : ∀ c : Term, c.eqb (normalizeTerm c) = true
  | .iri _ => Term.eqb_refl _
  | .bnode _ => Term.eqb_refl _
  | .literal l => by
    show Term.eqb _ (normalizeLit l) = true
    cases ht : l.val.langTag with
    | none =>
      unfold normalizeLit; rw [ht]; exact Term.eqb_refl _
    | some a =>
      rw [normalizeLit_tag l a ht]
      simp only [Term.eqb, Literal.eqb]
      simp [ht, langTagOptionEq, langTagEq, string_toLower_toLower]
  | .tripleTerm s p o => by
    simp only [normalizeTerm, Term.eqb, Subject.eqb_refl, beq_self_eq_true, Bool.true_and]
    exact eqb_normalize o

/-! ## The terms that have an id -/

/-- An inline term is a literal with no language tag, not of datatype
    `rdf:XMLLiteral`. -/
theorem inline_lit (t : Term) (c : Nat) (h : inlineCode? t = some c) :
    ∃ l, t = .literal l ∧ l.val.langTag = none ∧ l.val.datatype ≠ rdfXMLLiteral := by
  cases t with
  | literal l =>
    refine ⟨l, rfl, ?_⟩
    simp only [inlineCode?] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
      refine ⟨hc.1, ?_⟩
      split at h
      · rename_i hb
        have hb' : l.val.datatype = xsdBoolean := Subtype.ext (by simpa using hb)
        rw [hb']
        decide
      · split at h
        · rename_i i e hfind
          intro hx
          rw [hx] at hfind
          have : findIntType? rdfXMLLiteral = none := by decide
          rw [this] at hfind
          cases hfind
        · cases h
    · cases h
  | iri _ => simp [inlineCode?] at h
  | bnode _ => simp [inlineCode?] at h
  | tripleTerm _ _ _ => simp [inlineCode?] at h

/-- A term with an id in a dictionary that passes `keysOk` is in lower case
    and holds no `rdf:XMLLiteral` literal. -/
theorem code_norm (keys : List Key) (hk : keysOk keys = true) (t : Term) (n : Nat)
    (h : toCode? keys t = some n) : normalizeTerm t = t ∧ noXml t = true := by
  unfold toCode? at h
  cases hin : inlineCode? t with
  | some c =>
    obtain ⟨l, rfl, hl, hx⟩ := inline_lit t c hin
    refine ⟨?_, ?_⟩
    · show normalizeLit l = _
      unfold normalizeLit; rw [hl]
    · simp only [noXml, bne_iff_ne, ne_eq]
      exact hx
  | none =>
    rw [hin] at h
    cases hkey : termKey? t with
    | none => rw [hkey] at h; cases h
    | some k =>
      rw [hkey] at h
      simp only at h
      by_cases hc : (keys.idxOf k < keys.length && decide (keys.idxOf k < two60)) = true
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        have hmem : k ∈ keys := List.idxOf_lt_length_iff.mp hc.1
        have hall := List.all_eq_true.mp hk k hmem
        rw [decodeKey?_termKey? t k hkey] at hall
        simp only [Bool.and_eq_true, beq_iff_eq] at hall
        exact hall
      · rw [if_neg hc] at h; cases h

/-- The class byte of a literal's key is not the byte of a blank node, an IRI
    or a triple term. -/
theorem literalKey?_head (l : Literal) (k : Key) (h : literalKey? l = some k) :
    classTag k = tagLit := by
  obtain ⟨lex, dt, tag, dir⟩ := l
  cases tag with
  | none =>
    cases dir with
    | none =>
      simp only [literalKey?] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; rfl
      · split at h
        · simp only [Option.some.injEq] at h; subst h; rfl
        · cases h
    | some d => simp [literalKey?] at h
  | some t =>
    cases dir with
    | none =>
      simp only [literalKey?] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; rfl
      · cases h
    | some d =>
      simp only [literalKey?] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; rfl
      · cases h

/-- The tag of an id names the kind of its term: 1 a blank node, 2 an IRI,
    3, 4 or 5 a literal, 9 a triple term. -/
theorem code_kind (d : List Key) (t : Term) (n : Nat) (h : toCode? d t = some n) :
    (n / two60 = 1 ∧ ∃ b, t = .bnode b) ∨ (n / two60 = 2 ∧ ∃ i, t = .iri i) ∨
      ((n / two60 = 3 ∨ n / two60 = 4 ∨ n / two60 = 5) ∧ ∃ l, t = .literal l) ∨
      (n / two60 = 9 ∧ ∃ s p o, t = .tripleTerm s p o) := by
  unfold toCode? at h
  cases hin : inlineCode? t with
  | some c =>
    rw [hin] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨l, rfl, _, _⟩ := inline_lit t c hin
    have := inlineCode?_tag _ c hin
    simp only [tagInt, tagBool] at this
    right; right; left
    exact ⟨by omega, l, rfl⟩
  | none =>
    rw [hin] at h
    cases hkey : termKey? t with
    | none => rw [hkey] at h; cases h
    | some k =>
      rw [hkey] at h
      simp only at h
      by_cases hc : (d.idxOf k < d.length && decide (d.idxOf k < two60)) = true
      · rw [if_pos hc] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        have hdiv : dictCode k (d.idxOf k) / two60 = classTag k := by
          unfold dictCode; rw [two60_eq] at hc ⊢; omega
        rw [hdiv]
        cases t with
        | bnode b =>
          simp only [termKey?, atomKey?, Option.some.injEq] at hkey
          subst hkey
          left; exact ⟨rfl, b, rfl⟩
        | iri i =>
          simp only [termKey?, atomKey?, Option.some.injEq] at hkey
          subst hkey
          right; left; exact ⟨rfl, i, rfl⟩
        | literal l =>
          simp only [termKey?, atomKey?] at hkey
          right; right; left
          exact ⟨Or.inl (literalKey?_head l.val k hkey), l, rfl⟩
        | tripleTerm s p o =>
          obtain ⟨_, _, _, _, hh⟩ := termKey?_tripleTerm hkey
          right; right; right
          refine ⟨?_, s, p, o, rfl⟩
          rw [hh]; rfl
      · rw [if_neg hc] at h; cases h

/-! ## The dictionary hypotheses -/

variable (G : MemGen)

theorem code_toNat (t : Term) (n : Nat) (h : toCode? G.keys t = some n) : (UInt64.ofNat n).toNat = n := by
  apply UInt64.toNat_ofNat_of_lt'
  have := (toCode?_range G.keys t n h).2
  rw [two60_eq] at this
  show n < 18446744073709551616
  omega

theorem dec_of (t : Term) (x : UInt64) (h : toCode? G.keys t = some x.toNat) : G.dec x = t := by
  unfold MemGen.dec
  rw [ofCode?_toCode? G.keys t _ h]
  rfl

theorem cid_some (t : Term) (x : UInt64) (h : G.cid t = some x) :
    toCode? G.keys (normalizeTerm t) = some x.toNat := by
  unfold MemGen.cid at h
  cases hc : toCode? G.keys (normalizeTerm t) with
  | none => rw [hc] at h; cases h
  | some n =>
    rw [hc] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    rw [code_toNat G _ n hc]

/-- `hid` -/
theorem mem_hid (t : Term) : G.store.idOf t = pure (G.cid t) := rfl

/-- `hcidN` -/
theorem mem_hcidN (t : Term) (x : UInt64) (h : G.cid t = some x) : G.dec x = normalizeTerm t :=
  dec_of G _ x (cid_some G t x h)

/-- `hcidok` -/
theorem mem_hcidok (t : Term) (x : UInt64) (h : G.cid t = some x) : G.ok x :=
  ⟨_, cid_some G t x h⟩

/-- `hidv` -/
theorem mem_hidv (t : Term) (x : UInt64) (h : G.cid t = some x) : G.idv t = x := by
  unfold MemGen.idv; rw [h]; rfl

/-- `hcid0` -/
theorem mem_hcid0 (t : Term) (x : UInt64) (h : G.cid t = some x) : x ≠ 0 := by
  intro h0
  have hc := cid_some G t x h
  rw [h0] at hc
  have := toCode?_pos G.keys _ _ hc
  simp at this

/-- `htermOf` -/
theorem mem_htermOf (x : UInt64) (h : G.ok x) : G.store.termOf x = pure (G.dec x) := by
  obtain ⟨t, ht⟩ := h
  show (match ofCode? G.keys x.toNat with
    | some t => (pure t : ExceptT String Id Term)
    | none => throw s!"id {x}: no term") = _
  rw [ofCode?_toCode? G.keys t _ ht, dec_of G t x ht]

theorem tagOf_eq (x : UInt64) : tagOf x = x.toNat / two60 := by
  unfold tagOf
  rw [UInt64.toNat_shiftRight, two60_eq]
  simp [Nat.shiftRight_eq_div_pow]

/-- `hloc` -/
theorem mem_hloc (x : UInt64) (h : G.ok x) : tagOf x ≠ tagLocal := by
  obtain ⟨t, ht⟩ := h
  have := (toCode?_range G.keys t _ ht).2
  rw [tagOf_eq]
  unfold tagLocal
  rw [two60_eq] at this ⊢
  omega

/-- `htagk` -/
theorem mem_htagk (x : UInt64) (h : G.ok x) : TagKind x (G.dec x) := by
  obtain ⟨t, ht⟩ := h
  rw [dec_of G t x ht]
  unfold TagKind
  rw [tagOf_eq]
  rcases code_kind G.keys t _ ht with ⟨e, b, rfl⟩ | ⟨e, i, rfl⟩ | ⟨e, l, rfl⟩ | ⟨e, s, p, o, rfl⟩
  · rw [e]; exact ⟨fun _ => Or.inr ⟨b, rfl⟩, fun h => by omega⟩
  · rw [e]; exact ⟨fun _ => Or.inl ⟨i, rfl⟩, fun h => by omega⟩
  · exact ⟨fun h => by omega, fun _ => ⟨l, rfl⟩⟩
  · rw [e]; exact ⟨fun h => by omega, fun h => by omega⟩

/-- `htag` -/
theorem mem_htag (x : UInt64) (h : G.ok x) : IdPathEval.litTag x = some (!isNotLiteral (G.dec x)) := by
  obtain ⟨t, ht⟩ := h
  rw [dec_of G t x ht]
  unfold IdPathEval.litTag
  rw [tagOf_eq]
  rcases code_kind G.keys t _ ht with ⟨e, b, rfl⟩ | ⟨e, i, rfl⟩ | ⟨e, l, rfl⟩ | ⟨e, s, p, o, rfl⟩
  · rw [e]; rfl
  · rw [e]; rfl
  · rcases e with e | e | e <;> rw [e] <;> rfl
  · rw [e]; rfl

/-- `hdec`, for a dictionary that passes `keysOk`. -/
theorem mem_hdec (hk : keysOk G.keys = true) (x y : UInt64) (hx : G.ok x) (hy : G.ok y) :
    (G.dec x).eqb (G.dec y) = (x == y) := by
  obtain ⟨t1, h1⟩ := hx
  obtain ⟨t2, h2⟩ := hy
  rw [dec_of G t1 x h1, dec_of G t2 y h2]
  by_cases hxy : x = y
  · subst hxy
    rw [toCode?_injective G.keys t1 t2 _ h1 h2]
    simp
  · rw [show (x == y) = false from beq_eq_false_iff_ne.mpr hxy]
    cases he : t1.eqb t2 with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨hn2, hx2⟩ := code_norm G.keys hk t2 _ h2
      have e := eqb_norm t1 t2 hn2 hx2 he
      rw [(code_norm G.keys hk t1 _ h1).1] at e
      subst e
      rw [h1] at h2
      exact hxy (UInt64.toNat_inj.mp (Option.some.inj h2))

/-- `hcid`, for a dictionary that passes `keysOk`. -/
theorem mem_hcid (hk : keysOk G.keys = true) (c : Term) : CidOk G.dec G.ok c (G.cid c) := by
  cases hc : G.cid c with
  | some x =>
    have hx := cid_some G c x hc
    intro y hy
    obtain ⟨t2, h2⟩ := hy
    rw [dec_of G t2 y h2]
    by_cases hxy : x = y
    · subst hxy
      rw [toCode?_injective G.keys t2 _ _ h2 hx]
      simp [eqb_normalize]
    · rw [show (x == y) = false from beq_eq_false_iff_ne.mpr hxy]
      cases he : c.eqb t2 with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨hn2, hx2⟩ := code_norm G.keys hk t2 _ h2
        have e := eqb_norm c t2 hn2 hx2 he
        rw [e, h2] at hx
        exact hxy (UInt64.toNat_inj.mp (Option.some.inj hx)).symm
  | none =>
    intro y hy
    obtain ⟨t2, h2⟩ := hy
    rw [dec_of G t2 y h2]
    cases he : c.eqb t2 with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨hn2, hx2⟩ := code_norm G.keys hk t2 _ h2
      have e := eqb_norm c t2 hn2 hx2 he
      unfold MemGen.cid at hc
      rw [e, h2] at hc
      cases hc

end L4Factoidal.Storage.Sbm11.MemGen

#print axioms L4Factoidal.Storage.Sbm11.MemGen.mem_hdec
#print axioms L4Factoidal.Storage.Sbm11.MemGen.mem_hcid
#print axioms L4Factoidal.Storage.Sbm11.MemGen.mem_htag
#print axioms L4Factoidal.Storage.Sbm11.MemGen.mem_htagk
#print axioms L4Factoidal.Storage.Sbm11.MemGen.mem_htermOf
#print axioms L4Factoidal.Storage.Sbm11.MemGen.mem_hloc
#print axioms L4Factoidal.Storage.Sbm11.MemGen.mem_hcid0
#print axioms L4Factoidal.Storage.Sbm11.MemGen.mem_hcidN
