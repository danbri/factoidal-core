/-
L4Factoidal.Storage.Sbm11.TermKeyTheorems — the SBM11 term key round trip.

* `decodeKey?_termKey?`: `termKey? t = some k → decodeKey? k = some t`, for
  every RDF term, triple terms (class 7, any nesting) included. The only
  hypothesis is that the encoder admitted the term.
* `termKey?_injective`: two admitted terms with the same key are the same
  term (RDF 1.1 Concepts section 3 and RDF 1.2 Concepts section 3: term
  equality is structural equality of `RDF.Term`, with the language tag in
  its lower-case value space).
* `termKeyBytes?_eq`: the packer's `ByteArray` key holds the same bytes.
* `decodeAtom?_classTriple`: the decoder of stage 2 (`decodeAtom?`) returns
  `none` for every key of class 7, so a reader built before class 7 refuses
  such a key.
* `decodeTripleGo_termKey?`: the loop that decodes class 7, one nesting
  level per step, on the key of any admitted object.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.TermKey
import L4Factoidal.Storage.TermCodecTheorems

namespace L4Factoidal.Storage.Sbm11

open L4Factoidal.RDF
open L4Factoidal.Storage (bytesOfString stringOfBytes? stringOfBytes?_bytesOfString readU32LE
  writeU32LE readU32LE_writeU32LE_append u32_toNat_ofNat_of_lt writeU32LE_length)

theorem noZero_append (a b : List UInt8) : noZero (a ++ b) = (noZero a && noZero b) := by
  simp [noZero, List.all_append]

theorem noZero_reverse (a : List UInt8) : noZero a.reverse = noZero a := by
  simp [noZero, List.all_reverse]

theorem splitFirstGo_append (acc a b : List UInt8) (ha : noZero a = true) :
    splitFirstGo acc (a ++ 0 :: b) = some (acc.reverse ++ a, b) := by
  induction a generalizing acc with
  | nil => simp [splitFirstGo]
  | cons x xs ih =>
    simp only [noZero, List.all_cons, Bool.and_eq_true] at ha
    have hx : (x == 0) = false := by simpa using ha.1
    simp only [List.cons_append, splitFirstGo, hx, Bool.false_eq_true, if_false]
    rw [ih (x :: acc) ha.2]
    simp

theorem splitFirst_append (a b : List UInt8) (ha : noZero a = true) :
    splitFirst (a ++ 0 :: b) = some (a, b) := by
  simp [splitFirst, splitFirstGo_append [] a b ha]

theorem splitLast_append (a b : List UInt8) (hb : noZero b = true) :
    splitLast (a ++ 0 :: b) = some (a, b) := by
  have hrev : (a ++ 0 :: b).reverse = b.reverse ++ 0 :: a.reverse := by simp
  have hb' : noZero b.reverse = true := by rw [noZero_reverse]; exact hb
  simp only [splitLast, hrev, splitFirst_append _ _ hb', Option.map_some, List.reverse_reverse]

/-- Rebuilding a literal from its own fields returns it. -/
theorem mkLit_self (l : WfLiteral) :
    mkLit l.val.lexicalForm l.val.datatype.val l.val.langTag l.val.direction
      = some (.literal l) := by
  rw [mkLit, dif_pos l.val.datatype.property]
  have hrec : ({ lexicalForm := l.val.lexicalForm,
                 datatype := ⟨l.val.datatype.val, l.val.datatype.property⟩,
                 langTag := l.val.langTag,
                 direction := l.val.direction } : Literal) = l.val := rfl
  simp only [hrec]
  rw [dif_pos l.property]

theorem dirOfByte?_dirByte (d : TextDirection) : dirOfByte? (dirByte d) = some d := by
  cases d <;> rfl

theorem noZero_dirByte (d : TextDirection) : noZero [dirByte d] = true := by
  cases d <;> rfl

private theorem tagAdmitted_noZero {tag : String} (h : tagAdmitted tag = true) :
    noZero (bytesOfString tag) = true := by
  simp only [tagAdmitted, Bool.and_eq_true] at h; exact h.1

private theorem wfIri_val_ne {a b : WfIri} (h : (a == b) = false) : a.val ≠ b.val := by
  intro hv
  have : a = b := Subtype.ext hv
  simp [this] at h

/-! ## Classes 1 to 6 -/

/-- The literal case of the round trip. -/
theorem decodeAtom?_literalKey? (l : WfLiteral) (k : Key) (h : literalKey? l.val = some k) :
    decodeAtom? k = some (.literal l) := by
  obtain ⟨⟨lex, dt, tag, dir⟩, hw⟩ := l
  have hself := mkLit_self ⟨⟨lex, dt, tag, dir⟩, hw⟩
  simp only at hself
  cases tag with
  | none =>
    cases dir with
    | none =>
      simp only [literalKey?] at h
      by_cases hs : (dt == xsdString) = true
      · simp only [hs, if_true, Option.some.injEq] at h
        subst h
        have hdt : dt = xsdString := Subtype.ext (by simpa using hs)
        subst hdt
        simp [decodeAtom?, classString, classBnode, classIri, stringOfBytes?_bytesOfString,
          Literal.string]
      · have hs' : (dt == xsdString) = false := by simpa using hs
        simp only [hs', Bool.false_eq_true, if_false] at h
        by_cases hz : noZero (bytesOfString dt.val) = true
        · simp only [hz, if_true, Option.some.injEq] at h
          subst h
          have hne := wfIri_val_ne hs'
          simp [decodeAtom?, classTyped, classBnode, classIri, classString, classLang,
            decodeTyped?, splitFirst_append _ _ hz, stringOfBytes?_bytesOfString, hz, hne, hself]
        · simp [hz] at h
    | some d =>
      simp [literalKey?] at h
  | some t =>
    cases dir with
    | none =>
      simp only [literalKey?] at h
      by_cases ht : tagAdmitted t = true
      · simp only [ht, if_true, Option.some.injEq] at h
        subst h
        have hdt : dt = rdfLangString := Subtype.ext (by simp [literalWf] at hw; exact hw.1)
        subst hdt
        simp [decodeAtom?, classLang, classBnode, classIri, classString, decodeLang?,
          splitLast_append _ _ (tagAdmitted_noZero ht), stringOfBytes?_bytesOfString, ht, hself]
      · simp [ht] at h
    | some d =>
      simp only [literalKey?] at h
      by_cases ht : tagAdmitted t = true
      · simp only [ht, if_true, Option.some.injEq] at h
        subst h
        have hdt : dt = rdfDirLangString := Subtype.ext (by simp [literalWf] at hw; exact hw.1)
        subst hdt
        have h1 : splitLast (bytesOfString lex ++ 0 :: (bytesOfString t ++ [0, dirByte d])) =
            some (bytesOfString lex ++ 0 :: bytesOfString t, [dirByte d]) := by
          rw [show bytesOfString lex ++ 0 :: (bytesOfString t ++ [0, dirByte d]) =
              (bytesOfString lex ++ 0 :: bytesOfString t) ++ 0 :: [dirByte d] by simp]
          exact splitLast_append _ _ (noZero_dirByte d)
        simp [decodeAtom?, classDirLang, classBnode, classIri, classString, classLang, classTyped,
          decodeDirLang?, h1, dirOfByte?_dirByte, splitLast_append _ _ (tagAdmitted_noZero ht),
          stringOfBytes?_bytesOfString, ht, hself]
      · simp [ht] at h

/-- The round trip on classes 1 to 6: the stage 2 decoder inverts `atomKey?`. -/
theorem decodeAtom?_atomKey? (t : Term) (k : Key) (h : atomKey? t = some k) :
    decodeAtom? k = some t := by
  cases t with
  | bnode b =>
    simp only [atomKey?, Option.some.injEq] at h
    subst h
    simp [decodeAtom?, classBnode, stringOfBytes?_bytesOfString]
  | iri i =>
    simp only [atomKey?, Option.some.injEq] at h
    subst h
    simp [decodeAtom?, classBnode, classIri, decodeIri?, stringOfBytes?_bytesOfString,
      i.property]
  | literal l => exact decodeAtom?_literalKey? l k h
  | tripleTerm s p o => simp [atomKey?] at h

/-- The stage 2 decoder refuses every key of class 7. -/
theorem decodeAtom?_classTriple (body : List UInt8) : decodeAtom? (classTriple :: body) = none := by
  simp [decodeAtom?, classTriple, classBnode, classIri, classString, classLang, classTyped,
    classDirLang]

/-- A key of classes 1 to 6 does not start with the class byte 7. -/
theorem atomKey?_cons (t : Term) (k : Key) (h : atomKey? t = some k) :
    ∃ c rest, k = c :: rest ∧ (c == classTriple) = false := by
  cases t with
  | bnode b =>
    simp only [atomKey?, Option.some.injEq] at h
    exact ⟨classBnode, _, h.symm, by decide⟩
  | iri i =>
    simp only [atomKey?, Option.some.injEq] at h
    exact ⟨classIri, _, h.symm, by decide⟩
  | literal l =>
    simp only [atomKey?] at h
    obtain ⟨⟨lex, dt, tag, dir⟩, hw⟩ := l
    cases tag with
    | none =>
      cases dir with
      | none =>
        simp only [literalKey?] at h
        split at h
        · simp only [Option.some.injEq] at h
          exact ⟨classString, _, h.symm, by decide⟩
        · split at h
          · simp only [Option.some.injEq] at h
            exact ⟨classTyped, _, h.symm, by decide⟩
          · cases h
      | some d => simp [literalKey?] at h
    | some t =>
      cases dir with
      | none =>
        simp only [literalKey?] at h
        split at h
        · simp only [Option.some.injEq] at h
          exact ⟨classLang, _, h.symm, by decide⟩
        · cases h
      | some d =>
        simp only [literalKey?] at h
        split at h
        · simp only [Option.some.injEq] at h
          exact ⟨classDirLang, _, h.symm, by decide⟩
        · cases h
  | tripleTerm s p o => simp [atomKey?] at h

/-! ## Class 7: the parts -/

/-- A part with its length field is read back, with the bytes after it. -/
theorem splitPart?_lenPart (k rest : List UInt8) (hk : partFits k = true) :
    splitPart? (lenPart k ++ rest) = some (k, rest) := by
  have hlt : k.length < UInt32.size := by
    simpa [partFits, L4Factoidal.two32] using hk
  have hn : (UInt32.ofNat k.length).toNat = k.length := u32_toNat_ofNat_of_lt hlt
  have hread : readU32LE (lenPart k ++ rest) 0 = some (UInt32.ofNat k.length) := by
    simp only [lenPart, List.append_assoc]
    exact readU32LE_writeU32LE_append _ _
  have hdrop : (lenPart k ++ rest).drop 4 = k ++ rest := by
    simp only [lenPart, List.append_assoc]
    exact List.drop_left' (writeU32LE_length _)
  simp only [splitPart?, hread, hdrop, hn, List.take_left, List.drop_left, beq_self_eq_true,
    if_true]

theorem subjectOfKey?_subjectKey (s : Subject) : subjectOfKey? (subjectKey s) = some s := by
  cases s with
  | iri i =>
    have h := decodeAtom?_atomKey? (.iri i) (subjectKey (.iri i)) rfl
    simp [subjectOfKey?, h]
  | bnode b =>
    have h := decodeAtom?_atomKey? (.bnode b) (subjectKey (.bnode b)) rfl
    simp [subjectOfKey?, h]

theorem iriOfKey?_iriKey (p : WfIri) : iriOfKey? (iriKey p) = some p := by
  have h := decodeAtom?_atomKey? (.iri p) (iriKey p) rfl
  simp [iriOfKey?, h]

theorem tripleHead?_eq {s : Subject} {p : WfIri} {h : List UInt8} (hh : tripleHead? s p = some h) :
    h = lenPart (subjectKey s) ++ lenPart (iriKey p) ∧ partFits (subjectKey s) = true ∧
      partFits (iriKey p) = true := by
  unfold tripleHead? at hh
  split at hh
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    simp only [Option.some.injEq] at hh
    exact ⟨hh.symm, hc.1, hc.2⟩
  · cases hh

/-- The key of an admitted triple term: 7, the head, the object's key. -/
theorem termKey?_tripleTerm {s : Subject} {p : WfIri} {o : Term} {k : Key}
    (h : termKey? (.tripleTerm s p o) = some k) :
    ∃ hd ok, tripleHead? s p = some hd ∧ termKey? o = some ok ∧ k = classTriple :: (hd ++ ok) := by
  simp only [termKey?] at h
  split at h
  · rename_i hd ok h1 h2
    simp only [Option.some.injEq] at h
    exact ⟨hd, ok, h1, h2, h.symm⟩
  · cases h

/-- One step of the class-7 loop on a head the encoder wrote, followed by an
    object key that starts with the byte `c`. -/
theorem decodeTripleGo_step (f : Nat) (levels : List (Subject × WfIri)) (s : Subject) (p : WfIri)
    (hd : List UInt8) (c : UInt8) (rest : List UInt8) (hh : tripleHead? s p = some hd) :
    decodeTripleGo (f + 1) levels (hd ++ c :: rest) =
      if c == classTriple then decodeTripleGo f ((s, p) :: levels) rest
      else (decodeAtom? (c :: rest)).map (wrapLevels ((s, p) :: levels)) := by
  obtain ⟨rfl, hs, hp⟩ := tripleHead?_eq hh
  rw [List.append_assoc]
  simp only [decodeTripleGo, splitPart?_lenPart _ _ hs, splitPart?_lenPart _ _ hp,
    subjectOfKey?_subjectKey, iriOfKey?_iriKey]

/-- The class-7 loop on the bytes after the class byte of an admitted triple
    term: for any enclosing levels and any fuel above the length, it returns
    the term with the levels put around it. -/
theorem decodeTripleGo_termKey? (o : Term) :
    ∀ (ok : Key), termKey? o = some ok →
    ∀ (levels : List (Subject × WfIri)) (s : Subject) (p : WfIri) (hd : List UInt8) (fuel : Nat),
      tripleHead? s p = some hd → (hd ++ ok).length < fuel →
      decodeTripleGo fuel levels (hd ++ ok) = some (wrapLevels ((s, p) :: levels) o) := by
  induction o with
  | tripleTerm s' p' o' ih =>
    intro ok hk levels s p hd fuel hh hlen
    obtain ⟨hd', ok', hh', hk', rfl⟩ := termKey?_tripleTerm hk
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [decodeTripleGo_step f levels s p hd classTriple (hd' ++ ok') hh]
    simp only [beq_self_eq_true, if_true]
    have hlen' : (hd' ++ ok').length < f := by
      simp only [List.length_append, List.length_cons] at hlen ⊢
      omega
    rw [ih ok' hk' ((s, p) :: levels) s' p' hd' f hh' hlen', wrapLevels_cons]
  | iri i =>
    intro ok hk levels s p hd fuel hh hlen
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have ha : atomKey? (.iri i) = some ok := hk
    obtain ⟨c, rest, rfl, hc⟩ := atomKey?_cons _ _ ha
    rw [decodeTripleGo_step f levels s p hd c rest hh]
    simp [hc, decodeAtom?_atomKey? _ _ ha]
  | bnode b =>
    intro ok hk levels s p hd fuel hh hlen
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have ha : atomKey? (.bnode b) = some ok := hk
    obtain ⟨c, rest, rfl, hc⟩ := atomKey?_cons _ _ ha
    rw [decodeTripleGo_step f levels s p hd c rest hh]
    simp [hc, decodeAtom?_atomKey? _ _ ha]
  | literal l =>
    intro ok hk levels s p hd fuel hh hlen
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have ha : atomKey? (.literal l) = some ok := hk
    obtain ⟨c, rest, rfl, hc⟩ := atomKey?_cons _ _ ha
    rw [decodeTripleGo_step f levels s p hd c rest hh]
    simp [hc, decodeAtom?_atomKey? _ _ ha]

/-! ## The round trip -/

/-- The SBM11 term key round trip: the decoder inverts the encoder on every
    term the encoder admits, triple terms of any nesting included. -/
theorem decodeKey?_termKey? (t : Term) (k : Key) (h : termKey? t = some k) :
    decodeKey? k = some t := by
  cases t with
  | tripleTerm s p o =>
    obtain ⟨hd, ok, hh, hk, rfl⟩ := termKey?_tripleTerm h
    simp only [decodeKey?, beq_self_eq_true, if_true]
    rw [decodeTripleGo_termKey? o ok hk [] s p hd _ hh (Nat.lt_succ_self _)]
    rfl
  | iri i =>
    have ha : atomKey? (.iri i) = some k := h
    obtain ⟨c, rest, rfl, hc⟩ := atomKey?_cons _ _ ha
    simp only [decodeKey?, hc, Bool.false_eq_true, if_false]
    exact decodeAtom?_atomKey? _ _ ha
  | bnode b =>
    have ha : atomKey? (.bnode b) = some k := h
    obtain ⟨c, rest, rfl, hc⟩ := atomKey?_cons _ _ ha
    simp only [decodeKey?, hc, Bool.false_eq_true, if_false]
    exact decodeAtom?_atomKey? _ _ ha
  | literal l =>
    have ha : atomKey? (.literal l) = some k := h
    obtain ⟨c, rest, rfl, hc⟩ := atomKey?_cons _ _ ha
    simp only [decodeKey?, hc, Bool.false_eq_true, if_false]
    exact decodeAtom?_atomKey? _ _ ha

/-- Keys are injective on admitted terms. -/
theorem termKey?_injective (t₁ t₂ : Term) (k : Key)
    (h₁ : termKey? t₁ = some k) (h₂ : termKey? t₂ = some k) : t₁ = t₂ := by
  have e₁ := decodeKey?_termKey? t₁ k h₁
  have e₂ := decodeKey?_termKey? t₂ k h₂
  rw [e₁] at e₂
  exact Option.some.inj e₂

/-- The packer's `ByteArray` key is the list key's bytes. -/
theorem termKeyBytes?_eq (t : Term) :
    (termKeyBytes? t).map (fun b => b.data.toList) = termKey? t := by
  cases h : termKey? t <;> simp [termKeyBytes?, h]

#print axioms decodeAtom?_atomKey?
#print axioms decodeAtom?_classTriple
#print axioms splitPart?_lenPart
#print axioms decodeTripleGo_termKey?
#print axioms decodeKey?_termKey?
#print axioms termKey?_injective
#print axioms termKeyBytes?_eq
#print axioms termKey?_eq_impl
#print axioms normalizeTerm_eq_impl

end L4Factoidal.Storage.Sbm11
