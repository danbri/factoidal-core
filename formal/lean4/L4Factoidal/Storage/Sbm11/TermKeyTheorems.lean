/-
L4Factoidal.Storage.Sbm11.TermKeyTheorems — the SBM11 term key round trip.

* `decodeKey?_termKey?`: `termKey? t = some k → decodeKey? k = some t`.
  The only hypothesis is that the encoder admitted the term.
* `termKey?_injective`: two admitted terms with the same key are the same
  term (RDF 1.1 Concepts section 3: term equality is structural equality
  of `RDF.Term`, with the language tag in its lower-case value space).
* `termKeyBytes?_eq`: the packer's `ByteArray` key holds the same bytes.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.TermKey
import L4Factoidal.Storage.TermCodecTheorems

namespace L4Factoidal.Storage.Sbm11

open L4Factoidal.RDF
open L4Factoidal.Storage (bytesOfString stringOfBytes? stringOfBytes?_bytesOfString)

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

/-- The literal case of the round trip. -/
theorem decodeKey?_literalKey? (l : WfLiteral) (k : Key) (h : literalKey? l.val = some k) :
    decodeKey? k = some (.literal l) := by
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
        simp [decodeKey?, classString, classBnode, classIri, stringOfBytes?_bytesOfString,
          Literal.string]
      · have hs' : (dt == xsdString) = false := by simpa using hs
        simp only [hs', Bool.false_eq_true, if_false] at h
        by_cases hz : noZero (bytesOfString dt.val) = true
        · simp only [hz, if_true, Option.some.injEq] at h
          subst h
          have hne := wfIri_val_ne hs'
          simp [decodeKey?, classTyped, classBnode, classIri, classString, classLang,
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
        have hdt : dt = rdfLangString := Subtype.ext (by simpa [literalWf] using hw)
        subst hdt
        simp [decodeKey?, classLang, classBnode, classIri, classString, decodeLang?,
          splitLast_append _ _ (tagAdmitted_noZero ht), stringOfBytes?_bytesOfString, ht, hself]
      · simp [ht] at h
    | some d =>
      simp only [literalKey?] at h
      by_cases ht : tagAdmitted t = true
      · simp only [ht, if_true, Option.some.injEq] at h
        subst h
        have hdt : dt = rdfDirLangString := Subtype.ext (by simpa [literalWf] using hw)
        subst hdt
        have h1 : splitLast (bytesOfString lex ++ 0 :: (bytesOfString t ++ [0, dirByte d])) =
            some (bytesOfString lex ++ 0 :: bytesOfString t, [dirByte d]) := by
          rw [show bytesOfString lex ++ 0 :: (bytesOfString t ++ [0, dirByte d]) =
              (bytesOfString lex ++ 0 :: bytesOfString t) ++ 0 :: [dirByte d] by simp]
          exact splitLast_append _ _ (noZero_dirByte d)
        simp [decodeKey?, classDirLang, classBnode, classIri, classString, classLang, classTyped,
          decodeDirLang?, h1, dirOfByte?_dirByte, splitLast_append _ _ (tagAdmitted_noZero ht),
          stringOfBytes?_bytesOfString, ht, hself]
      · simp [ht] at h

/-- The SBM11 term key round trip: the decoder inverts the encoder on every
    term the encoder admits. -/
theorem decodeKey?_termKey? (t : Term) (k : Key) (h : termKey? t = some k) :
    decodeKey? k = some t := by
  cases t with
  | bnode b =>
    simp only [termKey?, Option.some.injEq] at h
    subst h
    simp [decodeKey?, classBnode, stringOfBytes?_bytesOfString]
  | iri i =>
    simp only [termKey?, Option.some.injEq] at h
    subst h
    simp [decodeKey?, classBnode, classIri, decodeIri?, stringOfBytes?_bytesOfString,
      i.property]
  | literal l => exact decodeKey?_literalKey? l k h
  | tripleTerm s p o => simp [termKey?] at h

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

end L4Factoidal.Storage.Sbm11
