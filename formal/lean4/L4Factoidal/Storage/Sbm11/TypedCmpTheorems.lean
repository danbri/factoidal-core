/-
L4Factoidal.Storage.Sbm11.TypedCmpTheorems — `TypedCmp.typedCmpKey?` equals
the reference FILTER value (https://github.com/danbri/factoidal/issues/930).

* `typedCmpKey?_some`: what an answer of `typedCmpKey?` says about the key.
* `typedCmpKey_sound`: for a constant `c` with `typedConstOk c`, a key that
  `decodeKey?` reads as the term `t`, and `typedCmpKey? ... = some r`, the
  reference FILTER value `ebvOrFalse (Expr.evalIn {} [(v, t)] e)` of
  `?v OP c` (or `c OP ?v` when `swap`) is `r`.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.TypedCmp
import L4Factoidal.Storage.Sbm11.TermKeyTheorems
import L4Factoidal.Storage.TermCodecTheorems

namespace L4Factoidal.Storage.Sbm11.TypedCmp

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage (bytesOfString)

theorem fromUTF8_toUTF8 (ba : ByteArray) (s : String) (h : String.fromUTF8? ba = some s) :
    s.toUTF8 = ba := by
  unfold String.fromUTF8? at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · cases h

/-- What an answer says: the key is `pre` then the UTF-8 bytes of the lexical
    form `lex`, and the answer is the operator on `lex` and the constant. -/
theorem typedCmpKey?_some (op : CompOp) (swap : Bool) (pre : ByteArray) (cLex : String)
    (buf : ByteArray) (a e : Nat) (r : Bool)
    (h : typedCmpKey? op swap pre cLex buf a e = some r) :
    ∃ lex : String, sliceList buf a e = pre.data.toList ++ lex.toUTF8.data.toList ∧
      r = applyCompOp (if swap then strCompare cLex lex else strCompare lex cLex) op := by
  unfold typedCmpKey? at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hok, hle⟩, hpre⟩ := hc
    have hpre' : buf.extract a (a + pre.size) = pre := by
      exact ByteArray.ext (eq_of_beq (show ((buf.extract a (a + pre.size)).data == pre.data) = true from hpre))
    split at h
    · rename_i lex hlex
      simp only [Option.some.injEq] at h
      refine ⟨lex, ?_, h.symm⟩
      have hs := fromUTF8_toUTF8 _ _ hlex
      have hsplit : buf.extract a (a + pre.size) ++ buf.extract (a + pre.size) e = buf.extract a e := by
        rw [ByteArray.extract_append_extract]
        congr 1 <;> omega
      unfold sliceList
      rw [← hsplit, hpre', hs]
      simp
    · cases h
  · cases h

theorem typedCmpKey_sound (op : CompOp) (swap : Bool) (c : WfLiteral) (hc : typedConstOk c = true)
    (v : String) (buf : ByteArray) (a e : Nat) (t : Term)
    (hdec : decodeKey? (sliceList buf a e) = some t) (r : Bool)
    (hr : typedCmpKey? op swap (typedPre c) c.val.lexicalForm buf a e = some r) :
    ebvOrFalse (Expr.evalIn {} [(v, t)]
      (if swap then Expr.compare op (.lit c) (.var v) else Expr.compare op (.var v) (.lit c))) = r := by
  obtain ⟨lex, hkey, hrr⟩ := typedCmpKey?_some op swap _ _ buf a e r hr
  obtain ⟨⟨clex, cdt, ctag, cdir⟩, cwf⟩ := c
  simp only [typedConstOk, typedPre, Bool.and_eq_true, Option.isNone_iff_eq_none, bne_iff_ne, ne_eq,
    Bool.not_eq_true', beq_eq_false_iff_ne] at hc hkey hrr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨htag, hdir⟩, hstr⟩, hnz⟩, hind⟩, hi⟩, hd⟩, hdb⟩, hf⟩, hb⟩ := hc
  subst htag hdir
  have hlex : bytesOfString lex = lex.toUTF8.data.toList := by
    unfold bytesOfString
    exact L4Factoidal.Storage.byteArray_toList_eq _
  have hs : (cdt == xsdString) = false := beq_false_of_ne hstr
  have hlk : literalKey? ({ lexicalForm := lex, datatype := cdt, langTag := none, direction := none } : Literal)
      = some (sliceList buf a e) := by
    simp only [literalKey?, hs, hlex, hnz, if_true, Bool.false_eq_true, if_false]
    rw [hkey]
    simp
  have hwf : literalWf { lexicalForm := lex, datatype := cdt, langTag := none, direction := none } = true := cwf
  have hdec2 : decodeKey? (sliceList buf a e) = some (.literal ⟨{ lexicalForm := lex, datatype := cdt, langTag := none, direction := none }, hwf⟩) :=
    decodeKey?_termKey? (.literal ⟨{ lexicalForm := lex, datatype := cdt, langTag := none, direction := none }, hwf⟩) _ hlk
  rw [hdec2] at hdec
  have ht : t = .literal ⟨{ lexicalForm := lex, datatype := cdt, langTag := none, direction := none }, hwf⟩ :=
    (Option.some.inj hdec).symm
  subst ht
  have h1 : (cdt == xsdInteger) = false := beq_false_of_ne hi
  have h2 : (cdt == xsdDecimal) = false := beq_false_of_ne hd
  have h3 : (cdt == xsdDouble) = false := beq_false_of_ne hdb
  have h4 : (cdt == xsdFloat) = false := beq_false_of_ne hf
  have h5 : (cdt == xsdBoolean) = false := beq_false_of_ne hb
  have hview : ∀ (x : WfLiteral), x.val.datatype = cdt → literalOperandView x = .term (.literal x) := fun x hx =>
    literalOperandView_of_datatype x (by rw [hx]; exact hind)
      (by rw [hx]; exact h1) (by rw [hx]; exact h2) (by rw [hx]; exact h3) (by rw [hx]; exact h4) (by rw [hx]; exact h5)
  have hL := hview ⟨{ lexicalForm := lex, datatype := cdt, langTag := none, direction := none }, hwf⟩ rfl
  have hC := hview ⟨{ lexicalForm := clex, datatype := cdt, langTag := none, direction := none }, cwf⟩ rfl
  have hprom : literalPromote ⟨{ lexicalForm := lex, datatype := cdt, langTag := none, direction := none }, hwf⟩
      = .term (.literal ⟨{ lexicalForm := lex, datatype := cdt, langTag := none, direction := none }, hwf⟩) := by
    simp [literalPromote, h1, h2, h3, h4, h5]
  subst hrr
  cases swap
  · simp [Expr.evalIn, Binding.lookup, hprom, valueCompare, numericView, hL, hC, ebvOrFalse, ebv]
  · simp [Expr.evalIn, Binding.lookup, hprom, valueCompare, numericView, hL, hC, ebvOrFalse, ebv]

#print axioms fromUTF8_toUTF8
#print axioms typedCmpKey?_some
#print axioms typedCmpKey_sound

end L4Factoidal.Storage.Sbm11.TypedCmp
