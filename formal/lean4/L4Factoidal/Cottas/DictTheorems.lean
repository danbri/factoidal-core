/-
L4Factoidal.Cottas.DictTheorems — `RDF.DictInjective` for the RDF term layer
of a COTTAS `.dict` file, with one id per RDF term
(https://github.com/danbri/factoidal/issues/977; issue 975 phase B4).

`cotd_dictInjective`: when `termRoundTripsAll` holds (a `Bool` test over
every id of the file), the ids and their decoded terms are a `DictInjective`
dictionary; `cotd_eq_iff_eqb`: two decoded terms have the same id exactly
when they are `Term.eqb`-equal. The reader's binary search is not proved
correct (the token sort is not proved sorted; module header of
`DictWriter`), so the test stands in for that proof.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Cottas.DictWriter
import L4Factoidal.Storage.TermFoldTheorems

namespace L4Factoidal.Cottas

open L4Factoidal.RDF
open L4Factoidal.Storage.TermFold

theorem termRoundTripsAll_spec (bs : ByteArray) (h : DictHeader) (hc : termRoundTripsAll bs h = true) :
    ∀ n, n < h.numTokens → ∃ t, dictDecodeTerm bs h n = some t ∧ dictEncodeTerm bs h t = some n := by
  intro n hn
  unfold termRoundTripsAll at hc
  rw [List.all_eq_true] at hc
  have := hc n (List.mem_range.mpr hn)
  split at this
  · rename_i t ht
    exact ⟨t, ht, by simpa using this⟩
  · cases this

theorem cotd_dictInjective (bs : ByteArray) (h : DictHeader) (hc : termRoundTripsAll bs h = true) :
    DictInjective (dictEncodeTerm bs h) (dictDecodeTerm bs h)
      (fun t => ∃ n, n < h.numTokens ∧ dictDecodeTerm bs h n = some t) (· < h.numTokens) :=
  DictInjective.ofDecodeCert (termRoundTripsAll_spec bs h hc)

theorem dictDecodeTerm_folded (bs : ByteArray) (h : DictHeader) (n : Nat) (t : Term)
    (hd : dictDecodeTerm bs h n = some t) : foldTerm t = t := by
  unfold dictDecodeTerm tokenTerm? at hd
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hd
  obtain ⟨_, _, u, _, rfl⟩ := hd
  exact foldTerm_idem u

theorem cotd_eq_iff_eqb (bs : ByteArray) (h : DictHeader) (hc : termRoundTripsAll bs h = true)
    {t u : Term} {n m : Nat} (hn : n < h.numTokens) (hm : m < h.numTokens)
    (ht : dictDecodeTerm bs h n = some t) (hu : dictDecodeTerm bs h m = some u) :
    n = m ↔ t.eqb u = true := by
  have D := cotd_dictInjective bs h hc
  rw [← D.dec_eq_iff hn hm ht hu]
  constructor
  · intro e; subst e; exact Term.eqb_refl t
  · intro e
    rw [← normalizeTerm_eq_iff_eqb] at e
    rwa [dictDecodeTerm_folded bs h n t ht, dictDecodeTerm_folded bs h m u hu] at e

end L4Factoidal.Cottas

#print axioms L4Factoidal.Cottas.cotd_dictInjective
#print axioms L4Factoidal.Cottas.cotd_eq_iff_eqb
