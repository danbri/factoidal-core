/-
L4Factoidal.RDF.TermJsonDictTheorems — the term table of the TermJson compact
form has one entry per RDF term (https://github.com/danbri/factoidal/issues/977;
issue 975 phase B4).

* `compactSpec_nodup`, `compactSpec_folded`: the table of `compactSpec qs` has
  no duplicate, and every entry is folded (language tags in lower case).
* `compactSpec_dictInjective`: the table, looked up through the fold, is
  `RDF.DictInjective` on its entries and positions;
  `compactSpec_eq_iff_eqb`: two terms with entries have one entry exactly when
  they are `Term.eqb`-equal.

The executable table `compactFast` is certified by `compactCertified` for the
read back (`compactCertified_sound`); that it equals the table of
`compactSpec` is checked by `#guard`, not proved. The proved one-pass writer
of the same table is `QuadsBin.quadsBin` (`QuadsBin.quadsBin_dictInjective`).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.TermJson
import L4Factoidal.Storage.TermFoldTheorems

namespace L4Factoidal.RDF.TermJson

open L4Factoidal.RDF
open L4Factoidal.Storage.TermFold

theorem nodup_foldl_addTerm : ∀ (l acc : List Term), acc.Nodup → (l.foldl addTerm acc).Nodup
  | [], _, h => h
  | x :: r, acc, h => by
    simp only [List.foldl_cons]
    apply nodup_foldl_addTerm r
    unfold addTerm
    split
    · exact h
    · rename_i hc
      have hx : x ∉ acc := by simpa using hc
      rw [List.nodup_append]
      exact ⟨h, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, fun a ha b hb => by
        simp only [List.mem_singleton] at hb
        subst hb
        exact fun e => hx (e ▸ ha)⟩

theorem mem_foldl_addTerm_inv : ∀ (l acc : List Term) (t : Term),
    t ∈ l.foldl addTerm acc → t ∈ acc ∨ t ∈ l
  | [], _, _, h => Or.inl h
  | x :: r, acc, t, h => by
    simp only [List.foldl_cons] at h
    rcases mem_foldl_addTerm_inv r _ t h with h | h
    · unfold addTerm at h
      split at h
      · exact Or.inl h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · simp only [List.mem_singleton] at h
          subst h
          exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem foldTerm_subjectToTerm (s : Subject) : foldTerm (subjectToTerm s) = subjectToTerm s := by
  cases s <;> rfl

/-- The terms of a folded quad are folded. -/
theorem quadTerms_foldQuad (q : Quad) : ∀ t ∈ quadTerms (foldQuad q), foldTerm t = t := by
  obtain ⟨g, ⟨s, p, o⟩⟩ := q
  intro t ht
  cases g with
  | none =>
    simp only [foldQuad, foldTriple, quadTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact foldTerm_subjectToTerm s
    · rfl
    · exact foldTerm_idem o
  | some gs =>
    simp only [foldQuad, foldTriple, quadTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact foldTerm_subjectToTerm s
    · rfl
    · exact foldTerm_idem o
    · exact foldTerm_subjectToTerm gs

theorem compactSpec_nodup (qs : List Quad) : (compactSpec qs).1.Nodup :=
  nodup_foldl_addTerm _ [] List.nodup_nil

theorem compactSpec_folded (qs : List Quad) : ∀ t ∈ (compactSpec qs).1, foldTerm t = t := by
  intro t ht
  rcases mem_foldl_addTerm_inv _ [] t ht with h | h
  · cases h
  · obtain ⟨q, hq, ht⟩ := List.mem_flatMap.mp h
    obtain ⟨q0, _, rfl⟩ := List.mem_map.mp hq
    exact quadTerms_foldQuad q0 t ht

/-- The table of the compact form, looked up through the fold, is
    `DictInjective` on its entries and positions. -/
theorem compactSpec_dictInjective (qs : List Quad) :
    DictInjective (fun t => listEnc (compactSpec qs).1 (foldTerm t)) (listDec (compactSpec qs).1)
      (· ∈ (compactSpec qs).1) (· < (compactSpec qs).1.length) :=
  foldedListDict_dictInjective _ (compactSpec_nodup qs) (compactSpec_folded qs)

/-- Two terms with entries in the table have one entry exactly when they are
    the same RDF term under `Term.eqb`. -/
theorem compactSpec_eq_iff_eqb (qs : List Quad) {t u : Term} {n m : Nat}
    (hn : listEnc (compactSpec qs).1 (foldTerm t) = some n)
    (hm : listEnc (compactSpec qs).1 (foldTerm u) = some m) : n = m ↔ t.eqb u = true :=
  foldedListEnc_eq_iff_eqb _ hn hm

private def exI (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩
private def exQs : List Quad :=
  [(none, ⟨.iri (exI "http://e/a"), exI "http://e/p", .literal (Literal.langString "x" "EN")⟩),
   (none, ⟨.iri (exI "http://e/b"), exI "http://e/p", .literal (Literal.langString "x" "en")⟩),
   (none, ⟨.iri (exI "http://e/b"), exI "http://e/p", .literal (Literal.string "v")⟩),
   (none, ⟨.iri (exI "http://e/a"), exI "http://e/p", .literal (Literal.string "v")⟩)]

-- the executable table is the table of the specification
#guard (compactCertified exQs).map (·.1.toList) == some (compactSpec exQs).1
#guard (compactSpec exQs).1.length == 5

end L4Factoidal.RDF.TermJson

#print axioms L4Factoidal.RDF.TermJson.compactSpec_dictInjective
#print axioms L4Factoidal.RDF.TermJson.compactSpec_eq_iff_eqb
