/-
L4Factoidal.Storage.IndexedBlockDictTheorems — the dictionary of an
`IndexedBlock` (IBK, and IBK1 to IBK3 on decode) satisfies
`RDF.DictInjective`, with one id per RDF term
(https://github.com/danbri/factoidal/issues/975 step 2 and phase B4,
https://github.com/danbri/factoidal/issues/977).

* `buildIdMap_spec`: when `buildIdMap` accepts a list of terms, the list has
  no duplicate, and the map gives each term of the list `next` plus its
  position.
* `fromParts?_nodup`: a block that `fromParts?` builds has the fold of the
  dictionary it was given (`TermFold.foldTerm`, language tags in lower case),
  and that has no duplicate; `fromParts?_folded`: its entries are folded.
* `fromParts?_dictInjective`: `listEnc` / `listDec` over the dictionary are a
  `DictInjective` dictionary on its entries and positions (`Eq` on `Term`).
* `fromParts?_idByTerm`: the hash map that `candidateRows` reads gives each
  term its position in the dictionary, and no id to a term outside it.
* `fromParts?_foldedDictInjective`: the lookup `Block.termId?`, which folds
  the wanted term, is `DictInjective` on the folded entries;
  `fromParts?_termId?_eq_iff_eqb`: two terms that have ids have the same id
  exactly when they are `Term.eqb`-equal, so `"x"@en` and `"x"@EN` have one
  id (RDF 1.2 Concepts section 3.4).

`IndexedBlockWireV3.supported` and `IndexedBlockWireV4.supported` include
`(fromParts? ...).isSome`, so a block that passes them has these properties.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.DictInjective
import L4Factoidal.Storage.IndexedBlock
import L4Factoidal.Storage.TermFoldTheorems

namespace L4Factoidal.Storage.IndexedBlock

open L4Factoidal.RDF
open L4Factoidal.Storage.TermFold

/-- `buildIdMap` accepts only a list without duplicates whose terms the start
    map does not hold, and maps each term of the list to `next` plus its
    position; other terms keep their entry of the start map. -/
theorem buildIdMap_spec : ∀ (l : List Term) (next : Nat) (ids m : Std.HashMap Term TermId),
    buildIdMap l next ids = some m →
      l.Nodup ∧ (∀ t ∈ l, ids[t]? = none) ∧
        (∀ t, t ∈ l → m[t]? = some (next + l.idxOf t)) ∧ (∀ t, t ∉ l → m[t]? = ids[t]?)
  | [], next, ids, m, h => by
    simp only [buildIdMap, Option.some.injEq] at h
    subst h
    simp
  | term :: rest, next, ids, m, h => by
    simp only [buildIdMap] at h
    split at h
    · cases h
    · rename_i hnone
      have hn : ids[term]? = none := by simpa using hnone
      obtain ⟨hnd, hfree, hin, hout⟩ := buildIdMap_spec rest (next + 1) (ids.insert term next) m h
      have hnot : term ∉ rest := by
        intro hm
        have := hfree term hm
        simp at this
      refine ⟨List.nodup_cons.mpr ⟨hnot, hnd⟩, ?_, ?_, ?_⟩
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact hn
        · have := hfree t ht
          rw [Std.HashMap.getElem?_insert] at this
          split at this
          · cases this
          · exact this
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · rw [hout t hnot, Std.HashMap.getElem?_insert]
          simp
        · rw [hin t ht, List.idxOf_cons]
          have hne : (term == t) = false := by
            apply beq_eq_false_iff_ne.mpr
            intro e; subst e; exact hnot ht
          rw [hne]
          simp only [cond_false, Option.some.injEq]
          omega
      · intro t ht
        have h1 : t ≠ term := fun e => ht (e ▸ List.mem_cons_self)
        have h2 : t ∉ rest := fun e => ht (List.mem_cons_of_mem _ e)
        rw [hout t h2, Std.HashMap.getElem?_insert]
        have : (term == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h1)
        simp [this]

/-- A block built by `fromParts?` holds the fold of the dictionary it was
    given, and that has no duplicate. -/
theorem fromParts?_nodup (dict : Array Term) (rows : Array IdTriple) (b : Block)
    (h : fromParts? dict rows = some b) :
    b.dict = dict.map foldTerm ∧ (dict.map foldTerm).toList.Nodup := by
  unfold fromParts? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨ids, hids, hb⟩ := h
  split at hb
  · simp only [Option.some.injEq] at hb
    subst hb
    exact ⟨rfl, (buildIdMap_spec _ 0 ∅ ids hids).1⟩
  · cases hb

/-- The entries of a block built by `fromParts?` are folded. -/
theorem fromParts?_folded (dict : Array Term) (rows : Array IdTriple) (b : Block)
    (h : fromParts? dict rows = some b) : ∀ t ∈ b.dict.toList, foldTerm t = t := by
  rw [(fromParts?_nodup dict rows b h).1, ← dictFolded_iff]
  exact dictFolded_map dict

/-- The dictionary of a block built by `fromParts?` is `DictInjective` on its
    entries and positions. -/
theorem fromParts?_dictInjective (dict : Array Term) (rows : Array IdTriple) (b : Block)
    (h : fromParts? dict rows = some b) :
    DictInjective (listEnc b.dict.toList) (listDec b.dict.toList) (· ∈ b.dict.toList)
      (· < b.dict.toList.length) := by
  obtain ⟨hd, hnd⟩ := fromParts?_nodup dict rows b h
  rw [hd]
  exact listDict_dictInjective _ hnd

/-- The lookup map of a block built by `fromParts?` is `listEnc` of its
    dictionary. -/
theorem fromParts?_idByTerm (dict : Array Term) (rows : Array IdTriple) (b : Block)
    (h : fromParts? dict rows = some b) (t : Term) : b.idByTerm[t]? = listEnc b.dict.toList t := by
  unfold fromParts? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨ids, hids, hb⟩ := h
  split at hb
  · simp only [Option.some.injEq] at hb
    subst hb
    obtain ⟨_, _, hin, hout⟩ := buildIdMap_spec _ 0 ∅ ids hids
    show ids[t]? = listEnc (dict.map foldTerm).toList t
    unfold listEnc
    by_cases hm : t ∈ (dict.map foldTerm).toList
    · rw [if_pos hm, hin t hm]; simp
    · rw [if_neg hm, hout t hm]; simp
  · cases hb

/-- The lookup `Block.termId?` of a block built by `fromParts?` (it folds the
    wanted term) is `DictInjective` on the folded entries and the positions. -/
theorem fromParts?_foldedDictInjective (dict : Array Term) (rows : Array IdTriple) (b : Block)
    (h : fromParts? dict rows = some b) :
    DictInjective b.termId? (listDec b.dict.toList) (· ∈ b.dict.toList) (· < b.dict.toList.length) := by
  have e : b.termId? = fun t => listEnc b.dict.toList (foldTerm t) := by
    funext t; exact fromParts?_idByTerm dict rows b h (foldTerm t)
  rw [e]
  obtain ⟨hd, hnd⟩ := fromParts?_nodup dict rows b h
  rw [← hd] at hnd
  exact foldedListDict_dictInjective _ hnd (fromParts?_folded dict rows b h)

/-- In a block built by `fromParts?`, two terms that have ids have the same id
    exactly when they are the same RDF term under `Term.eqb`. -/
theorem fromParts?_termId?_eq_iff_eqb (dict : Array Term) (rows : Array IdTriple) (b : Block)
    (h : fromParts? dict rows = some b) {t u : Term} {n m : Nat}
    (hn : b.termId? t = some n) (hm : b.termId? u = some m) : n = m ↔ t.eqb u = true := by
  have e : ∀ x, b.termId? x = listEnc b.dict.toList (foldTerm x) := fun x =>
    fromParts?_idByTerm dict rows b h (foldTerm x)
  rw [e] at hn hm
  exact foldedListEnc_eq_iff_eqb _ hn hm

/-! ## Tests -/

private def litEN : Term := .literal (Literal.langString "x" "EN")
private def liten : Term := .literal (Literal.langString "x" "en")

-- IBK ids are per RDF term: `"x"@en` and `"x"@EN` get one id (issue 977)
#guard (fromParts? #[liten, litEN] #[]).isNone
#guard (fromParts? #[liten, liten] #[]).isNone
-- a dictionary read from a file written before the fold is folded
#guard ((fromParts? #[litEN] #[]).map (·.dict)) == some #[liten]
#guard (fromGraph [⟨.iri ⟨"urn:s", by decide⟩, ⟨"urn:p", by decide⟩, liten⟩,
                   ⟨.iri ⟨"urn:s", by decide⟩, ⟨"urn:p", by decide⟩, litEN⟩]).dict.size == 3
#guard ((fromParts? #[liten] #[]).bind (·.termId? litEN)) == some 0

end L4Factoidal.Storage.IndexedBlock

#print axioms L4Factoidal.Storage.IndexedBlock.buildIdMap_spec
#print axioms L4Factoidal.Storage.IndexedBlock.fromParts?_dictInjective
#print axioms L4Factoidal.Storage.IndexedBlock.fromParts?_idByTerm
#print axioms L4Factoidal.Storage.IndexedBlock.fromParts?_folded
#print axioms L4Factoidal.Storage.IndexedBlock.fromParts?_foldedDictInjective
#print axioms L4Factoidal.Storage.IndexedBlock.fromParts?_termId?_eq_iff_eqb
#print axioms L4Factoidal.RDF.listDict_dictInjective
