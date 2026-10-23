/-
L4Factoidal.Storage.IndexedBlockDictTheorems — the dictionary of an
`IndexedBlock` (IBK, and IBK3 and IBK4 on decode) satisfies
`RDF.DictInjective` (https://github.com/danbri/factoidal/issues/975, step 2).

* `buildIdMap_spec`: when `buildIdMap` accepts a list of terms, the list has
  no duplicate, and the map gives each term of the list `next` plus its
  position.
* `fromParts?_dictInjective`: a block that `fromParts?` builds has a
  dictionary without duplicates, so `listEnc` / `listDec` over it are a
  `DictInjective` dictionary on its entries and positions.
* `fromParts?_idByTerm`: the hash map that `candidateRows` reads gives each
  term its position in the dictionary, and no id to a term outside it.
  `IndexedBlockWireV3.supported` and `IndexedBlockWireV4.supported` include
  `(fromParts? ...).isSome`, so a block that passes them has these
  properties.

Term equality is `Eq` on `Term` (structural): the dictionary interns
structurally distinct terms, and the engine applies `Term.eqb` after decoding
(module header of `IndexedBlock`). So `"x"@en` and `"x"@EN` have two ids
(test below). This is the IBK design, not a dictionary defect; a graph that
holds both triples is not a set under `Triple.eqb`
(https://github.com/danbri/factoidal/issues/971).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.DictInjective
import L4Factoidal.Storage.IndexedBlock

namespace L4Factoidal.Storage.IndexedBlock

open L4Factoidal.RDF

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

/-- A block built by `fromParts?` has a dictionary without duplicates. -/
theorem fromParts?_nodup (dict : Array Term) (rows : Array IdTriple) (b : Block)
    (h : fromParts? dict rows = some b) : b.dict = dict ∧ dict.toList.Nodup := by
  unfold fromParts? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨ids, hids, hb⟩ := h
  split at hb
  · simp only [Option.some.injEq] at hb
    subst hb
    exact ⟨rfl, (buildIdMap_spec dict.toList 0 ∅ ids hids).1⟩
  · cases hb

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
    obtain ⟨_, _, hin, hout⟩ := buildIdMap_spec dict.toList 0 ∅ ids hids
    show ids[t]? = listEnc dict.toList t
    unfold listEnc
    by_cases hm : t ∈ dict.toList
    · rw [if_pos hm, hin t hm]; simp
    · rw [if_neg hm, hout t hm]; simp
  · cases hb

/-! ## Tests -/

private def litEN : Term := .literal (Literal.langString "x" "EN")
private def liten : Term := .literal (Literal.langString "x" "en")

-- IBK ids are per structural term: `"x"@en` and `"x"@EN` get two ids
#guard (fromParts? #[liten, litEN] #[]).isSome
#guard (fromParts? #[liten, liten] #[]).isNone
#guard (fromGraph [⟨.iri ⟨"urn:s", by decide⟩, ⟨"urn:p", by decide⟩, liten⟩,
                   ⟨.iri ⟨"urn:s", by decide⟩, ⟨"urn:p", by decide⟩, litEN⟩]).dict.size == 4

end L4Factoidal.Storage.IndexedBlock

#print axioms L4Factoidal.Storage.IndexedBlock.buildIdMap_spec
#print axioms L4Factoidal.Storage.IndexedBlock.fromParts?_dictInjective
#print axioms L4Factoidal.Storage.IndexedBlock.fromParts?_idByTerm
#print axioms L4Factoidal.RDF.listDict_dictInjective
