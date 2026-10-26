/-
L4Factoidal.Storage.StoreDictTheorems — `RDF.DictInjective` for the IBK4,
IBK5, PTD1, PTD2 and TLI1 dictionaries, with one id per RDF term
(https://github.com/danbri/factoidal/issues/975 phase B4,
https://github.com/danbri/factoidal/issues/977). The IBK (IBK1 to IBK3)
instance is `IndexedBlockDictTheorems.fromParts?_foldedDictInjective`.

* IBK4 (`IndexedBlockWireV4.fromParts?`, every IBK4 decode):
  `v4_fromParts?_foldedDictInjective`, the lookup `QuadBlock.termId?` (it folds
  the wanted term) on the folded entries; `v4_termId?_eq_iff_eqb`.
* IBK5 (`IndexedBlockWireV5.fromParts?`, every IBK5 decode): `v5_buildIdMap_spec`,
  `v5_fromParts?_foldedDictInjective` over wire terms (`Eq` on `WireTerm`,
  entries folded by `TermWireV2.foldWire`); `v5_termId?_eq_iff` (one id
  exactly when the folds agree).
* PTD1 and PTD2 (`findTermId?`, which compares folds): `ptd1_dictInjective`,
  `ptd2_dictInjective`, when no two entries have one fold
  (`(terms.toList.map foldTerm).Nodup`, a `decide`-able test; every IBK3 and
  IBK4 dictionary passes it, `ptd1_nodup_of_fromParts?`). The entries need
  not be folded, so a PTD1 dictionary written before the fold keeps its
  meaning. `ptd1_eq_iff_eqb`: one id exactly when `Term.eqb`.
* TLI1 (`TermLocalIndex.lookup?`): `tli1_dictInjective`, from PTD1, when the
  index agrees with its dictionary on the dictionary's terms
  (`TermLocalIndex.agreesWithDictionary`, the reference contract of a TLI1
  index; a `Bool` test over the dictionary).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.IndexedBlockDictTheorems
import L4Factoidal.Storage.IndexedBlockWireV4
import L4Factoidal.Storage.IndexedBlockWireV5
import L4Factoidal.Storage.PagedTermDictionaryV2
import L4Factoidal.Storage.TermLocalIndex

namespace L4Factoidal.Storage.StoreDictTheorems

open L4Factoidal.RDF
open L4Factoidal.Storage.TermFold
open L4Factoidal.Storage.TermWireV2

/-! ## IBK4 -/

section V4
open L4Factoidal.Storage.IndexedBlockWireV4
open L4Factoidal.Storage.IndexedBlock (buildIdMap buildIdMap_spec)

theorem v4_fromParts?_nodup (dict : Array Term) (rows : Array IdQuad) (b : QuadBlock)
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

theorem v4_fromParts?_idByTerm (dict : Array Term) (rows : Array IdQuad) (b : QuadBlock)
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

/-- The lookup `QuadBlock.termId?` of an IBK4 block built by `fromParts?` is
    `DictInjective` on the folded entries and the positions. -/
theorem v4_fromParts?_foldedDictInjective (dict : Array Term) (rows : Array IdQuad) (b : QuadBlock)
    (h : fromParts? dict rows = some b) :
    DictInjective b.termId? (listDec b.dict.toList) (· ∈ b.dict.toList) (· < b.dict.toList.length) := by
  have e : b.termId? = fun t => listEnc b.dict.toList (foldTerm t) := by
    funext t; exact v4_fromParts?_idByTerm dict rows b h (foldTerm t)
  rw [e]
  obtain ⟨hd, hnd⟩ := v4_fromParts?_nodup dict rows b h
  have hf : ∀ t ∈ b.dict.toList, foldTerm t = t := by
    rw [hd, ← dictFolded_iff]; exact dictFolded_map dict
  rw [← hd] at hnd
  exact foldedListDict_dictInjective _ hnd hf

theorem v4_termId?_eq_iff_eqb (dict : Array Term) (rows : Array IdQuad) (b : QuadBlock)
    (h : fromParts? dict rows = some b) {t u : Term} {n m : Nat}
    (hn : b.termId? t = some n) (hm : b.termId? u = some m) : n = m ↔ t.eqb u = true := by
  have e : ∀ x, b.termId? x = listEnc b.dict.toList (foldTerm x) := fun x =>
    v4_fromParts?_idByTerm dict rows b h (foldTerm x)
  rw [e] at hn hm
  exact foldedListEnc_eq_iff_eqb _ hn hm

end V4

/-! ## IBK5 -/

section V5
open L4Factoidal.Storage.IndexedBlockWireV5
open L4Factoidal.Storage.IndexedBlock (TermId)
open L4Factoidal.Storage.IndexedBlockWireV4 (IdQuad)

/-- `IndexedBlockWireV5.buildIdMap` accepts only a list without duplicates
    whose terms the start map does not hold (as `IndexedBlock.buildIdMap_spec`). -/
theorem v5_buildIdMap_spec : ∀ (l : List WireTerm) (next : Nat) (ids m : Std.HashMap WireTerm TermId),
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
      obtain ⟨hnd, hfree, hin, hout⟩ := v5_buildIdMap_spec rest (next + 1) (ids.insert term next) m h
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

theorem v5_fromParts?_nodup (dict : Array WireTerm) (rows : Array IdQuad) (b : QuadBlock)
    (h : fromParts? dict rows = some b) :
    b.dict = dict.map foldWire ∧ (dict.map foldWire).toList.Nodup := by
  unfold fromParts? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨ids, hids, hb⟩ := h
  split at hb
  · simp only [Option.some.injEq] at hb
    subst hb
    exact ⟨rfl, (v5_buildIdMap_spec _ 0 ∅ ids hids).1⟩
  · cases hb

theorem v5_fromParts?_idByTerm (dict : Array WireTerm) (rows : Array IdQuad) (b : QuadBlock)
    (h : fromParts? dict rows = some b) (w : WireTerm) : b.idByTerm[w]? = listEnc b.dict.toList w := by
  unfold fromParts? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨ids, hids, hb⟩ := h
  split at hb
  · simp only [Option.some.injEq] at hb
    subst hb
    obtain ⟨_, _, hin, hout⟩ := v5_buildIdMap_spec _ 0 ∅ ids hids
    show ids[w]? = listEnc (dict.map foldWire).toList w
    unfold listEnc
    by_cases hm : w ∈ (dict.map foldWire).toList
    · rw [if_pos hm, hin w hm]; simp
    · rw [if_neg hm, hout w hm]; simp
  · cases hb

/-- The lookup `QuadBlock.termId?` of an IBK5 block built by `fromParts?`
    (it folds the wanted wire term) is `DictInjective` on the folded entries
    and the positions. -/
theorem v5_fromParts?_foldedDictInjective (dict : Array WireTerm) (rows : Array IdQuad) (b : QuadBlock)
    (h : fromParts? dict rows = some b) :
    DictInjective b.termId? (listDec b.dict.toList) (· ∈ b.dict.toList) (· < b.dict.toList.length) := by
  have e : b.termId? = fun w => listEnc b.dict.toList (foldWire w) := by
    funext w; exact v5_fromParts?_idByTerm dict rows b h (foldWire w)
  rw [e]
  obtain ⟨hd, hnd⟩ := v5_fromParts?_nodup dict rows b h
  have hf : ∀ w ∈ b.dict.toList, foldWire w = w := by
    rw [hd, ← wireDictFolded_iff]; exact wireDictFolded_map dict
  rw [← hd] at hnd
  have D := listDict_dictInjective _ hnd
  refine DictInjective.ofRoundTrip (fun w hw => ?_) (fun w n hw he => ?_) (fun n hn => ?_)
  · obtain ⟨n, hn, he⟩ := D.covers w hw
    exact ⟨n, hn, by simp only [hf w hw]; exact he⟩
  · simp only [hf w hw] at he
    exact D.decEnc w n hw he
  · obtain ⟨w, hw, hdw, he⟩ := D.encDec n hn
    exact ⟨w, hw, hdw, by simp only [hf w hw]; exact he⟩

/-- In an IBK5 block built by `fromParts?`, two wire terms that have ids have
    the same id exactly when they have the same fold. -/
theorem v5_termId?_eq_iff (dict : Array WireTerm) (rows : Array IdQuad) (b : QuadBlock)
    (h : fromParts? dict rows = some b) {v w : WireTerm} {n m : Nat}
    (hn : b.termId? v = some n) (hm : b.termId? w = some m) : n = m ↔ foldWire v = foldWire w := by
  have e : ∀ x, b.termId? x = listEnc b.dict.toList (foldWire x) := fun x =>
    v5_fromParts?_idByTerm dict rows b h (foldWire x)
  rw [e] at hn hm
  have s1 : ∀ {x : WireTerm} {k : Nat}, listEnc b.dict.toList x = some k → b.dict.toList[k]? = some x := by
    intro x k hx
    unfold listEnc at hx
    split at hx
    · rename_i hmem
      cases Option.some.inj hx
      rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem)]
      simp [List.getElem_idxOf]
    · cases hx
  constructor
  · intro eq
    subst eq
    have := (s1 hn).symm.trans (s1 hm)
    exact Option.some.inj this
  · intro eq
    rw [eq] at hn
    rw [hn] at hm
    exact Option.some.inj hm

/-- The IBK5 fold is the RDF term fold on an inline term. -/
theorem foldWire_inline (t : Term) : foldWire (.inline t) = .inline (foldTerm t) := rfl

end V5

/-! ## PTD1, PTD2 -/

/-- PTD1's `findTermId?` is `DictInjective` on the entries and the positions
    when no two entries have one fold. -/
theorem ptd1_dictInjective (terms : Array Term) (h : (terms.toList.map foldTerm).Nodup) :
    DictInjective (PagedTermDictionary.findTermId? terms) (fun n => terms[n]?) (· ∈ terms)
      (· < terms.size) :=
  findFold_dictInjective foldTerm terms h

/-- In PTD1, two terms that have ids have the same id exactly when they are
    `Term.eqb`-equal, under the same condition. -/
theorem ptd1_eq_iff_eqb (terms : Array Term) (h : (terms.toList.map foldTerm).Nodup)
    {t u : Term} {n m : Nat} (hn : PagedTermDictionary.findTermId? terms t = some n)
    (hm : PagedTermDictionary.findTermId? terms u = some m) : n = m ↔ t.eqb u = true := by
  rw [← normalizeTerm_eq_iff_eqb]
  exact findFold_eq_iff foldTerm terms h hn hm

/-- Every IBK3 and IBK4 dictionary (`fromParts?`) passes the PTD1 condition. -/
theorem ptd1_nodup_of_fromParts? (dict : Array Term) (rows : Array IndexedBlock.IdTriple)
    (b : IndexedBlock.Block) (h : IndexedBlock.fromParts? dict rows = some b) :
    (b.dict.toList.map foldTerm).Nodup := by
  have hf := IndexedBlock.fromParts?_folded dict rows b h
  obtain ⟨hd, hnd⟩ := IndexedBlock.fromParts?_nodup dict rows b h
  rw [show b.dict.toList.map foldTerm = b.dict.toList from
    (List.map_congr_left hf).trans (List.map_id _), hd]
  exact hnd

/-- PTD2's `findTermId?` is `DictInjective` on the entries and the positions
    when no two entries have one fold. -/
theorem ptd2_dictInjective (terms : Array WireTerm) (h : (terms.toList.map foldWire).Nodup) :
    DictInjective (PagedTermDictionaryV2.findTermId? terms) (fun n => terms[n]?) (· ∈ terms)
      (· < terms.size) :=
  findFold_dictInjective foldWire terms h

/-! ## TLI1 -/

/-- A TLI1 index that agrees with its PTD1 dictionary on the dictionary's
    terms (`agreesWithDictionary`, the reference contract of the module) is
    `DictInjective` on those terms, under the PTD1 condition. -/
theorem tli1_dictInjective (terms : Array Term) (h : (terms.toList.map foldTerm).Nodup)
    (hagree : ∀ t ∈ terms, TermLocalIndex.agreesWithDictionary terms t = true) :
    DictInjective (TermLocalIndex.lookup? (TermLocalIndex.entriesOf terms)) (fun n => terms[n]?)
      (· ∈ terms) (· < terms.size) :=
  (ptd1_dictInjective terms h).congr_on fun t ht => by
    have := hagree t ht
    simp only [TermLocalIndex.agreesWithDictionary, beq_iff_eq] at this
    exact this

end L4Factoidal.Storage.StoreDictTheorems

#print axioms L4Factoidal.Storage.StoreDictTheorems.v4_fromParts?_foldedDictInjective
#print axioms L4Factoidal.Storage.StoreDictTheorems.v4_termId?_eq_iff_eqb
#print axioms L4Factoidal.Storage.StoreDictTheorems.v5_fromParts?_foldedDictInjective
#print axioms L4Factoidal.Storage.StoreDictTheorems.v5_termId?_eq_iff
#print axioms L4Factoidal.Storage.StoreDictTheorems.ptd1_dictInjective
#print axioms L4Factoidal.Storage.StoreDictTheorems.ptd1_eq_iff_eqb
#print axioms L4Factoidal.Storage.StoreDictTheorems.ptd1_nodup_of_fromParts?
#print axioms L4Factoidal.Storage.StoreDictTheorems.ptd2_dictInjective
#print axioms L4Factoidal.Storage.StoreDictTheorems.tli1_dictInjective
