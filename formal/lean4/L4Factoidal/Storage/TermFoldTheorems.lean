/-
L4Factoidal.Storage.TermFoldTheorems — the fold of `TermFold` gives one id
per RDF term (https://github.com/danbri/factoidal/issues/977; issue 975 phase
B4).

* `normalizeTerm_eq_iff_eqb`: two terms have the same fold exactly when they
  are `Term.eqb`-equal (language tags without case; lexical form, datatype and
  base direction exactly; RDF 1.1 Concepts section 3.3, RDF 1.2 Concepts
  section 3.4).
* `joinKey_eq_foldTerm`: the fold is the join key of the dataset target
  (`Term.joinKey`), so a dictionary of folded terms satisfies `HeldFolded` of
  `Sbm11.DenotationTheorems` (`heldFolded_of_folded`).
* `foldedListDict_dictInjective`: a list dictionary without duplicates whose
  entries are folded, with the lookup that folds the wanted term first, is
  `DictInjective` on its entries and positions; `foldedListEnc_eq_iff_eqb`:
  two terms that have ids have the same id exactly when they are
  `Term.eqb`-equal. Every store of issue 977 instantiates these two.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.DictInjective
import L4Factoidal.Storage.TermFold
import L4Factoidal.Storage.TermWireV2
import L4Factoidal.Storage.Sbm11.MemGenDictTheorems
import L4Factoidal.Storage.Sbm11.FilterIdTheorems
import L4Factoidal.Storage.Sbm11.DenotationTheorems

namespace L4Factoidal.Storage.TermFold

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11

theorem foldTerm_idem (t : Term) : foldTerm (foldTerm t) = foldTerm t :=
  FilterIdTheorems.normalize_idem t

theorem termFolded_iff (t : Term) : termFolded t = true ↔ foldTerm t = t := by
  simp [termFolded]

theorem termFolded_foldTerm (t : Term) : termFolded (foldTerm t) = true :=
  (termFolded_iff _).mpr (foldTerm_idem t)

/-- Two terms have the same fold exactly when they are the same RDF term
    under `Term.eqb`. -/
theorem normalizeTerm_eq_iff_eqb (t u : Term) : foldTerm t = foldTerm u ↔ t.eqb u = true := by
  have ht : t.eqb (normalizeTerm t) = true := MemGen.eqb_normalize t
  have hu : u.eqb (normalizeTerm u) = true := MemGen.eqb_normalize u
  have hu' : (normalizeTerm u).eqb u = true := by rw [Term.eqb_symm]; exact hu
  constructor
  · intro e
    have : t.eqb (normalizeTerm u) = true := by
      show t.eqb (normalizeTerm u) = true
      rw [← show normalizeTerm t = normalizeTerm u from e]; exact ht
    exact Term.eqb_trans this hu'
  · intro e
    have h1 : t.eqb (normalizeTerm u) = true := Term.eqb_trans e hu
    exact MemGen.eqb_norm t (normalizeTerm u) (FilterIdTheorems.normalize_idem u) h1

/-- The join key of a term is its fold. -/
theorem joinKey_eq_foldTerm : ∀ t : Term, t.joinKey = foldTerm t
  | .iri _ => rfl
  | .bnode _ => rfl
  | .literal l => by
      obtain ⟨⟨lex, dt, tag, dir⟩, hwf⟩ := l
      cases tag with
      | none => rfl
      | some tg =>
        show Term.joinKey _ = normalizeLit _
        unfold normalizeLit
        simp only
        split
        · rfl
        · rename_i h
          exact absurd (by cases dir <;> simpa [literalWf] using hwf) h
  | .tripleTerm s p o => by
      show Term.tripleTerm s p o.joinKey = Term.tripleTerm s p (normalizeTerm o)
      rw [joinKey_eq_foldTerm o]

/-- A dictionary domain of folded terms is `HeldFolded`. -/
theorem heldFolded_of_folded (dom : Term → Prop) (h : ∀ t, dom t → foldTerm t = t) :
    Overlay.HeldFolded dom := by
  intro t ht
  rw [joinKey_eq_foldTerm]
  exact h t ht

theorem dictFolded_iff (dict : Array Term) :
    dictFolded dict = true ↔ ∀ t ∈ dict.toList, foldTerm t = t := by
  rw [dictFolded, Array.all_eq_true_iff_forall_mem]
  simp [termFolded_iff]

/-- The fold of every entry of an array is folded. -/
theorem dictFolded_map (dict : Array Term) : dictFolded (dict.map foldTerm) = true := by
  rw [dictFolded_iff]
  intro t ht
  simp only [Array.toList_map, List.mem_map] at ht
  obtain ⟨u, _, rfl⟩ := ht
  exact foldTerm_idem u

/-- The fold of a folded array is the array. -/
theorem map_foldTerm_of_folded (dict : Array Term) (h : dictFolded dict = true) :
    dict.map foldTerm = dict := by
  rw [dictFolded_iff] at h
  apply Array.ext'
  simp only [Array.toList_map]
  exact (List.map_congr_left h).trans (List.map_id _)

/-! ## Wire terms (IBK5, PTD2) -/

open L4Factoidal.Storage.TermWireV2 in
theorem foldWire_idem (w : WireTerm) : foldWire (foldWire w) = foldWire w := by
  cases w with
  | inline t => simp only [foldWire, foldTerm_idem]
  | blob b =>
    cases b with
    | mk dt tag dir len sha =>
      cases tag <;> simp [foldWire, FilterIdTheorems.string_toLower_idem]

open L4Factoidal.Storage.TermWireV2 in
theorem wireDictFolded_iff (dict : Array WireTerm) :
    wireDictFolded dict = true ↔ ∀ w ∈ dict.toList, foldWire w = w := by
  rw [wireDictFolded, Array.all_eq_true_iff_forall_mem]
  simp [wireFolded]

open L4Factoidal.Storage.TermWireV2 in
theorem wireDictFolded_map (dict : Array WireTerm) : wireDictFolded (dict.map foldWire) = true := by
  rw [wireDictFolded_iff]
  intro w hw
  simp only [Array.toList_map, List.mem_map] at hw
  obtain ⟨u, _, rfl⟩ := hw
  exact foldWire_idem u

open L4Factoidal.Storage.TermWireV2 in
theorem map_foldWire_of_folded (dict : Array WireTerm) (h : wireDictFolded dict = true) :
    dict.map foldWire = dict := by
  rw [wireDictFolded_iff] at h
  apply Array.ext'
  simp only [Array.toList_map]
  exact (List.map_congr_left h).trans (List.map_id _)

/-! ## A list dictionary of folded terms -/

/-- A list dictionary without duplicates whose entries are folded, looked up
    through the fold, is `DictInjective` on its entries and positions. -/
theorem foldedListDict_dictInjective (l : List Term) (hnd : l.Nodup)
    (hf : ∀ t ∈ l, foldTerm t = t) :
    DictInjective (fun t => listEnc l (foldTerm t)) (listDec l) (· ∈ l) (· < l.length) := by
  have D := listDict_dictInjective l hnd
  refine DictInjective.ofRoundTrip (fun t ht => ?_) (fun t n ht he => ?_) (fun n hn => ?_)
  · obtain ⟨n, hn, he⟩ := D.covers t ht
    exact ⟨n, hn, by simp only [hf t ht]; exact he⟩
  · simp only [hf t ht] at he
    exact D.decEnc t n ht he
  · obtain ⟨t, ht, hd, he⟩ := D.encDec n hn
    exact ⟨t, ht, hd, by simp only [hf t ht]; exact he⟩

/-- The id of a term in a list dictionary names its fold. -/
theorem listEnc_some {l : List Term} {t : Term} {n : Nat} (h : listEnc l t = some n) :
    l[n]? = some t := by
  unfold listEnc at h
  split at h
  · rename_i hm
    cases Option.some.inj h
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hm)]
    simp [List.getElem_idxOf]
  · cases h

/-- Two terms that have ids in a list dictionary of folded terms have the same
    id exactly when they are the same RDF term (`Term.eqb`). -/
theorem foldedListEnc_eq_iff_eqb (l : List Term) {t u : Term} {n m : Nat}
    (hn : listEnc l (foldTerm t) = some n) (hm : listEnc l (foldTerm u) = some m) :
    n = m ↔ t.eqb u = true := by
  rw [← normalizeTerm_eq_iff_eqb]
  have e1 := listEnc_some hn
  have e2 := listEnc_some hm
  constructor
  · intro e
    subst e
    rw [e1] at e2
    exact Option.some.inj e2
  · intro e
    rw [e] at hn
    rw [hn] at hm
    exact Option.some.inj hm

/-! ## A dictionary array looked up by fold (PTD1, PTD2)

The lookup returns the first position whose entry has the fold of the wanted
term. When no two entries have one fold, it is `DictInjective` on the entries
(they need not be folded: a dictionary written before the fold), and two
terms with ids have one id exactly when they have one fold. -/

/-- The lookup by fold is `DictInjective` when no two entries have one fold. -/
theorem findFold_dictInjective {α : Type} [DecidableEq α] (f : α → α) (a : Array α)
    (hnd : (a.toList.map f).Nodup) :
    DictInjective (fun t => a.findIdx? (fun u => f u == f t)) (fun n => a[n]?) (· ∈ a) (· < a.size) := by
  have hinj : ∀ i j (hi : i < a.size) (hj : j < a.size), f a[i] = f a[j] → i = j := by
    intro i j hi hj e
    have hi' : i < (a.toList.map f).length := by simpa using hi
    exact (List.getElem?_inj hi' hnd).mp (by simp [hi, hj, e])
  have spec : ∀ t n, a.findIdx? (fun u => f u == f t) = some n → ∃ h : n < a.size, f a[n] = f t := by
    intro t n h
    obtain ⟨hn, hp, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
    exact ⟨hn, by simpa using hp⟩
  have hsome : ∀ t, t ∈ a → ∃ n, n < a.size ∧ a.findIdx? (fun u => f u == f t) = some n := by
    intro t ht
    have := Array.findIdx?_eq_some_of_exists (p := fun u => f u == f t) ⟨t, ht, by simp⟩
    refine ⟨_, ?_, this⟩
    obtain ⟨hn, _⟩ := spec t _ this
    exact hn
  refine DictInjective.ofRoundTrip (fun t ht => ?_) (fun t n ht he => ?_) (fun n hn => ?_)
  · obtain ⟨n, hn, he⟩ := hsome t ht
    exact ⟨n, hn, he⟩
  · obtain ⟨hn, hf⟩ := spec t n he
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp ht
    have := hinj n k hn hk hf
    subst this
    simp [hn]
  · refine ⟨a[n], Array.getElem_mem hn, by simp [hn], ?_⟩
    obtain ⟨m, hm, he⟩ := hsome a[n] (Array.getElem_mem hn)
    obtain ⟨hm', hf⟩ := spec a[n] m he
    have := hinj m n hm' hn hf
    subst this
    exact he

/-- Under the same condition, two terms with ids have the same id exactly when
    they have the same fold. -/
theorem findFold_eq_iff {α : Type} [DecidableEq α] (f : α → α) (a : Array α)
    (hnd : (a.toList.map f).Nodup) {t u : α} {n m : Nat}
    (hn : a.findIdx? (fun x => f x == f t) = some n)
    (hm : a.findIdx? (fun x => f x == f u) = some m) : n = m ↔ f t = f u := by
  obtain ⟨hn', hpn, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp hn
  obtain ⟨hm', hpm, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp hm
  simp only [beq_iff_eq] at hpn hpm
  constructor
  · intro e
    subst e
    rw [← hpn, ← hpm]
  · intro e
    have : (fun x => f x == f t) = (fun x => f x == f u) := by funext x; rw [e]
    rw [this, hm] at hn
    exact (Option.some.inj hn).symm

end L4Factoidal.Storage.TermFold

#print axioms L4Factoidal.Storage.TermFold.normalizeTerm_eq_iff_eqb
#print axioms L4Factoidal.Storage.TermFold.joinKey_eq_foldTerm
#print axioms L4Factoidal.Storage.TermFold.heldFolded_of_folded
#print axioms L4Factoidal.Storage.TermFold.map_foldTerm_of_folded
#print axioms L4Factoidal.Storage.TermFold.foldedListDict_dictInjective
#print axioms L4Factoidal.Storage.TermFold.foldedListEnc_eq_iff_eqb
#print axioms L4Factoidal.Storage.TermFold.findFold_dictInjective
#print axioms L4Factoidal.Storage.TermFold.findFold_eq_iff
