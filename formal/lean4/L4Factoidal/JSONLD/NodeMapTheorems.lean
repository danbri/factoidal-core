/-
L4Factoidal.JSONLD.NodeMapTheorems — the node map operations agree with
the association-list operations they replaced.

`Flatten.lean` keeps the JSON-LD node map (API §7.1) in persistent maps so
that generating it costs `O(n log n)` instead of `O(n^2)`
(`docs/designissues/2026-10-10-jsonld-node-map-scaling.md`). This file
states, and proves, that the new operations compute what the old ones did:

  * `strLt_iff_compare_lt` — `compare` on `String`, the order of every
    `Std.TreeMap` below, is the `strLt` order the earlier port sorted with
    (code-point order, the spec's "ordered lexicographically");
  * `OMap.find?_eq`, `OMap.toList_upsert` — lookup and update of the
    insertion-ordered map agree with `flLookup` and `flUpd` on its
    entries in insertion order;
  * `DedupArr` — a canonical-form set answers the spec's "already in the
    array" test exactly as the scan over `expandedEqual` did;
  * `toFields_nodeAppendProp` and its siblings — each node operation, read
    through `NmNode.toFields`, equals the original list definition, which is
    kept below in namespace `Spec` as the specification;
  * the graph-level lookup laws.

No `sorry`, no `axiom`, no `native_decide`; the `#print axioms` block at
the end shows the trusted base is Lean's own.
-/
import L4Factoidal.JSONLD.Flatten

namespace L4Factoidal.JSONLD

open L4Factoidal.JSON

/-! ## The order of `String` keys -/

theorem charListLt_iff : ∀ (xs ys : List Char), charListLt xs ys = true ↔ xs < ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys
    cases ys with
    | nil => simp [charListLt]
    | cons b bs => simp [charListLt]
  | cons a as ih =>
    intro ys
    cases ys with
    | nil => simp [charListLt]
    | cons b bs =>
      rw [List.cons_lt_cons_iff]
      simp only [charListLt]
      by_cases hab : a < b
      · simp [hab]
      · by_cases hba : b < a
        · have : a ≠ b := fun h => by subst h; exact absurd hba (Char.lt_irrefl _)
          simp [hab, hba, this]
        · have heq : a = b := Char.le_antisymm (Char.not_lt.mp hba) (Char.not_lt.mp hab)
          subst heq
          simp [hab, ih]

theorem strLt_iff_compare_lt (a b : String) : strLt a b = true ↔ compare a b = .lt := by
  unfold strLt
  rw [charListLt_iff]
  show a.toList < b.toList ↔ String.compare a b = .lt
  unfold String.compare compareOfLessAndEq
  by_cases h : a < b
  · have h' : a.toList < b.toList := h
    simp [h, h']
  · have h' : ¬ a.toList < b.toList := h
    simp only [h, if_false]
    split <;> simp [h']

/-! ## `Std.TreeMap` facts at `String` keys -/

theorem tm_get?_insert {β : Type} (t : Std.TreeMap String β) (a k : String) (v : β) :
    (t.insert k v).get? a = if k = a then some v else t.get? a := by
  have := @Std.TreeMap.getElem?_insert _ _ _ t _ a k v
  simpa [Std.compare_eq_iff_eq] using this

theorem tm_contains_insert {β : Type} (t : Std.TreeMap String β) (a k : String) (v : β) :
    (t.insert k v).contains a = true ↔ k = a ∨ t.contains a = true := by
  have := @Std.TreeMap.contains_insert _ _ _ t _ k a v
  rw [this]
  simp

theorem tm_contains_iff_isSome {β : Type} (t : Std.TreeMap String β) (a : String) :
    t.contains a = true ↔ (t.get? a).isSome = true := by
  have := @Std.TreeMap.contains_eq_isSome_getElem? _ _ _ t _ a
  rw [this]; rfl

theorem flLookup_cons {β : Type} (j k : String) (w : β) (R : List (String × β)) :
    flLookup ((j, w) :: R) k = if j = k then some w else flLookup R k := by
  unfold flLookup
  rw [List.find?_cons]
  by_cases h : j = k
  · subst h; simp
  · have hb : (j == k) = false := by simpa using h
    simp [hb, h]

theorem flUpd_cons {β : Type} (j k : String) (w v : β) (R : List (String × β)) :
    flUpd ((j, w) :: R) k v = if j = k then (j, v) :: R else (j, w) :: flUpd R k v := by
  rw [flUpd.eq_2]
  by_cases h : j = k
  · subst h; simp
  · have hb : (j == k) = false := by simpa using h
    simp [hb, h]

theorem flUpd_of_absent {β : Type} (k : String) (v : β) :
    ∀ (xs : List (String × β)), (∀ p ∈ xs, p.1 ≠ k) → flUpd xs k v = xs ++ [(k, v)] := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons p xs ih =>
    intro h
    obtain ⟨j, w⟩ := p
    rw [flUpd_cons, if_neg (h (j, w) (List.mem_cons_self ..)), List.cons_append,
      ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

namespace OMap
variable {α : Type}

/-- The entries `L` names, looked up in `tab`, in the order of `L`. -/
def ents (tab : Std.TreeMap String α) (L : List String) : List (String × α) :=
  L.filterMap (fun k => (tab.get? k).map (fun v => (k, v)))

theorem toList_eq (m : OMap α) : m.toList = ents m.tab m.rev.reverse := rfl

theorem ents_nil (tab : Std.TreeMap String α) : ents tab [] = [] := rfl

theorem ents_cons (tab : Std.TreeMap String α) (j : String) (L : List String) :
    ents tab (j :: L) =
      (match tab.get? j with
       | some v => (j, v) :: ents tab L
       | none => ents tab L) := by
  unfold ents
  rw [List.filterMap_cons]
  cases tab.get? j <;> rfl

theorem ents_append (tab : Std.TreeMap String α) (L1 L2 : List String) :
    ents tab (L1 ++ L2) = ents tab L1 ++ ents tab L2 := by
  unfold ents; exact List.filterMap_append

theorem ents_congr (t1 t2 : Std.TreeMap String α) :
    ∀ (L : List String), (∀ j ∈ L, t1.get? j = t2.get? j) → ents t1 L = ents t2 L := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons j L ih =>
    intro h
    rw [ents_cons, ents_cons, h j (List.mem_cons_self ..),
        ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]

theorem flLookup_ents (tab : Std.TreeMap String α) (k : String) :
    ∀ (L : List String), flLookup (ents tab L) k = if k ∈ L then tab.get? k else none := by
  intro L
  induction L with
  | nil => simp [ents_nil, flLookup]
  | cons j L ih =>
    rw [ents_cons]
    cases h : tab.get? j with
    | none =>
      by_cases hjk : j = k
      · subst hjk
        rw [ih, h]; simp
      · rw [ih]; simp [Ne.symm hjk]
    | some w =>
      simp only [flLookup_cons]
      by_cases hjk : j = k
      · subst hjk; rw [h]; simp
      · rw [ih]; simp [hjk, Ne.symm hjk]


/-- Replacing a present key rewrites the entry in place. -/
theorem ents_insert_present (tab : Std.TreeMap String α) (k : String) (v : α) :
    ∀ (L : List String), L.Nodup → k ∈ L → (tab.get? k).isSome = true →
      ents (tab.insert k v) L = flUpd (ents tab L) k v := by
  intro L
  induction L with
  | nil => intro _ hk; exact absurd hk (List.not_mem_nil)
  | cons j L ih =>
    intro hnd hk hsome
    rw [List.nodup_cons] at hnd
    by_cases hjk : j = k
    · subst hjk
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hsome
      have hrest : ents (tab.insert j v) L = ents tab L := by
        apply ents_congr
        intro i hi
        have hij : j ≠ i := fun h => hnd.1 (h ▸ hi)
        rw [tm_get?_insert, if_neg hij]
      rw [ents_cons, ents_cons, tm_get?_insert, if_pos rfl, hw, flUpd_cons, if_pos rfl, hrest]
    · have hkL : k ∈ L := by
        rcases List.mem_cons.mp hk with h | h
        · exact absurd h.symm hjk
        · exact h
      rw [ents_cons, ents_cons, tm_get?_insert, if_neg (Ne.symm hjk)]
      cases hj : tab.get? j with
      | none => exact ih hnd.2 hkL hsome
      | some w =>
        simp only []
        rw [flUpd_cons, if_neg hjk, ih hnd.2 hkL hsome]

/-- Inserting an absent key leaves every other entry as it was. -/
theorem ents_insert_absent (tab : Std.TreeMap String α) (k : String) (v : α) (L : List String)
    (hk : k ∉ L) : ents (tab.insert k v) L = ents tab L := by
  apply ents_congr
  intro i hi
  have hki : k ≠ i := fun h => hk (h ▸ hi)
  rw [tm_get?_insert, if_neg hki]

theorem ents_keys_ne (tab : Std.TreeMap String α) (k : String) (L : List String) (hk : k ∉ L) :
    ∀ p ∈ ents tab L, p.1 ≠ k := by
  intro p hp hpk
  unfold ents at hp
  obtain ⟨j, hjL, hj⟩ := List.mem_filterMap.mp hp
  rcases htj : tab.get? j with _ | w
  · rw [htj] at hj; simp at hj
  · rw [htj] at hj
    simp only [Option.map_some, Option.some.injEq] at hj
    rw [← hj] at hpk
    exact hk (hpk ▸ hjL)

/-! ## Well-formedness and the refinement to association lists -/

theorem nodup_rev {l : List String} (h : l.Nodup) : l.reverse.Nodup := by
  unfold List.Nodup at *
  rw [List.pairwise_reverse]
  exact h.imp (fun h => Ne.symm h)

theorem WF_empty : (OMap.empty : OMap α).WF := by
  refine ⟨List.nodup_nil, fun k => ?_⟩
  simp [OMap.empty, Std.TreeMap.contains_emptyc]

theorem toList_empty : (OMap.empty : OMap α).toList = [] := rfl

theorem WF_upsert (m : OMap α) (hm : m.WF) (k : String) (v : α) : (m.upsert k v).WF := by
  obtain ⟨hnd, hmem⟩ := hm
  unfold OMap.upsert
  by_cases hc : m.tab.contains k = true
  · rw [if_pos hc]
    refine ⟨hnd, fun j => ?_⟩
    simp only []
    rw [hmem j, tm_contains_insert]
    constructor
    · intro h; exact Or.inr h
    · rintro (h | h)
      · subst h; exact hc
      · exact h
  · rw [if_neg hc]
    have hkr : k ∉ m.rev := fun h => hc ((hmem k).mp h)
    refine ⟨List.nodup_cons.mpr ⟨hkr, hnd⟩, fun j => ?_⟩
    simp only []
    rw [List.mem_cons, tm_contains_insert, hmem j]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

/-- Lookup agrees with the association-list lookup on the entries in
insertion order. -/
theorem find?_eq (m : OMap α) (hm : m.WF) (k : String) :
    m.find? k = flLookup m.toList k := by
  rw [toList_eq, flLookup_ents]
  unfold OMap.find?
  by_cases hk : k ∈ m.rev.reverse
  · rw [if_pos hk]
  · rw [if_neg hk]
    have : ¬ (m.tab.contains k = true) := fun h => hk (List.mem_reverse.mpr ((hm.2 k).mpr h))
    cases hg : m.tab.get? k with
    | none => rfl
    | some _ => exact absurd ((tm_contains_iff_isSome _ _).mpr (by rw [hg]; rfl)) this

/-- **Update agrees with the association-list update.** Replacing a
present key keeps its position; a new key goes to the end. -/
theorem toList_upsert (m : OMap α) (hm : m.WF) (k : String) (v : α) :
    (m.upsert k v).toList = flUpd m.toList k v := by
  unfold OMap.upsert
  by_cases hc : m.tab.contains k = true
  · rw [if_pos hc]
    rw [toList_eq, toList_eq]
    exact ents_insert_present m.tab k v _ (nodup_rev hm.1)
        (List.mem_reverse.mpr ((hm.2 k).mpr hc)) ((tm_contains_iff_isSome _ _).mp hc)
  · rw [if_neg hc]
    have hkr : k ∉ m.rev := fun h => hc ((hm.2 k).mp h)
    have hkr' : k ∉ m.rev.reverse := fun h => hkr (List.mem_reverse.mp h)
    rw [toList_eq, toList_eq]
    simp only [List.reverse_cons]
    rw [ents_append, ents_insert_absent m.tab k v _ hkr', ents_cons, tm_get?_insert, if_pos rfl,
        ents_nil, flUpd_of_absent k v _ (ents_keys_ne m.tab k _ hkr')]

end OMap

/-! ## Mapping an association list through a value function -/

theorem flLookup_map {α β : Type} (g : α → β) (k : String) :
    ∀ xs : List (String × α),
      flLookup (xs.map (fun kv => (kv.1, g kv.2))) k = (flLookup xs k).map g := by
  intro xs
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨j, w⟩ := p
    simp only [List.map_cons]
    rw [flLookup_cons, flLookup_cons]
    by_cases h : j = k
    · simp [h]
    · simp [h, ih]

theorem flUpd_map {α β : Type} (g : α → β) (k : String) (v : α) :
    ∀ xs : List (String × α),
      flUpd (xs.map (fun kv => (kv.1, g kv.2))) k (g v) =
        (flUpd xs k v).map (fun kv => (kv.1, g kv.2)) := by
  intro xs
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨j, w⟩ := p
    simp only [List.map_cons]
    rw [flUpd_cons, flUpd_cons]
    by_cases h : j = k
    · simp [h]
    · simp [h, ih]

theorem keys_ne_of_flLookup_none {α : Type} (k : String) :
    ∀ xs : List (String × α), flLookup xs k = none → ∀ p ∈ xs, p.1 ≠ k := by
  intro xs
  induction xs with
  | nil => intro _ p hp; exact absurd hp List.not_mem_nil
  | cons q xs ih =>
    intro h p hp
    obtain ⟨j, w⟩ := q
    rw [flLookup_cons] at h
    by_cases hj : j = k
    · rw [if_pos hj] at h; exact absurd h (by simp)
    · rw [if_neg hj] at h
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact hj
      · exact ih h p hp'

/-! ## The specification: the association-list node operations

These are the definitions `Flatten.lean` had before the node map moved to
persistent maps, kept verbatim as the specification the new operations are
proved against. -/

namespace Spec

def nodeAppendProp (n : List (String × Json)) (prop : String) (v : Json) (dedup : Bool)
    : List (String × Json) :=
  match flLookup n prop with
  | some (.array items) =>
    if dedup && flArrContains items v then n else flUpd n prop (.array (items ++ [v]))
  | some other => flUpd n prop (.array [other, v])
  | none       => n ++ [(prop, .array [v])]

def nodeEnsureProp (n : List (String × Json)) (prop : String) : List (String × Json) :=
  match flLookup n prop with
  | some _ => n
  | none   => n ++ [(prop, .array [])]

def flMergeTypeItems : List Json → List Json → List Json
  | existing, []        => existing
  | existing, hd :: tl  =>
    if flArrContains existing hd then flMergeTypeItems existing tl
    else flMergeTypeItems (existing ++ [hd]) tl

def nodeMergeTypes (n : List (String × Json)) (items : List Json) : List (String × Json) :=
  match flLookup n "@type" with
  | some (.array existing) => flUpd n "@type" (.array (flMergeTypeItems existing items))
  | some other             => flUpd n "@type" (.array (flMergeTypeItems [other] items))
  | none                   => n ++ [("@type", .array (flMergeTypeItems [] items))]

def nodeSetIndex (n : List (String × Json)) (idx : Json) : Option (List (String × Json)) :=
  match flLookup n "@index" with
  | some old => if expandedEqual old idx then some n else none
  | none     => some (n ++ [("@index", idx)])

def nodeHasOnlyId : List (String × Json) → Bool
  | [(k, _)] => k == "@id"
  | _        => false

end Spec

/-! ## `DedupArr`: a canonical-form set decides "already in the array" -/

namespace DedupArr

/-- Every item's canonical form is in `seen`, and nothing else is. -/
def Inv (a : DedupArr) : Prop :=
  ∀ x, a.seen.contains x = true ↔ ∃ it ∈ a.rev, jcsDocument it = x

theorem Inv_empty : Inv DedupArr.empty := by
  intro x
  simp [DedupArr.empty, Std.TreeSet.contains_emptyc]

theorem Inv_pushKeyed (a : DedupArr) (h : a.Inv) (v : Json) :
    (a.pushKeyed (jcsDocument v) v).Inv := by
  intro x
  unfold DedupArr.pushKeyed
  simp only []
  rw [Std.TreeSet.contains_insert]
  constructor
  · intro hx
    have hx' : (compare (jcsDocument v) x == Ordering.eq || a.seen.contains x) = true := hx
    simp only [Bool.or_eq_true, beq_iff_eq, Std.compare_eq_iff_eq] at hx'
    rcases hx' with e | e
    · exact ⟨v, List.mem_cons_self .., e⟩
    · obtain ⟨it, hit, hix⟩ := (h x).mp e
      exact ⟨it, List.mem_cons_of_mem _ hit, hix⟩
  · rintro ⟨it, hit, hix⟩
    show (compare (jcsDocument v) x == Ordering.eq || a.seen.contains x) = true
    simp only [Bool.or_eq_true, beq_iff_eq, Std.compare_eq_iff_eq]
    rcases List.mem_cons.mp hit with rfl | hit'
    · exact Or.inl hix
    · exact Or.inr ((h x).mpr ⟨it, hit', hix⟩)

theorem toList_pushKeyed (a : DedupArr) (key : String) (v : Json) :
    (a.pushKeyed key v).toList = a.toList ++ [v] := by
  simp [DedupArr.pushKeyed, DedupArr.toList]

theorem toList_empty : DedupArr.empty.toList = [] := rfl

/-- The set answers the spec's "already in the array" test. -/
theorem contains_iff (a : DedupArr) (h : a.Inv) (v : Json) :
    a.seen.contains (jcsDocument v) = flArrContains a.toList v := by
  unfold flArrContains
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  constructor
  · intro hc
    obtain ⟨it, hit, hix⟩ := (h _).mp hc
    exact ⟨it, List.mem_reverse.mpr hit, by simp [expandedEqual, hix]⟩
  · rintro ⟨it, hit, hx⟩
    refine (h _).mpr ⟨it, List.mem_reverse.mp hit, ?_⟩
    simpa [expandedEqual] using hx

theorem Inv_pushDedup (a : DedupArr) (h : a.Inv) (v : Json) (dedup : Bool) :
    (a.pushDedup v dedup).Inv := by
  unfold DedupArr.pushDedup
  simp only []
  split
  · exact h
  · exact Inv_pushKeyed a h v

/-- Appending without the duplicate test. -/
theorem toList_pushDedup_false (a : DedupArr) (v : Json) :
    (a.pushDedup v false).toList = a.toList ++ [v] := by
  simp [DedupArr.pushDedup, toList_pushKeyed]

theorem toList_pushDedup_true (a : DedupArr) (h : a.Inv) (v : Json) :
    (a.pushDedup v true).toList =
      if flArrContains a.toList v = true then a.toList else a.toList ++ [v] := by
  unfold DedupArr.pushDedup
  simp only [Bool.true_and, ← contains_iff a h v]
  by_cases hc : a.seen.contains (jcsDocument v) = true
  · simp [hc]
  · simp [hc, toList_pushKeyed]

/-- The `@type` merge of the node map, one item at a time, is the
original `flMergeTypeItems`. -/
theorem foldl_pushDedup (items : List Json) :
    ∀ (a : DedupArr), a.Inv →
      (items.foldl (fun a hd => a.pushDedup hd true) a).Inv ∧
      (items.foldl (fun a hd => a.pushDedup hd true) a).toList =
        Spec.flMergeTypeItems a.toList items := by
  induction items with
  | nil => intro a h; exact ⟨h, rfl⟩
  | cons hd tl ih =>
    intro a h
    simp only [List.foldl_cons]
    have hinv := Inv_pushDedup a h hd true
    obtain ⟨ih1, ih2⟩ := ih (a.pushDedup hd true) hinv
    refine ⟨ih1, ?_⟩
    rw [ih2, toList_pushDedup_true a h, Spec.flMergeTypeItems.eq_2]
    by_cases hc : flArrContains a.toList hd = true
    · simp [hc]
    · simp [hc]

end DedupArr

/-! ## Node-level refinement -/

/-- A value a node can hold without ambiguity: an array entry whose set is
consistent, or a scalar that is not itself an array. -/
def NmVal.Good : NmVal → Prop
  | .one j  => ∀ xs, j ≠ .array xs
  | .many a => a.Inv

/-- Well-formedness of a node. -/
def NodeWF (n : NmNode) : Prop :=
  n.WF ∧ ∀ k v, n.find? k = some v → v.Good

theorem NodeWF_empty : NodeWF (OMap.empty : NmNode) := by
  refine ⟨OMap.WF_empty, fun k v h => ?_⟩
  simp [OMap.find?, OMap.empty] at h

theorem NodeWF_upsert (n : NmNode) (hn : NodeWF n) (k : String) (v : NmVal) (hv : v.Good) :
    NodeWF (n.upsert k v) := by
  refine ⟨OMap.WF_upsert n hn.1 k v, fun k' v' h => ?_⟩
  unfold OMap.find? OMap.upsert at h
  by_cases hc : n.tab.contains k = true
  · rw [if_pos hc] at h
    simp only [] at h
    rw [tm_get?_insert] at h
    by_cases hk : k = k'
    · rw [if_pos hk] at h; cases h; exact hv
    · rw [if_neg hk] at h; exact hn.2 k' v' h
  · rw [if_neg hc] at h
    simp only [] at h
    rw [tm_get?_insert] at h
    by_cases hk : k = k'
    · rw [if_pos hk] at h; cases h; exact hv
    · rw [if_neg hk] at h; exact hn.2 k' v' h

theorem NodeWF_fresh (id : String) : NodeWF (NmNode.fresh id) := by
  unfold NmNode.fresh
  apply NodeWF_upsert _ NodeWF_empty
  intro xs h; cases h

theorem toFields_upsert (n : NmNode) (hn : n.WF) (k : String) (v : NmVal) :
    NmNode.toFields (n.upsert k v) = flUpd n.toFields k v.toJson := by
  unfold NmNode.toFields
  rw [OMap.toList_upsert n hn, flUpd_map]

theorem getJson_eq (n : NmNode) (hn : n.WF) (k : String) :
    n.getJson k = flLookup n.toFields k := by
  unfold NmNode.getJson NmNode.toFields
  rw [flLookup_map, OMap.find?_eq n hn]

theorem toFields_fresh (id : String) :
    (NmNode.fresh id).toFields = [("@id", Json.string id)] := by
  have h := toFields_upsert OMap.empty OMap.WF_empty "@id" (.one (.string id))
  unfold NmNode.fresh
  rw [h]
  rfl

theorem contains_iff_find (n : NmNode) (k : String) :
    n.contains k = true ↔ (n.find? k).isSome = true := tm_contains_iff_isSome _ _

theorem Spec.nodeAppendProp_of_nonarray (n : List (String × Json)) (prop : String) (o v : Json)
    (dedup : Bool) (h : flLookup n prop = some o) (hna : ∀ xs, o ≠ .array xs) :
    Spec.nodeAppendProp n prop v dedup = flUpd n prop (.array [o, v]) := by
  unfold Spec.nodeAppendProp
  rw [h]
  cases o with
  | array xs => exact absurd rfl (hna xs)
  | _ => rfl

theorem Spec.nodeMergeTypes_of_nonarray (n : List (String × Json)) (o : Json) (items : List Json)
    (h : flLookup n "@type" = some o) (hna : ∀ xs, o ≠ .array xs) :
    Spec.nodeMergeTypes n items = flUpd n "@type" (.array (Spec.flMergeTypeItems [o] items)) := by
  unfold Spec.nodeMergeTypes
  rw [h]
  cases o with
  | array xs => exact absurd rfl (hna xs)
  | _ => rfl

/-- `nodeAppendProp` is the original list operation. -/
theorem toFields_nodeAppendProp (n : NmNode) (hn : NodeWF n) (prop : String) (v : Json)
    (dedup : Bool) :
    (nodeAppendProp n prop v dedup).toFields = Spec.nodeAppendProp n.toFields prop v dedup := by
  have hlk := getJson_eq n hn.1 prop
  unfold NmNode.getJson at hlk
  rcases hfind : n.find? prop with _ | val
  · -- absent
    have hlk' : flLookup n.toFields prop = none := by
      rw [← hlk, hfind]; rfl
    unfold nodeAppendProp Spec.nodeAppendProp
    rw [hfind, hlk']
    simp only []
    rw [toFields_upsert n hn.1, flUpd_of_absent prop _ _
        (keys_ne_of_flLookup_none prop _ hlk')]
    simp [NmVal.toJson, DedupArr.toList, DedupArr.empty, DedupArr.push, DedupArr.pushKeyed]
  · cases val with
    | one o =>
      have hgood := hn.2 prop (.one o) hfind
      have hlk' : flLookup n.toFields prop = some o := by
        rw [← hlk, hfind]; rfl
      rw [Spec.nodeAppendProp_of_nonarray _ _ o v dedup hlk' hgood]
      unfold nodeAppendProp
      rw [hfind]
      simp only []
      rw [toFields_upsert n hn.1]
      simp [NmVal.toJson, DedupArr.toList, DedupArr.empty, DedupArr.push, DedupArr.pushKeyed]
    | many a =>
      have hinv : a.Inv := hn.2 prop (.many a) hfind
      have hlk' : flLookup n.toFields prop = some (.array a.toList) := by
        rw [← hlk, hfind]; rfl
      unfold nodeAppendProp Spec.nodeAppendProp
      rw [hfind, hlk']
      simp only []
      have hcont := DedupArr.contains_iff a hinv v
      by_cases hd : (dedup && a.seen.contains (jcsDocument v)) = true
      · have hd' : (dedup && flArrContains a.toList v) = true := by rw [← hcont]; exact hd
        simp only [hd, hd', if_true]
      · have hd' : ¬ (dedup && flArrContains a.toList v) = true := by rw [← hcont]; exact hd
        simp only [hd, hd', Bool.false_eq_true, if_false]
        rw [toFields_upsert n hn.1]
        simp [NmVal.toJson, DedupArr.toList_pushKeyed]

/-- `nodeEnsureProp` is the original list operation. -/
theorem toFields_nodeEnsureProp (n : NmNode) (hn : NodeWF n) (prop : String) :
    (nodeEnsureProp n prop).toFields = Spec.nodeEnsureProp n.toFields prop := by
  have hlk := getJson_eq n hn.1 prop
  unfold NmNode.getJson at hlk
  unfold nodeEnsureProp Spec.nodeEnsureProp
  rcases hfind : n.find? prop with _ | val
  · have hlk' : flLookup n.toFields prop = none := by rw [← hlk, hfind]; rfl
    have hc : ¬ (n.contains prop = true) := by
      intro h
      have := (contains_iff_find n prop).mp h
      rw [hfind] at this
      exact absurd this (by simp)
    rw [hlk', if_neg hc]
    simp only []
    rw [toFields_upsert n hn.1, flUpd_of_absent prop _ _
        (keys_ne_of_flLookup_none prop _ hlk')]
    simp [NmVal.toJson, DedupArr.toList, DedupArr.empty]
  · have hc : n.contains prop = true := (contains_iff_find n prop).mpr (by rw [hfind]; rfl)
    obtain ⟨j, hj⟩ : ∃ j, flLookup n.toFields prop = some j := ⟨_, by rw [← hlk, hfind]; rfl⟩
    rw [hj, if_pos hc]

/-- `nodeMergeTypes` is the original list operation. -/
theorem toFields_nodeMergeTypes (n : NmNode) (hn : NodeWF n) (items : List Json) :
    (nodeMergeTypes n items).toFields = Spec.nodeMergeTypes n.toFields items := by
  have hlk := getJson_eq n hn.1 "@type"
  unfold NmNode.getJson at hlk
  unfold nodeMergeTypes
  rcases hfind : n.find? "@type" with _ | val
  · have hlk' : flLookup n.toFields "@type" = none := by rw [← hlk, hfind]; rfl
    unfold Spec.nodeMergeTypes
    rw [hlk']
    simp only []
    obtain ⟨_, hl⟩ := DedupArr.foldl_pushDedup items DedupArr.empty DedupArr.Inv_empty
    rw [toFields_upsert n hn.1, flUpd_of_absent "@type" _ _
        (keys_ne_of_flLookup_none "@type" _ hlk')]
    simp [NmVal.toJson, hl, DedupArr.toList_empty]
  · cases val with
    | one o =>
      have hgood := hn.2 "@type" (.one o) hfind
      have hlk' : flLookup n.toFields "@type" = some o := by rw [← hlk, hfind]; rfl
      have hinv : (DedupArr.empty.push o).Inv :=
        DedupArr.Inv_pushKeyed _ DedupArr.Inv_empty o
      obtain ⟨_, hl⟩ := DedupArr.foldl_pushDedup items _ hinv
      have hpush : (DedupArr.empty.push o).toList = [o] := by
        simp [DedupArr.push, DedupArr.pushKeyed, DedupArr.toList, DedupArr.empty]
      rw [hpush] at hl
      rw [Spec.nodeMergeTypes_of_nonarray _ o items hlk' hgood]
      simp only []
      rw [toFields_upsert n hn.1]
      simp only [NmVal.toJson]
      rw [hl]
    | many a =>
      have hinv : a.Inv := hn.2 "@type" (.many a) hfind
      have hlk' : flLookup n.toFields "@type" = some (.array a.toList) := by
        rw [← hlk, hfind]; rfl
      obtain ⟨_, hl⟩ := DedupArr.foldl_pushDedup items a hinv
      unfold Spec.nodeMergeTypes
      rw [hlk']
      simp only []
      rw [toFields_upsert n hn.1]
      simp [NmVal.toJson, hl]

/-- `nodeSetIndex` is the original list operation. -/
theorem nodeSetIndex_toFields (n : NmNode) (hn : NodeWF n) (idx : Json) :
    (nodeSetIndex n idx).map NmNode.toFields = Spec.nodeSetIndex n.toFields idx := by
  have hlk := getJson_eq n hn.1 "@index"
  unfold NmNode.getJson at hlk
  unfold nodeSetIndex Spec.nodeSetIndex
  rcases hfind : n.find? "@index" with _ | val
  · have hlk' : flLookup n.toFields "@index" = none := by rw [← hlk, hfind]; rfl
    rw [hlk']
    simp only [Option.map_some]
    rw [toFields_upsert n hn.1, flUpd_of_absent "@index" _ _
        (keys_ne_of_flLookup_none "@index" _ hlk')]
    rfl
  · have hlk' : flLookup n.toFields "@index" = some val.toJson := by
      rw [← hlk, hfind]; rfl
    rw [hlk']
    simp only []
    by_cases h : expandedEqual val.toJson idx = true
    · simp [h]
    · simp [h]

theorem ents_length (tab : Std.TreeMap String α) :
    ∀ (L : List String), (∀ j ∈ L, tab.contains j = true) → (OMap.ents tab L).length = L.length := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons j L ih =>
    intro h
    have hj : (tab.get? j).isSome = true := (tm_contains_iff_isSome _ _).mp (h j (List.mem_cons_self ..))
    rw [OMap.ents_cons]
    rcases hg : tab.get? j with _ | w
    · rw [hg] at hj; exact absurd hj (by simp)
    · simp only [List.length_cons]
      rw [ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]

/-- The test for "only an `@id`" is the original pattern match. -/
theorem nodeHasOnlyId_eq (n : NmNode) (hn : n.WF) :
    nodeHasOnlyId n = Spec.nodeHasOnlyId n.toFields := by
  have hall : ∀ j ∈ n.rev.reverse, n.tab.contains j = true :=
    fun j hj => (hn.2 j).mp (List.mem_reverse.mp hj)
  have hlen : n.toFields.length = n.rev.length := by
    unfold NmNode.toFields
    rw [List.length_map, OMap.toList_eq, ents_length n.tab _ hall, List.length_reverse]
  unfold nodeHasOnlyId
  rcases hr : n.rev with _ | ⟨k, rest⟩
  · have : n.toFields.length = 0 := by rw [hlen, hr]; rfl
    rcases hf : n.toFields with _ | ⟨x, xs⟩
    · rfl
    · rw [hf] at this; simp at this
  · rcases rest with _ | ⟨k2, rest2⟩
    · simp only []
      have hk : n.tab.contains k = true := (hn.2 k).mp (by rw [hr]; exact List.mem_cons_self ..)
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((tm_contains_iff_isSome _ _).mp hk)
      have : n.toFields = [(k, w.toJson)] := by
        unfold NmNode.toFields
        rw [OMap.toList_eq, hr]
        show (OMap.ents n.tab [k]).map _ = _
        rw [OMap.ents_cons, hw]
        rfl
      rw [this]; rfl
    · have : n.toFields.length = rest2.length + 2 := by rw [hlen, hr]; rfl
      rcases hf : n.toFields with _ | ⟨x, _ | ⟨y, xs⟩⟩
      · rw [hf] at this; simp at this
      · rw [hf] at this; simp at this
      · rfl

/-! ## Appending the same value twice with the duplicate test is appending it once -/

theorem DedupArr.has_after_pushDedup (a : DedupArr) (v : Json) (dedup : Bool) (h : dedup = true) :
    (a.pushDedup v dedup).seen.contains (jcsDocument v) = true := by
  unfold DedupArr.pushDedup
  simp only [h, Bool.true_and]
  by_cases hc : a.seen.contains (jcsDocument v) = true
  · simp [hc]
  · simp only [hc, if_false, DedupArr.pushKeyed, Bool.false_eq_true]
    rw [Std.TreeSet.contains_insert]
    simp

theorem DedupArr.pushDedup_twice (a : DedupArr) (h : a.Inv) (v : Json) :
    ((a.pushDedup v true).pushDedup v true).toList = (a.pushDedup v true).toList := by
  have hinv := DedupArr.Inv_pushDedup a h v true
  rw [DedupArr.toList_pushDedup_true _ hinv, ← DedupArr.contains_iff _ hinv v,
      DedupArr.has_after_pushDedup a v true rfl]
  rfl

/-! ## Graph-level lookup laws -/

theorem stGraph_stPutGraph_same (st : NmState) (g : String) (gr : NmGraph) :
    stGraph (stPutGraph st g gr) g = gr := by
  show ((st.graphs.insert g gr).get? g).getD _ = gr
  rw [tm_get?_insert, if_pos rfl]
  rfl

theorem stGraph_stPutGraph_other (st : NmState) (g g' : String) (gr : NmGraph) (h : g ≠ g') :
    stGraph (stPutGraph st g gr) g' = stGraph st g' := by
  show ((st.graphs.insert g gr).get? g').getD _ = (st.graphs.get? g').getD _
  rw [tm_get?_insert, if_neg h]

/-- After `stNodeUpdate`, the node holds the updated value. -/
theorem stNodeUpdate_get_same (st : NmState) (g id : String) (f : NmNode → NmNode) :
    (stGraph (stNodeUpdate st g id f) g).get? id =
      some (f (((stGraph st g).get? id).getD (NmNode.fresh id))) := by
  unfold stNodeUpdate
  rcases hg : (stGraph st g).get? id with _ | n
  · simp only [hg]
    rw [stGraph_stPutGraph_same, tm_get?_insert, if_pos rfl]
    rfl
  · simp only [hg]
    rw [stGraph_stPutGraph_same, tm_get?_insert, if_pos rfl]
    rfl

/-- Other nodes of the same graph are unchanged. -/
theorem stNodeUpdate_get_other_node (st : NmState) (g id id' : String) (f : NmNode → NmNode)
    (h : id ≠ id') : (stGraph (stNodeUpdate st g id f) g).get? id' = (stGraph st g).get? id' := by
  unfold stNodeUpdate
  rcases hg : (stGraph st g).get? id with _ | n
  · simp only [hg]
    rw [stGraph_stPutGraph_same, tm_get?_insert, if_neg h]
  · simp only [hg]
    rw [stGraph_stPutGraph_same, tm_get?_insert, if_neg h]

/-- Other graphs are unchanged. -/
theorem stNodeUpdate_other_graph (st : NmState) (g g' id : String) (f : NmNode → NmNode)
    (h : g ≠ g') : stGraph (stNodeUpdate st g id f) g' = stGraph st g' := by
  unfold stNodeUpdate
  rcases hg : (stGraph st g).get? id with _ | n
  · simp only [hg]
    rw [stGraph_stPutGraph_other _ _ _ _ h]
  · simp only [hg]
    rw [stGraph_stPutGraph_other _ _ _ _ h]

/-- `stEnsureNode` makes the node exist and leaves an existing node alone. -/
theorem stEnsureNode_get (st : NmState) (g id : String) :
    (stGraph (stEnsureNode st g id) g).get? id =
      some (((stGraph st g).get? id).getD (NmNode.fresh id)) := by
  unfold stEnsureNode
  by_cases hc : (stGraph st g).contains id = true
  · rw [if_pos hc]
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ((tm_contains_iff_isSome _ _).mp hc)
    rw [hn]; rfl
  · rw [if_neg hc]
    have hn : (stGraph st g).get? id = none := by
      rcases hg : (stGraph st g).get? id with _ | n
      · rfl
      · exact absurd ((tm_contains_iff_isSome _ _).mpr (by rw [hg]; rfl)) hc
    rw [stGraph_stPutGraph_same, tm_get?_insert, hn]; simp

theorem stEnsureNode_other_node (st : NmState) (g id id' : String) (h : id ≠ id') :
    (stGraph (stEnsureNode st g id) g).get? id' = (stGraph st g).get? id' := by
  unfold stEnsureNode
  by_cases hc : (stGraph st g).contains id = true
  · rw [if_pos hc]
  · rw [if_neg hc, stGraph_stPutGraph_same, tm_get?_insert]; simp [h]

/-! ## The blank node issuer -/

theorem issueKeyed_new (st : NmState) (old : String) (h : st.idmap.get? old = none) :
    issueKeyed st old =
      ("_:b" ++ toString st.ctr,
       { st with idmap := st.idmap.insert old ("_:b" ++ toString st.ctr), ctr := st.ctr + 1 }) := by
  unfold issueKeyed
  rw [h]

theorem issueKeyed_known (st : NmState) (old nid : String) (h : st.idmap.get? old = some nid) :
    issueKeyed st old = (nid, st) := by
  unfold issueKeyed
  rw [h]

/-- Relabelling the same blank node identifier twice gives the same label
and does not advance the counter (API §7.2: the issuer's map). -/
theorem issueKeyed_repeat (st : NmState) (old : String) :
    (issueKeyed (issueKeyed st old).2 old).1 = (issueKeyed st old).1 ∧
    (issueKeyed (issueKeyed st old).2 old).2.ctr = (issueKeyed st old).2.ctr := by
  rcases h : st.idmap.get? old with _ | nid
  · rw [issueKeyed_new st old h]
    have h2 : ({ st with idmap := st.idmap.insert old ("_:b" ++ toString st.ctr),
                         ctr := st.ctr + 1 } : NmState).idmap.get? old
              = some ("_:b" ++ toString st.ctr) := by
      simp
    simp only []
    rw [issueKeyed_known _ old _ h2]
    exact ⟨rfl, rfl⟩
  · rw [issueKeyed_known st old nid h]
    simp only []
    rw [issueKeyed_known st old nid h]
    exact ⟨rfl, rfl⟩

/-- A label the issuer has not used yet gets the next number. -/
theorem issueKeyed_fresh_label (st : NmState) (old : String) (h : st.idmap.get? old = none) :
    (issueKeyed st old).1 = "_:b" ++ toString st.ctr ∧ (issueKeyed st old).2.ctr = st.ctr + 1 := by
  rw [issueKeyed_new st old h]
  exact ⟨rfl, rfl⟩

/-! ## Axioms -/

#print axioms strLt_iff_compare_lt
#print axioms OMap.find?_eq
#print axioms OMap.toList_upsert
#print axioms OMap.WF_upsert
#print axioms DedupArr.contains_iff
#print axioms DedupArr.foldl_pushDedup
#print axioms toFields_nodeAppendProp
#print axioms toFields_nodeEnsureProp
#print axioms toFields_nodeMergeTypes
#print axioms nodeSetIndex_toFields
#print axioms nodeHasOnlyId_eq
#print axioms DedupArr.pushDedup_twice
#print axioms stNodeUpdate_get_same
#print axioms stNodeUpdate_get_other_node
#print axioms stNodeUpdate_other_graph
#print axioms stEnsureNode_get
#print axioms issueKeyed_repeat

end L4Factoidal.JSONLD
