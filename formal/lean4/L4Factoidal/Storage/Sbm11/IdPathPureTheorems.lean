/-
L4Factoidal.Storage.Sbm11.IdPathPureTheorems — the pure helpers of the
property path evaluator on ids (`IdPath`: `sortedDistinct`, `firsts`,
`seconds`, `adjOf`, `compose`, `dedupPairs`, `reachPlus`) against list
models (https://github.com/danbri/factoidal/issues/776; part of lemma L4n of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

* `sortedDistinct_spec`: the values of the input, each once, in increasing
  order; so the candidates a path step passes to a scan are in order
  (`Sip.Sorted`, `sortedDistinct_sorted`) and hold no value twice.
* `firsts_mem`, `seconds_mem`: the subjects and the objects of a relation.
* `adjOf_getD`: the objects the adjacency map holds for `x` are
  `IdPath.succs` of the relation, in order.
* `compose_toList`: the sequence of two relations is, list for list, per
  pair `(a, m)` of the first in order, `(a, c)` per successor `c` of `m` in
  the second (`compose_eq_model`: the list `idEvalPath` builds for a
  sequence).
* `dedupPairs_spec`: each pair of the input once.
* `reachPlus_eq`: the hash-map worklist answers the list model
  `IdPath.reachModel` (`IdPathClosureTheorems`), list for list, over the
  adjacency map of the relation.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdPathClosureTheorems
import L4Factoidal.Storage.Sbm11.SipTheorems

namespace L4Factoidal.Storage.Sbm11.IdPath

/-! ## `dedupSorted` and `sortedDistinct` -/

theorem back?_toList (out : Array UInt64) : out.back? = out.toList.getLast? := by
  rw [Array.back?_eq_getElem?, List.getLast?_eq_getElem?]
  simp

theorem dedupStep_spec (out : Array UInt64) (x : UInt64) (hp : out.toList.Pairwise (· < ·))
    (hle : ∀ y ∈ out.toList, y ≤ x) :
    (dedupStep out x).toList.Pairwise (· < ·) ∧ (∀ z, z ∈ (dedupStep out x).toList ↔ z ∈ out.toList ∨ z = x) ∧
      ∀ y ∈ (dedupStep out x).toList, y ≤ x := by
  unfold dedupStep
  rw [back?_toList]
  cases hl : out.toList.getLast? with
  | none =>
    have he : out.toList = [] := List.getLast?_eq_none_iff.mp hl
    simp only [Array.toList_push, he, List.nil_append]
    refine ⟨List.pairwise_singleton _ _, fun z => by simp, fun y hy => ?_⟩
    simp at hy; rw [hy]; exact UInt64.le_refl _
  | some y =>
    have hy : y ∈ out.toList := List.mem_of_getLast? hl
    by_cases hyx : (y != x) = true
    · simp only [hyx, if_true, Array.toList_push]
      have hne : y ≠ x := by simpa using hyx
      refine ⟨?_, fun z => by simp, ?_⟩
      · rw [List.pairwise_append]
        refine ⟨hp, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        simp at hb; subst hb
        have hyx' : y < b := UInt64.lt_of_le_of_ne (hle y hy) hne
        obtain ⟨l', hl'⟩ : ∃ l', out.toList = l' ++ [y] := List.getLast?_eq_some_iff.mp hl
        rw [hl'] at hp ha
        rcases List.mem_append.mp ha with ha | ha
        · exact UInt64.lt_trans ((List.pairwise_append.mp hp).2.2 a ha y (by simp)) hyx'
        · simp at ha; subst ha; exact hyx'
      · intro z hz
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | hz
        · exact hle z hz
        · rw [hz]; exact UInt64.le_refl _
    · simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hyx
      simp only [bne_self_eq_false, hyx, Bool.false_eq_true, if_false]
      subst hyx
      exact ⟨hp, fun z => ⟨Or.inl, fun h => h.elim id (fun e => e ▸ hy)⟩, hle⟩

theorem dedupSorted_go (l : List UInt64) (hl : l.Pairwise (· ≤ ·)) :
    ∀ (out : Array UInt64), out.toList.Pairwise (· < ·) → (∀ y ∈ out.toList, ∀ x ∈ l, y ≤ x) →
      (l.foldl dedupStep out).toList.Pairwise (· < ·) ∧
        ∀ z, z ∈ (l.foldl dedupStep out).toList ↔ z ∈ out.toList ∨ z ∈ l := by
  induction l with
  | nil => intro out hp _; exact ⟨hp, fun z => by simp⟩
  | cons x xs ih =>
    intro out hp hle
    have ⟨hx, hxs⟩ := List.pairwise_cons.mp hl
    obtain ⟨h1, h2, h3⟩ := dedupStep_spec out x hp (fun y hy => hle y hy x (by simp))
    obtain ⟨g1, g2⟩ := ih hxs (dedupStep out x) h1 (by
      intro y hy z hz
      exact UInt64.le_trans (h3 y hy) (hx z hz))
    refine ⟨g1, fun z => ?_⟩
    rw [List.foldl_cons, g2, h2]
    simp only [List.mem_cons, or_assoc]

theorem dedupSorted_spec (xs : Array UInt64) (h : xs.toList.Pairwise (· ≤ ·)) :
    (dedupSorted xs).toList.Pairwise (· < ·) ∧ ∀ z, z ∈ (dedupSorted xs).toList ↔ z ∈ xs.toList := by
  unfold dedupSorted
  rw [← Array.foldl_toList]
  obtain ⟨h1, h2⟩ := dedupSorted_go xs.toList h (Array.mkEmpty xs.size) (by simp) (by simp)
  exact ⟨h1, fun z => by rw [h2]; simp⟩

/-- **`sortedDistinct`**: the values of the input, each once, increasing. -/
theorem sortedDistinct_spec (xs : Array UInt64) :
    (sortedDistinct xs).toList.Pairwise (· < ·) ∧ ∀ z, z ∈ (sortedDistinct xs).toList ↔ z ∈ xs.toList := by
  unfold sortedDistinct
  have hs : (xs.mergeSort (fun a b => decide (a ≤ b))).toList.Pairwise (· ≤ ·) := by
    rw [Array.toList_mergeSort]
    have := List.pairwise_mergeSort (le := fun a b : UInt64 => decide (a ≤ b))
      (fun a b c h1 h2 => by simp at *; exact UInt64.le_trans h1 h2)
      (fun a b => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        rcases UInt64.le_total a b with h | h
        · exact Or.inl h
        · exact Or.inr h) xs.toList
    exact this.imp (fun h => by simpa using h)
  obtain ⟨h1, h2⟩ := dedupSorted_spec _ hs
  refine ⟨h1, fun z => ?_⟩
  rw [h2, Array.toList_mergeSort]
  exact (List.mergeSort_perm _ _).mem_iff

theorem sortedDistinct_nodup (xs : Array UInt64) : (sortedDistinct xs).toList.Nodup :=
  (sortedDistinct_spec xs).1.imp (fun h => UInt64.ne_of_lt h)

theorem sorted_of_pairwise (c : Array UInt64) (h : c.toList.Pairwise (· < ·)) : Sip.Sorted c := by
  intro i j hij hj
  rw [getElem!_pos c i (by omega), getElem!_pos c j hj]
  rcases Nat.eq_or_lt_of_le hij with e | e
  · subst e; exact UInt64.le_refl _
  · have := List.pairwise_iff_getElem.mp h i j (by simp; omega) (by simp; omega) e
    simpa using UInt64.le_of_lt this

theorem sortedDistinct_sorted (xs : Array UInt64) : Sip.Sorted (sortedDistinct xs) :=
  sorted_of_pairwise _ (sortedDistinct_spec xs).1

theorem firsts_mem (r : Pairs) (x : UInt64) : x ∈ (firsts r).toList ↔ ∃ p ∈ r.toList, p.1 = x := by
  unfold firsts
  rw [(sortedDistinct_spec _).2]
  simp

theorem seconds_mem (r : Pairs) (x : UInt64) : x ∈ (seconds r).toList ↔ ∃ p ∈ r.toList, p.2 = x := by
  unfold seconds
  rw [(sortedDistinct_spec _).2]
  simp

/-! ## `adjOf` and `compose` -/

theorem adjOf_go (l : List (UInt64 × UInt64)) :
    ∀ (idx : Std.HashMap UInt64 (Array UInt64)) (x : UInt64),
      ((l.foldl adjStep idx).getD x #[]).toList = (idx.getD x #[]).toList ++ succs l x := by
  induction l with
  | nil => intro idx x; simp [succs]
  | cons p ps ih =>
    intro idx x
    rw [List.foldl_cons, ih]
    unfold adjStep
    rw [Std.HashMap.getD_alter]
    by_cases e : p.1 = x
    · subst e
      have hc : succs (p :: ps) p.1 = p.2 :: succs ps p.1 := by simp [succs]
      rw [hc]
      cases h : idx[p.1]? with
      | none =>
        have : idx.getD p.1 #[] = #[] := by rw [Std.HashMap.getD_eq_getD_getElem?, h]; rfl
        simp [this]
      | some xs =>
        have : idx.getD p.1 #[] = xs := by rw [Std.HashMap.getD_eq_getD_getElem?, h]; rfl
        simp [this]
    · have hb : (p.1 == x) = false := by simpa using e
      have hc : succs (p :: ps) x = succs ps x := by simp [succs, e]
      simp [hb, hc]

/-- The objects `adjOf` holds for `x`: the successors of `x`, in order. -/
theorem adjOf_getD (r : Pairs) (x : UInt64) : ((adjOf r).getD x #[]).toList = succs r.toList x := by
  unfold adjOf
  rw [← Array.foldl_toList, adjOf_go]
  simp

theorem push_fold (a : UInt64) (cs : List UInt64) :
    ∀ (out : Pairs), (cs.foldl (fun out c => out.push (a, c)) out).toList = out.toList ++ cs.map (fun c => (a, c)) := by
  induction cs with
  | nil => intro out; simp
  | cons c cs ih => intro out; rw [List.foldl_cons, ih]; simp

/-- **`compose`**, list for list. -/
theorem compose_toList (r1 r2 : Pairs) :
    (compose r1 r2).toList = r1.toList.flatMap (fun p => (succs r2.toList p.2).map (fun c => (p.1, c))) := by
  unfold compose
  simp only []
  rw [← Array.foldl_toList]
  suffices ∀ (l : List (UInt64 × UInt64)) (out : Pairs),
      (l.foldl (fun out p => ((adjOf r2).getD p.2 #[]).foldl (fun out c => out.push (p.1, c)) out) out).toList =
        out.toList ++ l.flatMap (fun p => (succs r2.toList p.2).map (fun c => (p.1, c))) by
    rw [this]; simp
  intro l
  induction l with
  | nil => intro out; simp
  | cons p ps ih =>
    intro out
    rw [List.foldl_cons, ih, ← Array.foldl_toList, push_fold, adjOf_getD]
    simp

/-- The sequence `idEvalPath` builds is `compose`'s list. -/
theorem compose_eq_model (r1 r2 : List (UInt64 × UInt64)) :
    (r1.flatMap fun a => r2.filterMap fun b => if a.2 == b.1 then some (a.1, b.2) else none) =
      r1.flatMap (fun p => (succs r2 p.2).map (fun c => (p.1, c))) := by
  congr 1
  funext a
  unfold succs
  rw [List.map_filterMap]
  congr 1
  funext b
  by_cases h : a.2 = b.1
  · have h1 : (a.2 == b.1) = true := by rw [h]; exact beq_self_eq_true _
    have h2 : (b.1 == a.2) = true := by rw [h]; exact beq_self_eq_true _
    rw [if_pos h1, if_pos h2]; rfl
  · have h1 : (a.2 == b.1) = false := by simpa using h
    have h2 : (b.1 == a.2) = false := beq_eq_false_iff_ne.mpr (fun e => h e.symm)
    rw [if_neg (by simp [h1]), if_neg (by simp [h2])]; rfl

/-! ## `dedupPairs` -/

theorem dedupPairs_go (l : List (UInt64 × UInt64)) :
    ∀ (s : Std.HashSet (UInt64 × UInt64) × Pairs), s.2.toList.Nodup → (∀ x, s.1.contains x = true ↔ x ∈ s.2.toList) →
      (l.foldl dedupPairStep s).2.toList.Nodup ∧
        ∀ x, x ∈ (l.foldl dedupPairStep s).2.toList ↔ x ∈ s.2.toList ∨ x ∈ l := by
  induction l with
  | nil => intro s hn _; exact ⟨hn, fun x => by simp⟩
  | cons y ys ih =>
    intro s hn hc
    rw [List.foldl_cons]
    have es : dedupPairStep s y = if s.1.contains y then s else (s.1.insert y, s.2.push y) := rfl
    rw [es]
    by_cases hy : s.1.contains y = true
    · rw [if_pos hy]
      obtain ⟨h1, h2⟩ := ih s hn hc
      refine ⟨h1, fun x => ?_⟩
      rw [h2]
      have := (hc y).mp hy
      simp only [List.mem_cons]
      constructor
      · rintro (h | h); exact Or.inl h; exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · subst h; exact Or.inl this
        · exact Or.inr h
    · rw [if_neg hy]
      have hy' : y ∉ s.2.toList := fun h => hy ((hc y).mpr h)
      obtain ⟨h1, h2⟩ := ih (s.1.insert y, s.2.push y)
        (by simp only [Array.toList_push]; exact List.nodup_append.mpr ⟨hn, by simp, by
          intro a ha b hb; simp at hb; subst hb; intro e; subst e; exact hy' ha⟩)
        (by
          intro x
          simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, Array.toList_push,
            List.mem_append, List.mem_singleton]
          rw [hc x]
          constructor
          · rintro (h | h); exact Or.inr h.symm; exact Or.inl h
          · rintro (h | h); exact Or.inr h; exact Or.inl h.symm)
      refine ⟨h1, fun x => ?_⟩
      rw [h2]
      simp only [Array.toList_push, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc]

/-- **`dedupPairs`**: each pair of the input once. -/
theorem dedupPairs_spec (r : Pairs) :
    (dedupPairs r).toList.Nodup ∧ ∀ x, x ∈ (dedupPairs r).toList ↔ x ∈ r.toList := by
  unfold dedupPairs
  rw [← Array.foldl_toList]
  obtain ⟨h1, h2⟩ := dedupPairs_go r.toList ({}, Array.mkEmpty r.size) (by simp) (by
    intro x; simp)
  exact ⟨h1, fun x => by rw [h2]; simp⟩

/-! ## `reachPlus` against `reachModel` -/

theorem visit_append (ys out work : List UInt64) :
    visit out work ys = ((visit out [] ys).1, work ++ (visit out [] ys).2) := by
  induction ys generalizing out work with
  | nil => simp [visit]
  | cons y ys ih =>
    simp only [visit]
    split
    · exact ih out work
    · rw [ih (out ++ [y]) (work ++ [y]), ih (out ++ [y]) ([] ++ [y])]
      simp

theorem visitStep_fold (ys : List UInt64) :
    ∀ (seen : Std.HashSet UInt64) (out work : Array UInt64), (∀ y, seen.contains y = true ↔ y ∈ out.toList) →
      let s := ys.foldl visitStep (seen, out, work)
      s.2.1.toList = (visit out.toList [] ys).1 ∧ s.2.2.toList = work.toList ++ (visit out.toList [] ys).2 ∧
        ∀ y, s.1.contains y = true ↔ y ∈ s.2.1.toList := by
  induction ys with
  | nil => intro seen out work h; simp [visit, h]
  | cons y ys ih =>
    intro seen out work h
    simp only [List.foldl_cons]
    have es : visitStep (seen, out, work) y =
        if seen.contains y then (seen, out, work) else (seen.insert y, out.push y, work.push y) := rfl
    rw [es]
    by_cases hy : seen.contains y = true
    · rw [if_pos hy]
      have hm : y ∈ out.toList := (h y).mp hy
      have := ih seen out work h
      simp only [visit, if_pos hm]
      exact this
    · rw [if_neg hy]
      have hm : y ∉ out.toList := fun e => hy ((h y).mpr e)
      have h' : ∀ z, (seen.insert y).contains z = true ↔ z ∈ (out.push y).toList := by
        intro z
        simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, Array.toList_push,
          List.mem_append, List.mem_singleton]
        rw [h z]
        constructor
        · rintro (e | e); exact Or.inr e.symm; exact Or.inl e
        · rintro (e | e); exact Or.inr e; exact Or.inl e.symm
      obtain ⟨g1, g2, g3⟩ := ih (seen.insert y) (out.push y) (work.push y) h'
      simp only [visit, if_neg hm]
      rw [visit_append ys (out.toList ++ [y]) ([] ++ [y])]
      simp only [Array.toList_push] at g1 g2
      refine ⟨g1, ?_, g3⟩
      rw [g2]
      simp

theorem reachGo_eq (E : Pairs) :
    ∀ (fuel : Nat) (seen : Std.HashSet UInt64) (out work : Array UInt64) (i : Nat),
      (∀ y, seen.contains y = true ↔ y ∈ out.toList) →
      (reachGo (adjOf E) fuel seen out work i).map Array.toList =
        bfsGo E.toList fuel out.toList (work.toList.drop i) := by
  intro fuel
  induction fuel with
  | zero =>
    intro seen out work i _
    simp only [reachGo, bfsGo, List.isEmpty_iff, List.drop_eq_nil_iff, Array.length_toList]
    by_cases h : i ≥ work.size
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h]; rfl
  | succ n ih =>
    intro seen out work i h
    simp only [reachGo]
    by_cases hi : i ≥ work.size
    · rw [if_pos hi]
      have : work.toList.drop i = [] := List.drop_eq_nil_iff.mpr (by simpa using hi)
      rw [this]; rfl
    · rw [if_neg hi]
      have hlt : i < work.toList.length := by simp; omega
      have hd : work.toList.drop i = work[i]! :: work.toList.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons hlt, getElem!_pos work i (by omega)]
        simp
      rw [hd]
      simp only [bfsGo]
      rw [← Array.foldl_toList]
      obtain ⟨g1, g2, g3⟩ := visitStep_fold ((adjOf E).getD work[i]! #[]).toList seen out work h
      rw [ih _ _ _ _ g3, g1, g2, adjOf_getD, visit_append _ _ (work.toList.drop (i + 1))]
      congr 1
      rw [List.drop_append_of_le_length (by omega)]

/-- **The hash-map worklist answers the list model.** -/
theorem reachPlus_eq (E : Pairs) (a : UInt64) (fuel : Nat) :
    (reachPlus (adjOf E) a fuel).map Array.toList = reachModel E.toList a fuel := by
  unfold reachPlus reachModel
  rw [reachGo_eq E fuel {} #[] #[a] 0 (by intro y; simp)]
  rfl

end L4Factoidal.Storage.Sbm11.IdPath

#print axioms L4Factoidal.Storage.Sbm11.IdPath.sortedDistinct_spec
#print axioms L4Factoidal.Storage.Sbm11.IdPath.compose_toList
#print axioms L4Factoidal.Storage.Sbm11.IdPath.dedupPairs_spec
#print axioms L4Factoidal.Storage.Sbm11.IdPath.reachPlus_eq
