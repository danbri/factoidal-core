/-
L4Factoidal.SPARQL.GroupFastTheorems — the hash grouping `groupSolutionsFast`
returns the same list of groups as the specification `groupSolutions`
(SPARQL 1.1 §18.5.1, `Group(exprlist, Ω)`).

The proof is about the `GroupAcc` implementation that the evaluator runs
(`groupWhere` calls `groupSolutionsFast`). It keeps an invariant between an
accumulator and the list of groups that `addToGroups` has built after the
same rows:

  * `acc.groups` is that list (rows of each group reversed once);
  * for every key bucket `b`, `acc.index` maps `b` to the positions, in
    increasing order, of exactly the groups whose key bucket is `b`.

`keysEqual` implies equal key buckets (`keysEqual_keyBucket`), so filtering
the positions of the row's bucket by `keysEqual` gives the same positions as
filtering all positions. The proof does not use transitivity of `keysEqual`:
a row is added to every group whose key is `keysEqual` to the row's key.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.SPARQL.GroupFast

open L4Factoidal.SPARQL

/-- The group that a record stands for. -/
def recGroup (g : GroupRec) : SolutionGroup := ⟨g.key, g.solsRev.reverse⟩

theorem GroupAcc.groups_eq (acc : GroupAcc) :
    acc.groups = acc.recs.toList.map recGroup := rfl

/-- The positions of the records whose key bucket is `b`, in increasing order. -/
def bucketIds (recs : Array GroupRec) (b : List (Nat × String)) : List Nat :=
  (List.range recs.size).filter (fun i => keyBucket (recs[i]!).key == b)

/-- The invariant between an accumulator and the reference groups. -/
structure Inv (acc : GroupAcc) (ref : List SolutionGroup) : Prop where
  groups : acc.recs.toList.map recGroup = ref
  index  : ∀ b, (acc.index.getD b #[]).toList = bucketIds acc.recs b

theorem inv_empty : Inv ({} : GroupAcc) [] where
  groups := rfl
  index := by
    intro b
    simp [bucketIds, Std.HashMap.getD_empty]

/-- Folding `modify` over a duplicate-free list of positions changes exactly
those positions. -/
theorem foldl_modify_getElem (f : GroupRec → GroupRec) :
    ∀ (l : List Nat) (rs : Array GroupRec), l.Nodup →
      ∃ hs : (l.foldl (fun rs i => rs.modify i f) rs).size = rs.size,
        ∀ j (hj : j < rs.size),
          (l.foldl (fun rs i => rs.modify i f) rs)[j]'(hs ▸ hj) =
            if j ∈ l then f rs[j] else rs[j]
  | [], rs, _ => ⟨rfl, by intro j hj; simp⟩
  | i :: t, rs, nd => by
      rw [List.nodup_cons] at nd
      obtain ⟨hs, ih⟩ := foldl_modify_getElem f t (rs.modify i f) nd.2
      have hsz : (rs.modify i f).size = rs.size := Array.size_modify ..
      refine ⟨by simp only [List.foldl_cons]; rw [hs, hsz], ?_⟩
      intro j hj
      have hj' : j < (rs.modify i f).size := by rw [hsz]; exact hj
      simp only [List.foldl_cons]
      rw [ih j hj']
      simp only [Array.getElem_modify, List.mem_cons]
      by_cases hji : j = i
      · subst hji
        simp [nd.1]
      · by_cases hjt : j ∈ t
        · simp [hjt, Ne.symm hji, hji]
        · simp [hjt, Ne.symm hji, hji]

theorem getElem!_of_lt (recs : Array GroupRec) (i : Nat) (h : i < recs.size) :
    recs[i]! = recs[i] := by
  simp [getElem!_pos recs i h]

/-- The positions of the row's bucket that match the row's key are all the
positions that match it. -/
theorem bucket_hits (recs : Array GroupRec) (key : List EvalResult) :
    (bucketIds recs (keyBucket key)).filter (fun i => keysEqual key (recs[i]!).key) =
      (List.range recs.size).filter (fun i => keysEqual key (recs[i]!).key) := by
  unfold bucketIds
  rw [List.filter_filter]
  apply List.filter_congr
  intro i _
  by_cases h : keysEqual key (recs[i]!).key = true
  · simp [h, keysEqual_keyBucket h]
  · simp [h]

theorem range_filter_eq_nil_iff (recs : Array GroupRec) (p : GroupRec → Bool) :
    (List.range recs.size).filter (fun i => p (recs[i]!)) = [] ↔
      recs.toList.any p = false := by
  rw [List.filter_eq_nil_iff]
  constructor
  · intro h
    rw [List.any_eq_false]
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    have hi' : i < recs.size := by simpa using hi
    have := h i (List.mem_range.mpr hi')
    rw [getElem!_of_lt recs i hi'] at this
    simpa using this
  · intro h i hi
    rw [List.any_eq_false] at h
    have hi' : i < recs.size := List.mem_range.mp hi
    rw [getElem!_of_lt recs i hi']
    have := h recs[i] (Array.getElem_mem_toList hi')
    simpa using this

theorem inv_add (acc : GroupAcc) (ref : List SolutionGroup) (key : List EvalResult)
    (mu : Binding) (inv : Inv acc ref) :
    Inv (acc.add key mu) (addToGroups key mu ref) := by
  obtain ⟨hgroups, hindex⟩ := inv
  subst hgroups
  have hits_list :
      ((acc.index.getD (keyBucket key) #[]).filter
        (fun i => keysEqual key (acc.recs[i]!).key)).toList =
        (List.range acc.recs.size).filter (fun i => keysEqual key (acc.recs[i]!).key) := by
    rw [Array.toList_filter, hindex, bucket_hits]
  have anyEq : (acc.recs.toList.map recGroup).any (fun g => keysEqual key g.key) =
      acc.recs.toList.any (fun g => keysEqual key g.key) := by
    simp [List.any_map, Function.comp_def, recGroup]
  unfold GroupAcc.add addToGroups
  simp only []
  split
  · -- no group matches: a new last group
    rename_i hempty
    have hnil : (List.range acc.recs.size).filter
        (fun i => keysEqual key (acc.recs[i]!).key) = [] := by
      rw [← hits_list]
      simpa [Array.isEmpty_iff] using hempty
    have hany := (range_filter_eq_nil_iff acc.recs (fun g => keysEqual key g.key)).mp hnil
    rw [anyEq, hany]
    refine ⟨?_, ?_⟩
    · simp [recGroup]
    · intro b
      have pushGet : ∀ i, i < acc.recs.size →
          (acc.recs.push ⟨key, [mu]⟩)[i]! = acc.recs[i]! := by
        intro i hi
        rw [getElem!_of_lt _ i (by simp; omega), getElem!_of_lt _ i hi,
          Array.getElem_push_lt hi]
      have lastGet : (acc.recs.push ⟨key, [mu]⟩)[acc.recs.size]! = ⟨key, [mu]⟩ := by
        rw [getElem!_of_lt _ _ (by simp)]
        simp
      have ids_succ : bucketIds (acc.recs.push ⟨key, [mu]⟩) b =
          bucketIds acc.recs b ++ (if keyBucket key == b then [acc.recs.size] else []) := by
        unfold bucketIds
        rw [Array.size_push, List.range_succ, List.filter_append]
        congr 1
        · apply List.filter_congr
          intro i hi
          rw [pushGet i (List.mem_range.mp hi)]
        · simp only [List.filter_cons, List.filter_nil, lastGet]
      rw [ids_succ, Std.HashMap.getD_insert]
      by_cases hb : (keyBucket key == b) = true
      · simp only [hb, if_true]
        have hbe : keyBucket key = b := by simpa using hb
        subst hbe
        simp [hindex]
      · simp only [hb, Bool.false_eq_true, if_false, List.append_nil]
        rw [Std.HashMap.getD_erase]
        simp [hb, hindex]
  · -- some groups match: the row is added to each of them
    rename_i hnonempty
    have hne : (List.range acc.recs.size).filter
        (fun i => keysEqual key (acc.recs[i]!).key) ≠ [] := by
      rw [← hits_list]
      intro h
      apply hnonempty
      simp [Array.isEmpty_iff, ← Array.toList_eq_nil_iff, h]
    have hany : acc.recs.toList.any (fun g => keysEqual key g.key) = true := by
      cases h : acc.recs.toList.any (fun g => keysEqual key g.key)
      · exact absurd ((range_filter_eq_nil_iff acc.recs _).mpr h) hne
      · rfl
    rw [anyEq, hany, if_pos rfl]
    let f : GroupRec → GroupRec := fun g => { g with solsRev := mu :: g.solsRev }
    have hfold := foldl_modify_getElem f
      ((List.range acc.recs.size).filter (fun i => keysEqual key (acc.recs[i]!).key))
      acc.recs ((List.nodup_range).filter _)
    obtain ⟨hs, hget⟩ := hfold
    have recsEq : ((acc.index.getD (keyBucket key) #[]).filter
          (fun i => keysEqual key (acc.recs[i]!).key)).foldl
          (fun rs i => rs.modify i f) acc.recs =
        acc.recs.map (fun g => if keysEqual key g.key then f g else g) := by
      rw [← Array.foldl_toList, hits_list]
      apply Array.ext
      · rw [hs, Array.size_map]
      · intro j h1 h2
        have hj : j < acc.recs.size := by rwa [Array.size_map] at h2
        rw [hget j hj, Array.getElem_map]
        simp only [List.mem_filter, List.mem_range, hj, true_and,
          getElem!_of_lt acc.recs j hj]
    refine ⟨?_, ?_⟩
    · show (((acc.index.getD (keyBucket key) #[]).filter
          (fun i => keysEqual key (acc.recs[i]!).key)).foldl
          (fun rs i => rs.modify i f) acc.recs).toList.map recGroup = _
      rw [recsEq, Array.toList_map, List.map_map, List.map_map]
      apply List.map_congr_left
      intro g _
      by_cases h : keysEqual key g.key = true
      · simp [h, f, recGroup]
      · simp [h, recGroup]
    · intro b
      show ((acc.index).getD b #[]).toList = bucketIds (((acc.index.getD (keyBucket key) #[]).filter
          (fun i => keysEqual key (acc.recs[i]!).key)).foldl
          (fun rs i => rs.modify i f) acc.recs) b
      rw [recsEq, hindex]
      unfold bucketIds
      rw [Array.size_map]
      apply List.filter_congr
      intro i hi
      have hi' := List.mem_range.mp hi
      rw [getElem!_of_lt acc.recs i hi',
        getElem!_of_lt (acc.recs.map _) i (by simpa using hi'), Array.getElem_map]
      by_cases h : keysEqual key acc.recs[i].key = true
      · simp [h, f]
      · simp [h]

theorem inv_foldl (keyOf : Binding → List EvalResult) (valOf : Binding → Binding) :
    ∀ (rows : List Binding) (acc : GroupAcc) (ref : List SolutionGroup), Inv acc ref →
      Inv (rows.foldl (fun acc mu => acc.add (keyOf mu) (valOf mu)) acc)
        (rows.foldl (fun groups mu => addToGroups (keyOf mu) (valOf mu) groups) ref)
  | [], _, _, inv => inv
  | mu :: rows, acc, ref, inv => by
      simp only [List.foldl_cons]
      exact inv_foldl keyOf valOf rows _ _ (inv_add acc ref _ _ inv)

end L4Factoidal.SPARQL.GroupFast

namespace L4Factoidal.SPARQL

/-- The hash grouping that the evaluator runs returns the groups of the
§18.5.1 specification, in the same order and with the same rows in the
same order. -/
theorem groupSolutionsFast_eq (env : EvalEnv) (conds : List GroupCondition)
    (omega : SolutionSeq) :
    groupSolutionsFast env conds omega = groupSolutions env conds omega := by
  unfold groupSolutionsFast groupSolutions
  rw [GroupFast.GroupAcc.groups_eq]
  exact (GroupFast.inv_foldl (evalGroupKey env conds) (extendWithGroupAliases env conds)
    omega {} [] GroupFast.inv_empty).groups

#print axioms groupSolutionsFast_eq

end L4Factoidal.SPARQL
