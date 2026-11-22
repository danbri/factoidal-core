import L4Factoidal.GpuDomainSpecificLanguage.IndexedJoin
import L4Factoidal.GpuDomainSpecificLanguage.IndexedJoinIntervals

/-!
# Complete ordered refinement of checked index joins

The device is untrusted. Stable sorting, endpoint checks and complete ordered
readback validation together establish the original nested equijoin semantics.
The proof concerns the actual preparation and acceptance functions.
-/
namespace L4Factoidal.GpuDomainSpecificLanguage.IndexedJoin

private theorem list_eq_range_map (xs : List α) (d : α) :
    xs = (List.range xs.length).map (fun i => xs[i]?.getD d) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp [List.getElem?_eq_getElem hi]

private theorem array_zipIdx_eq_range (xs : Array α) (d : α) :
    xs.toList.zipIdx = (List.range xs.size).map (fun i => (xs[i]?.getD d, i)) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  have h : i < xs.size := by simpa using hi
  simp [h, List.getElem_zipIdx]

private theorem entry_key (xs : List (UInt64 × Nat)) (i : Nat) :
    ((xs.toArray.map Prod.fst)[i]?.getD 0) = (xs[i]?.getD (0,0)).1 := by
  simp only [Array.getElem?_map, List.getElem?_toArray]
  cases xs[i]? <;> rfl

private theorem entry_order (xs : List (UInt64 × Nat)) (i : Nat) :
    ((xs.toArray.map Prod.snd)[i]?.getD 0) = (xs[i]?.getD (0,0)).2 := by
  simp only [Array.getElem?_map, List.getElem?_toArray]
  cases xs[i]? <;> rfl

private theorem sorted_values_mono (xs : List (UInt64 × Nat))
    (hs : xs.Pairwise (fun a b => a.1 ≤ b.1)) :
    ∀ i j, i ≤ j → j < xs.length →
      (xs[i]?.getD (0,0)).1.toNat ≤ (xs[j]?.getD (0,0)).1.toNat := by
  intro i j hij hj
  have hi : i < xs.length := by omega
  by_cases heq : i = j
  · simp [heq]
  · have h := List.pairwise_iff_getElem.mp hs i j hi hj (by omega)
    simpa [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
      UInt64.le_iff_toNat_le] using h

/-- Exact checked endpoints characterize every matching position in the
    actual stable index, including all duplicate occurrences. -/
theorem rangeValid_complete (left right : Array UInt64) (row lo hi : Nat)
    (hv : rangeValid (buildPrepared left right) row lo hi = true)
    (j : Nat) (hj : j < (buildPrepared left right).sortedRight.size) :
    ((buildPrepared left right).sortedRight[j]?.getD 0 == left[row]?.getD 0) = true ↔
      lo ≤ j ∧ j < hi := by
  let p := buildPrepared left right
  let r := p.sortedRight
  let key := left[row]?.getD 0
  have hm : ∀ i j, i ≤ j → j < r.size →
      (r[i]?.getD 0).toNat ≤ (r[j]?.getD 0).toNat := by
    simpa only [r, p, buildPrepared, Array.size_map, List.size_toArray, entry_key]
      using sorted_values_mono (sortEntries right.toList.zipIdx)
        (sortEntries_sorted right.toList.zipIdx)
  have hb := hv
  simp only [rangeValid, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt,
    and_assoc] at hb
  rcases hb with ⟨hlo, hhi, beforeLo, atLo, beforeHi, atHi⟩
  have h := interval_complete r.size lo hi key.toNat
    (fun i => (r[i]?.getD 0).toNat) hm ⟨hlo,hhi⟩
    beforeLo atLo beforeHi atHi j hj
  simpa only [beq_iff_eq, UInt64.toNat_inj] using h

private theorem rangeValid_bounds (p : Prepared) (row lo hi : Nat)
    (hv : rangeValid p row lo hi = true) : lo ≤ hi ∧ hi ≤ p.sortedRight.size := by
  simp only [rangeValid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hv
  exact ⟨hv.1,hv.2.1⟩

private theorem filter_map_as_filterMap (xs : List α) (keep : α → Bool) (f : α → β) :
    (xs.filter keep).map f = xs.filterMap (fun x => if keep x then some (f x) else none) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : keep x <;> simp [h, ih]

/-- One accepted interval decodes to the complete original right-hand
    matches, in original order. Stability is what preserves duplicate order. -/
theorem checked_row_eq (left right : Array UInt64) (row lo hi : Nat)
    (hv : rangeValid (buildPrepared left right) row lo hi = true) :
    (List.range (hi-lo)).map (fun d =>
      (row,(buildPrepared left right).rightOrder[lo+d]?.getD 0)) =
    right.toList.zipIdx.filterMap (fun r =>
      if left[row]?.getD 0 == r.1 then some (row,r.2) else none) := by
  let es := sortEntries right.toList.zipIdx
  let p := buildPrepared left right
  let key := left[row]?.getD 0
  have hrange := filter_range_of_interval p.sortedRight.size lo hi
    (fun j => p.sortedRight[j]?.getD 0 == key)
    (rangeValid_bounds p row lo hi hv)
    (fun j hj => rangeValid_complete left right row lo hi hv j hj)
  calc
    _ = ((List.range p.sortedRight.size).filter
        (fun j => p.sortedRight[j]?.getD 0 == key)).map
        (fun j => (row,p.rightOrder[j]?.getD 0)) := by
      rw [hrange]
      simp only [List.map_map, Function.comp_def, p]
    _ = (es.filter (fun e => e.1 == key)).map (fun e => (row,e.2)) := by
      conv => rhs; rw [list_eq_range_map es (0,0)]
      simp only [List.filter_map, List.map_map, Function.comp_def]
      simp only [p, buildPrepared, Array.size_map, List.size_toArray, entry_key, entry_order, es]
    _ = (right.toList.zipIdx.filter (fun e => e.1 == key)).map (fun e => (row,e.2)) := by
      simp only [es, filter_sortEntries]
    _ = _ := by
      rw [filter_map_as_filterMap]
      congr 1
      funext x
      simp only [key]
      have hc : (x.1 == left[row]?.getD 0) = (left[row]?.getD 0 == x.1) := by
        apply Bool.eq_iff_iff.mpr
        simpa only [beq_iff_eq] using (eq_comm : x.1 = left[row]?.getD 0 ↔ left[row]?.getD 0 = x.1)
      rw [hc]

/-- Kind: complete ordered numeric refinement.
    Says: accepted interval certificates on the actual stable index decode
    to exactly the original nested UInt64 equijoin, with all duplicates and
    the original left-major, right-major order.
    Does not say: an unchecked device computation is correct. -/
theorem originalPairs_eq_reference (left right : Array UInt64) (c : Counted)
    (h : checkedRanges (buildPrepared left right) c = true) :
    originalPairs (buildPrepared left right) c = referencePairs left right := by
  have hsize : c.lower.size = left.size := by
    have hc := h
    simp only [checkedRanges, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      and_assoc] at hc
    exact hc.1
  unfold originalPairs sortedPairs referencePairs
  rw [array_zipIdx_eq_range c.lower 0, array_zipIdx_eq_range left 0]
  simp only [List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
  rw [hsize]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i hi
  exact checked_row_eq left right i _ _
    (checkedRanges_each (buildPrepared left right) c h i (List.mem_range.mp hi))

/-- Kind: public parser-to-reference refinement.
    Says: the actual prepare, range-readback and pair-readback functions can
    only return the complete original ordered equijoin. Device corruption,
    omissions, extra pairs and altered order are rejected by those functions.
    Does not say: a device must return a successful result. -/
theorem accepted_join_eq_reference (left right : Array UInt64) (p : Prepared)
    (c : Counted) (rangeReply pairReply : Lean.Json) (answer : List (Nat × Nat))
    (hp : prepare? left right = .ok p)
    (hr : acceptRanges? p rangeReply = .ok c)
    (ha : acceptPairs? p c pairReply = .ok answer) :
    answer = referencePairs left right := by
  have hc := acceptRanges_sound p rangeReply c hr
  have hm := acceptPairs_sound p c pairReply answer ha
  have he := prepare?_exact left right p hp
  rw [he] at hc hm
  exact hm.trans (originalPairs_eq_reference left right c hc)

/-- The same refinement at the typed word-buffer boundary. -/
theorem accepted_packed_eq_reference (left right : Array UInt64) (p : Prepared)
    (c : Counted) (rangeReply : Lean.Json) (words : List UInt32) (answer : List (Nat × Nat))
    (hp : prepare? left right = .ok p)
    (hr : acceptRanges? p rangeReply = .ok c)
    (ha : acceptPacked? p c words = .ok answer) :
    answer = referencePairs left right := by
  have hc := acceptRanges_sound p rangeReply c hr
  have hm := acceptPacked_sound p c words answer ha
  have he := prepare?_exact left right p hp
  rw [he] at hc hm
  exact hm.trans (originalPairs_eq_reference left right c hc)

#print axioms rangeValid_complete
#print axioms checked_row_eq
#print axioms originalPairs_eq_reference
#print axioms accepted_join_eq_reference
#print axioms accepted_packed_eq_reference

end L4Factoidal.GpuDomainSpecificLanguage.IndexedJoin
