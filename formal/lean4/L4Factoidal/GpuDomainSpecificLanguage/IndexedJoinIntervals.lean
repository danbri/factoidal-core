import Init

namespace L4Factoidal.GpuDomainSpecificLanguage.IndexedJoin

/-- A sorted index's four boundary neighbours certify the complete equality
interval. Checking endpoints is sufficient; no matching row can be omitted.
The key domain is expressed as natural numbers (UInt64.toNat in the runner).
This theorem concerns the actual validator's inequalities, not GPU code. -/
theorem interval_complete (n lo hi key : Nat) (value : Nat → Nat)
    (mono : ∀ i j, i ≤ j → j < n → value i ≤ value j)
    (bounds : lo ≤ hi ∧ hi ≤ n)
    (beforeLo : lo = 0 ∨ value (lo - 1) < key)
    (atLo : lo = n ∨ key ≤ value lo)
    (beforeHi : hi = 0 ∨ value (hi - 1) ≤ key)
    (atHi : hi = n ∨ key < value hi)
    (j : Nat) (hj : j < n) :
    value j = key ↔ lo ≤ j ∧ j < hi := by
  constructor
  · intro heq
    constructor
    · by_cases h : lo ≤ j
      · exact h
      · have hlast := mono j (lo - 1) (by omega) (by omega)
        rcases beforeLo with hzero | hlt <;> omega
    · by_cases h : j < hi
      · exact h
      · have hfirst := mono hi j (by omega) hj
        rcases atHi with hend | hlt <;> omega
  · rintro ⟨hlo, hhi⟩
    have hfirst := mono lo j hlo hj
    have hlast := mono j (hi - 1) (by omega) (by omega)
    rcases atLo with hend | hle <;>
      rcases beforeHi with hzero | hle' <;> omega

#print axioms interval_complete

/-- The matching interval enumerates exactly the retained original index
positions, in order and with every occurrence. -/
theorem filter_range_interval (n lo hi : Nat) (bounds : lo ≤ hi ∧ hi ≤ n) :
    (List.range n).filter (fun i => decide (lo ≤ i ∧ i < hi)) =
      (List.range (hi - lo)).map (lo + ·) := by
  have hsplit : List.range n = List.range lo ++ List.range' lo (n - lo) := by
    rw [List.range_eq_range', List.range_eq_range']
    apply List.range'_eq_append_iff.mpr
    exact ⟨lo, by omega, rfl, by simp⟩
  have hmiddle : List.range' lo (n - lo) =
      List.range' lo (hi - lo) ++ List.range' hi (n - hi) := by
    apply List.range'_eq_append_iff.mpr
    refine ⟨hi - lo, by omega, rfl, ?_⟩
    congr 1 <;> omega
  let keep := fun i => decide (lo ≤ i ∧ i < hi)
  have hbefore : (List.range lo).filter keep = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro i hmem
    simp only [List.mem_range] at hmem
    simp only [keep, decide_eq_true_eq]
    omega
  have hin : (List.range' lo (hi - lo)).filter keep = List.range' lo (hi - lo) := by
    apply List.filter_eq_self.mpr
    intro i hmem
    simp only [List.mem_range'_1] at hmem
    simp only [keep, decide_eq_true_eq]
    omega
  have hafter : (List.range' hi (n - hi)).filter keep = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro i hmem
    simp only [List.mem_range'_1] at hmem
    simp only [keep, decide_eq_true_eq]
    omega
  change (List.range n).filter keep = _
  rw [hsplit, hmiddle, List.filter_append, List.filter_append, hbefore, hin, hafter]
  simpa using (List.range'_eq_map_range (s := lo) (n := hi - lo))

/-- Any predicate certified by the interval has the same complete ordered
index list. Used to connect checked bounds with stable sorted-key matches. -/
theorem filter_range_of_interval (n lo hi : Nat) (keep : Nat → Bool)
    (bounds : lo ≤ hi ∧ hi ≤ n)
    (valid : ∀ i, i < n → (keep i = true ↔ lo ≤ i ∧ i < hi)) :
    (List.range n).filter keep = (List.range (hi - lo)).map (lo + ·) := by
  rw [← filter_range_interval n lo hi bounds]
  apply List.filter_congr
  intro i hmem
  have h := valid i (List.mem_range.mp hmem)
  exact Bool.eq_iff_iff.mpr (by simpa using h)

#print axioms filter_range_interval
#print axioms filter_range_of_interval

end L4Factoidal.GpuDomainSpecificLanguage.IndexedJoin
