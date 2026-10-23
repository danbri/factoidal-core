/-
L4Factoidal.Storage.Sbm11.ParallelJoinTheorems — the merge join computed in
left row ranges equals `Qlvr.mergeJoin` (KR 1.2 of OKR batch 3,
https://github.com/danbri/factoidal/issues/875 and
https://github.com/danbri/factoidal/issues/961; record
docs/designissues/2026-10-12-parallel-block-scans.md, stage 1f).

* `lowerBound_spec`: for a non-decreasing column, every row before the
  result has a value below the key, and the result is at most the row count.
* `rangePairs_fst`, `rangePairs_snd`: the merge loop of one left range
  `[lo, hi)`, started at `lowerBound`, appends the matching pairs of the left
  rows `lo .. hi - 1` against all right rows (`rowPairs`).
* `mergeJoinRanges_eq`: for join columns in non-decreasing order and ranges
  that cover the left rows `[0, l.rows)` in order (`Chain`), the join
  computed range by range is `mergeJoin l r v`.
* `mergeJoinRanges_rangeChunks`: the ranges of `rangeChunks` are such ranges.

The hypotheses are the order of the join columns (the precondition of
`MergeTheorems.mergeGo_spec`) and the cover of the left rows; no hypothesis
states a conclusion. Not proved: that `IdQuery.Par.fold` folds the range
results in range order (its contract; the native driver is tested by
`tests/sbm11/threads.sh`).

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Qlvr.MergeTheorems
import L4Factoidal.Storage.Sbm11.ParallelJoin

namespace L4Factoidal.Storage.Sbm11.ParallelJoin

open L4Factoidal.Qlvr

/-! ## The binary search -/

theorem lbGo_spec (B : Nat → UInt64) (a : UInt64) (n : Nat)
    (hB : ∀ x y, x ≤ y → y < n → (B x).toNat ≤ (B y).toNat) :
    ∀ f lo hi, lo ≤ hi → hi ≤ n → (∀ y, y < lo → (B y).toNat < a.toNat) →
      lbGo B a f lo hi ≤ n ∧ ∀ y, y < lbGo B a f lo hi → (B y).toNat < a.toNat := by
  intro f
  induction f with
  | zero =>
    intro lo hi h1 h2 h3
    exact ⟨by simp only [lbGo]; omega, by simpa only [lbGo] using h3⟩
  | succ f ih =>
    intro lo hi h1 h2 h3
    simp only [lbGo]
    by_cases hlt : lo < hi
    · rw [if_pos hlt]
      by_cases hm : B ((lo + hi) / 2) < a
      · rw [if_pos hm]
        apply ih _ _ (by omega) h2
        intro y hy
        by_cases hy' : y < lo
        · exact h3 y hy'
        · have hle := hB y ((lo + hi) / 2) (by omega) (by omega)
          rw [UInt64.lt_iff_toNat_lt] at hm
          omega
      · rw [if_neg hm]
        exact ih _ _ (by omega) (by omega) h3
    · rw [if_neg hlt]
      exact ⟨by omega, h3⟩

theorem lowerBound_spec (B : Nat → UInt64) (n : Nat) (a : UInt64)
    (hB : ∀ x y, x ≤ y → y < n → (B x).toNat ≤ (B y).toNat) :
    lowerBound B n a ≤ n ∧ ∀ y, y < lowerBound B n a → (B y).toNat < a.toNat :=
  lbGo_spec B a n hB (n + 1) 0 n (Nat.zero_le n) (Nat.le_refl n) (fun _ h => absurd h (Nat.not_lt_zero _))

/-! ## One range -/

/-- The matching pairs of left row `x` against all right rows `[0, nr)`. -/
def rowPairs (A B : Nat → UInt64) (ok : Nat → Nat → Bool) (nr x : Nat) : List (Nat × Nat) :=
  ((List.range' 0 nr).filter fun y => A x == B y && ok x y).map fun y => (x, y)

/-- Right rows below `j` cannot match left row `x` when their values are
    below the value of `x`. -/
theorem filter_skip (A B : Nat → UInt64) (ok : Nat → Nat → Bool) (nr j x : Nat) (hj : j ≤ nr)
    (hlt : ∀ y, y < j → (B y).toNat < (A x).toNat) :
    (List.range' 0 nr).filter (fun y => A x == B y && ok x y) =
      (List.range' j (nr - j)).filter (fun y => A x == B y && ok x y) := by
  rw [range'_split 0 nr j hj, List.filter_append, Nat.zero_add]
  have hnil : (List.range' 0 j).filter (fun y => A x == B y && ok x y) = [] := by
    rw [List.filter_eq_nil_iff]
    intro y hy
    rw [List.mem_range'_1] at hy
    have h := hlt y (by omega)
    intro hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    rw [hc.1] at h
    omega
  rw [hnil, List.nil_append]

/-- The pairs `mergeGo` produces from left row `lo` (to `hi`) and right row
    `j`, when every right row before `j` is below the value of row `lo`: the
    pairs of the left rows `lo .. hi - 1` against all right rows. -/
theorem mergeSpec_range (A B : Nat → UInt64) (ok : Nat → Nat → Bool) (nl nr lo hi j : Nat)
    (hA : ∀ x y, x ≤ y → y < nl → (A x).toNat ≤ (A y).toNat)
    (hhi : hi ≤ nl) (hj : j ≤ nr) (hlt : ∀ y, y < j → (B y).toNat < (A lo).toNat) :
    mergeSpec A B ok hi nr lo j = (List.range' lo (hi - lo)).flatMap (rowPairs A B ok nr) := by
  unfold mergeSpec
  apply flatMap_congr'
  intro x hx
  rw [List.mem_range'_1] at hx
  unfold rowPairs
  rw [filter_skip A B ok nr j x hj (fun y hy => by
    have := hA lo x (by omega) (by omega)
    have := hlt y hy
    omega)]

theorem rangePairs_spec (A B : Nat → UInt64) (ok : Nat → Nat → Bool) (nl nr lo hi : Nat)
    (hA : ∀ x y, x ≤ y → y < nl → (A x).toNat ≤ (A y).toNat)
    (hB : ∀ x y, x ≤ y → y < nr → (B x).toNat ≤ (B y).toNat) (hhi : hi ≤ nl) :
    (rangePairs A B ok nr lo hi).1.toList =
        ((List.range' lo (hi - lo)).flatMap (rowPairs A B ok nr)).map Prod.fst ∧
      (rangePairs A B ok nr lo hi).2.toList =
        ((List.range' lo (hi - lo)).flatMap (rowPairs A B ok nr)).map Prod.snd := by
  obtain ⟨hjn, hj⟩ := lowerBound_spec B nr (A lo) hB
  have hA' : ∀ x y, x ≤ y → y < hi → (A x).toNat ≤ (A y).toNat :=
    fun x y h1 h2 => hA x y h1 (by omega)
  obtain ⟨h1, h2⟩ := mergeGo_spec A B ok hi nr hA' hB
    (hi - lo + (nr - lowerBound B nr (A lo)) + 1) lo (lowerBound B nr (A lo)) #[] #[] (by omega)
  unfold rangePairs
  rw [h1, h2, mergeSpec_range A B ok nl nr lo hi _ hA hhi hjn hj]
  simp

/-! ## Ranges that cover the left rows -/

/-- `rs` is a list of ranges `[lo, hi)` that starts at `s`, ends at `e` and
    leaves no gap: each range starts where the one before it ended. -/
def Chain : Nat → List (Nat × Nat) → Nat → Prop
  | s, [], e => s = e
  | s, p :: rs, e => p.1 = s ∧ s ≤ p.2 ∧ Chain p.2 rs e

theorem chain_le : ∀ (rs : List (Nat × Nat)) (s e : Nat), Chain s rs e → s ≤ e
  | [], s, e, h => by simp only [Chain] at h; omega
  | p :: rs, s, e, h => by
    simp only [Chain] at h
    have := chain_le rs p.2 e h.2.2
    omega

theorem chain_mem : ∀ (rs : List (Nat × Nat)) (s e : Nat), Chain s rs e →
    ∀ p ∈ rs, p.1 ≤ p.2 ∧ p.2 ≤ e
  | [], _, _, _, p, hp => by simp at hp
  | q :: rs, s, e, h, p, hp => by
    simp only [Chain] at h
    rcases List.mem_cons.mp hp with hp | hp
    · subst hp
      exact ⟨by omega, chain_le rs _ e h.2.2⟩
    · exact chain_mem rs q.2 e h.2.2 p hp

theorem chain_flatten {β : Type} (G : Nat → List β) :
    ∀ (rs : List (Nat × Nat)) (s e : Nat), Chain s rs e →
      (rs.map fun p => (List.range' p.1 (p.2 - p.1)).flatMap G).flatten = (List.range' s (e - s)).flatMap G
  | [], s, e, h => by
    simp only [Chain] at h
    subst h
    simp
  | p :: rs, s, e, h => by
    simp only [Chain] at h
    obtain ⟨h1, h2, h3⟩ := h
    have hle := chain_le rs p.2 e h3
    rw [List.map_cons, List.flatten_cons, chain_flatten G rs p.2 e h3, h1,
      range'_split s (e - s) (p.2 - s) (by omega), List.flatMap_append,
      show s + (p.2 - s) = p.2 by omega, show e - s - (p.2 - s) = e - p.2 by omega]

theorem concatPairs_acc (parts : List (Array Nat × Array Nat)) :
    ∀ (acc : Array Nat × Array Nat),
      (parts.foldl (fun acc p => (acc.1 ++ p.1, acc.2 ++ p.2)) acc).1.toList =
          acc.1.toList ++ (parts.map fun p => p.1.toList).flatten ∧
        (parts.foldl (fun acc p => (acc.1 ++ p.1, acc.2 ++ p.2)) acc).2.toList =
          acc.2.toList ++ (parts.map fun p => p.2.toList).flatten := by
  induction parts with
  | nil => intro acc; simp
  | cons p ps ih =>
    intro acc
    obtain ⟨h1, h2⟩ := ih (acc.1 ++ p.1, acc.2 ++ p.2)
    simp only [List.foldl_cons, List.map_cons, List.flatten_cons]
    rw [h1, h2]
    simp

theorem concatPairs_fst (parts : List (Array Nat × Array Nat)) :
    (concatPairs parts).1.toList = (parts.map fun p => p.1.toList).flatten := by
  have := (concatPairs_acc parts (#[], #[])).1
  simpa [concatPairs] using this

theorem concatPairs_snd (parts : List (Array Nat × Array Nat)) :
    (concatPairs parts).2.toList = (parts.map fun p => p.2.toList).flatten := by
  have := (concatPairs_acc parts (#[], #[])).2
  simpa [concatPairs] using this

/-! ## The join -/

/-- The index pairs of the ranges, appended, are the index pairs of the single
    merge loop (the first components). -/
theorem ranges_fst (A B : Nat → UInt64) (ok : Nat → Nat → Bool) (nl nr : Nat)
    (hA : ∀ x y, x ≤ y → y < nl → (A x).toNat ≤ (A y).toNat)
    (hB : ∀ x y, x ≤ y → y < nr → (B x).toNat ≤ (B y).toNat)
    (rs : List (Nat × Nat)) (hc : Chain 0 rs nl) :
    (concatPairs (rs.map fun p => rangePairs A B ok nr p.1 p.2)).1 =
      (mergeGo A B ok nl nr (nl + nr + 1) 0 0 #[] #[]).1 := by
  apply Array.toList_inj.mp
  rw [concatPairs_fst, (mergeGo_spec A B ok nl nr hA hB (nl + nr + 1) 0 0 #[] #[] (by omega)).1]
  have hm := chain_mem rs 0 nl hc
  have e1 : (rs.map fun p => rangePairs A B ok nr p.1 p.2).map (fun p => p.1.toList) =
      (rs.map fun p => (List.range' p.1 (p.2 - p.1)).flatMap (rowPairs A B ok nr)).map (List.map Prod.fst) := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left (fun p hp => (rangePairs_spec A B ok nl nr p.1 p.2 hA hB (hm p hp).2).1)
  rw [e1, ← List.map_flatten, chain_flatten _ rs 0 nl hc]
  simp only [List.nil_append, Nat.sub_zero]
  rfl

theorem ranges_snd (A B : Nat → UInt64) (ok : Nat → Nat → Bool) (nl nr : Nat)
    (hA : ∀ x y, x ≤ y → y < nl → (A x).toNat ≤ (A y).toNat)
    (hB : ∀ x y, x ≤ y → y < nr → (B x).toNat ≤ (B y).toNat)
    (rs : List (Nat × Nat)) (hc : Chain 0 rs nl) :
    (concatPairs (rs.map fun p => rangePairs A B ok nr p.1 p.2)).2 =
      (mergeGo A B ok nl nr (nl + nr + 1) 0 0 #[] #[]).2 := by
  apply Array.toList_inj.mp
  rw [concatPairs_snd, (mergeGo_spec A B ok nl nr hA hB (nl + nr + 1) 0 0 #[] #[] (by omega)).2]
  have hm := chain_mem rs 0 nl hc
  have e1 : (rs.map fun p => rangePairs A B ok nr p.1 p.2).map (fun p => p.2.toList) =
      (rs.map fun p => (List.range' p.1 (p.2 - p.1)).flatMap (rowPairs A B ok nr)).map (List.map Prod.snd) := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left (fun p hp => (rangePairs_spec A B ok nl nr p.1 p.2 hA hB (hm p hp).2).2)
  rw [e1, ← List.map_flatten, chain_flatten _ rs 0 nl hc]
  simp only [List.nil_append, Nat.sub_zero]
  rfl

/-- The merge join computed in left row ranges that cover the left rows in
    order is `mergeJoin`, for join columns in non-decreasing order. -/
theorem mergeJoinRanges_eq (l r : Table) (v : String) (rs : List (Nat × Nat))
    (hA : ∀ x y, x ≤ y → y < l.rows →
      (l.at ((l.idx v).getD 0) x).toNat ≤ (l.at ((l.idx v).getD 0) y).toNat)
    (hB : ∀ x y, x ≤ y → y < r.rows →
      (r.at ((r.idx v).getD 0) x).toNat ≤ (r.at ((r.idx v).getD 0) y).toNat)
    (hc : Chain 0 rs l.rows) :
    mergeJoinRanges l r v (rs.map fun p => [p.1, p.2]) = mergeJoin l r v := by
  rw [mergeJoin_eq]
  have hpart : (rs.map fun p => [p.1, p.2]).map (rangePairsOf l r v) =
      rs.map fun p => rangePairs (l.at ((l.idx v).getD 0)) (r.at ((r.idx v).getD 0)) (joinOk l r (otherCols l r v))
        r.rows p.1 p.2 := by
    rw [List.map_map]
    rfl
  unfold mergeJoinRanges
  rw [hpart, ranges_fst (l.at ((l.idx v).getD 0)) (r.at ((r.idx v).getD 0)) (joinOk l r (otherCols l r v)) l.rows r.rows hA hB rs hc,
    ranges_snd (l.at ((l.idx v).getD 0)) (r.at ((r.idx v).getD 0)) (joinOk l r (otherCols l r v)) l.rows r.rows hA hB rs hc]
  rfl

/-! ## The ranges of `ranges` -/

theorem rangesAcc_chain (n step : Nat) :
    ∀ f lo (acc : List (Nat × Nat)), lo ≤ n →
      ∃ R, rangesAcc n step f lo acc = acc.reverse ++ R ∧ Chain lo R n := by
  intro f
  induction f with
  | zero =>
    intro lo acc hlo
    exact ⟨[(lo, n)], by simp [rangesAcc], by simp [Chain]; omega⟩
  | succ f ih =>
    intro lo acc hlo
    simp only [rangesAcc]
    by_cases hs : lo + step < n
    · rw [if_pos hs]
      obtain ⟨R, h1, h2⟩ := ih (lo + step) ((lo, lo + step) :: acc) (by omega)
      refine ⟨(lo, lo + step) :: R, ?_, ?_⟩
      · rw [h1]; simp
      · exact ⟨rfl, Nat.le_add_right lo step, h2⟩
    · rw [if_neg hs]
      exact ⟨[(lo, n)], by simp, by simp [Chain]; omega⟩

theorem ranges_chain (n k : Nat) : Chain 0 (ranges n k) n := by
  obtain ⟨R, h1, h2⟩ := rangesAcc_chain n (max 1 ((n + k - 1) / max k 1)) k 0 [] (Nat.zero_le n)
  unfold ranges
  rw [h1]
  simpa using h2

/-- The divided merge join of the native driver (`IdQuery.mergeJoinParM`,
    with the ranges of `rangeChunks`) is `mergeJoin`. -/
theorem mergeJoinRanges_rangeChunks (l r : Table) (v : String) (k : Nat)
    (hA : ∀ x y, x ≤ y → y < l.rows →
      (l.at ((l.idx v).getD 0) x).toNat ≤ (l.at ((l.idx v).getD 0) y).toNat)
    (hB : ∀ x y, x ≤ y → y < r.rows →
      (r.at ((r.idx v).getD 0) x).toNat ≤ (r.at ((r.idx v).getD 0) y).toNat) :
    mergeJoinRanges l r v (rangeChunks l.rows k) = mergeJoin l r v :=
  mergeJoinRanges_eq l r v (ranges l.rows k) hA hB (ranges_chain l.rows k)

#print axioms mergeJoinRanges_rangeChunks

end L4Factoidal.Storage.Sbm11.ParallelJoin
