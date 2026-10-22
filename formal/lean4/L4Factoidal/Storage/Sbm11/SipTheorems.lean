/-
L4Factoidal.Storage.Sbm11.SipTheorems — the frame-level functions of
sideways information passing (https://github.com/danbri/factoidal/issues/809;
lemmas L4g and L4h of docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

* `sorted_spec`: the run-time check `Sip.sorted` gives `Sorted`.
* `probe_mem`: for candidates in non-decreasing order, the pointer test
  (`Sip.probeFrom` from any start) answers `cands.contains w`.
* `mayHold_false`: when `Sip.mayHold` is false, no candidate lies in
  `[vlo, vhi]`.
* `findWords_spec`: on a frame that decodes to the words `ws`, the rows
  `Sip.findWords` returns are exactly
  `(List.range' lo (hi - lo)).filter fun r => cands.contains (at64 ws r)`,
  and the words it returns are the words of those rows.
* `gatherWords_spec`: on a frame that decodes to `ws`, for strictly
  increasing rows below the row count, `Sip.gatherWords` returns the words
  of those rows; `pickWords_data`: the same for `Sip.pickWords`.

The delta loops are related to `Column.deltaAtGo` (the decoder of the
round-trip theorem) by one varint step at a time, as
`FrameRangeTheorems.deltaRangeGo_step` and `deltaRangeGo_eq` do for the range
decoder.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.SipFastTheorems
import L4Factoidal.Storage.Sbm11.FrameRangeTheorems
import L4Factoidal.Storage.Sbm11.BlockAtTheorems

namespace L4Factoidal.Storage.Sbm11.Sip

open L4Factoidal (two64)
open L4Factoidal.Storage.Sbm11.Column (getVarAtGo getVarAt deltaAtGo unzz tagConst tagRaw tagDelta)
open L4Factoidal.Storage.Sbm11.FrameWords (put64 words)
open L4Factoidal.Codec.Zstd (word64)

/-! ## Candidates in non-decreasing order -/

/-- The candidates are in non-decreasing order. -/
def Sorted (cands : Array UInt64) : Prop :=
  ∀ i j, i ≤ j → j < cands.size → cands[i]! ≤ cands[j]!

theorem sortedGo_step (cands : Array UInt64) :
    ∀ f i, cands.size - i ≤ f + 1 → sortedGo cands f i = true →
      ∀ k, i ≤ k → k + 1 < cands.size → cands[k]! ≤ cands[k + 1]! := by
  intro f
  induction f with
  | zero =>
    intro i hf _ k hik hk
    omega
  | succ f ih =>
    intro i hf h k hik hk
    simp only [sortedGo] at h
    split at h
    · split at h
      · rename_i hle
        rcases Nat.eq_or_lt_of_le hik with he | hlt
        · subst he; exact hle
        · exact ih (i + 1) (by omega) h k (by omega) hk
      · cases h
    · omega

theorem sorted_spec (cands : Array UInt64) (h : sorted cands = true) : Sorted cands := by
  have hstep := sortedGo_step cands cands.size 0 (by omega) h
  have : ∀ d i, i + d < cands.size → cands[i]! ≤ cands[i + d]! := by
    intro d
    induction d with
    | zero => intro i _; exact UInt64.le_refl _
    | succ d ih =>
      intro i hd
      exact UInt64.le_trans (ih i (by omega)) (by rw [← Nat.add_assoc]; exact hstep (i + d) (by omega) (by omega))
  intro i j hij hj
  have := this (j - i) i (by omega)
  rwa [Nat.add_sub_cancel' hij] at this

/-! ## The candidate pointer -/

theorem advGo_spec (cands : Array UInt64) (w : UInt64) :
    ∀ f p, cands.size - p ≤ f → p ≤ cands.size →
      p ≤ advGo cands w f p ∧ advGo cands w f p ≤ cands.size ∧
      (∀ k, p ≤ k → k < advGo cands w f p → cands[k]! < w) ∧
      (advGo cands w f p < cands.size → ¬ cands[advGo cands w f p]! < w) := by
  intro f
  induction f with
  | zero =>
    intro p hf hp
    simp only [advGo]
    refine ⟨Nat.le_refl _, hp, fun k h1 h2 => by omega, fun h => by omega⟩
  | succ f ih =>
    intro p hf hp
    simp only [advGo]
    by_cases hc : (p < cands.size && cands[p]! < w) = true
    · rw [if_pos hc]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨h1, h2, h3, h4⟩ := ih (p + 1) (by omega) (by omega)
      refine ⟨by omega, h2, fun k hk1 hk2 => ?_, h4⟩
      rcases Nat.eq_or_lt_of_le hk1 with he | hlt
      · subst he; exact hc.2
      · exact h3 k (by omega) hk2
    · rw [if_neg hc]
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hc
      exact ⟨Nat.le_refl _, hp, fun k h1 h2 => by omega, fun h => hc h⟩

theorem startFor_spec (cands : Array UInt64) (hs : Sorted cands) (w : UInt64) (p : Nat) :
    startFor cands w p ≤ cands.size ∧ ∀ k, k < startFor cands w p → cands[k]! < w := by
  unfold startFor
  by_cases hc : (p ≤ cands.size && (p == 0 || cands[p - 1]! < w)) = true
  · rw [if_pos hc]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hc
    refine ⟨hc.1, fun k hk => ?_⟩
    rcases hc.2 with h0 | hlt
    · omega
    · exact UInt64.lt_of_le_of_lt (hs k (p - 1) (by omega) (by omega)) hlt
  · rw [if_neg hc]
    exact ⟨Nat.zero_le _, fun k hk => by omega⟩

/-- The pointer facts of `probeFrom`: every candidate before the result is
    below `w`, the result is at most the size, and the candidate at the
    result (if any) is not below `w`. -/
theorem probeFrom_spec (cands : Array UInt64) (hs : Sorted cands) (w : UInt64) (p : Nat) :
    probeFrom cands w p ≤ cands.size ∧ (∀ k, k < probeFrom cands w p → cands[k]! < w) ∧
      (probeFrom cands w p < cands.size → ¬ cands[probeFrom cands w p]! < w) := by
  obtain ⟨s1, s2⟩ := startFor_spec cands hs w p
  obtain ⟨a1, a2, a3, a4⟩ := advGo_spec cands w (cands.size - startFor cands w p) (startFor cands w p)
    (Nat.le_refl _) s1
  refine ⟨a2, fun k hk => ?_, a4⟩
  by_cases hk' : k < startFor cands w p
  · exact s2 k hk'
  · exact a3 k (by omega) hk

theorem contains_iff_getElem (cands : Array UInt64) (w : UInt64) :
    cands.contains w = true ↔ ∃ k, k < cands.size ∧ cands[k]! = w := by
  rw [Array.contains_iff_mem, Array.mem_iff_getElem]
  constructor
  · rintro ⟨k, hk, he⟩
    exact ⟨k, hk, by rw [getElem!_pos cands k hk]; exact he⟩
  · rintro ⟨k, hk, he⟩
    exact ⟨k, hk, by rw [← getElem!_pos cands k hk]; exact he⟩

/-- The candidate test of the find loops is membership. -/
theorem probe_mem (cands : Array UInt64) (hs : Sorted cands) (w : UInt64) (p : Nat) :
    (probeFrom cands w p < cands.size && cands[probeFrom cands w p]! == w) = cands.contains w := by
  obtain ⟨h1, h2, h3⟩ := probeFrom_spec cands hs w p
  generalize probeFrom cands w p = q at h1 h2 h3
  apply Bool.eq_iff_iff.mpr
  rw [contains_iff_getElem]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨hq, he⟩
    exact ⟨q, hq, he⟩
  · rintro ⟨k, hk, he⟩
    have hqk : q ≤ k := by
      apply Nat.le_of_not_lt
      intro hlt
      have := h2 k hlt
      rw [he] at this
      exact UInt64.lt_irrefl _ this
    have hq : q < cands.size := by omega
    refine ⟨hq, ?_⟩
    have hle := hs q k hqk hk
    rw [he] at hle
    have hge : w ≤ cands[q]! := UInt64.not_lt.mp (h3 hq)
    exact UInt64.le_antisymm hle hge

/-- When `mayHold` is false, every candidate is below `vlo` or above
    `vhi`. -/
theorem mayHold_false (cands : Array UInt64) (hs : Sorted cands) (vlo vhi : UInt64) (q : Nat)
    (h : mayHold cands vlo vhi q = false) : ∀ x, cands.contains x = true → x < vlo ∨ vhi < x := by
  intro x hx
  obtain ⟨k, hk, he⟩ := (contains_iff_getElem cands x).mp hx
  subst he
  unfold mayHold at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hc
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
    by_cases hkq : k < q
    · left
      rcases hc.2 with h0 | hlt
      · omega
      · exact UInt64.lt_of_le_of_lt (hs k (q - 1) (by omega) (by omega)) hlt
    · right
      have hq : q < cands.size := by omega
      rcases h with h1 | h2
      · exact absurd hq h1
      · exact UInt64.lt_of_lt_of_le (UInt64.not_le.mp h2) (hs q k (by omega) hk)
  · cases h

/-! ## Words -/

theorem put64_u (out : ByteArray) (w : UInt64) :
    (put64 out w).data.toList = out.data.toList ++ Column.put64 w.toNat := by
  have := FrameWords.put64_data out w.toNat
  rw [show (w.toNat.toUInt64) = w from UInt64.ofNat_toNat] at this
  exact this

theorem pickWords_data (ws : ByteArray) (pos : Array Nat) :
    (pickWords ws pos).data.toList = (pos.toList.map fun r => Column.put64 (word64 ws (8 * r)).toNat).flatten := by
  unfold pickWords
  rw [← Array.foldl_toList]
  have : ∀ (l : List Nat) (acc : ByteArray),
      (l.foldl (fun out r => put64 out (word64 ws (8 * r))) acc).data.toList =
        acc.data.toList ++ (l.map fun r => Column.put64 (word64 ws (8 * r)).toNat).flatten := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons r rs ih =>
      intro acc
      rw [List.foldl_cons, ih, put64_u, List.map_cons, List.flatten_cons, List.append_assoc]
  rw [this]
  rfl

/-! ## Finding the rows in a column of words -/

/-- The rows `[r, hi)` of a column of words whose word is a candidate. -/
def foundIn (ws : ByteArray) (cands : Array UInt64) (r hi : Nat) : List Nat :=
  (List.range' r (hi - r)).filter fun k => cands.contains (word64 ws (8 * k))

theorem range'_cons {r n : Nat} (h : r < n) : List.range' r (n - r) = r :: List.range' (r + 1) (n - (r + 1)) := by
  rw [show n - r = (n - (r + 1)) + 1 by omega, List.range'_succ]

theorem wordsFindGo_spec (ws : ByteArray) (hi : Nat) (cands : Array UInt64) (hs : Sorted cands) :
    ∀ f r p (pos : Array Nat) (out : ByteArray), hi - r ≤ f →
      (wordsFindGo ws hi cands f r p pos out).1.toList = pos.toList ++ foundIn ws cands r hi ∧
      (wordsFindGo ws hi cands f r p pos out).2.data.toList =
        out.data.toList ++ ((foundIn ws cands r hi).map fun k => Column.put64 (word64 ws (8 * k)).toNat).flatten := by
  intro f
  induction f with
  | zero =>
    intro r p pos out hf
    have : hi - r = 0 := by omega
    simp [wordsFindGo, foundIn, this]
  | succ f ih =>
    intro r p pos out hf
    simp only [wordsFindGo]
    by_cases hr : r < hi
    · rw [if_pos hr]
      have hcons : foundIn ws cands r hi =
          (if cands.contains (word64 ws (8 * r)) then r :: foundIn ws cands (r + 1) hi
           else foundIn ws cands (r + 1) hi) := by
        unfold foundIn
        rw [range'_cons hr, List.filter_cons]
      rw [probe_mem cands hs]
      by_cases hc : cands.contains (word64 ws (8 * r)) = true
      · rw [if_pos hc]
        obtain ⟨i1, i2⟩ := ih (r + 1) _ (pos.push r) (put64 out (word64 ws (8 * r))) (by omega)
        rw [hcons, if_pos hc]
        refine ⟨by rw [i1, Array.toList_push]; simp, ?_⟩
        rw [i2, put64_u]
        simp
      · rw [if_neg hc]
        obtain ⟨i1, i2⟩ := ih (r + 1) _ pos out (by omega)
        rw [hcons, if_neg hc]
        exact ⟨i1, i2⟩
    · rw [if_neg hr]
      have : hi - r = 0 := by omega
      simp [foundIn, this]

/-! ## The delta find loop -/

private theorem byte_get!'' (b : ByteArray) (i : Nat) (h : i < b.size) : b.get! i = b[i] := by
  simp [ByteArray.get!, ByteArray.getElem_eq_getElem_data, getElem!_pos, h]

/-- The emit step of `deltaFindGo` for the value `v` of row `idx`. -/
def findEmit (b : ByteArray) (lo hi : Nat) (cands : Array UInt64) (F idx p : Nat) (pos : Array Nat)
    (out : ByteArray) (v j : Nat) : Option (Array Nat × ByteArray) :=
  if idx ≥ lo then
    if probeFrom cands v.toUInt64 p < cands.size && cands[probeFrom cands v.toUInt64 p]! == v.toUInt64 then
      deltaFindGo b lo hi cands F (idx + 1) v j 0 (probeFrom cands v.toUInt64 p) (pos.push idx) (put64 out v.toUInt64)
    else deltaFindGo b lo hi cands F (idx + 1) v j 0 (probeFrom cands v.toUInt64 p) pos out
  else deltaFindGo b lo hi cands F (idx + 1) v j 0 p pos out

/-- One row of the find loop is one varint of `getVarAtGo` (`c` is the fuel
    above the minimum). -/
theorem deltaFindGo_step (b : ByteArray) (lo hi : Nat) (cands : Array UInt64) (c idx prev p : Nat)
    (pos : Array Nat) (out : ByteArray) (hp : prev < two64) (hidx : idx < hi) :
    ∀ d acc i, b.size - i = d → i ≤ b.size →
      deltaFindGo b lo hi cands (d + c + 2) idx prev i acc p pos out =
        match getVarAtGo b d acc i with
        | none => none
        | some (z, j) =>
          match unzz prev z with
          | none => none
          | some v => if v < two64 then findEmit b lo hi cands (b.size - j + c + 2) idx p pos out v j else none := by
  intro d
  induction d with
  | zero =>
    intro acc i hd hi'
    have : i = b.size := by omega
    subst this
    rw [show 0 + c + 2 = (c + 1) + 1 by omega, deltaFindGo.eq_2]
    simp only [show ¬ (idx ≥ hi) by omega, if_false, Nat.lt_irrefl]
    simp [getVarAtGo]
  | succ d ih =>
    intro acc i hd hi'
    have hlt : i < b.size := by omega
    rw [show d + 1 + c + 2 = (d + c + 2) + 1 by omega, deltaFindGo.eq_2, getVarAtGo.eq_2]
    simp only [show ¬ (idx ≥ hi) by omega, if_false, if_pos hlt, byte_get!'' b i hlt, dif_pos hlt]
    by_cases hx : b[i].toNat < 128
    · rw [if_pos hx, if_pos hx]
      have hj : b.size - (i + 1) + c + 2 = d + c + 2 := by omega
      simp only [unzz, hj, findEmit]
      by_cases he : (acc * 128 + b[i].toNat) % 2 = 0
      · simp only [he, beq_self_eq_true, if_true]
        by_cases hv : prev + (acc * 128 + b[i].toNat) / 2 < two64
        · simp only [hv, if_true]
        · simp only [hv, if_false]
      · have he2 : ((acc * 128 + b[i].toNat) % 2 == 0) = false := by simpa using he
        simp only [he2, he, Bool.false_eq_true, if_false]
        by_cases hle : (acc * 128 + b[i].toNat + 1) / 2 ≤ prev
        · simp only [hle, if_true, show prev - (acc * 128 + b[i].toNat + 1) / 2 < two64 by omega]
        · simp only [hle, if_false]
    · rw [if_neg hx, if_neg hx]
      exact ih _ _ (by omega) (by omega)

/-- The rows `[idx, idx + k)` at or above `lo` whose value `val t` is a
    candidate. -/
def foundVals (lo : Nat) (cands : Array UInt64) (val : Nat → Nat) (idx k : Nat) : List Nat :=
  (List.range' idx k).filter fun t => decide (lo ≤ t) && cands.contains (val t).toUInt64

theorem foundVals_succ (lo : Nat) (cands : Array UInt64) (val : Nat → Nat) (idx k : Nat) :
    foundVals lo cands val idx (k + 1) =
      if (decide (lo ≤ idx) && cands.contains (val idx).toUInt64) then idx :: foundVals lo cands val (idx + 1) k
      else foundVals lo cands val (idx + 1) k := by
  unfold foundVals
  rw [List.range'_succ, List.filter_cons]

theorem getElem!_append_zero (v : Nat) (a' : Array Nat) : (#[v] ++ a')[0]! = v := by
  rw [getElem!_pos _ 0 (by simp; omega)]
  simp

theorem getElem!_append_one (v : Nat) (a' : Array Nat) (t : Nat) :
    (#[v] ++ a')[t + 1]! = a'[t]! := by
  by_cases h : t < a'.size
  · rw [getElem!_pos _ (t + 1) (by simp; omega), getElem!_pos a' t h]
    simp [Array.getElem_append_right]
  · rw [getElem!_neg _ (t + 1) (by simp; omega), getElem!_neg a' t h]

/-- The find loop over a delta frame whose next `k = hi - idx` values (from
    position `i`) are `val idx, ..., val (hi - 1)`: it returns the rows of
    `[idx, hi)` at or above `lo` whose value is a candidate, and their
    values as words. -/
theorem deltaFindGo_eq (b : ByteArray) (lo hi : Nat) (cands : Array UInt64) (hs : Sorted cands) (c : Nat)
    (val : Nat → Nat) :
    ∀ k idx prev i p (pos : Array Nat) (out : ByteArray) (a : Array Nat) (j : Nat),
      k = hi - idx → idx ≤ hi → prev < two64 → i ≤ b.size →
      deltaAtGo b k prev i #[] = some (a, j) →
      (∀ t, idx ≤ t → t < hi → a[t - idx]! = val t) →
      ∃ pos' out', deltaFindGo b lo hi cands (b.size - i + c + 2) idx prev i 0 p pos out = some (pos', out') ∧
        pos'.toList = pos.toList ++ foundVals lo cands val idx k ∧
        out'.data.toList = out.data.toList ++ ((foundVals lo cands val idx k).map fun t => Column.put64 (val t)).flatten := by
  intro k
  induction k with
  | zero =>
    intro idx prev i p pos out a j hk hih _ _ _ _
    refine ⟨pos, out, ?_, by simp [foundVals], by simp [foundVals]⟩
    rw [show b.size - i + c + 2 = (b.size - i + c + 1) + 1 by omega, deltaFindGo.eq_2, if_pos (by omega)]
  | succ k ih =>
    intro idx prev i p pos out a j hk hih hp hib hda hval
    have hidx : idx < hi := by omega
    rw [deltaFindGo_step b lo hi cands c idx prev p pos out hp hidx (b.size - i) 0 i rfl hib]
    simp only [deltaAtGo, getVarAt] at hda
    cases hv : getVarAtGo b (b.size - i) 0 i with
    | none => rw [hv] at hda; cases hda
    | some zj =>
      obtain ⟨z, j1⟩ := zj
      rw [hv] at hda
      have hj1 := FrameWords.getVarAtGo_le b _ _ _ _ _ hv
      simp only at hda ⊢
      cases hu : unzz prev z with
      | none => rw [hu] at hda; cases hda
      | some v =>
        rw [hu] at hda
        simp only at hda ⊢
        by_cases hvl : v < two64
        · rw [if_pos hvl] at hda
          rw [if_pos hvl]
          rw [FrameWords.deltaAtGo_acc] at hda
          cases hr : deltaAtGo b k v j1 #[] with
          | none => rw [hr] at hda; cases hda
          | some r =>
            obtain ⟨a', j'⟩ := r
            rw [hr] at hda
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hda
            obtain ⟨ha, hj⟩ := hda
            subst hj
            have ha' : a = #[v] ++ a' := by rw [← ha]; rfl
            have hv0 : val idx = v := by
              have := hval idx (Nat.le_refl _) hidx
              rw [Nat.sub_self, ha', getElem!_append_zero] at this
              exact this.symm
            have hval' : ∀ t, idx + 1 ≤ t → t < hi → a'[t - (idx + 1)]! = val t := by
              intro t h1 h2
              have := hval t (by omega) h2
              rw [ha', show t - idx = (t - (idx + 1)) + 1 by omega, getElem!_append_one] at this
              exact this
            rw [foundVals_succ]
            unfold findEmit
            by_cases hl : idx ≥ lo
            · rw [if_pos hl, probe_mem cands hs]
              by_cases hc : cands.contains v.toUInt64 = true
              · rw [if_pos hc]
                have hcond : (decide (lo ≤ idx) && cands.contains (val idx).toUInt64) = true := by
                  rw [hv0, hc, Bool.and_true]; exact decide_eq_true hl
                obtain ⟨pos', out', h1, h2, h3⟩ := ih (idx + 1) v j1 (probeFrom cands v.toUInt64 p) (pos.push idx)
                  (put64 out v.toUInt64) a' j' (by omega) (by omega) hvl hj1 hr hval'
                refine ⟨pos', out', h1, ?_, ?_⟩
                · rw [h2, if_pos hcond, Array.toList_push]
                  simp
                · rw [h3, if_pos hcond, FrameWords.put64_data, List.map_cons, List.flatten_cons, hv0]
                  simp
              · have hc' : cands.contains v.toUInt64 = false := Bool.eq_false_iff.mpr hc
                rw [if_neg hc]
                have hcond : (decide (lo ≤ idx) && cands.contains (val idx).toUInt64) = false := by
                  rw [hv0, hc', Bool.and_false]
                obtain ⟨pos', out', h1, h2, h3⟩ := ih (idx + 1) v j1 (probeFrom cands v.toUInt64 p) pos out a' j'
                  (by omega) (by omega) hvl hj1 hr hval'
                refine ⟨pos', out', h1, ?_, ?_⟩
                · rw [h2, if_neg (by rw [hcond]; exact Bool.false_ne_true)]
                · rw [h3, if_neg (by rw [hcond]; exact Bool.false_ne_true)]
            · rw [if_neg hl]
              have hcond : (decide (lo ≤ idx) && cands.contains (val idx).toUInt64) = false := by
                rw [decide_eq_false (by omega : ¬ lo ≤ idx), Bool.false_and]
              obtain ⟨pos', out', h1, h2, h3⟩ := ih (idx + 1) v j1 p pos out a' j'
                (by omega) (by omega) hvl hj1 hr hval'
              refine ⟨pos', out', h1, ?_, ?_⟩
              · rw [h2, if_neg (by rw [hcond]; exact Bool.false_ne_true)]
              · rw [h3, if_neg (by rw [hcond]; exact Bool.false_ne_true)]
        · rw [if_neg hvl] at hda; cases hda

/-! ## A delta frame's words -/

/-- A delta frame that `decodeWords` decodes is the words of the values
    `Column.deltaAtGo` decodes. -/
theorem decodeWords_delta (b : ByteArray) (n i : Nat) (ws : ByteArray) (j : Nat)
    (hi : i < b.size) (ht : b.get! i = tagDelta) (h : FrameWords.decodeWords b n i = some (ws, j)) :
    ∃ a j', deltaAtGo b n 0 (i + 1) #[] = some (a, j') ∧ ws = words a ∧ a.size = n ∧ ∀ x ∈ a, x < two64 := by
  unfold FrameWords.decodeWords at h
  rw [if_pos hi] at h
  simp only [ht, show (tagDelta == tagConst) = false from rfl, show (tagDelta == tagRaw) = false from rfl,
    show (tagDelta == tagDelta) = true from rfl, Bool.false_eq_true, if_false, if_true] at h
  unfold FrameWords.deltaWords at h
  have hw := FrameWords.deltaGo_eq b n 0 (i + 1) (ByteArray.emptyWithCapacity (8 * n)) (by decide) (by omega)
  rw [h] at hw
  cases ha : deltaAtGo b n 0 (i + 1) #[] with
  | none => rw [ha] at hw; cases hw
  | some r =>
    obtain ⟨a, j'⟩ := r
    rw [ha] at hw
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hw
    refine ⟨a, j', rfl, ?_, ?_, ?_⟩
    · apply ByteArray.ext
      apply Array.toList_inj.mp
      rw [hw.1, FrameWords.words_data]
      rfl
    · have := FrameWords.deltaAtGo_size b _ _ _ _ _ _ ha
      simpa using this
    · exact Block.deltaAtGo_lt b n 0 (i + 1) #[] a j' (by simp) ha

/-- The word of row `t` of `words a` read with `word64`. -/
theorem word64_words (a : Array Nat) (t : Nat) (ht : t < a.size) (hv : ∀ x ∈ a, x < two64) :
    (word64 (words a) (8 * t)).toNat = a[t]! := by
  have := ScanTheorems.at64_words a t ht
  unfold IdQuery.at64 at this
  rw [this, getElem!_pos a t ht]
  have hlt := hv a[t] (Array.getElem_mem ht)
  simp only [Nat.toUInt64, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hlt

theorem foundVals_zero (lo hi : Nat) (cands : Array UInt64) (val : Nat → Nat) (h : lo ≤ hi) :
    foundVals lo cands val 0 hi = (List.range' lo (hi - lo)).filter fun t => cands.contains (val t).toUInt64 := by
  unfold foundVals
  have hsplit : List.range' 0 hi = List.range' 0 lo ++ List.range' lo (hi - lo) := by
    have := @List.range'_append 0 lo (hi - lo) 1
    simp only [Nat.one_mul, Nat.zero_add] at this
    rw [this, Nat.add_sub_cancel' h]
  rw [hsplit, List.filter_append]
  have h1 : (List.range' 0 lo).filter (fun t => decide (lo ≤ t) && cands.contains (val t).toUInt64) = [] := by
    rw [List.filter_eq_nil_iff]
    intro t ht
    have := List.mem_range'_1.mp ht
    simp only [decide_eq_true_eq, Bool.and_eq_true, not_and]
    intro hl; omega
  rw [h1, List.nil_append]
  apply List.filter_congr
  intro t ht
  have := List.mem_range'_1.mp ht
  simp only [show lo ≤ t from this.1, decide_true, Bool.true_and]

/-! ## `findWords` -/

/-- **The candidate search.** On a frame that decodes to the words `ws`,
    `findWords` returns exactly the rows of `[lo, hi)` whose word is a
    candidate (`foundIn`), in order, and the words of those rows. -/
theorem findWords_spec (b : ByteArray) (n i lo hi : Nat) (cands : Array UInt64) (hs : Sorted cands) (p : Nat)
    (ws : ByteArray) (j : Nat) (hlh : lo ≤ hi) (hhi : hi ≤ n)
    (h : FrameWords.decodeWords b n i = some (ws, j)) :
    ∃ pos jw, findWords b n i lo hi cands p = some (pos, jw) ∧
      pos.toList = foundIn ws cands lo hi ∧
      jw.data.toList = ((foundIn ws cands lo hi).map fun k => Column.put64 (word64 ws (8 * k)).toNat).flatten := by
  unfold findWords
  rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)]
  by_cases hd : (i < b.size && b.get! i == tagDelta) = true
  · rw [if_pos hd]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hd
    rw [deltaFindStart_eq b lo hi cands i p hd.1]
    obtain ⟨a, j', ha, hws, hsz, hlt⟩ := decodeWords_delta b n i ws j hd.1 hd.2 h
    obtain ⟨a', j2, ha', hpre⟩ := FrameWords.deltaAtGo_prefix b hi (n - hi) 0 (i + 1) #[] a j'
      (by rw [show hi + (n - hi) = n by omega]; exact ha)
    have hval : ∀ t, 0 ≤ t → t < hi → a'[t - 0]! = a[t]! := by
      intro t _ ht
      have hsz' : a'.size = hi := by
        have := congrArg List.length hpre
        simp only [Array.length_toList, List.length_take] at this
        rw [this]; simp; omega
      rw [Nat.sub_zero, getElem!_pos a' t (by omega), getElem!_pos a t (by omega)]
      have : a'.toList[t]'(by simp; omega) = a.toList[t]'(by simp; omega) := by
        simp only [hpre, List.getElem_take]
      simpa using this
    obtain ⟨pos', out', h1, h2, h3⟩ := deltaFindGo_eq b lo hi cands hs 1 (fun t => a[t]!) hi 0 0 (i + 1) p #[] .empty a' j2
      (by omega) (by omega) (by decide) (by omega) ha' hval
    rw [show b.size - (i + 1) + 1 + 2 = b.size - i + 2 by omega] at h1
    have hfound : foundVals lo cands (fun t => a[t]!) 0 hi = foundIn ws cands lo hi := by
      rw [foundVals_zero lo hi cands _ hlh]
      unfold foundIn
      apply List.filter_congr
      intro t ht
      have := List.mem_range'_1.mp ht
      rw [hws, ← word64_words a t (by omega) hlt]
      simp only [Nat.toUInt64, UInt64.ofNat_toNat]
    refine ⟨pos', out', h1, by rw [h2, hfound]; rfl, ?_⟩
    rw [h3, hfound]
    show [] ++ _ = _
    rw [List.nil_append]
    congr 1
    apply List.map_congr_left
    intro t ht
    have := List.mem_range'_1.mp (List.mem_filter.mp ht).1
    rw [hws, word64_words a t (by omega) hlt]
  · rw [if_neg hd, h]
    obtain ⟨i1, i2⟩ := wordsFindGo_spec ws hi cands hs (hi - lo) lo p #[] .empty (Nat.le_refl _)
    exact ⟨_, _, rfl, by rw [i1]; rfl, by rw [i2]; rfl⟩

/-! ## The delta gather loop -/

/-- The emit step of `deltaGatherGo` for the value `v` of row `idx`. -/
def gatherEmit (b : ByteArray) (pos : Array Nat) (F idx kk : Nat) (out : ByteArray) (v j : Nat) : Option ByteArray :=
  if idx == pos[kk]! then deltaGatherGo b pos F (idx + 1) v j 0 (kk + 1) (put64 out v.toUInt64)
  else deltaGatherGo b pos F (idx + 1) v j 0 kk out

theorem deltaGatherGo_step (b : ByteArray) (pos : Array Nat) (c idx prev kk : Nat) (out : ByteArray)
    (hp : prev < two64) (hk : kk < pos.size) :
    ∀ d acc i, b.size - i = d → i ≤ b.size →
      deltaGatherGo b pos (d + c + 2) idx prev i acc kk out =
        match getVarAtGo b d acc i with
        | none => none
        | some (z, j) =>
          match unzz prev z with
          | none => none
          | some v => if v < two64 then gatherEmit b pos (b.size - j + c + 2) idx kk out v j else none := by
  intro d
  induction d with
  | zero =>
    intro acc i hd hi'
    have : i = b.size := by omega
    subst this
    rw [show 0 + c + 2 = (c + 1) + 1 by omega, deltaGatherGo.eq_2]
    simp only [show ¬ (kk ≥ pos.size) by omega, if_false, Nat.lt_irrefl]
    simp [getVarAtGo]
  | succ d ih =>
    intro acc i hd hi'
    have hlt : i < b.size := by omega
    rw [show d + 1 + c + 2 = (d + c + 2) + 1 by omega, deltaGatherGo.eq_2, getVarAtGo.eq_2]
    simp only [show ¬ (kk ≥ pos.size) by omega, if_false, if_pos hlt, byte_get!'' b i hlt, dif_pos hlt]
    by_cases hx : b[i].toNat < 128
    · rw [if_pos hx, if_pos hx]
      have hj : b.size - (i + 1) + c + 2 = d + c + 2 := by omega
      simp only [unzz, hj, gatherEmit]
      by_cases he : (acc * 128 + b[i].toNat) % 2 = 0
      · simp only [he, beq_self_eq_true, if_true]
        by_cases hv : prev + (acc * 128 + b[i].toNat) / 2 < two64
        · simp only [hv, if_true]
        · simp only [hv, if_false]
      · have he2 : ((acc * 128 + b[i].toNat) % 2 == 0) = false := by simpa using he
        simp only [he2, he, Bool.false_eq_true, if_false]
        by_cases hle : (acc * 128 + b[i].toNat + 1) / 2 ≤ prev
        · simp only [hle, if_true, show prev - (acc * 128 + b[i].toNat + 1) / 2 < two64 by omega]
        · simp only [hle, if_false]
    · rw [if_neg hx, if_neg hx]
      exact ih _ _ (by omega) (by omega)

/-- The gather loop over a delta frame whose next `K` values (from position
    `i`) are `val idx, ..., val (idx + K - 1)`, for strictly increasing rows
    `pos[kk..]` in `[idx, idx + K)`: it appends the words of those rows'
    values. -/
theorem deltaGatherGo_eq (b : ByteArray) (pos : Array Nat) (c : Nat) (val : Nat → Nat)
    (hinc : ∀ m m', m < m' → m' < pos.size → pos[m]! < pos[m']!) :
    ∀ K idx prev i kk (out : ByteArray) (a : Array Nat) (j : Nat),
      prev < two64 → i ≤ b.size →
      deltaAtGo b K prev i #[] = some (a, j) →
      (∀ t, idx ≤ t → t < idx + K → a[t - idx]! = val t) →
      (∀ m, kk ≤ m → m < pos.size → idx ≤ pos[m]! ∧ pos[m]! < idx + K) →
      ∃ out', deltaGatherGo b pos (b.size - i + c + 2) idx prev i 0 kk out = some out' ∧
        out'.data.toList = out.data.toList ++ ((pos.toList.drop kk).map fun t => Column.put64 (val t)).flatten := by
  intro K
  induction K with
  | zero =>
    intro idx prev i kk out a j _ _ _ _ hpos
    have hkk : pos.size ≤ kk := by
      apply Nat.le_of_not_lt
      intro hlt
      have := hpos kk (Nat.le_refl _) hlt
      omega
    refine ⟨out, ?_, by rw [List.drop_eq_nil_of_le (by rw [Array.length_toList]; omega)]; simp⟩
    rw [show b.size - i + c + 2 = (b.size - i + c + 1) + 1 by omega, deltaGatherGo.eq_2, if_pos hkk]
  | succ K ih =>
    intro idx prev i kk out a j hp hib hda hval hpos
    by_cases hkk : kk ≥ pos.size
    · refine ⟨out, ?_, by rw [List.drop_eq_nil_of_le (by rw [Array.length_toList]; omega)]; simp⟩
      rw [show b.size - i + c + 2 = (b.size - i + c + 1) + 1 by omega, deltaGatherGo.eq_2, if_pos hkk]
    have hk : kk < pos.size := by omega
    rw [deltaGatherGo_step b pos c idx prev kk out hp hk (b.size - i) 0 i rfl hib]
    simp only [deltaAtGo, getVarAt] at hda
    cases hv : getVarAtGo b (b.size - i) 0 i with
    | none => rw [hv] at hda; cases hda
    | some zj =>
      obtain ⟨z, j1⟩ := zj
      rw [hv] at hda
      have hj1 := FrameWords.getVarAtGo_le b _ _ _ _ _ hv
      simp only at hda ⊢
      cases hu : unzz prev z with
      | none => rw [hu] at hda; cases hda
      | some v =>
        rw [hu] at hda
        simp only at hda ⊢
        by_cases hvl : v < two64
        · rw [if_pos hvl] at hda
          rw [if_pos hvl]
          rw [FrameWords.deltaAtGo_acc] at hda
          cases hr : deltaAtGo b K v j1 #[] with
          | none => rw [hr] at hda; cases hda
          | some r =>
            obtain ⟨a', j'⟩ := r
            rw [hr] at hda
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hda
            obtain ⟨ha, hj⟩ := hda
            subst hj
            have ha' : a = #[v] ++ a' := by rw [← ha]; rfl
            have hv0 : val idx = v := by
              have := hval idx (Nat.le_refl _) (by omega)
              rw [Nat.sub_self, ha', getElem!_append_zero] at this
              exact this.symm
            have hval' : ∀ t, idx + 1 ≤ t → t < idx + 1 + K → a'[t - (idx + 1)]! = val t := by
              intro t h1 h2
              have := hval t (by omega) (by omega)
              rw [ha', show t - idx = (t - (idx + 1)) + 1 by omega, getElem!_append_one] at this
              exact this
            have hdrop : pos.toList.drop kk = pos[kk]! :: pos.toList.drop (kk + 1) := by
              rw [getElem!_pos pos kk hk, List.drop_eq_getElem_cons (by rw [Array.length_toList]; exact hk)]
              simp
            unfold gatherEmit
            by_cases he : idx = pos[kk]!
            · rw [if_pos (by simp [he])]
              obtain ⟨out', h1, h2⟩ := ih (idx + 1) v j1 (kk + 1) (put64 out v.toUInt64) a' j' hvl hj1 hr hval'
                (fun m h1 h2 => by
                  have := hpos m (by omega) h2
                  have := hinc kk m (by omega) h2
                  omega)
              refine ⟨out', h1, ?_⟩
              rw [h2, hdrop, FrameWords.put64_data, List.map_cons, List.flatten_cons, ← he, hv0]
              simp
            · rw [if_neg (by simp [he])]
              obtain ⟨out', h1, h2⟩ := ih (idx + 1) v j1 kk out a' j' hvl hj1 hr hval'
                (fun m h1 h2 => by
                  have hm := hpos m h1 h2
                  have hk0 := hpos kk (Nat.le_refl _) hk
                  have : pos[kk]! ≤ pos[m]! := by
                    rcases Nat.eq_or_lt_of_le h1 with e | l
                    · subst e; exact Nat.le_refl _
                    · exact Nat.le_of_lt (hinc kk m l h2)
                  omega)
              exact ⟨out', h1, h2⟩
        · rw [if_neg hvl] at hda; cases hda

/-! ## `gatherWords` -/

/-- **The gather.** On a frame that decodes to the words `ws`, for strictly
    increasing rows `pos` below the row count `n`, `gatherWords` returns the
    words of those rows. -/
theorem gatherWords_spec (b : ByteArray) (n i : Nat) (pos : Array Nat) (ws : ByteArray) (j : Nat)
    (h : FrameWords.decodeWords b n i = some (ws, j))
    (hinc : ∀ m m', m < m' → m' < pos.size → pos[m]! < pos[m']!) (hlt : ∀ m, m < pos.size → pos[m]! < n) :
    ∃ out, gatherWords b n i pos = some out ∧
      out.data.toList = (pos.toList.map fun r => Column.put64 (word64 ws (8 * r)).toNat).flatten := by
  unfold gatherWords
  by_cases hd : (i < b.size && b.get! i == tagDelta) = true
  · rw [if_pos hd]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hd
    rw [deltaGatherStart_eq b pos i hd.1]
    obtain ⟨a, j', ha, hws, hsz, hv⟩ := decodeWords_delta b n i ws j hd.1 hd.2 h
    obtain ⟨out', h1, h2⟩ := deltaGatherGo_eq b pos 1 (fun t => a[t]!) hinc n 0 0 (i + 1) 0
      (ByteArray.emptyWithCapacity (8 * pos.size)) a j' (by decide) (by omega) ha
      (fun t _ _ => by rw [Nat.sub_zero]) (fun m _ hm => ⟨Nat.zero_le _, by have := hlt m hm; omega⟩)
    rw [show b.size - (i + 1) + 1 + 2 = b.size - i + 2 by omega] at h1
    refine ⟨out', h1, ?_⟩
    rw [h2]
    show [] ++ _ = _
    rw [List.nil_append, List.drop_zero]
    congr 1
    apply List.map_congr_left
    intro r hr
    obtain ⟨m, hm, he⟩ := List.getElem_of_mem hr
    have hm' : m < pos.size := by simpa using hm
    have := hlt m hm'
    rw [getElem!_pos pos m hm'] at this
    simp only [Array.getElem_toList] at he
    rw [he] at this
    rw [hws, word64_words a r (by omega) hv]
  · rw [if_neg hd, h]
    exact ⟨_, rfl, pickWords_data ws pos⟩

#print axioms sorted_spec
#print axioms probe_mem
#print axioms mayHold_false
#print axioms wordsFindGo_spec
#print axioms deltaFindGo_eq
#print axioms findWords_spec
#print axioms deltaGatherGo_eq
#print axioms gatherWords_spec
#print axioms pickWords_data

end L4Factoidal.Storage.Sbm11.Sip
