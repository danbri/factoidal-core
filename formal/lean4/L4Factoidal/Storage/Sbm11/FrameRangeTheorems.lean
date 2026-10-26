/-
L4Factoidal.Storage.Sbm11.FrameRangeTheorems — the query path's row-range
frame decoder (`FrameWords.decodeWordsRange`) gives the rows `[lo, hi)` of
the words of the whole frame (lemma L2 of
`docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md`;
https://github.com/danbri/factoidal/issues/776).

* `deltaRangeGo_step`, `deltaRangeGo_eq`: the range loop equals `deltaAtGo`
  over the first `hi` rows, keeping the rows from `lo`.
* `deltaAtGo_prefix`: the first `k` rows of a delta frame decode to the
  first `k` values of the whole frame.
* `decodeWordsRange_eq`: when the frame of `n ≤ 2^64` rows decodes to the
  words `ws` (`decodeWords b n i = some (ws, j)`), then for `lo ≤ hi ≤ n`,
  `decodeWordsRange b n i lo hi = some (ws.extract (8 * lo) (8 * hi))`.

The hypothesis that the whole frame decodes is what the generation gives:
activation decodes every frame of every block. Without it the range decoder
can answer where the whole-frame decoder refuses (it does not read past row
`hi - 1`); that is its purpose and is not a defect.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.FrameWordsTheorems

namespace L4Factoidal.Storage.Sbm11.FrameWords

open L4Factoidal (two64)
open L4Factoidal.Storage.Sbm11.Column (getVarAtGo getVarAt deltaAtGo unzz tagConst tagRaw tagDelta)
open L4Factoidal.Storage.Sbm11.Dict (bytesToList bytesToList_length bytesToList_extract)

private theorem byte_get!' (b : ByteArray) (i : Nat) (h : i < b.size) : b.get! i = b[i] := by
  simp [ByteArray.get!, ByteArray.getElem_eq_getElem_data, getElem!_pos, h]

/-! ## Words of a list of values -/

theorem put64_length (v : Nat) : (Column.put64 v).length = 8 := rfl

theorem drop_flatten_put64 : ∀ (l : List Nat) (k : Nat),
    ((l.map Column.put64).flatten).drop (8 * k) = ((l.drop k).map Column.put64).flatten := by
  intro l
  induction l with
  | nil => intro k; simp
  | cons x xs ih =>
    intro k
    cases k with
    | zero => simp
    | succ k =>
      rw [List.map_cons, List.flatten_cons, show 8 * (k + 1) = (Column.put64 x).length + 8 * k by
        rw [put64_length]; omega, List.drop_length_add_append, ih]
      rfl

theorem take_flatten_put64 : ∀ (l : List Nat) (k : Nat),
    ((l.map Column.put64).flatten).take (8 * k) = ((l.take k).map Column.put64).flatten := by
  intro l
  induction l with
  | nil => intro k; simp
  | cons x xs ih =>
    intro k
    cases k with
    | zero => simp
    | succ k =>
      rw [List.map_cons, List.flatten_cons, show 8 * (k + 1) = (Column.put64 x).length + 8 * k by
        rw [put64_length]; omega, List.take_length_add_append, ih]
      rfl

theorem drop_flatten_replicate (L : List UInt8) (hL : L.length = 8) :
    ∀ n k, k ≤ n → ((List.replicate n L).flatten).drop (8 * k) = (List.replicate (n - k) L).flatten := by
  intro n
  induction n with
  | zero => intro k hk; have : k = 0 := by omega
            subst this; simp
  | succ n ih =>
    intro k hk
    cases k with
    | zero => simp
    | succ k =>
      rw [List.replicate_succ, List.flatten_cons, show 8 * (k + 1) = L.length + 8 * k by omega,
        List.drop_length_add_append, ih k (by omega)]
      congr 2
      omega

/-! ## The delta range loop -/

/-- One row of the range loop is one varint of `getVarAtGo` (`c` is the
    fuel above the minimum). -/
theorem deltaRangeGo_step (b : ByteArray) (lo hi c idx prev : Nat) (out : ByteArray)
    (hp : prev < two64) (hidx : idx < hi) :
    ∀ d acc i, b.size - i = d → i ≤ b.size →
      deltaRangeGo b lo hi (d + c + 2) idx prev i acc out =
        match getVarAtGo b d acc i with
        | none => none
        | some (z, j) =>
          match unzz prev z with
          | none => none
          | some v => if v < two64 then
              deltaRangeGo b lo hi (b.size - j + c + 2) (idx + 1) v j 0
                (if idx ≥ lo then put64 out v.toUInt64 else out)
            else none := by
  intro d
  induction d with
  | zero =>
    intro acc i hd hi'
    have : i = b.size := by omega
    subst this
    rw [show 0 + c + 2 = (c + 1) + 1 by omega, deltaRangeGo.eq_2]
    simp only [show ¬ (idx ≥ hi) by omega, if_false, Nat.lt_irrefl]
    simp [getVarAtGo]
  | succ d ih =>
    intro acc i hd hi'
    have hlt : i < b.size := by omega
    rw [show d + 1 + c + 2 = (d + c + 2) + 1 by omega, deltaRangeGo.eq_2, getVarAtGo.eq_2]
    simp only [show ¬ (idx ≥ hi) by omega, if_false, if_pos hlt, byte_get!' b i hlt, dif_pos hlt]
    by_cases hx : b[i].toNat < 128
    · rw [if_pos hx, if_pos hx]
      have hj : b.size - (i + 1) + c + 2 = d + c + 2 := by omega
      simp only [unzz, hj]
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

theorem deltaRangeGo_eq (b : ByteArray) (lo hi c : Nat) :
    ∀ k idx prev i (out : ByteArray), k = hi - idx → idx ≤ hi → prev < two64 → i ≤ b.size →
      (deltaRangeGo b lo hi (b.size - i + c + 2) idx prev i 0 out).map (fun r => r.data.toList) =
        (deltaAtGo b k prev i #[]).map
          (fun r => out.data.toList ++ ((r.1.toList.drop (lo - idx)).map Column.put64).flatten) := by
  intro k
  induction k with
  | zero =>
    intro idx prev i out hk hih _ _
    rw [show b.size - i + c + 2 = (b.size - i + c + 1) + 1 by omega, deltaRangeGo.eq_2]
    rw [if_pos (by omega)]
    simp [deltaAtGo]
  | succ k ih =>
    intro idx prev i out hk hih hp hib
    rw [deltaRangeGo_step b lo hi c idx prev out hp (by omega) (b.size - i) 0 i rfl hib]
    simp only [deltaAtGo, getVarAt]
    cases hv : getVarAtGo b (b.size - i) 0 i with
    | none => rfl
    | some p =>
      obtain ⟨z, j⟩ := p
      have hj := getVarAtGo_le b _ _ _ _ _ hv
      dsimp only
      cases hu : unzz prev z with
      | none => rfl
      | some v =>
        dsimp only
        by_cases hvl : v < two64
        · rw [if_pos hvl, if_pos hvl, ih (idx + 1) v j _ (by omega) (by omega) hvl hj,
            deltaAtGo_acc b k v j (#[].push v)]
          simp only [Option.map_map]
          congr 1
          funext r
          simp only [Function.comp]
          by_cases hl : idx ≥ lo
          · rw [if_pos hl, put64_data]
            have e1 : lo - idx = 0 := by omega
            have e2 : lo - (idx + 1) = 0 := by omega
            simp [e1, e2]
          · rw [if_neg hl]
            have e1 : lo - idx = (lo - (idx + 1)) + 1 := by omega
            simp [e1]
        · rw [if_neg hvl, if_neg hvl]; rfl

theorem deltaAtGo_prefix (b : ByteArray) : ∀ k m prev i (acc : Array Nat) a j,
    deltaAtGo b (k + m) prev i acc = some (a, j) →
      ∃ a' j', deltaAtGo b k prev i acc = some (a', j') ∧ a'.toList = a.toList.take (acc.size + k) := by
  intro k
  induction k with
  | zero =>
    intro m prev i acc a j h
    refine ⟨acc, i, by simp [deltaAtGo], ?_⟩
    rw [deltaAtGo_acc] at h
    cases hr : deltaAtGo b (0 + m) prev i #[] with
    | none => rw [hr] at h; cases h
    | some r =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      simp
  | succ k ih =>
    intro m prev i acc a j h
    rw [show k + 1 + m = (k + m) + 1 by omega] at h
    simp only [deltaAtGo] at h ⊢
    split at h
    · cases h
    · rename_i z j1 _
      try dsimp only at h ⊢
      split at h
      · cases h
      · rename_i v _
        try dsimp only at h ⊢
        split at h
        · rename_i hvl
          rw [if_pos hvl]
          obtain ⟨a', j', h1, h2⟩ := ih m v j1 (acc.push v) a j h
          refine ⟨a', j', h1, ?_⟩
          rw [h2, Array.size_push]
          congr 1
          omega
        · cases h

theorem deltaAtGo_size (b : ByteArray) : ∀ n prev i (acc : Array Nat) a j,
    deltaAtGo b n prev i acc = some (a, j) → a.size = acc.size + n := by
  intro n
  induction n with
  | zero => intro prev i acc a j h; simp only [deltaAtGo, Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1]; rfl
  | succ n ih =>
    intro prev i acc a j h
    simp only [deltaAtGo] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · have := ih _ _ _ _ _ h
          rw [this, Array.size_push]; omega
        · cases h

/-! ## The range decoder -/

/-- When the frame of `n ≤ 2^64` rows at `i` decodes to the words `ws`, the
    range decoder gives the words of rows `[lo, hi)`. -/
theorem decodeWordsRange_eq (b : ByteArray) (n i lo hi : Nat) (ws : ByteArray) (j : Nat)
    (hn : n ≤ two64) (hlh : lo ≤ hi) (hhi : hi ≤ n) (h : decodeWords b n i = some (ws, j)) :
    decodeWordsRange b n i lo hi = some (ws.extract (8 * lo) (8 * hi)) := by
  unfold decodeWords at h
  unfold decodeWordsRange
  rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)]
  by_cases hi0 : i < b.size
  · rw [if_pos hi0] at h ⊢
    by_cases t0 : (b.get! i == tagConst) = true
    · rw [if_pos t0] at h ⊢
      by_cases h9 : i + 9 ≤ b.size
      · rw [if_pos h9] at h ⊢
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        congr 1
        have hsz : (b.extract (i + 1) (i + 9)).size = 8 := by
          rw [ByteArray.size_extract]; omega
        have hL : (b.extract (i + 1) (i + 9)).data.toList.length = 8 := by
          rw [Array.length_toList]; exact hsz
        apply ByteArray.ext
        apply Array.toList_inj.mp
        have hrhs : ((repeatWords (b.extract (i + 1) (i + 9)) n).extract (8 * lo) (8 * hi)).data.toList =
            (((repeatWords (b.extract (i + 1) (i + 9)) n).data.toList).drop (8 * lo)).take (8 * hi - 8 * lo) := by
          simp only [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
        rw [hrhs, repeatWords_data _ hsz (hi - lo) (by omega), repeatWords_data _ hsz _ hn,
          drop_flatten_replicate _ hL n lo (by omega),
          show 8 * hi - 8 * lo = 8 * (hi - lo) by omega,
          take_flatten_replicate _ hL (n - lo) (hi - lo) (by omega)]
      · rw [if_neg h9] at h; cases h
    · rw [if_neg t0] at h ⊢
      by_cases t1 : (b.get! i == tagRaw) = true
      · rw [if_pos t1] at h ⊢
        by_cases hr : i + 1 + 8 * n ≤ b.size
        · rw [if_pos hr] at h ⊢
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          congr 1
          apply ByteArray.ext
          apply Array.toList_inj.mp
          simp only [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
            List.drop_take, List.take_take, List.drop_drop]
          congr 1
          omega
        · rw [if_neg hr] at h; cases h
      · rw [if_neg t1] at h ⊢
        by_cases t2 : (b.get! i == tagDelta) = true
        · rw [if_pos t2] at h ⊢
          unfold deltaWords at h
          -- the whole frame: its values `a`
          have hw := deltaGo_eq b n 0 (i + 1) (ByteArray.emptyWithCapacity (8 * n)) (by decide) (by omega)
          rw [show b.size - (i + 1) + 2 = b.size - (i + 1) + 2 from rfl, h] at hw
          cases ha : deltaAtGo b n 0 (i + 1) #[] with
          | none => rw [ha] at hw; cases hw
          | some r =>
            obtain ⟨a, j'⟩ := r
            rw [ha] at hw
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hw
            have hws : ws.data.toList = (a.toList.map Column.put64).flatten := by
              rw [hw.1]; rfl
            have hasz := deltaAtGo_size b _ _ _ _ _ _ ha
            -- the first `hi` rows
            obtain ⟨a', j2, ha', hpre⟩ := deltaAtGo_prefix b hi (n - hi) 0 (i + 1) #[] a j'
              (by rw [show hi + (n - hi) = n by omega]; exact ha)
            have hr := deltaRangeGo_eq b lo hi 1 hi 0 0 (i + 1)
              (ByteArray.emptyWithCapacity (8 * (hi - lo))) (by omega) (by omega) (by decide) (by omega)
            rw [show b.size - (i + 1) + 1 + 2 = b.size - i + 2 by omega, ha'] at hr
            cases hq : deltaRangeGo b lo hi (b.size - i + 2) 0 0 (i + 1) 0
                (ByteArray.emptyWithCapacity (8 * (hi - lo))) with
            | none => rw [hq] at hr; cases hr
            | some q =>
              rw [hq] at hr
              simp only [Option.map_some, Option.some.injEq] at hr
              congr 1
              apply ByteArray.ext
              apply Array.toList_inj.mp
              rw [hr, ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop, hws,
                drop_flatten_put64, show 8 * hi - 8 * lo = 8 * (hi - lo) by omega, take_flatten_put64,
                hpre]
              simp only [Array.size_empty, Nat.zero_add, Nat.sub_zero]
              show [] ++ _ = _
              rw [List.nil_append, List.drop_take]
        · rw [if_neg t2] at h; cases h
  · rw [if_neg hi0] at h; cases h

end L4Factoidal.Storage.Sbm11.FrameWords
