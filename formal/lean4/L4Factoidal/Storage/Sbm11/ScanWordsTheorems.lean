/-
L4Factoidal.Storage.Sbm11.ScanWordsTheorems — the scan's word reads are the
decoded ids, so its in-block row range is exact over the decoded columns
(lemmas L2g and L4c of
`docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md`;
https://github.com/danbri/factoidal/issues/776).

* `word64_bytes`: `Codec.Zstd.word64` is the little-endian value of its
  eight bytes.
* `at64_words`: `at64 (words xs) r = xs[r].toUInt64` (the word read the
  scan does on a decoded column).
* `rowKeyCmp_words`: over the words of the key columns, `rowKeyCmp` is
  `prefixCmp` of the row, for ids below `2^64` and a key of at most four
  columns.
* `scanRows_exact`: for a block whose decoded rows are strictly increasing,
  the two binary searches of `scanFoldM` over the words of its key columns
  select exactly the rows whose key prefix equals the key.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.ScanTheorems
import L4Factoidal.Storage.Sbm11.FrameRangeTheorems

namespace L4Factoidal.Storage.Sbm11.ScanTheorems

open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.FrameWords (words words_data drop_flatten_put64)
open L4Factoidal.Codec.Zstd (word64)
open L4Factoidal (two64)

/-! ## The word read -/

theorem or_mul (A x M n : Nat) (hM : M = 2 ^ n) (hA : A < M) : A ||| x * M = A + x * M := by
  subst hM
  rw [Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hA, Nat.shiftLeft_eq]
  omega

theorem word64_bytes (d : ByteArray) (i : Nat) (h : i + 8 ≤ d.size) :
    (word64 d i).toNat = d[i].toNat + d[i+1].toNat * 256 + d[i+2].toNat * 65536 +
      d[i+3].toNat * 16777216 + d[i+4].toNat * 4294967296 + d[i+5].toNat * 1099511627776 +
      d[i+6].toNat * 281474976710656 + d[i+7].toNat * 72057594037927936 := by
  unfold word64
  rw [dif_pos h]
  have h0 := d[i].toNat_lt
  have h1 := (d[i+1]'(by omega)).toNat_lt
  have h2 := (d[i+2]'(by omega)).toNat_lt
  have h3 := (d[i+3]'(by omega)).toNat_lt
  have h4 := (d[i+4]'(by omega)).toNat_lt
  have h5 := (d[i+5]'(by omega)).toNat_lt
  have h6 := (d[i+6]'(by omega)).toNat_lt
  have h7 := (d[i+7]'(by omega)).toNat_lt
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64]
  simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.shiftLeft_eq] at *
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  rw [or_mul _ _ 256 8 rfl (by omega), or_mul _ _ 65536 16 rfl (by omega),
    or_mul _ _ 16777216 24 rfl (by omega), or_mul _ _ 4294967296 32 rfl (by omega),
    or_mul _ _ 1099511627776 40 rfl (by omega), or_mul _ _ 281474976710656 48 rfl (by omega),
    or_mul _ _ 72057594037927936 56 rfl (by omega)]

private theorem flatten_put64_length (l : List Nat) :
    ((l.map Column.put64).flatten).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, ih, List.length_cons,
      FrameWords.put64_length]
    omega

private theorem words_size (xs : Array Nat) : (words xs).size = 8 * xs.size := by
  show (words xs).data.size = _
  rw [← Array.length_toList, words_data, flatten_put64_length, Array.length_toList]

/-- Byte `8 r + k` of the words of `xs` is byte `k` of `Column.put64 xs[r]`. -/
private theorem words_byte (xs : Array Nat) (r k i : Nat) (hi : i = 8 * r + k) (hr : r < xs.size)
    (hk : k < 8) (h : i < (words xs).size) :
    (words xs)[i] = (Column.put64 xs[r])[k]'(by rw [FrameWords.put64_length]; exact hk) := by
  subst hi
  have e1 : (words xs)[8 * r + k] = (words xs).data.toList[8 * r + k]'(by
      rw [Array.length_toList]; exact h) := by
    simp [ByteArray.getElem_eq_getElem_data]
  rw [e1]
  have hd : ((words xs).data.toList.drop (8 * r)) =
      Column.put64 xs[r] ++ ((xs.toList.drop (r + 1)).map Column.put64).flatten := by
    rw [words_data, drop_flatten_put64, List.drop_eq_getElem_cons (by simpa using hr)]
    simp
  have := congrArg (fun l => l[k]?) hd
  simp only [List.getElem?_drop] at this
  rw [List.getElem?_append_left (by rw [FrameWords.put64_length]; exact hk)] at this
  rw [List.getElem?_eq_getElem (by rw [Array.length_toList]; exact h),
    List.getElem?_eq_getElem (by rw [FrameWords.put64_length]; exact hk)] at this
  simpa using this

/-- The scan's word read on a decoded column is the id. -/
theorem at64_words (xs : Array Nat) (r : Nat) (hr : r < xs.size) :
    at64 (words xs) r = xs[r].toUInt64 := by
  have hs := words_size xs
  unfold at64
  apply UInt64.toNat_inj.mp
  rw [word64_bytes _ _ (by omega)]
  rw [words_byte xs r 0 (8 * r) (by omega) hr (by omega) (by omega),
    words_byte xs r 1 (8 * r + 1) rfl hr (by omega) (by omega),
    words_byte xs r 2 (8 * r + 2) rfl hr (by omega) (by omega),
    words_byte xs r 3 (8 * r + 3) rfl hr (by omega) (by omega),
    words_byte xs r 4 (8 * r + 4) rfl hr (by omega) (by omega),
    words_byte xs r 5 (8 * r + 5) rfl hr (by omega) (by omega),
    words_byte xs r 6 (8 * r + 6) rfl hr (by omega) (by omega),
    words_byte xs r 7 (8 * r + 7) rfl hr (by omega) (by omega)]
  simp only [Column.put64, List.getElem_cons_succ, List.getElem_cons_zero, Nat.toUInt8,
    UInt8.toNat_ofNat', Nat.toUInt64, UInt64.toNat_ofNat']
  omega

/-! ## The key comparison over words -/

/-- The four decoded columns of a block. -/
def colOf (c0 c1 c2 g : Array Nat) : Nat → Array Nat
  | 0 => c0
  | 1 => c1
  | 2 => c2
  | _ => g

/-- Row `r` of four decoded columns. -/
def rowOf (c0 c1 c2 g : Array Nat) (r : Nat) : Row := ⟨c0[r]!, c1[r]!, c2[r]!, g[r]!⟩

theorem rowKeyCmpGo_words (c0 c1 c2 g : Array Nat) (key : Array UInt64) (r : Nat)
    (cols : Array ByteArray) (hkey : key.size ≤ 4)
    (hcols : ∀ j, j < key.size → cols[j]! = words (colOf c0 c1 c2 g j))
    (hr : ∀ j, j < 4 → r < (colOf c0 c1 c2 g j).size)
    (hv : ∀ j, j < 4 → (colOf c0 c1 c2 g j)[r]! < two64) :
    ∀ f j, rowKeyCmpGo cols key r f j = prefixCmpGo (rowOf c0 c1 c2 g r) key f j := by
  intro f
  induction f with
  | zero => intro j; rfl
  | succ f ih =>
    intro j
    simp only [rowKeyCmpGo, prefixCmpGo]
    by_cases hj : j < key.size
    · rw [if_pos hj, if_pos hj]
      have hj4 : j < 4 := by omega
      have hw : at64 cols[j]! r = (colOf c0 c1 c2 g j)[r]!.toUInt64 := by
        rw [hcols j hj, at64_words _ _ (hr j hj4), getElem!_pos (colOf c0 c1 c2 g j) r (hr j hj4)]
      have hrc : rowCol (rowOf c0 c1 c2 g r) j = (colOf c0 c1 c2 g j)[r]! := by
        match j, hj4 with
        | 0, _ => rfl
        | 1, _ => rfl
        | 2, _ => rfl
        | 3, _ => rfl
      rw [hw, hrc]
      have hlt := hv j hj4
      simp only [two64] at hlt
      have e1 : ((colOf c0 c1 c2 g j)[r]!.toUInt64 < key[j]!) ↔ ((colOf c0 c1 c2 g j)[r]! < key[j]!.toNat) := by
        rw [UInt64.lt_iff_toNat_lt, Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
      have e2 : (key[j]! < (colOf c0 c1 c2 g j)[r]!.toUInt64) ↔ (key[j]!.toNat < (colOf c0 c1 c2 g j)[r]!) := by
        rw [UInt64.lt_iff_toNat_lt, Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
      by_cases h1 : (colOf c0 c1 c2 g j)[r]! < key[j]!.toNat
      · rw [if_pos (e1.mpr h1), if_pos h1]
      · rw [if_neg (fun h => h1 (e1.mp h)), if_neg h1]
        by_cases h2 : key[j]!.toNat < (colOf c0 c1 c2 g j)[r]!
        · rw [if_pos (e2.mpr h2), if_pos h2]
        · rw [if_neg (fun h => h2 (e2.mp h)), if_neg h2]
          exact ih (j + 1)
    · rw [if_neg hj, if_neg hj]

/-- Over the words of the key columns, `rowKeyCmp` is `prefixCmp` of the
    decoded row. -/
theorem rowKeyCmp_words (c0 c1 c2 g : Array Nat) (key : Array UInt64) (r : Nat)
    (cols : Array ByteArray) (hkey : key.size ≤ 4)
    (hcols : ∀ j, j < key.size → cols[j]! = words (colOf c0 c1 c2 g j))
    (hr : ∀ j, j < 4 → r < (colOf c0 c1 c2 g j).size)
    (hv : ∀ j, j < 4 → (colOf c0 c1 c2 g j)[r]! < two64) :
    rowKeyCmp cols key r = prefixCmp (rowOf c0 c1 c2 g r) key :=
  rowKeyCmpGo_words c0 c1 c2 g key r cols hkey hcols hr hv _ 0

/-- For a block whose decoded rows are strictly increasing and whose ids are
    below `2^64`, the two binary searches of `scanFoldM` over the words of
    its key columns select exactly the rows whose key prefix equals the key. -/
theorem scanRows_exact (c0 c1 c2 g : Array Nat) (n : Nat) (key : Array UInt64)
    (cols : Array ByteArray) (hkey : key.size ≤ 4)
    (hcols : ∀ j, j < key.size → cols[j]! = words (colOf c0 c1 c2 g j))
    (hsize : ∀ j, j < 4 → (colOf c0 c1 c2 g j).size = n)
    (hv : ∀ j r, j < 4 → r < n → (colOf c0 c1 c2 g j)[r]! < two64)
    (hsorted : ∀ r s, r < s → s < n → (rowOf c0 c1 c2 g r).lt (rowOf c0 c1 c2 g s) = true)
    (r : Nat) (hr : r < n) :
    (keyBound cols key false (Nat.log2 n + 2) 0 n ≤ r ∧
      r < keyBound cols key true (Nat.log2 n + 2) (keyBound cols key false (Nat.log2 n + 2) 0 n) n) ↔
      prefixCmp (rowOf c0 c1 c2 g r) key = .eq := by
  have hcmp : ∀ s, s < n → rowKeyCmp cols key s = prefixCmp (rowOf c0 c1 c2 g s) key := by
    intro s hs
    exact rowKeyCmp_words c0 c1 c2 g key s cols hkey hcols (fun j hj => by rw [hsize j hj]; exact hs)
      (fun j hj => hv j s hj hs)
  rw [← hcmp r hr]
  apply blockRows_exact cols key n _ r hr
  intro a b hab hb
  rw [hcmp a (by omega), hcmp b hb]
  have hle : (rowOf c0 c1 c2 g a).le (rowOf c0 c1 c2 g b) = true := by
    rcases Nat.lt_or_eq_of_le hab with h | h
    · exact le_of_lt (hsorted a b h hb)
    · subst h; exact le_refl _
  exact ⟨prefixCmp_lt_of_le key hle, prefixCmp_gt_of_le key hle⟩

/-! ## `rowKeyCmp` before the refactor, compared on samples

`rowKeyCmp` was a `for` loop with early `return` until 2026-10-12; it is now
the tail call `rowKeyCmpGo`. -/

private def rowKeyCmpOld (cols : Array ByteArray) (key : Array UInt64) (r : Nat) : Ordering := Id.run do
  for j in [0:key.size] do
    let a := at64 cols[j]! r
    let b := key[j]!
    if a < b then return .lt
    if b < a then return .gt
  return .eq

private def sampleCols : Array ByteArray :=
  #[words #[1, 1, 1, 2, 7], words #[2, 2, 5, 0, 7], words #[3, 4, 0, 0, 7], words #[0, 0, 0, 0, 7]]

#guard [#[], #[1], #[1, 2], #[1, 2, 3], #[1, 2, 4, 0], #[2], #[7, 7, 7, 7], #[0], #[9, 9]].all fun (k : Array UInt64) =>
  (List.range 6).all fun r => rowKeyCmp sampleCols k r == rowKeyCmpOld sampleCols k r

end L4Factoidal.Storage.Sbm11.ScanTheorems
