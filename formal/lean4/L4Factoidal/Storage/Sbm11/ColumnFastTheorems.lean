/-
L4Factoidal.Storage.Sbm11.ColumnFastTheorems — the packer's frame encoder
`Column.encodeColumnFast` writes the bytes of the specification frame
`Column.frameBytes` (https://github.com/danbri/factoidal/issues/776; row L3c
of docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

* `pushU64_data`, `pushVar_data`: one 64-bit word and one varint, pushed on a
  byte array, append `put64` and `putVar`;
* `digits`: the base-128 digits of a number, most significant first, each
  with the continuation bit; `vbeGo_eq` and `pushVarGo_eq` show that the two
  varint loops write them;
* `encodeColumnFast_eq`: `(encodeColumnFast xs).data.toList = frameBytes
  xs.toList` for every array `xs`.

With it the packer needs no decoding of its own frames to know them: the
round trip of `frameBytes` is `BlockTheorems.decodeFrame_frameBytes`.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.ColumnTheorems

namespace L4Factoidal.Storage.Sbm11.Column

/-! ## Words -/

theorem pushU64_data (out : ByteArray) (v : Nat) :
    (pushU64 out v).data.toList = out.data.toList ++ put64 v := by
  simp [pushU64, put64, ByteArray.data_push, Array.toList_push]

/-! ## Varints -/

/-- The number of base-128 digits of `m` (0 for 0). -/
def ndigits (m : Nat) : Nat := if m = 0 then 0 else ndigits (m / 128) + 1
decreasing_by omega

/-- The base-128 digits of `m`, most significant first, each with the
    continuation bit. -/
def digits (m : Nat) : List UInt8 :=
  (List.range (ndigits m)).reverse.map fun i => ((m / 128 ^ i) % 128 + 128).toUInt8

theorem ndigits_pos (m : Nat) (h : m ≠ 0) : ndigits m = ndigits (m / 128) + 1 := by
  rw [ndigits]; simp [h]

theorem digits_step (m : Nat) (h : m ≠ 0) :
    digits m = digits (m / 128) ++ [((m % 128) + 128).toUInt8] := by
  unfold digits
  rw [ndigits_pos m h, List.range_succ_eq_map, List.reverse_cons, List.map_append, List.map_reverse,
    List.map_map, List.map_reverse]
  simp only [List.map_cons, List.map_nil, Nat.pow_zero, Nat.div_one]
  congr 2
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.succ_eq_add_one, Nat.pow_succ, Nat.div_div_eq_div_mul,
    Nat.mul_comm 128 (128 ^ i)]

theorem digits_zero : digits 0 = [] := by
  simp [digits, ndigits]

theorem vbeGo_eq : ∀ (f m : Nat) (acc : List UInt8), m ≤ f → vbeGo f m acc = digits m ++ acc
  | 0, m, acc, h => by
    have : m = 0 := by omega
    subst this
    simp [vbeGo, digits_zero]
  | f + 1, m, acc, h => by
    unfold vbeGo
    by_cases hm : m = 0
    · subst hm; simp [digits_zero]
    · rw [if_neg hm, vbeGo_eq f (m / 128) _ (by omega), digits_step m hm]
      simp

theorem putVar_eq (n : Nat) (rest : List UInt8) :
    putVar n rest = digits (n / 128) ++ (n % 128).toUInt8 :: rest := by
  unfold putVar
  exact vbeGo_eq _ _ _ (Nat.div_le_self n 128)

theorem pushVarGo_eq (n : Nat) : ∀ (j : Nat) (out : ByteArray),
    (pushVarGo n j out).data.toList = out.data.toList ++
      (List.range j).reverse.map (fun i => ((n / 128 ^ (i + 1)) % 128 + 128).toUInt8) ++
        [(n % 128).toUInt8]
  | 0, out => by simp [pushVarGo, ByteArray.data_push, Array.toList_push]
  | j + 1, out => by
    rw [pushVarGo, pushVarGo_eq n j]
    simp only [ByteArray.data_push, Array.toList_push, List.range_succ, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.cons_append, List.singleton_append]
    congr 3
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem varExtraGo_eq : ∀ (f n c : Nat), n ≤ f → varExtraGo f n c = c + ndigits (n / 128)
  | 0, n, c, h => by
    have : n = 0 := by omega
    subst this; simp [varExtraGo, ndigits]
  | f + 1, n, c, h => by
    unfold varExtraGo
    by_cases hn : n < 128
    · rw [if_pos hn, show n / 128 = 0 by omega]; simp [ndigits]
    · rw [if_neg hn, varExtraGo_eq f (n / 128) (c + 1) (by omega), ndigits_pos (n / 128) (by omega)]
      omega

theorem pushVar_data (out : ByteArray) (n : Nat) :
    (pushVar out n).data.toList = out.data.toList ++ putVar n [] := by
  unfold pushVar
  rw [pushVarGo_eq, varExtraGo_eq n n 0 (Nat.le_refl _), Nat.zero_add, putVar_eq]
  unfold digits
  simp only [List.append_assoc]
  congr 2
  apply List.map_congr_left
  intro i _
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']

/-! ## The loops of the encoder -/

theorem rawFastGo_eq (xs : Array Nat) : ∀ (f i : Nat) (out : ByteArray), xs.size - i ≤ f →
    (rawFastGo xs f i out).data.toList = out.data.toList ++ rawBytes (xs.toList.drop i)
  | 0, i, out, h => by
    have : xs.toList.drop i = [] := by simp; omega
    simp [rawFastGo, this, rawBytes]
  | f + 1, i, out, h => by
    unfold rawFastGo
    by_cases hi : i < xs.size
    · rw [dif_pos hi, rawFastGo_eq xs f (i + 1) _ (by omega), pushU64_data]
      have : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hi)]; simp
      rw [this]
      simp [rawBytes]
    · rw [dif_neg hi]
      have : xs.toList.drop i = [] := by simp; omega
      simp [this, rawBytes]

theorem deltaFastGo_eq (xs : Array Nat) : ∀ (f i prev : Nat) (out : ByteArray), xs.size - i ≤ f →
    (deltaFastGo xs f i prev out).data.toList = out.data.toList ++
      (List.zipWith (fun p x => putVar (zz p x) []) (prev :: xs.toList.drop i) (xs.toList.drop i)).flatten
  | 0, i, prev, out, h => by
    have : xs.toList.drop i = [] := by simp; omega
    simp [deltaFastGo, this]
  | f + 1, i, prev, out, h => by
    unfold deltaFastGo
    by_cases hi : i < xs.size
    · rw [dif_pos hi, deltaFastGo_eq xs f (i + 1) _ _ (by omega), pushVar_data]
      have : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hi)]; simp
      rw [this]
      simp
    · rw [dif_neg hi]
      have : xs.toList.drop i = [] := by simp; omega
      simp [this]

theorem allSameGo_eq (xs : Array Nat) (x : Nat) : ∀ (f i : Nat), xs.size - i ≤ f →
    allSameGo xs x f i = (xs.toList.drop i).all (· == x)
  | 0, i, h => by
    have : xs.toList.drop i = [] := by simp; omega
    simp [allSameGo, this]
  | f + 1, i, h => by
    unfold allSameGo
    by_cases hi : i < xs.size
    · rw [dif_pos hi, allSameGo_eq xs x f (i + 1) (by omega)]
      have : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hi)]; simp
      rw [this]
      simp
    · rw [dif_neg hi]
      have : xs.toList.drop i = [] := by simp; omega
      simp [this]

theorem emptyWithCapacity_data (n : Nat) : (ByteArray.emptyWithCapacity n).data.toList = [] := rfl

/-- The packer's frame encoder writes the specification frame. -/
theorem encodeColumnFast_eq (xs : Array Nat) : (encodeColumnFast xs).data.toList = frameBytes xs.toList := by
  unfold encodeColumnFast
  by_cases h0 : 0 < xs.size
  · rw [dif_pos h0]
    obtain ⟨l⟩ := xs
    cases l with
    | nil => simp at h0
    | cons x rest =>
      simp only [List.getElem_toArray, List.getElem_cons_zero, List.size_toArray, List.length_cons]
      have hall := allSameGo_eq ⟨x :: rest⟩ x (rest.length + 1) 1 (by simp)
      simp only [List.toList_toArray, List.drop_succ_cons, List.drop_zero] at hall
      simp only [frameBytes, List.toList_toArray]
      rw [hall]
      by_cases hs : (rest.all fun y => y == x) = true
      · rw [if_pos hs, if_pos hs, pushU64_data]
        simp [tagConst]
      · rw [if_neg hs, if_neg hs]
        have hd := deltaFastGo_eq ⟨x :: rest⟩ (rest.length + 1) 0 0
          ((ByteArray.emptyWithCapacity (2 * (rest.length + 1) + 8)).push tagDelta) (by simp)
        simp only [List.toList_toArray, List.drop_zero, ByteArray.data_push, Array.toList_push,
          emptyWithCapacity_data, List.nil_append] at hd
        have hsz : ∀ b : ByteArray, b.size = b.data.toList.length := fun b => by rw [Array.length_toList]; rfl
        have hdl : (deltaFastGo ⟨x :: rest⟩ (rest.length + 1) 0 0
            ((ByteArray.emptyWithCapacity (2 * (rest.length + 1) + 8)).push tagDelta)).size - 1 =
            (deltaBytes (x :: rest)).length := by
          rw [hsz, hd]
          simp only [deltaBytes, List.length_cons, List.length_append, List.length_nil]
          omega
        by_cases hc : (deltaBytes (x :: rest)).length < 8 * (rest.length + 1)
        · rw [if_pos (by rw [hdl]; exact hc), if_pos hc, hd]
          simp [deltaBytes]
        · rw [if_neg (by rw [hdl]; exact hc), if_neg hc]
          have hr := rawFastGo_eq ⟨x :: rest⟩ (rest.length + 1) 0
            ((ByteArray.emptyWithCapacity (8 * (rest.length + 1) + 1)).push tagRaw) (by simp)
          simp only [List.toList_toArray, List.drop_zero, ByteArray.data_push, Array.toList_push,
            emptyWithCapacity_data, List.nil_append] at hr
          rw [hr]
          simp
  · rw [dif_neg h0]
    have : xs.toList = [] := List.length_eq_zero_iff.1 (by rw [Array.length_toList]; omega)
    rw [this]
    simp [frameBytes]

end L4Factoidal.Storage.Sbm11.Column
