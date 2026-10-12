/-
L4Factoidal.Storage.Sbm11.FrameWordsTheorems — the query path's frame
decoder (`FrameWords.decodeWords`) equals the proved decoder followed by
`words` (lemma L2 of
`docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md`;
https://github.com/danbri/factoidal/issues/776).

* `put64_data`: `FrameWords.put64 out x.toUInt64` appends `Column.put64 x`
  (no bound on `x`: both keep the low 64 bits).
* `words_data`: the words of a column are the `Column.put64` bytes of its
  values.
* `repeatWords_data`: `n` copies of an 8-byte value, for `n ≤ 2^64`.
* `deltaGo_step`, `deltaGo_eq`: the fused delta loop equals `deltaAtGo`
  (one varint per row through `getVarAt`).
* `decodeWords_eq`: `decodeWords b n i = decodeWordsRef b n i` for every
  `b`, `i` and `n ≤ 2^64`. The bound is real: `repeatWords` doubles at most
  64 times. A PRM1 block has fewer than `2^32` rows.

With `ColumnTheorems.decodeColumnAt_eq`, the words the scan reads are the
`Column.put64` bytes of the column `Column.decodeColumn` reads.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.FrameWords
import L4Factoidal.Storage.Sbm11.ColumnTheorems

namespace L4Factoidal.Storage.Sbm11.FrameWords

open L4Factoidal (two64)
open L4Factoidal.Storage.Sbm11.Column (getVarAtGo getVarAt deltaAtGo rawAtGo decodeColumnAt
  get64At unzz tagConst tagRaw tagDelta getRawGo get64 rawAtGo_spec)
open L4Factoidal.Storage.Sbm11.Dict (bytesToList bytesToList_length drop_bytesToList_cons
  drop_bytesToList_of_le bytesToList_extract)

/-! ## Bytes -/

theorem put64_data (out : ByteArray) (x : Nat) :
    (put64 out x.toUInt64).data.toList = out.data.toList ++ Column.put64 x := by
  simp only [put64, ByteArray.data_push, Array.toList_push, Column.put64, List.append_assoc,
    List.cons_append, List.nil_append, List.append_cancel_left_eq, List.cons.injEq, ← UInt8.toNat_inj,
    and_true]
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.toUInt8,
    Nat.toUInt64, UInt64.toNat_ofNat, UInt8.toNat_ofNat', UInt64.toNat_ofNat']
  and_intros <;> simp <;> omega

theorem words_foldl (l : List Nat) (init : ByteArray) :
    (l.foldl (fun b a => put64 b a.toUInt64) init).data.toList =
      init.data.toList ++ (l.map Column.put64).flatten := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih => simp [ih, put64_data]

theorem words_data (xs : Array Nat) :
    (words xs).data.toList = (xs.toList.map Column.put64).flatten := by
  unfold words
  rw [← Array.foldl_toList, words_foldl]
  rfl

private theorem byte_get! (b : ByteArray) (i : Nat) (h : i < b.size) : b.get! i = b[i] := by
  simp [ByteArray.get!, ByteArray.getElem_eq_getElem_data, getElem!_pos, h]

/-! ## Repeated words -/

theorem take_flatten_replicate (L : List UInt8) (hL : L.length = 8) :
    ∀ k j, j ≤ k → ((List.replicate k L).flatten).take (8 * j) = (List.replicate j L).flatten := by
  intro k
  induction k with
  | zero => intro j hj; have : j = 0 := by omega
            subst this; simp
  | succ k ih =>
    intro j hj
    cases j with
    | zero => simp
    | succ j =>
      rw [List.replicate_succ, List.replicate_succ, List.flatten_cons, List.flatten_cons,
        show 8 * (j + 1) = L.length + 8 * j by omega, List.take_length_add_append, ih j (by omega)]

theorem length_flatten_replicate (L : List UInt8) (k : Nat) :
    ((List.replicate k L).flatten).length = k * L.length := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih, Nat.succ_mul]; omega

theorem repeatGo_data (L : List UInt8) (hL : L.length = 8) (n : Nat) :
    ∀ f k (out : ByteArray), out.data.toList = (List.replicate k L).flatten → 1 ≤ k → k ≤ n →
      n ≤ k * 2 ^ f → (repeatGo (8 * n) f out).data.toList = (List.replicate n L).flatten := by
  intro f
  induction f with
  | zero =>
    intro k out hout _ hkn hf
    have : k = n := by simp at hf; omega
    subst this
    simpa [repeatGo] using hout
  | succ f ih =>
    intro k out hout hk hkn hf
    have hsz : out.size = 8 * k := by
      have := congrArg List.length hout
      simp only [Array.length_toList, length_flatten_replicate, hL] at this
      rw [ByteArray.size]; omega
    simp only [repeatGo]
    by_cases hge : out.size ≥ 8 * n
    · rw [if_pos hge]
      have : k = n := by omega
      subst this; exact hout
    · rw [if_neg hge]
      have hm : min out.size (8 * n - out.size) = 8 * min k (n - k) := by
        rw [hsz]; omega
      apply ih (k + min k (n - k)) _ _ (by omega) (by omega)
      · rw [Nat.pow_succ] at hf
        by_cases h2 : 2 * k ≤ n
        · have : k + min k (n - k) = 2 * k := by omega
          rw [this]
          calc n ≤ k * (2 ^ f * 2) := hf
            _ = 2 * k * 2 ^ f := by rw [Nat.mul_comm (2 ^ f) 2, ← Nat.mul_assoc, Nat.mul_comm k 2]
        · have : k + min k (n - k) = n := by omega
          rw [this]
          exact Nat.le_mul_of_pos_right n (Nat.two_pow_pos f)
      · rw [hm]
        simp only [ByteArray.copySlice, Array.toList_append, Array.toList_extract, List.extract_eq_take_drop,
          Nat.sub_zero, List.drop_zero, Nat.zero_add]
        have hsz' : out.data.size = 8 * k := hsz
        rw [hsz', hout]
        try rw [hsz]
        have hlen : (List.replicate k L).flatten.length = 8 * k := by
          rw [length_flatten_replicate, hL, Nat.mul_comm]
        rw [List.take_of_length_le (by omega), take_flatten_replicate L hL k _ (by omega)]
        have hdrop : List.take (8 * k - (8 * k + min (8 * min k (n - k)) (8 * k)))
            (List.drop (8 * k + min (8 * min k (n - k)) (8 * k)) (List.replicate k L).flatten) = [] := by
          simp only [List.take_eq_nil_iff]; left; omega
        rw [hdrop, List.append_nil, ← List.flatten_append, List.replicate_append_replicate]

theorem repeatWords_data (v8 : ByteArray) (hv : v8.size = 8) (n : Nat) (hn : n ≤ two64) :
    (repeatWords v8 n).data.toList = (List.replicate n v8.data.toList).flatten := by
  unfold repeatWords
  by_cases h0 : n = 0
  · subst h0; rfl
  · rw [if_neg (by simpa using h0)]
    apply repeatGo_data v8.data.toList (by rw [Array.length_toList]; exact hv) n 64 1 _ _ (by omega) (by omega)
      (by simp only [two64] at hn; omega)
    rw [ByteArray.data_append, Array.toList_append, List.replicate_one, List.flatten_singleton]
    rfl

/-! ## The delta loop -/

theorem getVarAtGo_le (b : ByteArray) : ∀ f acc i z j, getVarAtGo b f acc i = some (z, j) → j ≤ b.size := by
  intro f
  induction f with
  | zero => intro _ _ _ _ h; simp [getVarAtGo] at h
  | succ f ih =>
    intro acc i z j h
    simp only [getVarAtGo] at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
      · exact ih _ _ _ _ h
    · cases h

/-- One row of the fused loop is one varint of `getVarAtGo`. -/
theorem deltaGo_step (b : ByteArray) (rows prev : Nat) (out : ByteArray) (hp : prev < two64) :
    ∀ d acc i, b.size - i = d → i ≤ b.size →
      deltaGo b (d + 2) (rows + 1) prev i acc out =
        match getVarAtGo b d acc i with
        | none => none
        | some (z, j) =>
          match unzz prev z with
          | none => none
          | some v => if v < two64 then deltaGo b (b.size - j + 2) rows v j 0 (put64 out v.toUInt64) else none := by
  intro d
  induction d with
  | zero =>
    intro acc i hd hi
    have : i = b.size := by omega
    subst this
    simp [deltaGo, getVarAtGo]
  | succ d ih =>
    intro acc i hd hi
    have hlt : i < b.size := by omega
    rw [show d + 1 + 2 = (d + 2) + 1 from rfl, deltaGo.eq_2, getVarAtGo.eq_2]
    simp only [Nat.add_one_ne_zero, beq_iff_eq, if_false, if_pos hlt, byte_get! b i hlt,
      Nat.add_sub_cancel, dif_pos hlt]
    by_cases hx : b[i].toNat < 128
    · rw [if_pos hx, if_pos hx]
      have hj : b.size - (i + 1) + 2 = d + 2 := by omega
      simp only [unzz]
      by_cases he : (b[i].toNat + acc * 128) % 2 = 0
      · have he' : (acc * 128 + b[i].toNat) % 2 = 0 := by omega
        simp only [he', if_true, hj]
      · have he' : ¬ (acc * 128 + b[i].toNat) % 2 = 0 := by omega
        simp only [he', if_false, hj]
        split
        · rename_i hle
          dsimp only
          rw [if_pos (by omega)]
        · rfl
    · rw [if_neg hx, if_neg hx]
      exact ih _ _ (by omega) (by omega)

theorem deltaAtGo_acc (b : ByteArray) : ∀ n prev i (acc : Array Nat),
    deltaAtGo b n prev i acc = (deltaAtGo b n prev i #[]).map (fun r => (acc ++ r.1, r.2)) := by
  intro n
  induction n with
  | zero => intro prev i acc; simp [deltaAtGo]
  | succ n ih =>
    intro prev i acc
    simp only [deltaAtGo]
    split
    · rfl
    · split
      · rfl
      · split
        · rw [ih, ih _ _ (#[].push _)]
          simp only [Option.map_map]
          congr 1
          funext r
          congr 1
          apply Array.toList_inj.mp
          simp
        · rfl

/-- The fused delta loop equals `deltaAtGo` followed by `words`. -/
theorem deltaGo_eq (b : ByteArray) : ∀ n prev i (out : ByteArray), prev < two64 → i ≤ b.size →
    (deltaGo b (b.size - i + 2) n prev i 0 out).map (fun r => (r.1.data.toList, r.2)) =
      (deltaAtGo b n prev i #[]).map (fun r => (out.data.toList ++ (r.1.toList.map Column.put64).flatten, r.2)) := by
  intro n
  induction n with
  | zero =>
    intro prev i out _ _
    simp [deltaGo, deltaAtGo]
  | succ n ih =>
    intro prev i out hp hi
    rw [deltaGo_step b n prev out hp (b.size - i) 0 i rfl hi]
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
        · rw [if_pos hvl, if_pos hvl, ih v j _ hvl hj, deltaAtGo_acc b n v j (#[].push v)]
          simp only [Option.map_map]
          congr 1
          funext r
          simp [put64_data]
        · rw [if_neg hvl, if_neg hvl]; rfl

/-! ## The raw frame -/

theorem get64_some (l : List UInt8) (h : 8 ≤ l.length) :
    ∃ v, get64 l = some (v, l.drop 8) ∧ Column.put64 v = l.take 8 := by
  match l, h with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, _ =>
    refine ⟨_, rfl, ?_⟩
    simp only [Column.put64, List.take, List.cons.injEq, ← UInt8.toNat_inj, Nat.toUInt8,
      UInt8.toNat_ofNat', and_true]
    have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
    have := b4.toNat_lt; have := b5.toNat_lt; have := b6.toNat_lt; have := b7.toNat_lt
    and_intros <;> omega

theorem get64_none (l : List UInt8) (h : l.length < 8) : get64 l = none := by
  match l, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | [_, _, _, _], _ => rfl
  | [_, _, _, _, _], _ => rfl
  | [_, _, _, _, _, _], _ => rfl
  | [_, _, _, _, _, _, _], _ => rfl

theorem getRawGo_acc : ∀ n (l : List UInt8) (acc : List Nat),
    getRawGo n l acc = (getRawGo n l []).map (fun r => (acc.reverse ++ r.1, r.2)) := by
  intro n
  induction n with
  | zero => intro l acc; simp [getRawGo]
  | succ n ih =>
    intro l acc
    simp only [getRawGo]
    split
    · rfl
    · rw [ih, ih _ [_]]
      simp only [Option.map_map]
      congr 1
      funext r
      simp

theorem getRawGo_take : ∀ n (l : List UInt8),
    (getRawGo n l []).map (fun r => ((r.1.map Column.put64).flatten, r.2)) =
      if 8 * n ≤ l.length then some (l.take (8 * n), l.drop (8 * n)) else none := by
  intro n
  induction n with
  | zero => intro l; simp [getRawGo]
  | succ n ih =>
    intro l
    simp only [getRawGo]
    by_cases h8 : 8 ≤ l.length
    · obtain ⟨v, hv, hp⟩ := get64_some l h8
      rw [hv]
      dsimp only
      rw [getRawGo_acc, Option.map_map]
      have := ih (l.drop 8)
      simp only [List.length_drop] at this
      cases hg : getRawGo n (l.drop 8) [] with
      | none =>
        rw [hg] at this
        simp only [Option.map_none] at this
        by_cases hn : 8 * (n + 1) ≤ l.length
        · rw [if_pos (by omega)] at this; cases this
        · rw [if_neg hn]; rfl
      | some r =>
        rw [hg] at this
        simp only [Option.map_some] at this
        by_cases hn : 8 * (n + 1) ≤ l.length
        · rw [if_pos (by omega)] at this
          rw [if_pos hn]
          simp only [Option.some.injEq, Prod.mk.injEq] at this
          simp only [Option.map_some, Function.comp, Option.some.injEq, Prod.mk.injEq, List.reverse_cons,
            List.reverse_nil, List.nil_append, List.cons_append, List.map_cons, List.flatten_cons]
          rw [this.1, this.2, hp, List.drop_drop]
          refine ⟨?_, by congr 1; omega⟩
          rw [show 8 * (n + 1) = 8 + 8 * n by omega, List.take_add]
        · rw [if_neg (by omega)] at this; cases this
    · rw [get64_none l (by omega), if_neg (by omega)]
      rfl

theorem get64At_pos (b : ByteArray) (i v j : Nat) (h : get64At b i = some (v, j)) : j = i + 8 := by
  unfold get64At at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
  · cases h

theorem rawAtGo_pos (b : ByteArray) : ∀ n j (acc : Array Nat) a k, rawAtGo b n j acc = some (a, k) →
    k = j + 8 * n := by
  intro n
  induction n with
  | zero => intro j acc a k h; simp only [rawAtGo, Option.some.injEq, Prod.mk.injEq] at h; omega
  | succ n ih =>
    intro j acc a k h
    simp only [rawAtGo] at h
    split at h
    · cases h
    · rename_i v j' hg
      have := get64At_pos b _ _ _ hg
      have := ih _ _ _ _ h
      omega

/-! ## The frame decoder -/

private def view (r : ByteArray × Nat) : List UInt8 × Nat := (r.1.data.toList, r.2)

private theorem view_inj (x y : Option (ByteArray × Nat)) (h : x.map view = y.map view) : x = y := by
  cases x with
  | none => cases y with
    | none => rfl
    | some _ => cases h
  | some p => cases y with
    | none => cases h
    | some q =>
      simp only [Option.map_some, Option.some.injEq, view, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have : p.1 = q.1 := ByteArray.ext (Array.toList_inj.mp h1)
      rw [Prod.ext this h2]

/-- The query path's frame decoder equals `decodeColumnAt` followed by
    `words`, for at most `2^64` rows. -/
theorem decodeWords_eq (b : ByteArray) (n i : Nat) (hn : n ≤ two64) :
    decodeWords b n i = decodeWordsRef b n i := by
  apply view_inj
  unfold decodeWords decodeWordsRef decodeColumnAt
  by_cases h : i < b.size
  · rw [if_pos h, dif_pos h, byte_get! b i h]
    by_cases t0 : (b[i] == tagConst) = true
    · rw [if_pos t0, if_pos t0]
      by_cases h9 : i + 9 ≤ b.size
      · rw [if_pos h9]
        have hl : 8 ≤ ((bytesToList b).drop (i + 1)).length := by
          simp only [List.length_drop, bytesToList_length]; omega
        obtain ⟨v, hv, hp⟩ := get64_some _ hl
        have hs := Column.get64At_spec b (i + 1)
        rw [hv] at hs
        cases hg : get64At b (i + 1) with
        | none => rw [hg] at hs; cases hs
        | some q =>
          obtain ⟨v', j⟩ := q
          rw [hg] at hs
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, _⟩ := hs
          have hj := get64At_pos b _ _ _ hg
          subst hj
          simp only [Option.map_some, view, Option.some.injEq, Prod.mk.injEq]
          refine ⟨?_, trivial⟩
          have hsz : (b.extract (i + 1) (i + 9)).size = 8 := by
            rw [ByteArray.size_extract]; omega
          rw [repeatWords_data _ hsz n hn, words_data]
          have he : (b.extract (i + 1) (i + 9)).data.toList = Column.put64 v' := by
            have := bytesToList_extract b (i + 1) (i + 9)
            simp only [bytesToList] at this
            rw [this, hp]
            congr 1
            omega
          rw [he]
          simp
      · rw [if_neg h9]
        have hg : get64At b (i + 1) = none := by
          unfold get64At; rw [dif_neg (by omega)]
        rw [hg]
        rfl
    · rw [if_neg t0, if_neg t0]
      by_cases t1 : (b[i] == tagRaw) = true
      · rw [if_pos t1, if_pos t1]
        have hs := rawAtGo_spec b n (i + 1) (Array.mkEmpty n)
        have hmk : (Array.mkEmpty n : Array Nat).toList.reverse = [] := rfl
        rw [hmk] at hs
        have ht := getRawGo_take n ((bytesToList b).drop (i + 1))
        simp only [List.length_drop, bytesToList_length] at ht
        cases hr : rawAtGo b n (i + 1) (Array.mkEmpty n) with
        | none =>
          rw [hr] at hs
          rw [← hs] at ht
          simp only [Option.map_none] at ht
          rw [if_neg (by intro hc; rw [if_pos (by omega)] at ht; cases ht)]
          rfl
        | some q =>
          obtain ⟨a, k⟩ := q
          have hk := rawAtGo_pos b _ _ _ _ _ hr
          rw [hr] at hs
          rw [← hs] at ht
          simp only [Option.map_some] at ht
          by_cases hle : 8 * n ≤ b.size - (i + 1)
          · rw [if_pos hle] at ht
            simp only [Option.some.injEq, Prod.mk.injEq] at ht
            rw [if_pos (by omega)]
            simp only [Option.map_some, view, Option.some.injEq, Prod.mk.injEq]
            refine ⟨?_, by omega⟩
            rw [words_data, ht.1]
            have := bytesToList_extract b (i + 1) (i + 1 + 8 * n)
            simp only [bytesToList] at this
            rw [this]
            congr 1
            omega
          · rw [if_neg hle] at ht; cases ht
      · rw [if_neg t1, if_neg t1]
        by_cases t2 : (b[i] == tagDelta) = true
        · rw [if_pos t2, if_pos t2]
          unfold deltaWords
          have he := deltaGo_eq b n 0 (i + 1) (ByteArray.emptyWithCapacity (8 * n)) (by decide) (by omega)
          have hmk : (Array.mkEmpty n : Array Nat) = #[] := rfl
          rw [hmk, Option.map_map]
          have hv : (fun r : ByteArray × Nat => (r.1.data.toList, r.2)) = view := rfl
          rw [← hv, he]
          congr 1
          funext r
          simp [words_data]
          rfl
        · rw [if_neg t2, if_neg t2]
          rfl
  · rw [if_neg h, dif_neg h]
    rfl

/-! ## `repeatWords` before the refactor, compared on samples

`repeatWords` was a `for` loop over `[0:64]` with `break` until 2026-10-12;
it is now the tail call `repeatGo` with the same steps. -/

private def repeatWordsOld (v8 : ByteArray) (n : Nat) : ByteArray := Id.run do
  if n == 0 then return ByteArray.empty
  let total := 8 * n
  let mut out := ByteArray.emptyWithCapacity total
  out := out ++ v8
  for _ in [0:64] do
    if out.size ≥ total then break
    let take := min out.size (total - out.size)
    out := out.copySlice 0 out out.size take
  return out

#guard [0, 1, 2, 3, 5, 8, 13, 64, 100, 1000].all fun n =>
  (repeatWords (ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8]) n).data ==
    (repeatWordsOld (ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8]) n).data

end L4Factoidal.Storage.Sbm11.FrameWords
