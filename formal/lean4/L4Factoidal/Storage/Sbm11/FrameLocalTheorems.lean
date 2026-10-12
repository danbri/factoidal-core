/-
L4Factoidal.Storage.Sbm11.FrameLocalTheorems — a frame decoder reads only
the bytes of its frame (lemma L4f of
`docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md`;
https://github.com/danbri/factoidal/issues/776).

The scan reads one slice of PRB1 per block, from the first needed frame to
the end of the last one (`IdQuery.readFrames`), and decodes each frame at
its offset in the slice.

* `decodeColumn_local`: a frame that `Column.decodeColumn` reads from a list
  is read the same in front of any other rest.
* `decodeColumnAt_le`: the position after a frame is inside the array.
* `decodeColumnAt_extract`, `decodeWords_extract`: a frame at `i` that ends
  at `j` decodes to the same column (the same words) in any slice
  `[s, e)` with `s ≤ i` and `j ≤ e`, at `i - s`, ending at `j - s`.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.FrameWordsTheorems

namespace L4Factoidal.Storage.Sbm11.Column

open L4Factoidal (two64)
open L4Factoidal.Storage.Sbm11.Dict (bytesToList bytesToList_length drop_bytesToList_cons
  drop_bytesToList_of_le bytesToList_extract)

/-! ## Lists -/

theorem getVarGo_local : ∀ f acc (l : List UInt8) z r, getVarGo f acc l = some (z, r) →
    ∃ P, l = P ++ r ∧ P.length ≤ f ∧ ∀ f' (r' : List UInt8), P.length ≤ f' →
      getVarGo f' acc (P ++ r') = some (z, r') := by
  intro f
  induction f with
  | zero => intro acc l z r h; simp [getVarGo] at h
  | succ f ih =>
    intro acc l z r h
    cases l with
    | nil => simp [getVarGo] at h
    | cons b rest =>
      simp only [getVarGo] at h
      split at h
      · rename_i hb
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[b], rfl, by simp, fun f' r' hf' => ?_⟩
        cases f' with
        | zero => simp at hf'
        | succ f' => simp [getVarGo, hb]
      · rename_i hb
        obtain ⟨P, hP, hlen, hgo⟩ := ih _ rest z r h
        refine ⟨b :: P, by rw [hP]; rfl, by simp; omega, fun f' r' hf' => ?_⟩
        cases f' with
        | zero => simp at hf'
        | succ f' =>
          simp only [List.cons_append, getVarGo, hb, if_false]
          exact hgo f' r' (by simp at hf'; omega)

theorem getVar_local (l : List UInt8) (z : Nat) (r : List UInt8) (h : getVar l = some (z, r)) :
    ∃ P, l = P ++ r ∧ ∀ r', getVar (P ++ r') = some (z, r') := by
  obtain ⟨P, hP, _, hgo⟩ := getVarGo_local _ 0 l z r h
  exact ⟨P, hP, fun r' => hgo _ r' (by simp)⟩

theorem get64_local (l : List UInt8) (v : Nat) (r : List UInt8) (h : get64 l = some (v, r)) :
    ∃ P, l = P ++ r ∧ ∀ r', get64 (P ++ r') = some (v, r') := by
  match l, h with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, h =>
    simp only [get64, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[b0, b1, b2, b3, b4, b5, b6, b7], rfl, fun r' => rfl⟩

theorem getRawGo_local : ∀ n (l : List UInt8) (acc : List Nat) c r, getRawGo n l acc = some (c, r) →
    ∃ P, l = P ++ r ∧ ∀ r', getRawGo n (P ++ r') acc = some (c, r') := by
  intro n
  induction n with
  | zero =>
    intro l acc c r h
    simp only [getRawGo, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, fun r' => rfl⟩
  | succ n ih =>
    intro l acc c r h
    simp only [getRawGo] at h
    split at h
    · cases h
    · rename_i v rest hg
      obtain ⟨P1, hP1, hgo1⟩ := get64_local _ _ _ hg
      obtain ⟨P2, hP2, hgo2⟩ := ih rest (v :: acc) c r h
      refine ⟨P1 ++ P2, by rw [hP1, hP2, List.append_assoc], fun r' => ?_⟩
      simp only [getRawGo, List.append_assoc, hgo1 (P2 ++ r')]
      exact hgo2 r'

theorem getDeltaGo_local : ∀ n prev (l : List UInt8) (acc : List Nat) c r, getDeltaGo n prev l acc = some (c, r) →
    ∃ P, l = P ++ r ∧ ∀ r', getDeltaGo n prev (P ++ r') acc = some (c, r') := by
  intro n
  induction n with
  | zero =>
    intro prev l acc c r h
    simp only [getDeltaGo, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, fun r' => rfl⟩
  | succ n ih =>
    intro prev l acc c r h
    simp only [getDeltaGo] at h
    split at h
    · cases h
    · rename_i z rest hg
      obtain ⟨P1, hP1, hgo1⟩ := getVar_local _ _ _ hg
      split at h
      · cases h
      · rename_i v hv
        split at h
        · rename_i hlt
          obtain ⟨P2, hP2, hgo2⟩ := ih v rest (v :: acc) c r h
          refine ⟨P1 ++ P2, by rw [hP1, hP2, List.append_assoc], fun r' => ?_⟩
          simp only [getDeltaGo, List.append_assoc, hgo1 (P2 ++ r'), hv, if_pos hlt]
          exact hgo2 r'
        · cases h

/-- A frame that `decodeColumn` reads from a list is read the same in front of
    any other rest. -/
theorem decodeColumn_local (n : Nat) (l : List UInt8) (c : List Nat) (r : List UInt8)
    (h : decodeColumn n l = some (c, r)) :
    ∃ P, l = P ++ r ∧ ∀ r', decodeColumn n (P ++ r') = some (c, r') := by
  cases l with
  | nil => simp [decodeColumn] at h
  | cons t bs =>
    simp only [decodeColumn] at h
    split at h
    · rename_i ht
      split at h
      · rename_i v rest hg
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨P, hP, hgo⟩ := get64_local _ _ _ hg
        refine ⟨t :: P, by rw [hP]; rfl, fun r' => ?_⟩
        simp only [List.cons_append, decodeColumn, ht, if_true, hgo r']
      · cases h
    · rename_i ht
      split at h
      · rename_i hr
        obtain ⟨P, hP, hgo⟩ := getRawGo_local _ _ _ _ _ h
        refine ⟨t :: P, by rw [hP]; rfl, fun r' => ?_⟩
        simp only [List.cons_append, decodeColumn, ht, hr, if_true]
        exact hgo r'
      · rename_i hr
        split at h
        · rename_i hd
          obtain ⟨P, hP, hgo⟩ := getDeltaGo_local _ _ _ _ _ _ h
          refine ⟨t :: P, by rw [hP]; rfl, fun r' => ?_⟩
          simp only [List.cons_append, decodeColumn, ht, hr, hd, if_true]
          exact hgo r'
        · cases h

/-! ## Byte arrays -/

theorem rawAtGo_le (b : ByteArray) : ∀ n i (acc : Array Nat) a k, i ≤ b.size →
    rawAtGo b n i acc = some (a, k) → k ≤ b.size := by
  intro n
  induction n with
  | zero => intro i acc a k hi h; simp only [rawAtGo, Option.some.injEq, Prod.mk.injEq] at h; omega
  | succ n ih =>
    intro i acc a k hi h
    simp only [rawAtGo] at h
    split at h
    · cases h
    · rename_i v j hg
      have : j ≤ b.size := by
        unfold get64At at hg
        split at hg
        · simp only [Option.some.injEq, Prod.mk.injEq] at hg; omega
        · cases hg
      exact ih _ _ _ _ this h

theorem deltaAtGo_le (b : ByteArray) : ∀ n prev i (acc : Array Nat) a k, i ≤ b.size →
    deltaAtGo b n prev i acc = some (a, k) → k ≤ b.size := by
  intro n
  induction n with
  | zero => intro prev i acc a k hi h; simp only [deltaAtGo, Option.some.injEq, Prod.mk.injEq] at h; omega
  | succ n ih =>
    intro prev i acc a k hi h
    simp only [deltaAtGo] at h
    split at h
    · cases h
    · rename_i z j hg
      have : j ≤ b.size := FrameWords.getVarAtGo_le b _ _ _ _ _ hg
      split at h
      · cases h
      · split at h
        · exact ih _ _ _ _ _ this h
        · cases h

/-- The position after a frame is inside the array. -/
theorem decodeColumnAt_le (b : ByteArray) (n i : Nat) (c : Array Nat) (j : Nat)
    (h : decodeColumnAt b n i = some (c, j)) : j ≤ b.size := by
  unfold decodeColumnAt at h
  by_cases hi : i < b.size
  · rw [dif_pos hi] at h
    dsimp only at h
    by_cases t0 : (b[i] == tagConst) = true
    · rw [if_pos t0] at h
      cases hg : get64At b (i + 1) with
      | none => rw [hg] at h; cases h
      | some p =>
        obtain ⟨v, j'⟩ := p
        rw [hg] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        unfold get64At at hg
        split at hg
        · simp only [Option.some.injEq, Prod.mk.injEq] at hg; omega
        · cases hg
    · rw [if_neg t0] at h
      by_cases t1 : (b[i] == tagRaw) = true
      · rw [if_pos t1] at h
        exact rawAtGo_le b _ _ _ _ _ (by omega) h
      · rw [if_neg t1] at h
        by_cases t2 : (b[i] == tagDelta) = true
        · rw [if_pos t2] at h
          exact deltaAtGo_le b _ _ _ _ _ _ (by omega) h
        · rw [if_neg t2] at h; cases h
  · rw [dif_neg hi] at h; cases h

/-- A frame at `i` that ends at `j` decodes to the same column in any slice
    `[s, e)` of the array with `s ≤ i` and `j ≤ e`. -/
theorem decodeColumnAt_extract (b : ByteArray) (n i : Nat) (c : Array Nat) (j s e : Nat)
    (h : decodeColumnAt b n i = some (c, j)) (hs : s ≤ i) (he : j ≤ e) (heb : e ≤ b.size) :
    decodeColumnAt (b.extract s e) n (i - s) = some (c, j - s) := by
  have hjb := decodeColumnAt_le b n i c j h
  have hib : i < b.size := by
    unfold decodeColumnAt at h
    by_cases hi : i < b.size
    · exact hi
    · rw [dif_neg hi] at h; cases h
  have hl := decodeColumnAt_some b n i j c h
  obtain ⟨P, hP, hgo⟩ := decodeColumn_local n _ _ _ hl
  have hlenP := congrArg List.length hP
  simp only [List.length_drop, bytesToList_length, List.length_append] at hlenP
  have hij : i ≤ j := by omega
  have a1 : s + (i - s) = i := by omega
  have a2 : e - s - (i - s) = e - i := by omega
  have a3 : e - i = P.length + (e - j) := by omega
  have hdrop : (bytesToList (b.extract s e)).drop (i - s) =
      P ++ ((bytesToList b).drop j).take (e - j) := by
    rw [bytesToList_extract, List.drop_take, List.drop_drop, a1, a2, hP, a3, List.take_length_add_append]
  have hs' := decodeColumnAt_eq (b.extract s e) n (i - s)
  rw [hdrop, hgo] at hs'
  cases hd : decodeColumnAt (b.extract s e) n (i - s) with
  | none => rw [hd] at hs'; cases hs'
  | some q =>
    obtain ⟨c', j'⟩ := q
    rw [hd] at hs'
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs'
    obtain ⟨hc, hj⟩ := hs'
    have hj'le := decodeColumnAt_le _ _ _ _ _ hd
    have hsz : (b.extract s e).size = e - s := by rw [ByteArray.size_extract]; omega
    have hlen := congrArg List.length hj
    simp only [List.length_drop, bytesToList_length, List.length_take] at hlen
    rw [hsz] at hlen hj'le
    have : c' = c := Array.toList_inj.mp hc
    subst this
    congr 2
    omega

end L4Factoidal.Storage.Sbm11.Column

namespace L4Factoidal.Storage.Sbm11.FrameWords

open L4Factoidal (two64)

/-- The query path's word decoder reads only the bytes of its frame: in any
    slice `[s, e)` with `s ≤ i` and `j ≤ e` it gives the same words, ending
    at `j - s`. -/
theorem decodeWords_extract (b : ByteArray) (n i : Nat) (ws : ByteArray) (j s e : Nat) (hn : n ≤ two64)
    (h : decodeWords b n i = some (ws, j)) (hs : s ≤ i) (he : j ≤ e) (heb : e ≤ b.size) :
    decodeWords (b.extract s e) n (i - s) = some (ws, j - s) := by
  rw [decodeWords_eq _ _ _ hn] at h ⊢
  unfold decodeWordsRef at h ⊢
  cases hd : Column.decodeColumnAt b n i with
  | none => rw [hd] at h; cases h
  | some q =>
    obtain ⟨c, j'⟩ := q
    rw [hd] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Column.decodeColumnAt_extract b n i c j' s e hd hs he heb]
    rfl

end L4Factoidal.Storage.Sbm11.FrameWords
