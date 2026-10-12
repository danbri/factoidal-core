/-
L4Factoidal.Storage.Sbm11.BlockAtTheorems — what activation's block check
(`Block.decodeBlockAt`) gives the query path (lemmas L2e and L4c of
`docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md`;
https://github.com/danbri/factoidal/issues/776).

* `decodeColumnAt_lt`: every id a frame decodes to is below `2^64`.
* `colsSortedGo_sorted`: the order check of `decodeBlockAt` gives strictly
  increasing rows (every pair, not only neighbours).
* `decodeBlockAt_ok`: a block that `decodeBlockAt` admits has four frames
  that `decodeColumnAt` decodes, each to `m.rows` ids below `2^64` and
  ending at its PRM1 length, and its rows are strictly increasing from
  `m.first` to `m.last`.
* `scanRows_exact_of_decodeBlockAt`: so, for such a block, the two binary
  searches of the scan over the words of its key columns select exactly the
  rows whose key prefix equals the key (`ScanTheorems.scanRows_exact`
  without its hypotheses on the columns).

Activation (`l4sbm11 activate`) runs `decodeBlockAt` on every block of every
permutation before it writes `CURRENT`. That `decodeBlockAt` equals
`Block.decodeBlock` is not proved (L2e in the record).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.ScanWordsTheorems

namespace L4Factoidal.Storage.Sbm11.Block

open L4Factoidal (two64)
open L4Factoidal.Storage.Sbm11.Column (decodeColumnAt get64At rawAtGo deltaAtGo unzz)
open L4Factoidal.Storage.Sbm11.ScanTheorems (lt_trans colOf rowOf)
open L4Factoidal.Storage.Sbm11.IdQuery (keyBound prefixCmp)

/-! ## Ids are below `2^64` -/

theorem get64At_lt (b : ByteArray) (i v j : Nat) (h : get64At b i = some (v, j)) : v < two64 := by
  unfold get64At at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    rename_i hb
    have := (b[i]'(by omega)).toNat_lt
    have := (b[i+1]'(by omega)).toNat_lt
    have := (b[i+2]'(by omega)).toNat_lt
    have := (b[i+3]'(by omega)).toNat_lt
    have := (b[i+4]'(by omega)).toNat_lt
    have := (b[i+5]'(by omega)).toNat_lt
    have := (b[i+6]'(by omega)).toNat_lt
    have := (b[i+7]'(by omega)).toNat_lt
    simp only [two64]
    omega
  · cases h

theorem rawAtGo_lt (b : ByteArray) : ∀ n i (acc : Array Nat) c j, (∀ x ∈ acc, x < two64) →
    rawAtGo b n i acc = some (c, j) → ∀ x ∈ c, x < two64 := by
  intro n
  induction n with
  | zero =>
    intro i acc c j hacc h
    simp only [rawAtGo, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact hacc
  | succ n ih =>
    intro i acc c j hacc h
    simp only [rawAtGo] at h
    split at h
    · cases h
    · rename_i v j' hg
      refine ih _ _ _ _ ?_ h
      intro x hx
      rcases Array.mem_push.mp hx with hx | hx
      · exact hacc x hx
      · subst hx; exact get64At_lt b _ _ _ hg

theorem deltaAtGo_lt (b : ByteArray) : ∀ n prev i (acc : Array Nat) c j, (∀ x ∈ acc, x < two64) →
    deltaAtGo b n prev i acc = some (c, j) → ∀ x ∈ c, x < two64 := by
  intro n
  induction n with
  | zero =>
    intro prev i acc c j hacc h
    simp only [deltaAtGo, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact hacc
  | succ n ih =>
    intro prev i acc c j hacc h
    simp only [deltaAtGo] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · rename_i v _ hv
          refine ih _ _ _ _ _ ?_ h
          intro x hx
          rcases Array.mem_push.mp hx with hx | hx
          · exact hacc x hx
          · subst hx; exact hv
        · cases h

theorem decodeColumnAt_lt (b : ByteArray) (n i : Nat) (c : Array Nat) (j : Nat)
    (h : decodeColumnAt b n i = some (c, j)) : ∀ x ∈ c, x < two64 := by
  unfold decodeColumnAt at h
  by_cases hi : i < b.size
  · rw [dif_pos hi] at h
    dsimp only at h
    by_cases t0 : (b[i] == Column.tagConst) = true
    · rw [if_pos t0] at h
      cases hg : get64At b (i + 1) with
      | none => rw [hg] at h; cases h
      | some p =>
        obtain ⟨v, j'⟩ := p
        rw [hg] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        intro x hx
        rw [(Array.mem_replicate.mp hx).2]
        exact get64At_lt b _ _ _ hg
    · rw [if_neg t0] at h
      by_cases t1 : (b[i] == Column.tagRaw) = true
      · rw [if_pos t1] at h
        exact rawAtGo_lt b _ _ _ _ _ (fun x hx => by simp at hx) h
      · rw [if_neg t1] at h
        by_cases t2 : (b[i] == Column.tagDelta) = true
        · rw [if_pos t2] at h
          exact deltaAtGo_lt b _ _ _ _ _ _ (fun x hx => by simp at hx) h
        · rw [if_neg t2] at h; cases h
  · rw [dif_neg hi] at h; cases h

/-! ## The order check -/

theorem colsSortedGo_step (c : Cols) : ∀ f i, colsSortedGo c f i = true →
    ∀ k, i ≤ k → k + 1 < c.size → k < i + f → (c.row k).lt (c.row (k + 1)) = true := by
  intro f
  induction f with
  | zero => intro i _ k h1 _ h3; omega
  | succ f ih =>
    intro i h k hik hk hkf
    simp only [colsSortedGo] at h
    split at h
    · split at h
      · rename_i _ hlt
        by_cases hki : k = i
        · subst hki; exact hlt
        · exact ih (i + 1) h k (by omega) hk (by omega)
      · cases h
    · omega

/-- The order check of `decodeBlockAt` gives strictly increasing rows. -/
theorem colsSortedGo_sorted (c : Cols) (n : Nat) (hn : c.size ≤ n + 1) (h : colsSortedGo c n 0 = true) :
    ∀ r s, r < s → s < c.size → (c.row r).lt (c.row s) = true := by
  intro r s hrs hs
  induction s with
  | zero => omega
  | succ s ih =>
    have hstep := colsSortedGo_step c n 0 h s (Nat.zero_le _) hs (by omega)
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hrs) with h1 | h1
    · exact lt_trans (ih h1 (by omega)) hstep
    · subst h1; exact hstep

/-! ## A block that `decodeBlockAt` admits -/

private theorem frame_ok (b : ByteArray) (n off len : Nat) (e1 e2 : String) (c : Array Nat)
    (h : (match decodeColumnAt b n off with
      | some (c, j) => if (j == off + len && c.size == n) = true then Except.ok c else Except.error e1
      | none => Except.error e2) = (Except.ok c : Except String (Array Nat))) :
    decodeColumnAt b n off = some (c, off + len) ∧ c.size = n := by
  split at h
  · rename_i c' j hd
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      cases h
      rw [hd, hc.1]
      exact ⟨rfl, hc.2⟩
    · cases h
  · cases h

theorem decodeBlockAt_ok (b : ByteArray) (m : BlockMeta) (base : Nat) (cols : Cols)
    (h : decodeBlockAt b m base = .ok cols) :
    decodeColumnAt b m.rows base = some (cols.c0, base + m.len0) ∧
    decodeColumnAt b m.rows (base + m.len0) = some (cols.c1, base + m.len0 + m.len1) ∧
    decodeColumnAt b m.rows (base + m.len0 + m.len1) = some (cols.c2, base + m.len0 + m.len1 + m.len2) ∧
    decodeColumnAt b m.rows (base + m.len0 + m.len1 + m.len2) =
      some (cols.g, base + m.len0 + m.len1 + m.len2 + m.len3) ∧
    cols.c0.size = m.rows ∧ cols.c1.size = m.rows ∧ cols.c2.size = m.rows ∧ cols.g.size = m.rows ∧
    0 < m.rows ∧ cols.row 0 = m.first ∧ cols.row (m.rows - 1) = m.last ∧
    (∀ r s, r < s → s < m.rows → (cols.row r).lt (cols.row s) = true) := by
  unfold decodeBlockAt at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i c0 h0
      split at h
      · cases h
      · rename_i c1 h1
        split at h
        · cases h
        · rename_i c2 h2
          split at h
          · cases h
          · rename_i g h3
            obtain ⟨d0, s0⟩ := frame_ok _ _ _ _ _ _ _ h0
            obtain ⟨d1, s1⟩ := frame_ok _ _ _ _ _ _ _ h1
            obtain ⟨d2, s2⟩ := frame_ok _ _ _ _ _ _ _ h2
            obtain ⟨d3, s3⟩ := frame_ok _ _ _ _ _ _ _ h3
            split at h
            · cases h
            · rename_i hz
              split at h
              · cases h
              · rename_i hf
                split at h
                · cases h
                · rename_i hl
                  split at h
                  · cases h
                  · rename_i hs
                    cases h
                    have hz' : m.rows ≠ 0 := by simpa using hz
                    have hf' : Cols.row ⟨c0, c1, c2, g⟩ 0 = m.first := by simpa using hf
                    have hl' : Cols.row ⟨c0, c1, c2, g⟩ (m.rows - 1) = m.last := by simpa using hl
                    have hs' : colsSortedGo ⟨c0, c1, c2, g⟩ m.rows 0 = true := by simpa using hs
                    have hsz : Cols.size ⟨c0, c1, c2, g⟩ = m.rows := s0
                    refine ⟨d0, d1, d2, d3, s0, s1, s2, s3, by omega, hf', hl', ?_⟩
                    intro r t hrt ht
                    exact colsSortedGo_sorted _ m.rows (by omega) hs' r t hrt (by omega)

/-- The frame starts of a block at `base`. -/
def frameStart (m : BlockMeta) (base : Nat) : Nat → Nat
  | 0 => base
  | 1 => base + m.len0
  | 2 => base + m.len0 + m.len1
  | _ => base + m.len0 + m.len1 + m.len2

/-- The query path's word decoder on a frame of a block that activation
    admitted gives the words of the column `decodeBlockAt` checked. -/
theorem decodeWords_of_decodeBlockAt (b : ByteArray) (m : BlockMeta) (base : Nat) (cols : Cols)
    (h : decodeBlockAt b m base = .ok cols) (hrows : m.rows ≤ two64) (j : Nat) (hj : j < 4) :
    ∃ e, FrameWords.decodeWords b m.rows (frameStart m base j) =
      some (FrameWords.words (colOf cols.c0 cols.c1 cols.c2 cols.g j), e) := by
  obtain ⟨d0, d1, d2, d3, -⟩ := decodeBlockAt_ok b m base cols h
  rw [FrameWords.decodeWords_eq _ _ _ hrows]
  unfold FrameWords.decodeWordsRef
  match j, hj with
  | 0, _ => exact ⟨_, by rw [show frameStart m base 0 = base from rfl, d0]; rfl⟩
  | 1, _ => exact ⟨_, by rw [show frameStart m base 1 = base + m.len0 from rfl, d1]; rfl⟩
  | 2, _ => exact ⟨_, by rw [show frameStart m base 2 = base + m.len0 + m.len1 from rfl, d2]; rfl⟩
  | 3, _ => exact ⟨_, by rw [show frameStart m base 3 = base + m.len0 + m.len1 + m.len2 from rfl, d3]; rfl⟩

/-- For a block that activation admitted, the two binary searches of the scan
    over the words of its key columns select exactly the rows whose key
    prefix equals the key. -/
theorem scanRows_exact_of_decodeBlockAt (b : ByteArray) (m : BlockMeta) (base : Nat) (cols : Cols)
    (h : decodeBlockAt b m base = .ok cols) (key : Array UInt64) (hkey : key.size ≤ 4)
    (kw : Array ByteArray) (hkw : ∀ j, j < key.size → kw[j]! = FrameWords.words (colOf cols.c0 cols.c1 cols.c2 cols.g j))
    (r : Nat) (hr : r < m.rows) :
    (keyBound kw key false (Nat.log2 m.rows + 2) 0 m.rows ≤ r ∧
      r < keyBound kw key true (Nat.log2 m.rows + 2) (keyBound kw key false (Nat.log2 m.rows + 2) 0 m.rows) m.rows) ↔
      prefixCmp (cols.row r) key = .eq := by
  obtain ⟨d0, d1, d2, d3, s0, s1, s2, s3, -, -, -, hs⟩ := decodeBlockAt_ok b m base cols h
  have hsize : ∀ j, j < 4 → (colOf cols.c0 cols.c1 cols.c2 cols.g j).size = m.rows := by
    intro j hj
    match j, hj with
    | 0, _ => exact s0
    | 1, _ => exact s1
    | 2, _ => exact s2
    | 3, _ => exact s3
  have hv : ∀ j r, j < 4 → r < m.rows → (colOf cols.c0 cols.c1 cols.c2 cols.g j)[r]! < two64 := by
    intro j r hj hr
    have hmem : (colOf cols.c0 cols.c1 cols.c2 cols.g j)[r]! ∈ colOf cols.c0 cols.c1 cols.c2 cols.g j := by
      rw [getElem!_pos (colOf cols.c0 cols.c1 cols.c2 cols.g j) r (by rw [hsize j hj]; exact hr)]
      exact Array.getElem_mem _
    match j, hj with
    | 0, _ => exact decodeColumnAt_lt _ _ _ _ _ d0 _ hmem
    | 1, _ => exact decodeColumnAt_lt _ _ _ _ _ d1 _ hmem
    | 2, _ => exact decodeColumnAt_lt _ _ _ _ _ d2 _ hmem
    | 3, _ => exact decodeColumnAt_lt _ _ _ _ _ d3 _ hmem
  exact ScanTheorems.scanRows_exact cols.c0 cols.c1 cols.c2 cols.g m.rows key kw hkey hkw hsize hv
    (fun r s hrs hs' => hs r s hrs hs') r hr

end L4Factoidal.Storage.Sbm11.Block
