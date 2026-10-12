/-
L4Factoidal.Storage.Sbm11.ScanTheorems — block skipping by PRM1 metadata
(lemma L4 of `docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md`;
https://github.com/danbri/factoidal/issues/776).

* `Row` order: `lt_trans`, `le_trans`, `lt_of_le_of_lt`, `lt_of_lt_of_le`.
* `prefixCmp_gt_of_le`, `prefixCmp_lt_of_le`: the comparison of a row's key
  prefix is monotone in the row order.
* `chain_sorted`: an admitted PRM1 (`prmAdmitted`) has its blocks in row
  order: for `i ≤ j`, the first and the last rows of block `i` are not above
  those of block `j`; for `i < j`, the last row of block `i` is below the
  first row of block `j`.
* `blocksFor_complete`: a row between the first and the last row of block
  `k` of an admitted PRM1 whose key prefix equals the scan key is in a block
  that `blocksFor` returns and `selects` admits.
* `decodedRow_selected`: the same for every row of a block that decodes
  (`Block.decodeBlock`).

These say that `IdQuery.scanFoldM` reads every block that can hold a row with
the key prefix. The rows inside a block (`keyBound`, `selectRows`) and the
metadata shortcuts (`colConst?`) are other lemmas of the record.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdQuery
import L4Factoidal.Storage.Sbm11.BlockTheorems

namespace L4Factoidal.Storage.Sbm11.ScanTheorems

open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.IdQuery

/-! ## The row order -/

theorem lt_iff (a b : Row) : a.lt b = true ↔
    (a.c0 < b.c0 ∨ (a.c0 = b.c0 ∧ (a.c1 < b.c1 ∨ (a.c1 = b.c1 ∧
      (a.c2 < b.c2 ∨ (a.c2 = b.c2 ∧ a.g < b.g)))))) := by
  unfold Row.lt
  by_cases h0 : a.c0 = b.c0 <;> by_cases h1 : a.c1 = b.c1 <;> by_cases h2 : a.c2 = b.c2 <;>
    simp [h0, h1, h2] <;> omega

theorem le_iff (a b : Row) : a.le b = true ↔ a = b ∨ a.lt b = true := by
  simp [Row.le]

theorem row_eq_iff (a b : Row) : a = b ↔ (a.c0 = b.c0 ∧ a.c1 = b.c1 ∧ a.c2 = b.c2 ∧ a.g = b.g) := by
  cases a; cases b; simp

theorem lt_trans {a b c : Row} (h1 : a.lt b = true) (h2 : b.lt c = true) : a.lt c = true := by
  rw [lt_iff] at h1 h2 ⊢; omega

theorem lt_of_le_of_lt {a b c : Row} (h1 : a.le b = true) (h2 : b.lt c = true) : a.lt c = true := by
  rw [le_iff] at h1
  rcases h1 with h | h
  · subst h; exact h2
  · exact lt_trans h h2

theorem lt_of_lt_of_le {a b c : Row} (h1 : a.lt b = true) (h2 : b.le c = true) : a.lt c = true := by
  rw [le_iff] at h2
  rcases h2 with h | h
  · subst h; exact h1
  · exact lt_trans h1 h

theorem le_of_lt {a b : Row} (h : a.lt b = true) : a.le b = true := by
  rw [le_iff]; exact Or.inr h

theorem le_refl (a : Row) : a.le a = true := by
  rw [le_iff]; exact Or.inl rfl

theorem le_trans {a b c : Row} (h1 : a.le b = true) (h2 : b.le c = true) : a.le c = true := by
  rw [le_iff] at h1
  rcases h1 with h | h
  · subst h; exact h2
  · exact le_of_lt (lt_of_lt_of_le h h2)

/-- A strict row order step: the rows agree on the columns before `d` and
    differ at `d`, where the first is smaller. -/
theorem lt_exists_diff {a b : Row} (h : a.lt b = true) :
    ∃ d, (∀ i, i < d → rowCol a i = rowCol b i) ∧ rowCol a d < rowCol b d := by
  rw [lt_iff] at h
  rcases h with h | ⟨e0, h | ⟨e1, h | ⟨e2, h⟩⟩⟩
  · exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _), h⟩
  · refine ⟨1, fun i hi => ?_, h⟩
    have : i = 0 := by omega
    subst this; exact e0
  · refine ⟨2, fun i hi => ?_, h⟩
    rcases i with _ | _ | i
    · exact e0
    · exact e1
    · omega
  · refine ⟨3, fun i hi => ?_, h⟩
    rcases i with _ | _ | _ | i
    · exact e0
    · exact e1
    · exact e2
    · omega

/-! ## The key prefix comparison is monotone -/

theorem prefixCmpGo_gt_mono (a b : Row) (key : Array UInt64) (d : Nat)
    (hag : ∀ i, i < d → rowCol a i = rowCol b i) (hd : rowCol a d < rowCol b d) :
    ∀ f j, j ≤ d → prefixCmpGo a key f j = .gt → prefixCmpGo b key f j = .gt := by
  intro f
  induction f with
  | zero => intro j _ h; simp [prefixCmpGo] at h
  | succ f ih =>
    intro j hj h
    simp only [prefixCmpGo] at h ⊢
    by_cases hk : j < key.size
    · rw [if_pos hk] at h ⊢
      by_cases hjd : j < d
      · rw [← hag j hjd]
        split at h
        · simp at h
        · split at h
          · rw [if_neg (by assumption), if_pos (by assumption)]
          · rw [if_neg (by assumption), if_neg (by assumption)]
            exact ih (j + 1) (by omega) h
      · have hje : j = d := by omega
        subst hje
        split at h
        · simp at h
        · rw [if_neg (by omega), if_pos (by omega)]
    · rw [if_neg hk] at h; simp at h

theorem prefixCmpGo_lt_mono (a b : Row) (key : Array UInt64) (d : Nat)
    (hag : ∀ i, i < d → rowCol a i = rowCol b i) (hd : rowCol a d < rowCol b d) :
    ∀ f j, j ≤ d → prefixCmpGo b key f j = .lt → prefixCmpGo a key f j = .lt := by
  intro f
  induction f with
  | zero => intro j _ h; simp [prefixCmpGo] at h
  | succ f ih =>
    intro j hj h
    simp only [prefixCmpGo] at h ⊢
    by_cases hk : j < key.size
    · rw [if_pos hk] at h ⊢
      by_cases hjd : j < d
      · rw [hag j hjd]
        split at h
        · rw [if_pos (by assumption)]
        · split at h
          · simp at h
          · rw [if_neg (by assumption), if_neg (by assumption)]
            exact ih (j + 1) (by omega) h
      · have hje : j = d := by omega
        subst hje
        split at h
        · rw [if_pos (by omega)]
        · split at h
          · simp at h
          · rw [if_pos (by omega)]
    · rw [if_neg hk] at h; simp at h

/-- A row not below `a` has a key prefix above `key` when `a` does. -/
theorem prefixCmp_gt_of_le {a b : Row} (key : Array UInt64) (h : a.le b = true)
    (ha : prefixCmp a key = .gt) : prefixCmp b key = .gt := by
  rw [le_iff] at h
  rcases h with h | h
  · subst h; exact ha
  · obtain ⟨d, hag, hd⟩ := lt_exists_diff h
    unfold prefixCmp at ha ⊢
    exact prefixCmpGo_gt_mono a b key d hag hd _ 0 (Nat.zero_le _) ha

/-- A row not above `b` has a key prefix below `key` when `b` does. -/
theorem prefixCmp_lt_of_le {a b : Row} (key : Array UInt64) (h : a.le b = true)
    (hb : prefixCmp b key = .lt) : prefixCmp a key = .lt := by
  rw [le_iff] at h
  rcases h with h | h
  · subst h; exact hb
  · obtain ⟨d, hag, hd⟩ := lt_exists_diff h
    unfold prefixCmp at hb ⊢
    exact prefixCmpGo_lt_mono a b key d hag hd _ 0 (Nat.zero_le _) hb

/-! ## An admitted PRM1 is in row order -/

theorem metaFits_le {m : BlockMeta} (h : metaFits m = true) : m.first.le m.last = true := by
  simp only [metaFits, Bool.and_eq_true] at h
  exact h.2

theorem chainGo_pairwise : ∀ (ms : List BlockMeta) (off : Nat), chainGo off ms = true →
    ms.Pairwise (fun a b => a.last.lt b.first = true) := by
  intro ms
  induction ms with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons m ms ih =>
    intro off h
    simp only [chainGo] at h
    split at h
    · cases ms with
      | nil => exact List.pairwise_singleton _ _
      | cons n rest =>
        dsimp only at h
        split at h
        · rename_i hmn
          have hp := ih _ h
          have hfit := chainGo_fits (n :: rest) _ h
          refine List.Pairwise.cons ?_ hp
          intro x hx
          rcases List.mem_cons.mp hx with hx | hx
          · subst hx; exact hmn
          · have hnx : n.last.lt x.first = true := (List.pairwise_cons.mp hp).1 x hx
            exact lt_trans (lt_of_lt_of_le hmn (metaFits_le (hfit n (by simp)))) hnx
        · cases h
    · cases h

/-- Blocks of an admitted PRM1 are in row order. -/
theorem chain_sorted (ms : List BlockMeta) (off : Nat) (h : chainGo off ms = true)
    (i j : Nat) (hi : i < ms.length) (hj : j < ms.length) :
    (i < j → ms[i].last.lt ms[j].first = true) ∧
    (i ≤ j → ms[i].first.le ms[j].first = true ∧ ms[i].last.le ms[j].last = true) := by
  have hp := chainGo_pairwise ms off h
  have hfit := chainGo_fits ms off h
  have hlt : i < j → ms[i].last.lt ms[j].first = true := by
    intro hij
    exact List.pairwise_iff_getElem.mp hp i j hi hj hij
  refine ⟨hlt, fun hij => ?_⟩
  rcases Nat.lt_or_eq_of_le hij with hij | hij
  · have h1 := hlt hij
    have fi := metaFits_le (hfit _ (List.getElem_mem hi))
    have fj := metaFits_le (hfit _ (List.getElem_mem hj))
    exact ⟨le_of_lt (lt_of_le_of_lt fi h1), le_of_lt (lt_of_lt_of_le h1 fj)⟩
  · subst hij; exact ⟨le_refl _, le_refl _⟩

/-! ## The binary search and the block walk -/

theorem firstBlockGo_le (metas : Array BlockMeta) (key : Array UInt64) (k : Nat)
    (hk : k < metas.size) (hnk : prefixCmp metas[k]!.last key ≠ .lt)
    (hsorted : ∀ i, k ≤ i → i < metas.size → prefixCmp metas[i]!.last key = .lt →
      prefixCmp metas[k]!.last key = .lt) :
    ∀ f l h, h ≤ metas.size → l ≤ k → firstBlockGo metas key f l h ≤ k := by
  intro f
  induction f with
  | zero => intro l h _ hl; simpa [firstBlockGo] using hl
  | succ f ih =>
    intro l h hh hl
    simp only [firstBlockGo]
    split
    · split
      · rename_i hlh hc
        apply ih _ _ hh
        have hc' : prefixCmp metas[(l + h) / 2]!.last key = .lt := by simpa using hc
        by_cases hkm : k ≤ (l + h) / 2
        · exact absurd (hsorted _ hkm (by omega) hc') hnk
        · omega
      · exact ih _ _ (by omega) hl
    · exact hl

theorem blocksForGo_keeps (metas : Array BlockMeta) (key : Array UInt64) (x : Nat) :
    ∀ f i (out : Array Nat), x ∈ out → x ∈ blocksForGo metas key f i out := by
  intro f
  induction f with
  | zero => intro i out h; simpa [blocksForGo] using h
  | succ f ih =>
    intro i out h
    simp only [blocksForGo]
    split
    · exact h
    · split
      · exact h
      · exact ih _ _ (Array.mem_push.mpr (Or.inl h))

theorem blocksForGo_reach (metas : Array BlockMeta) (key : Array UInt64) (k : Nat)
    (hk : k < metas.size) :
    ∀ f i (out : Array Nat), i ≤ k → k - i < f →
      (∀ j, i ≤ j → j ≤ k → prefixCmp metas[j]!.first key ≠ .gt) →
      k ∈ blocksForGo metas key f i out := by
  intro f
  induction f with
  | zero => intro i out _ hf _; omega
  | succ f ih =>
    intro i out hik hf hj
    simp only [blocksForGo]
    rw [if_neg (by omega)]
    have hgt : (prefixCmp metas[i]!.first key == .gt) = false := by
      have := hj i (Nat.le_refl _) hik
      cases hc : prefixCmp metas[i]!.first key <;> simp_all
    rw [hgt, if_neg (by simp)]
    by_cases hik' : i = k
    · subst hik'
      exact blocksForGo_keeps metas key i f _ _ (Array.mem_push.mpr (Or.inr rfl))
    · exact ih _ _ (by omega) (by omega) (fun j h1 h2 => hj j (by omega) h2)

/-! ## Block skipping -/

private theorem getElem!_toArray (ms : List BlockMeta) (i : Nat) (h : i < ms.length) :
    ms.toArray[i]! = ms[i] := by
  simp [getElem!_pos, h]

/-- Block skipping is complete: a row between the first and the last row of
    block `k` of an admitted PRM1, whose key prefix equals the scan key, is
    in a block that `blocksFor` returns and that `selects` admits. -/
theorem blocksFor_complete (perm : Nat) (ms : List BlockMeta) (hadm : prmAdmitted perm ms = true)
    (key : Array UInt64) (k : Nat) (hk : k < ms.length) (r : Row)
    (h1 : ms[k].first.le r = true) (h2 : r.le ms[k].last = true) (hr : prefixCmp r key = .eq) :
    k ∈ blocksFor ms.toArray key ∧ selects ms[k] key = true := by
  have hch : chainGo prbHeaderBytes ms = true := by
    simp only [prmAdmitted, Bool.and_eq_true] at hadm
    exact hadm.1.1.2
  have hsz : ms.toArray.size = ms.length := List.size_toArray
  -- the last row of block k is not below the key
  have hlast : prefixCmp ms[k].last key ≠ .lt := by
    intro hc
    have := prefixCmp_lt_of_le key h2 hc
    rw [hr] at this; cases this
  have hfirst : prefixCmp ms[k].first key ≠ .gt := by
    intro hc
    have := prefixCmp_gt_of_le key h1 hc
    rw [hr] at this; cases this
  refine ⟨?_, ?_⟩
  · unfold blocksFor
    have hstart : firstBlockGo ms.toArray key (Nat.log2 ms.toArray.size + 2) 0 ms.toArray.size ≤ k := by
      apply firstBlockGo_le ms.toArray key k (by omega)
      · rw [getElem!_toArray ms k hk]; exact hlast
      · intro i hki hi hc
        rw [getElem!_toArray ms i (by omega)] at hc
        rw [getElem!_toArray ms k hk]
        exact prefixCmp_lt_of_le key ((chain_sorted ms _ hch k i hk (by omega)).2 hki).2 hc
      · omega
      · omega
    apply blocksForGo_reach ms.toArray key k (by omega) _ _ _ hstart (by omega)
    intro j _ hjk
    rw [getElem!_toArray ms j (by omega)]
    intro hc
    exact hfirst (prefixCmp_gt_of_le key ((chain_sorted ms _ hch j k (by omega) hk).2 hjk).1 hc)
  · unfold selects
    cases hf : prefixCmp ms[k].first key <;> cases hl : prefixCmp ms[k].last key <;> simp_all

/-! ## Rows of a decoded block -/

theorem sortedGo_bounds : ∀ (rows : List Row) (prev : Row), sortedGo prev rows = true →
    ∀ r ∈ rows, prev.lt r = true ∧ ∀ l, rows.getLast? = some l → r.le l = true := by
  intro rows
  induction rows with
  | nil => intro _ _ r hr; cases hr
  | cons x xs ih =>
    intro prev h r hr
    simp only [sortedGo] at h
    split at h
    · rename_i hpx
      have hrest := ih x h
      rcases List.mem_cons.mp hr with hr | hr
      · subst hr
        refine ⟨hpx, fun l hl => ?_⟩
        cases xs with
        | nil => simp at hl; subst hl; exact le_refl _
        | cons y ys =>
          have hl' : (y :: ys).getLast? = some l := by simpa using hl
          exact le_of_lt (lt_of_lt_of_le (hrest y (by simp)).1
            ((hrest y (by simp)).2 l hl'))
      · obtain ⟨hxr, hrl⟩ := hrest r hr
        refine ⟨lt_trans hpx hxr, fun l hl => ?_⟩
        cases xs with
        | nil => cases hr
        | cons y ys => exact hrl l (by simpa using hl)
    · cases h

/-- Every row of a sorted list lies between its first and its last row. -/
theorem rowsSorted_bounds (rows : List Row) (h : rowsSorted rows = true) (f l : Row)
    (hf : rows.head? = some f) (hl : rows.getLast? = some l) :
    ∀ r ∈ rows, f.le r = true ∧ r.le l = true := by
  cases rows with
  | nil => intro r hr; cases hr
  | cons x xs =>
    simp only [List.head?_cons, Option.some.injEq] at hf
    subst hf
    simp only [rowsSorted] at h
    intro r hr
    rcases List.mem_cons.mp hr with hr | hr
    · subst hr
      refine ⟨le_refl _, ?_⟩
      cases xs with
      | nil => simp at hl; subst hl; exact le_refl _
      | cons y ys =>
        have hb := sortedGo_bounds (y :: ys) r h y (by simp)
        exact le_of_lt (lt_of_lt_of_le hb.1 (hb.2 l (by simpa using hl)))
    · have hb := sortedGo_bounds xs x h r hr
      refine ⟨le_of_lt hb.1, ?_⟩
      cases xs with
      | nil => cases hr
      | cons y ys => exact hb.2 l (by simpa using hl)

/-- Every row of block `k` of an admitted PRM1 that decodes, and whose key
    prefix equals the scan key, is in a block that the scan reads. -/
theorem decodedRow_selected (perm : Nat) (ms : List BlockMeta) (hadm : prmAdmitted perm ms = true)
    (key : Array UInt64) (k : Nat) (hk : k < ms.length) (bs : List UInt8) (rows : List Row)
    (hdec : decodeBlock ms[k] bs = some rows) (r : Row) (hr : r ∈ rows)
    (hkey : prefixCmp r key = .eq) :
    k ∈ blocksFor ms.toArray key ∧ selects ms[k] key = true := by
  obtain ⟨_, hf, hl, hs⟩ := decodeBlock_bounds _ _ _ hdec
  obtain ⟨h1, h2⟩ := rowsSorted_bounds rows hs _ _ hf hl r hr
  exact blocksFor_complete perm ms hadm key k hk r h1 h2 hkey

/-! ## The loop forms before the refactor, compared on samples

`prefixCmp` and `blocksFor` were `for` loops with early exit until
2026-10-12; they were rewritten as tail calls with fuel for these proofs.
The `#guard`s compare the old forms with the new ones. -/

namespace OldForms

private def prefixCmpOld (r : Row) (key : Array UInt64) : Ordering := Id.run do
  for j in [0:key.size] do
    let a := rowCol r j
    let b := key[j]!.toNat
    if a < b then return .lt
    if b < a then return .gt
  return .eq

private def blocksForOld (metas : Array BlockMeta) (key : Array UInt64) : Array Nat := Id.run do
  let start := firstBlockGo metas key (Nat.log2 metas.size + 2) 0 metas.size
  let mut out : Array Nat := #[]
  let mut i := start
  for _ in [0:metas.size] do
    if i ≥ metas.size then break
    if prefixCmpOld metas[i]!.first key == .gt then break
    out := out.push i
    i := i + 1
  return out

private def sampleRows : List Row :=
  [⟨0, 0, 0, 0⟩, ⟨1, 2, 3, 0⟩, ⟨1, 2, 3, 5⟩, ⟨1, 2, 4, 0⟩, ⟨1, 5, 0, 0⟩, ⟨2, 0, 0, 0⟩, ⟨7, 7, 7, 7⟩]

private def sampleKeys : List (Array UInt64) :=
  [#[], #[0], #[1], #[1, 2], #[1, 2, 3], #[1, 2, 3, 5], #[1, 2, 3, 5, 5], #[1, 3], #[2], #[3],
   #[7, 7, 7, 7, 7]]

private def mk (f l : Row) : BlockMeta :=
  { first := f, last := l, rows := 1, offset := 0, len0 := 0, len1 := 0, len2 := 0, len3 := 0 }

private def sampleMetas : List (Array BlockMeta) :=
  [#[], #[mk ⟨1, 2, 3, 0⟩ ⟨1, 2, 3, 5⟩],
   #[mk ⟨0, 0, 0, 0⟩ ⟨1, 2, 3, 0⟩, mk ⟨1, 2, 3, 5⟩ ⟨1, 2, 4, 0⟩, mk ⟨1, 5, 0, 0⟩ ⟨2, 0, 0, 0⟩,
     mk ⟨7, 7, 7, 7⟩ ⟨7, 7, 7, 7⟩],
   #[mk ⟨1, 0, 0, 0⟩ ⟨1, 1, 0, 0⟩, mk ⟨1, 1, 1, 0⟩ ⟨1, 2, 0, 0⟩, mk ⟨1, 2, 1, 0⟩ ⟨1, 2, 9, 0⟩,
     mk ⟨1, 3, 0, 0⟩ ⟨2, 0, 0, 0⟩]]

#guard sampleRows.all fun r => sampleKeys.all fun k => prefixCmp r k == prefixCmpOld r k
#guard sampleMetas.all fun ms => sampleKeys.all fun k => blocksFor ms k == blocksForOld ms k

end OldForms

end L4Factoidal.Storage.Sbm11.ScanTheorems
