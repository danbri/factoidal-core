/-
L4Factoidal.Storage.Sbm11.ParallelMergeTheorems — the parent's merge of the
divided single-pattern paths gives the single pass's answer (stage 1b of
https://github.com/danbri/factoidal/issues/799; record
docs/designissues/2026-10-12-parallel-block-scans.md, section "Stage 1b").

`IdQuery.runPlanM` divides the selected blocks `L` of a scan into consecutive
block ranges (`ParallelScan.chunksOf c L`), runs one job per range, and folds
the range results in range order. The statements are list lemmas over the
rows of the blocks: `R b` is the list of rows (after the FILTERs) that block
`b` gives, in row order, as the single-thread loop sees them (for a full scan
of an admitted permutation with no overlay, `ParallelScanTheorems` and
`ScanFoldTheorems.forIn_blocks` give the scan rows block by block).

* Streamed path. The single-thread loop steps over the blocks with
  `winStep off lim` (skip what is left of OFFSET, keep what is left of
  LIMIT). A range keeps the first `cap` of its rows (`cap` = OFFSET + LIMIT,
  `IdQuery.streamPartM`) and the parent steps over the ranges' rows with the
  same `winStep` (`IdQuery.emitPieceM`, over pieces of a range: any partition
  of the rows gives the same window, `window_fold`).
  `stream_divided_eq_single`: the two answers are equal.
* Counted path. A group map is modelled as `GM`: the keys in order of first
  appearance and a count per key. `IdQuery.countChunk` adds a list of
  (key, count) pairs per block; `IdQuery.Groups.merge a b` adds `b`'s keys
  with their counts to `a`, in `b`'s order (`GM.merge`).
  `groups_divided_eq_single`: merging the range maps in range order gives
  the map of the single pass (same keys in the same order, same counts).
  `count_divided_eq_single`: the range counts add up to the count of the
  concatenation.
* ORDER BY ... LIMIT k. The order is a total preorder `le` on rows (the
  ORDER BY comparison of `IdQuery.orderPermM`), the sort stable (equal rows
  keep their order: `List.mergeSort`, the stable merge sort of the Lean core
  library), `topK k l = (l.mergeSort le).take k`. `topK_divided_eq_single`:
  `topK k` of the concatenation of the ranges' `topK k` equals `topK k` of
  all rows.

Tested, not proved: that the production code computes these list functions
(`Table`, `ByteArray` rendering, the `Std.HashMap` of `Groups`, the array
code of `Qlvr.Query.topK` and `sortPermByKey`, per-range order keys giving
the same comparison as keys over the union), and the `IO` instance; the
answer tests are tests/sbm11/threads.sh. No hypothesis states a conclusion:
the hypotheses are `off + lim ≤ cap` (the cap the code uses), and for the
sort the transitivity and totality of `le`.
-/
import L4Factoidal.Storage.Sbm11.ParallelScan

namespace L4Factoidal.Storage.Sbm11.ParallelMergeTheorems

open L4Factoidal.Storage.Sbm11.ParallelScan (chunksOf chunksOf_flatten)

/-! ## Concatenating per-range results -/

/-- A `flatMap` of per-chunk `flatMap`s is the `flatMap` of the flattened
    chunks. -/
theorem flatMap_chunks {α β : Type} (xss : List (List α)) (F : α → List β) :
    (xss.map fun X => X.flatMap F).flatten = xss.flatten.flatMap F := by
  induction xss with
  | nil => rfl
  | cons X xs ih => simp [List.flatten_cons, List.flatMap_append, ih]

/-! ## Streamed path: the window [OFFSET, OFFSET + LIMIT) -/

/-- One step of the streamed path over a list of rows: skip what is left of
    `off`, keep up to what is left of `lim`. The state is (rows skipped, rows
    kept, kept rows). -/
def winStep {α : Type} (off lim : Nat) (st : Nat × Nat × List α) (P : List α) : Nat × Nat × List α :=
  let skipHere := min (off - st.1) P.length
  let takeHere := min (lim - st.2.1) (P.length - skipHere)
  (st.1 + skipHere, st.2.1 + takeHere, st.2.2 ++ (P.drop skipHere).take takeHere)

/-- The state after the rows `pre`: `min off |pre|` skipped and the window of
    `pre` kept. -/
def winState {α : Type} (off lim : Nat) (pre : List α) : Nat × Nat × List α :=
  (min off pre.length, ((pre.drop off).take lim).length, (pre.drop off).take lim)

/-- `l.take (min n l.length) = l.take n`. -/
theorem take_min_length {α : Type} (l : List α) (n : Nat) : l.take (min n l.length) = l.take n := by
  by_cases h : n ≤ l.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.take_length, List.take_of_length_le (by omega)]

/-- The kept rows after one more part. -/
theorem winStep_rows {α : Type} (off lim : Nat) (pre P : List α) :
    (pre.drop off).take lim ++
        (P.drop (min (off - min off pre.length) P.length)).take
          (min (lim - ((pre.drop off).take lim).length)
            (P.length - min (off - min off pre.length) P.length))
      = ((pre ++ P).drop off).take lim := by
  by_cases h : off ≤ pre.length
  · -- the OFFSET lies in `pre`: nothing of `P` is skipped
    rw [Nat.min_eq_left h, Nat.sub_self, Nat.zero_min, List.drop_zero, Nat.sub_zero,
      List.drop_append_of_le_length h, List.take_append, List.length_take, List.length_drop,
      take_min_length]
    congr 2
    omega
  · -- the OFFSET lies beyond `pre`: nothing kept yet
    have h' : pre.length ≤ off := by omega
    have hpre : pre.drop off = [] := List.drop_eq_nil_of_le h'
    rw [Nat.min_eq_right h', hpre, List.take_nil, List.nil_append, List.length_nil, Nat.sub_zero,
      List.drop_append, hpre, List.nil_append]
    by_cases hp : off - pre.length ≤ P.length
    · rw [Nat.min_eq_left hp]
      have hl : P.length - (off - pre.length) = (P.drop (off - pre.length)).length := by
        rw [List.length_drop]
      rw [hl, take_min_length]
    · have hp' : P.length ≤ off - pre.length := Nat.le_of_lt (Nat.lt_of_not_le hp)
      rw [Nat.min_eq_right hp', List.drop_length, List.take_nil, List.drop_eq_nil_of_le hp',
        List.take_nil]

theorem winStep_state {α : Type} (off lim : Nat) (pre P : List α) :
    winStep off lim (winState off lim pre) P = winState off lim (pre ++ P) := by
  have hrows := winStep_rows off lim pre P
  simp only [winStep, winState]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [List.length_append]; omega
  · simp only
    rw [← hrows]
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  · exact hrows

/-- Stepping over the parts in order keeps the window of their
    concatenation. -/
theorem window_fold_state {α : Type} (off lim : Nat) :
    ∀ (parts : List (List α)) (pre : List α),
      parts.foldl (winStep off lim) (winState off lim pre) = winState off lim (pre ++ parts.flatten)
  | [], pre => by simp
  | P :: ps, pre => by
    simp only [List.foldl_cons, List.flatten_cons]
    rw [winStep_state, window_fold_state off lim ps (pre ++ P), List.append_assoc]

/-- **The window of any partition.** The streamed step over the parts of a
    list, in order, from the start, keeps rows `[off, off + lim)` of the
    concatenation. -/
theorem window_fold {α : Type} (off lim : Nat) (parts : List (List α)) :
    (parts.foldl (winStep off lim) (0, 0, [])).2.2 = (parts.flatten.drop off).take lim := by
  have h := window_fold_state off lim parts []
  simp only [winState, List.length_nil, Nat.min_zero, List.drop_nil, List.take_nil,
    List.nil_append] at h
  rw [h]

/-- `(l.take n ++ r).take n = (l ++ r).take n`. -/
theorem take_take_append {α : Type} (l r : List α) (n : Nat) :
    (l.take n ++ r).take n = (l ++ r).take n := by
  rw [List.take_append, List.take_append, List.take_take, Nat.min_self, List.length_take]
  by_cases h : n ≤ l.length
  · rw [Nat.min_eq_left h]
    simp [Nat.sub_eq_zero_of_le h]
  · rw [Nat.min_eq_right (by omega), List.take_of_length_le (by omega)]

/-- Keeping the first `cap ≥ off + lim` rows of each part does not change
    the window `[off, off + lim)` of the concatenation. -/
theorem window_cap {α : Type} (cap : Nat) :
    ∀ (parts : List (List α)) (off lim : Nat), off + lim ≤ cap →
      (((parts.map (·.take cap)).flatten.drop off).take lim) = ((parts.flatten.drop off).take lim)
  | [], _, _, _ => rfl
  | P :: ps, off, lim, h => by
    simp only [List.map_cons, List.flatten_cons]
    by_cases hP : P.length ≤ cap
    · rw [List.take_of_length_le hP, List.drop_append, List.drop_append, List.take_append,
        List.take_append]
      have ih := window_cap cap ps (off - P.length) (lim - (P.drop off).length) (by
        simp only [List.length_drop]; omega)
      rw [ih]
    · have hP' : cap < P.length := Nat.lt_of_not_le hP
      have hl : (P.take cap).length = cap := List.length_take_of_le (Nat.le_of_lt hP')
      have h1 : lim ≤ ((P.take cap).drop off).length := by
        simp only [List.length_drop, hl]; omega
      have h2 : lim ≤ (P.drop off).length := by
        simp only [List.length_drop]; omega
      rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length h1,
        List.drop_append_of_le_length (by omega), List.take_append_of_le_length h2,
        List.drop_take, List.take_take]
      congr 1
      omega

/-- A range's rows: the rows of its blocks, in order, at most `cap` of them
    (the loop of `IdQuery.streamPartM`, which stops at `cap`, keeps exactly
    these: once `cap` rows are kept, a later block adds none). The step
    adds the first `cap - |acc|` rows of each block. -/
theorem capFold {α β : Type} (R : β → List α) (cap : Nat) :
    ∀ (X : List β) (acc : List α), acc.length ≤ cap →
      X.foldl (fun acc b => acc ++ (R b).take (cap - acc.length)) acc = (acc ++ X.flatMap R).take cap
  | [], acc, h => by simp [List.take_of_length_le h]
  | b :: bs, acc, h => by
    simp only [List.foldl_cons, List.flatMap_cons]
    have hstep : acc ++ (R b).take (cap - acc.length) = (acc ++ R b).take cap := by
      rw [List.take_append, List.take_of_length_le h]
    rw [hstep, capFold R cap bs _ (by rw [List.length_take]; exact Nat.min_le_left _ _),
      take_take_append, List.append_assoc]

/-- **Streamed path: the divided answer is the single-thread answer.** The
    blocks `L` cut into ranges of at most `c` blocks; each range keeps the
    first `cap` of its rows; the parent steps over the ranges in order. With
    `off + lim ≤ cap`, the rows kept are the rows the single-thread loop
    keeps stepping block by block. -/
theorem stream_divided_eq_single {α β : Type} (R : β → List α) (L : List β) (c off lim cap : Nat)
    (hcap : off + lim ≤ cap) :
    (((chunksOf c L).map fun X => (X.flatMap R).take cap).foldl (winStep off lim) (0, 0, [])).2.2
      = ((L.map R).foldl (winStep off lim) (0, 0, [])).2.2 := by
  rw [window_fold, window_fold]
  have hmap : ((chunksOf c L).map fun X => (X.flatMap R).take cap)
      = ((chunksOf c L).map fun X => X.flatMap R).map (·.take cap) := by
    simp [List.map_map, Function.comp_def]
  rw [hmap, window_cap cap _ off lim hcap, flatMap_chunks, chunksOf_flatten]
  congr 2

/-! ## Counted path: counts and group maps -/

/-- **Counts.** The rows of the ranges add up to the rows of all blocks. -/
theorem count_divided_eq_single {α β : Type} (R : β → List α) (L : List β) (c : Nat) :
    ((chunksOf c L).map fun X => (X.flatMap R).length).sum = (L.flatMap R).length := by
  have h := flatMap_chunks (chunksOf c L) R
  rw [chunksOf_flatten] at h
  rw [← h, List.length_flatten, List.map_map]
  rfl

/-- A group map: the keys in order of first appearance and a count per key.
    These are what `IdQuery.groupTable` reads of `IdQuery.Groups`: its `keys`
    array and `counts.getD k 0`. -/
structure GM (K : Type) where
  keys : List K
  cnt : K → Nat

section Groups

variable {K : Type} [DecidableEq K]

/-- `IdQuery.Groups.add`: `n` more rows of key `k`; a new key goes last. -/
def GM.add (g : GM K) (k : K) (n : Nat) : GM K :=
  { keys := if k ∈ g.keys then g.keys else g.keys ++ [k]
    cnt := fun x => if x = k then g.cnt x + n else g.cnt x }

/-- (key, count) pairs added in order (`IdQuery.countChunk` adds the runs of
    a block so). -/
def GM.addAll (g : GM K) (ps : List (K × Nat)) : GM K :=
  ps.foldl (fun g p => g.add p.1 p.2) g

/-- No groups. -/
def GM.empty : GM K := { keys := [], cnt := fun _ => 0 }

/-- `IdQuery.Groups.merge a b`: `b`'s keys with their counts added to `a`,
    in `b`'s key order. -/
def GM.merge (a b : GM K) : GM K := a.addAll (b.keys.map fun k => (k, b.cnt k))

/-- A key added to a key list: last when it is new. -/
def kstep (ks : List K) (k : K) : List K := if k ∈ ks then ks else ks ++ [k]

/-- Keys added in order. -/
def kfold (ks l : List K) : List K := l.foldl kstep ks

/-- The count of key `x` in a list of pairs. -/
def psum (ps : List (K × Nat)) (x : K) : Nat := ((ps.filter fun p => p.1 = x).map (·.2)).sum

omit [DecidableEq K] in
theorem GM.ext' {g h : GM K} (hk : g.keys = h.keys) (hc : ∀ x, g.cnt x = h.cnt x) : g = h := by
  obtain ⟨k1, c1⟩ := g
  obtain ⟨k2, c2⟩ := h
  simp only at hk hc
  subst hk
  have : c1 = c2 := funext hc
  subst this
  rfl

theorem addAll_keys : ∀ (g : GM K) (ps : List (K × Nat)),
    (g.addAll ps).keys = kfold g.keys (ps.map (·.1))
  | _, [] => rfl
  | g, p :: ps => by
    simp only [GM.addAll, List.foldl_cons, List.map_cons, kfold] at *
    exact addAll_keys (g.add p.1 p.2) ps

theorem psum_cons (p : K × Nat) (ps : List (K × Nat)) (x : K) :
    psum (p :: ps) x = (if p.1 = x then p.2 else 0) + psum ps x := by
  unfold psum
  by_cases h : p.1 = x <;> simp [h]

theorem addAll_cnt : ∀ (g : GM K) (ps : List (K × Nat)) (x : K),
    (g.addAll ps).cnt x = g.cnt x + psum ps x
  | _, [], _ => by simp [GM.addAll, psum]
  | g, p :: ps, x => by
    have ih := addAll_cnt (g.add p.1 p.2) ps x
    simp only [GM.addAll, List.foldl_cons] at *
    rw [ih, psum_cons]
    simp only [GM.add]
    by_cases h : x = p.1
    · subst h; simp; omega
    · have h' : ¬ p.1 = x := fun e => h e.symm
      simp [h, h']

theorem mem_kfold : ∀ (ks l : List K) (x : K), x ∈ kfold ks l ↔ x ∈ ks ∨ x ∈ l
  | ks, [], x => by simp [kfold]
  | ks, k :: l, x => by
    have ih := mem_kfold (kstep ks k) l x
    simp only [kfold, List.foldl_cons] at *
    rw [ih]
    unfold kstep
    by_cases hk : k ∈ ks
    · simp only [hk, if_true, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · subst h; exact Or.inl hk
        · exact Or.inr h
    · simp only [hk, if_false, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

theorem kfold_nodup : ∀ (ks l : List K), ks.Nodup → (kfold ks l).Nodup
  | ks, [], h => by simpa [kfold] using h
  | ks, k :: l, h => by
    simp only [kfold, List.foldl_cons]
    apply kfold_nodup
    unfold kstep
    by_cases hk : k ∈ ks
    · simpa [hk] using h
    · simp only [hk, if_false]
      rw [List.nodup_append]
      refine ⟨h, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      intro e; subst e; exact hk ha

/-- Keys added to `ks`: `ks`, then the new keys in order of first
    appearance. -/
theorem kfold_eq : ∀ (ks l : List K), kfold ks l = ks ++ (kfold [] l).filter (fun k => k ∉ ks)
  | ks, [] => by simp [kfold]
  | ks, k :: l => by
    have ih1 := kfold_eq (kstep ks k) l
    have ih2 := kfold_eq [k] l
    simp only [kfold, List.foldl_cons] at *
    rw [ih1]
    have hk0 : kstep [] k = [k] := by simp [kstep]
    rw [hk0, ih2]
    unfold kstep
    by_cases hk : k ∈ ks
    · simp only [hk, if_true, List.filter_append, List.filter_cons, List.filter_nil,
        List.filter_filter]
      congr 1
      apply List.filter_congr
      intro x _
      by_cases hx : x ∈ ks
      · simp [hx]
      · have : x ≠ k := fun e => hx (e ▸ hk)
        simp [hx, this]
    · simp only [hk, if_false, List.filter_append, List.filter_cons, List.filter_nil,
        List.append_assoc, List.filter_filter]
      simp only [List.singleton_append]
      congr 2
      apply List.filter_congr
      intro x _
      by_cases hx : x = k
      · subst hx; simp [hk]
      · simp [List.mem_append, hx]

/-- A list of distinct keys added to `ks`, none of them in `ks`, goes after
    `ks` as it is. -/
theorem kfold_nodup_eq : ∀ (ks l : List K), l.Nodup → (∀ x ∈ l, x ∉ ks) → kfold ks l = ks ++ l
  | ks, [], _, _ => by simp [kfold]
  | ks, k :: l, hn, hd => by
    simp only [kfold, List.foldl_cons]
    have hk : k ∉ ks := hd k (by simp)
    have hks : kstep ks k = ks ++ [k] := by simp [kstep, hk]
    rw [hks]
    have hn' := List.nodup_cons.mp hn
    have := kfold_nodup_eq (ks ++ [k]) l hn'.2 (by
      intro x hx hmem
      rw [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with h | h
      · exact hd x (by simp [hx]) h
      · subst h; exact hn'.1 hx)
    simp only [kfold] at this
    rw [this]
    simp

/-- The count of key `x` in the pairs of distinct keys `ks` with counts
    `c`. -/
theorem psum_keys (c : K → Nat) : ∀ (ks : List K), ks.Nodup → ∀ x,
    psum (ks.map fun k => (k, c k)) x = if x ∈ ks then c x else 0
  | [], _, x => by simp [psum]
  | k :: ks, hn, x => by
    have hn' := List.nodup_cons.mp hn
    simp only [List.map_cons]
    rw [psum_cons, psum_keys c ks hn'.2 x]
    by_cases h : k = x
    · subst h; simp [hn'.1]
    · have h' : x ≠ k := fun e => h e.symm
      simp [h, h']

/-- No pair has key `x`: count 0. -/
theorem psum_eq_zero (ps : List (K × Nat)) (x : K) (h : x ∉ ps.map (·.1)) : psum ps x = 0 := by
  unfold psum
  have : (ps.filter fun p => p.1 = x) = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp hpx
    exact h (List.mem_map.mpr ⟨p, hp, of_decide_eq_true hpx⟩)
  rw [this]
  rfl

/-- **Merging a range's map is adding its pairs.** -/
theorem merge_addAll (g : GM K) (ps : List (K × Nat)) :
    g.merge (GM.empty.addAll ps) = g.addAll ps := by
  have hkH : (GM.empty.addAll ps).keys = kfold [] (ps.map (·.1)) := addAll_keys _ _
  have hcH : ∀ x, (GM.empty.addAll ps).cnt x = psum ps x := by
    intro x; rw [addAll_cnt]; simp [GM.empty]
  generalize GM.empty.addAll ps = H at hkH hcH ⊢
  have hnd : H.keys.Nodup := by
    rw [hkH]; exact kfold_nodup [] _ List.nodup_nil
  apply GM.ext'
  · simp only [GM.merge]
    rw [addAll_keys g, addAll_keys g, List.map_map]
    have hid : (List.map ((fun x => x.1) ∘ fun k => (k, H.cnt k)) H.keys) = H.keys := by
      simp [Function.comp_def]
    rw [hid, kfold_eq g.keys H.keys, kfold_eq g.keys,
      kfold_nodup_eq [] _ hnd (by intro x _ h; simp at h), List.nil_append, hkH]
  · intro x
    simp only [GM.merge]
    rw [addAll_cnt, addAll_cnt, psum_keys _ _ hnd]
    by_cases hx : x ∈ H.keys
    · rw [if_pos hx, hcH]
    · rw [if_neg hx, psum_eq_zero ps x (by
        intro hm
        apply hx
        rw [hkH, mem_kfold]
        exact Or.inr hm)]

/-- Folding `addAll` over lists is `addAll` of their concatenation. -/
theorem foldl_addAll {β : Type} (F : β → List (K × Nat)) :
    ∀ (xs : List β) (g : GM K), xs.foldl (fun g X => g.addAll (F X)) g = g.addAll (xs.flatMap F)
  | [], g => rfl
  | X :: xs, g => by
    simp only [List.foldl_cons, List.flatMap_cons]
    rw [foldl_addAll F xs, GM.addAll, GM.addAll, GM.addAll, List.foldl_append]

/-- **Group maps: the divided answer is the single-thread answer.** Each
    block `b` adds its pairs `pairs b` (`IdQuery.countChunk`); each range
    builds its own map from no groups; the parent merges the range maps in
    range order (`IdQuery.Groups.merge`). The result is the map of one pass
    over all blocks: the same keys in the same order, the same counts. -/
theorem groups_divided_eq_single {β : Type} (pairs : β → List (K × Nat)) (L : List β) (c : Nat) :
    (chunksOf c L).foldl (fun g X => g.merge (GM.empty.addAll (X.flatMap pairs))) GM.empty
      = L.foldl (fun g b => g.addAll (pairs b)) GM.empty := by
  have hm : (chunksOf c L).foldl (fun g X => g.merge (GM.empty.addAll (X.flatMap pairs))) GM.empty
      = (chunksOf c L).foldl (fun g X => g.addAll (X.flatMap pairs)) GM.empty := by
    congr 1
    funext g X
    exact merge_addAll g _
  rw [hm, foldl_addAll, foldl_addAll]
  congr 1
  rw [show (chunksOf c L).flatMap (List.flatMap pairs)
      = ((chunksOf c L).map fun X => X.flatMap pairs).flatten from rfl, flatMap_chunks,
    chunksOf_flatten]

end Groups

/-! ## ORDER BY ... LIMIT: the first k rows of a stable sort -/

section TopK

variable {α : Type}

/-- The first `k` rows of `l` in the stable order of `le`. -/
def topK (le : α → α → Bool) (k : Nat) (l : List α) : List α := (l.mergeSort le).take k

variable {le : α → α → Bool}

/-- `List.mergeSort_zipIdx` from any first index: the sort of `l` is the sort
    of its rows numbered from `i` (the number breaks ties), numbers dropped. -/
theorem mergeSort_zipIdx_from (i : Nat) (l : List α) :
    ((l.zipIdx i).mergeSort (List.zipIdxLE le)).map (·.1) = l.mergeSort le := by
  have h1 : l.zipIdx i = (l.zipIdx 0).map (Prod.map id (· + i)) := by
    rw [List.map_snd_add_zipIdx_eq_zipIdx, Nat.add_zero]
  rw [h1, ← List.map_mergeSort (r := List.zipIdxLE le) (s := List.zipIdxLE le) (by
      intro a _ b _
      simp only [List.zipIdxLE, Prod.map, id]
      by_cases h1 : le a.1 b.1 <;> by_cases h2 : le b.1 a.1 <;> simp [h1, h2]), List.map_map]
  have : ((·.1) ∘ Prod.map id (· + i) : α × Nat → α) = (·.1) := by funext p; rfl
  rw [this]
  exact List.mergeSort_zipIdx

/-- The stable merge sort of a concatenation is the merge of the sorts of the
    parts (the rows of the first part go first among rows that compare
    equal). -/
theorem mergeSort_append (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a) (xs ys : List α) :
    (xs ++ ys).mergeSort le = (xs.mergeSort le).merge (ys.mergeSort le) le := by
  have hz : (xs ++ ys).zipIdx = xs.zipIdx 0 ++ ys.zipIdx xs.length := by
    rw [List.zipIdx_append]; simp
  rw [← List.mergeSort_zipIdx (l := xs ++ ys), ← mergeSort_zipIdx_from 0 xs,
    ← mergeSort_zipIdx_from xs.length ys, ← List.merge_stable]
  · congr 1
    rw [hz]
    have hperm : List.Perm ((xs.zipIdx 0 ++ ys.zipIdx xs.length).mergeSort (List.zipIdxLE le))
        (List.merge ((xs.zipIdx 0).mergeSort (List.zipIdxLE le))
            ((ys.zipIdx xs.length).mergeSort (List.zipIdxLE le)) (List.zipIdxLE le)) :=
      (List.mergeSort_perm _ _).trans
        ((List.merge_perm_append _).trans
          ((List.mergeSort_perm _ _).append (List.mergeSort_perm _ _))).symm
    apply List.Perm.eq_of_pairwise (le := fun a b => List.zipIdxLE le a b = true)
    · rintro ⟨a, i⟩ ⟨b, j⟩ ha hb
      have ha' : (a, i) ∈ (xs ++ ys).zipIdx := by
        rw [hz]; exact (List.mergeSort_perm _ _).subset ha
      have hb' : (b, j) ∈ (xs ++ ys).zipIdx := by
        rw [hz]; exact (List.mergeSort_perm _ _).subset (hperm.symm.subset hb)
      simp only [List.zipIdxLE]
      simp only [Bool.if_false_right, Bool.and_eq_true, Prod.mk.injEq, and_imp]
      intro ab h ba h'
      simp only [Bool.decide_eq_true] at ba
      replace h : i ≤ j := by simpa [ab, ba] using h
      replace h' : j ≤ i := by simpa [ab, ba] using h'
      cases Nat.le_antisymm h h'
      constructor
      · have := List.mem_zipIdx ha'
        have := List.mem_zipIdx hb'
        simp_all
      · rfl
    · exact List.pairwise_mergeSort (List.zipIdxLE_trans trans) (List.zipIdxLE_total total) _
    · exact List.pairwise_merge (List.zipIdxLE_trans trans) (List.zipIdxLE_total total) _ _
        (List.pairwise_mergeSort (List.zipIdxLE_trans trans) (List.zipIdxLE_total total) _)
        (List.pairwise_mergeSort (List.zipIdxLE_trans trans) (List.zipIdxLE_total total) _)
    · exact hperm
  · intro x y hx hy
    rw [List.mem_mergeSort] at hx hy
    have := List.mem_zipIdx hx
    have := List.mem_zipIdx hy
    omega

theorem take_cons_congr {a : α} {l l' : List α} {k : Nat} (h : l.take k = l'.take k) :
    (a :: l).take k = (a :: l').take k := by
  cases k with
  | zero => rfl
  | succ j =>
    simp only [List.take_succ_cons, List.cons.injEq, true_and]
    have := congrArg (List.take j) h
    rwa [List.take_take, List.take_take, Nat.min_eq_left (Nat.le_succ j)] at this

/-- The first `k` rows of a merge read only the first `k` rows of each
    input. -/
theorem take_merge_congr : ∀ (k : Nat) (xs xs' ys ys' : List α),
    xs.take k = xs'.take k → ys.take k = ys'.take k →
      (xs.merge ys le).take k = (xs'.merge ys' le).take k
  | 0, _, _, _, _, _, _ => by simp
  | k + 1, [], xs', ys, ys', hx, hy => by
    have : xs' = [] := by
      cases xs' with
      | nil => rfl
      | cons _ _ => simp at hx
    subst this
    simpa using hy
  | k + 1, x :: xs, [], ys, ys', hx, _ => by simp at hx
  | k + 1, x :: xs, x' :: xs', [], ys', hx, hy => by
    have : ys' = [] := by
      cases ys' with
      | nil => rfl
      | cons _ _ => simp at hy
    subst this
    simpa using hx
  | k + 1, x :: xs, x' :: xs', y :: ys, [], _, hy => by simp at hy
  | k + 1, x :: xs, x' :: xs', y :: ys, y' :: ys', hx, hy => by
    simp only [List.take_succ_cons, List.cons.injEq] at hx hy
    obtain ⟨rfl, hx⟩ := hx
    obtain ⟨rfl, hy⟩ := hy
    rw [List.cons_merge_cons, List.cons_merge_cons]
    split
    · simp only [List.take_succ_cons, List.cons.injEq, true_and]
      exact take_merge_congr k xs xs' (y :: ys) (y :: ys') hx (take_cons_congr hy)
    · simp only [List.take_succ_cons, List.cons.injEq, true_and]
      exact take_merge_congr k (x :: xs) (x :: xs') ys ys' (take_cons_congr hx) hy

/-- The first `k` rows of the concatenation of two lists are the first `k`
    rows of the concatenation of their first `k` rows. -/
theorem topK_append (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a) (k : Nat) (xs ys : List α) :
    topK le k (topK le k xs ++ topK le k ys) = topK le k (xs ++ ys) := by
  unfold topK
  have sx := (List.pairwise_mergeSort trans total xs).sublist (List.take_sublist k _)
  have sy := (List.pairwise_mergeSort trans total ys).sublist (List.take_sublist k _)
  rw [mergeSort_append trans total, List.mergeSort_of_pairwise sx, List.mergeSort_of_pairwise sy,
    mergeSort_append trans total]
  exact take_merge_congr k _ _ _ _ (by rw [List.take_take, Nat.min_self])
    (by rw [List.take_take, Nat.min_self])

theorem topK_topK (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a) (k : Nat) (l : List α) :
    topK le k (topK le k l) = topK le k l := by
  unfold topK
  rw [List.mergeSort_of_pairwise ((List.pairwise_mergeSort trans total l).sublist
    (List.take_sublist k _)), List.take_take, Nat.min_self]

/-- The first `k` rows of a concatenation of lists, from the first `k` rows
    of each. -/
theorem topK_flatten (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a) (k : Nat) :
    ∀ (Ls : List (List α)), topK le k (Ls.map (topK le k)).flatten = topK le k Ls.flatten
  | [] => rfl
  | L :: Ls => by
    simp only [List.map_cons, List.flatten_cons]
    rw [← topK_append trans total k (topK le k L), topK_topK trans total, topK_flatten trans total k Ls,
      topK_append trans total]

/-- **ORDER BY ... LIMIT: the divided answer is the single-thread answer.**
    Each range keeps the first `k` rows of its rows in the order; the first
    `k` rows of their concatenation (in range order) are the first `k` rows
    of all rows. `le` is the ORDER BY comparison (a total preorder), the
    sort stable. -/
theorem topK_divided_eq_single {β : Type} (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a) (R : β → List α) (L : List β) (c k : Nat) :
    topK le k ((chunksOf c L).map fun X => topK le k (X.flatMap R)).flatten
      = topK le k (L.flatMap R) := by
  have h := topK_flatten trans total k ((chunksOf c L).map fun X => X.flatMap R)
  rw [List.map_map, flatMap_chunks, chunksOf_flatten] at h
  exact h

end TopK

#print axioms stream_divided_eq_single
#print axioms count_divided_eq_single
#print axioms groups_divided_eq_single
#print axioms topK_divided_eq_single

end L4Factoidal.Storage.Sbm11.ParallelMergeTheorems
