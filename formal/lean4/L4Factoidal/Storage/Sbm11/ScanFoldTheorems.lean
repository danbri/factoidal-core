/-
L4Factoidal.Storage.Sbm11.ScanFoldTheorems — the SBM11 scan as a whole
(lemmas L4d and L4e of `docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md`,
section 10; https://github.com/danbri/factoidal/issues/776).

* `colConst_sound` (L4d): on a block that activation admitted
  (`decodeBlockAt`), `colConst?` gives a value only when every row has it in
  that column: columns 0 to 2 by the row order; the graph column because a
  frame of nine bytes that holds nine rows or more is a constant frame.
* `blockChunk_tuples`: the chunk of one admitted block that `blockPlan` does
  not skip holds the output tuples of the block's rows that the scan keeps.
* `scanFoldM_tuples` (L4e): over a store in memory (`m = Id`) of an admitted
  permutation with no overlay, the scan returns the output tuples of exactly
  the rows of the permutation that carry the key prefix and pass the checks,
  the named-graph test and the repeated-variable tests, in row order;
  `scanFoldM_columns`: with `fill = true`, the chunks' columns alone.

The hypotheses are the activation checks (`prmAdmitted`, `decodeBlockAt`
of every block) and the shape of the planner's scan specifications
(`SpecOk`). Not covered: the delta overlay (L7e) and a store in `IO`.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdQuery
import L4Factoidal.Storage.Sbm11.BlockAtTheorems
import L4Factoidal.Storage.Sbm11.FrameLocalTheorems

namespace L4Factoidal.Storage.Sbm11.ScanFoldTheorems

open L4Factoidal (two64)
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.FrameWords (words)
open L4Factoidal.Storage.Sbm11.ScanTheorems (colOf rowOf at64_words)
open L4Factoidal.Codec.Zstd (word64 word64Slow byteAt word64_eq_slow)

/-! ## Word reads in a slice -/

theorem byteAt_extract (d : ByteArray) (s e j : Nat) (hj : j < e - s) (he : e ≤ d.size) :
    byteAt (d.extract s e) j = byteAt d (s + j) := by
  unfold byteAt
  have h1 : j < (d.extract s e).size := by simp; omega
  have h2 : s + j < d.size := by omega
  rw [dif_pos h1, dif_pos h2, ByteArray.getElem_extract]

theorem word64_extract (d : ByteArray) (s e j : Nat) (hj : j + 8 ≤ e - s) (he : e ≤ d.size) :
    word64 (d.extract s e) j = word64 d (s + j) := by
  rw [word64_eq_slow, word64_eq_slow]
  unfold word64Slow
  rw [byteAt_extract _ _ _ j (by omega) he, byteAt_extract _ _ _ (j + 1) (by omega) he,
    byteAt_extract _ _ _ (j + 2) (by omega) he, byteAt_extract _ _ _ (j + 3) (by omega) he,
    byteAt_extract _ _ _ (j + 4) (by omega) he, byteAt_extract _ _ _ (j + 5) (by omega) he,
    byteAt_extract _ _ _ (j + 6) (by omega) he, byteAt_extract _ _ _ (j + 7) (by omega) he]
  simp only [Nat.add_assoc]

/-- Row `i` of the words cut to rows `[lo, hi)` is row `lo + i`. -/
theorem at64_extract (d : ByteArray) (lo hi i : Nat) (hi' : lo + i < hi) (hd : 8 * hi ≤ d.size) :
    at64 (d.extract (8 * lo) (8 * hi)) i = at64 d (lo + i) := by
  unfold at64
  rw [word64_extract _ _ _ _ (by omega) hd]
  congr 1
  omega

/-! ## Columns of a block that activation admitted -/

/-- Column `c` of decoded columns (`colOf`). -/
abbrev colv (cols : Cols) (c : Nat) : Array Nat := colOf cols.c0 cols.c1 cols.c2 cols.g c

theorem rowCol_row (cols : Cols) (c i : Nat) : rowCol (cols.row i) c = (colv cols c)[i]! := by
  match c with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

theorem getVarAtGo_ge (b : ByteArray) : ∀ f acc i z j, Column.getVarAtGo b f acc i = some (z, j) → i + 1 ≤ j := by
  intro f
  induction f with
  | zero => intro _ _ _ _ h; simp [Column.getVarAtGo] at h
  | succ f ih =>
    intro acc i z j h
    simp only [Column.getVarAtGo] at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
      · have := ih _ _ _ _ h; omega
    · cases h

/-- A delta frame takes at least one byte per value. -/
theorem deltaAtGo_ge (b : ByteArray) : ∀ n prev i (acc : Array Nat) a j,
    Column.deltaAtGo b n prev i acc = some (a, j) → i + n ≤ j := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; simp only [Column.deltaAtGo, Option.some.injEq, Prod.mk.injEq] at h; omega
  | succ n ih =>
    intro prev i acc a j h
    simp only [Column.deltaAtGo] at h
    split at h
    · cases h
    · rename_i z j' hv
      have hz := getVarAtGo_ge b _ _ _ _ _ hv
      split at h
      · cases h
      · split at h
        · have := ih _ _ _ _ _ h; omega
        · cases h

/-- A frame of nine bytes or fewer that holds nine values or more is a
    constant frame: every value is the first. -/
theorem decodeColumnAt_short (b : ByteArray) (n i : Nat) (c : Array Nat) (j : Nat)
    (h : Column.decodeColumnAt b n i = some (c, j)) (hj : j ≤ i + 9) (hn : 9 ≤ n) :
    ∀ k, k < n → c[k]! = c[0]! := by
  unfold Column.decodeColumnAt at h
  by_cases hi : i < b.size
  · rw [dif_pos hi] at h
    dsimp only at h
    by_cases t0 : (b[i] == Column.tagConst) = true
    · rw [if_pos t0] at h
      cases hg : Column.get64At b (i + 1) with
      | none => rw [hg] at h; cases h
      | some p =>
        obtain ⟨v, j'⟩ := p
        rw [hg] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        intro k hk
        rw [getElem!_pos _ k (by simp; omega), getElem!_pos _ 0 (by simp; omega)]
        simp
    · rw [if_neg t0] at h
      by_cases t1 : (b[i] == Column.tagRaw) = true
      · rw [if_pos t1] at h
        have := FrameWords.rawAtGo_pos b _ _ _ _ _ h
        omega
      · rw [if_neg t1] at h
        by_cases t2 : (b[i] == Column.tagDelta) = true
        · rw [if_pos t2] at h
          have := deltaAtGo_ge b _ _ _ _ _ _ h
          omega
        · rw [if_neg t2] at h; cases h
  · rw [dif_neg hi] at h; cases h

/-- The facts of `decodeBlockAt_ok`, with every value below `2^64`. -/
theorem admitted_facts (prb : ByteArray) (b : BlockMeta) (cols : Cols)
    (h : decodeBlockAt prb b b.offset = .ok cols) :
    (∀ c, c < 4 → (colv cols c).size = b.rows) ∧
    (∀ c i, c < 4 → i < b.rows → (colv cols c)[i]! < two64) ∧
    0 < b.rows ∧ cols.row 0 = b.first ∧ cols.row (b.rows - 1) = b.last ∧
    (∀ r s, r < s → s < b.rows → (cols.row r).lt (cols.row s) = true) := by
  obtain ⟨d0, d1, d2, d3, s0, s1, s2, s3, hpos, hf, hl, hs⟩ := decodeBlockAt_ok prb b b.offset cols h
  have hsize : ∀ c, c < 4 → (colv cols c).size = b.rows := by
    intro c hc
    match c, hc with
    | 0, _ => exact s0
    | 1, _ => exact s1
    | 2, _ => exact s2
    | 3, _ => exact s3
  refine ⟨hsize, ?_, hpos, hf, hl, hs⟩
  intro c i hc hi
  have hmem : (colv cols c)[i]! ∈ colv cols c := by
    rw [getElem!_pos (colv cols c) i (by rw [hsize c hc]; exact hi)]
    exact Array.getElem_mem _
  match c, hc with
  | 0, _ => exact decodeColumnAt_lt _ _ _ _ _ d0 _ hmem
  | 1, _ => exact decodeColumnAt_lt _ _ _ _ _ d1 _ hmem
  | 2, _ => exact decodeColumnAt_lt _ _ _ _ _ d2 _ hmem
  | 3, _ => exact decodeColumnAt_lt _ _ _ _ _ d3 _ hmem

/-- Every row of an admitted block lies between its PRM1 first and last row. -/
theorem row_between (prb : ByteArray) (b : BlockMeta) (cols : Cols)
    (h : decodeBlockAt prb b b.offset = .ok cols) (i : Nat) (hi : i < b.rows) :
    b.first.le (cols.row i) = true ∧ (cols.row i).le b.last = true := by
  obtain ⟨-, -, hpos, hf, hl, hs⟩ := admitted_facts prb b cols h
  constructor
  · rw [← hf]
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; exact ScanTheorems.le_refl _
    · exact ScanTheorems.le_of_lt (hs 0 i h0 hi)
  · rw [← hl]
    rcases Nat.lt_or_eq_of_le (show i ≤ b.rows - 1 by omega) with h0 | h0
    · exact ScanTheorems.le_of_lt (hs i (b.rows - 1) h0 (by omega))
    · rw [h0]; exact ScanTheorems.le_refl _

/-- Columns `0..c` (with `c < 3`) of a row between two rows that agree on
    them are those of the two rows. -/
theorem between_agree (a r z : Row) (c : Nat) (hc : c < 3) (h1 : a.le r = true) (h2 : r.le z = true)
    (hag : ∀ j, j < c + 1 → rowCol a j = rowCol z j) : rowCol r c = rowCol a c := by
  rw [ScanTheorems.le_iff, ScanTheorems.lt_iff, ScanTheorems.row_eq_iff] at h1 h2
  have e0 := hag 0 (by omega)
  simp only [rowCol] at e0
  match c, hc with
  | 0, _ => simp only [rowCol]; omega
  | 1, _ =>
    have e1 := hag 1 (by omega)
    simp only [rowCol] at e1 ⊢; omega
  | 2, _ =>
    have e1 := hag 1 (by omega)
    have e2 := hag 2 (by omega)
    simp only [rowCol] at e1 e2 ⊢; omega

/-- `colConst?` is sound on an admitted block: when it gives a value, every
    row has that value in the column (lemma L4d). Columns 0 to 2 by the row
    order; the graph column from a frame of nine bytes that holds nine rows
    or more, which only the constant codec can be. -/
theorem colConst_sound (prb : ByteArray) (b : BlockMeta) (cols : Cols)
    (h : decodeBlockAt prb b b.offset = .ok cols) (c y : Nat) (hc : colConst? b c = some y)
    (i : Nat) (hi : i < b.rows) : rowCol (cols.row i) c = y := by
  obtain ⟨hsz, -, hpos, hf, hl, hs⟩ := admitted_facts prb b cols h
  unfold colConst? at hc
  by_cases h3 : c < 3
  · rw [if_pos h3] at hc
    split at hc
    · rename_i hall
      simp only [Option.some.injEq] at hc
      subst hc
      obtain ⟨hb1, hb2⟩ := row_between prb b cols h i hi
      apply between_agree _ _ _ c h3 hb1 hb2
      intro j hj
      have := List.all_eq_true.mp hall j (List.mem_range.mpr hj)
      simpa using this
    · cases hc
  · rw [if_neg h3] at hc
    split at hc
    · rename_i hcond
      simp only [Option.some.injEq] at hc
      subst hc
      have hrc : rowCol (cols.row i) c = cols.g[i]! := by
        match c, h3 with
        | _ + 3, _ => rfl
      rw [hrc]
      have hg0 : b.first.g = cols.g[0]! := by rw [← hf]; rfl
      rw [hg0]
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hcond
      rcases hcond with h1 | ⟨h9, hl9⟩
      · have : i = 0 := by omega
        rw [this]
      · obtain ⟨-, -, -, d3, -⟩ := decodeBlockAt_ok prb b b.offset cols h
        exact decodeColumnAt_short _ _ _ _ _ d3 (by omega) h9 i hi
    · cases hc

/-! ## What the PRM1 entry decides (`blockPlan`) -/

/-- Check `ck` (column, value) on row `r`. -/
def chk (r : Row) (ck : Nat × UInt64) : Bool := rowCol r ck.1 == ck.2.toNat

theorem planChecksGo_spec (b : BlockMeta) (r : Row)
    (hs : ∀ c y, colConst? b c = some y → rowCol r c = y) :
    ∀ (l : List (Nat × UInt64)) skip acc,
      (!(planChecksGo b l skip acc).1 && (planChecksGo b l skip acc).2.toList.all (chk r)) =
        (!skip && acc.toList.all (chk r) && l.all (chk r)) := by
  intro l
  induction l with
  | nil => intro skip acc; simp [planChecksGo]
  | cons ck cs ih =>
    intro skip acc
    obtain ⟨c, x⟩ := ck
    simp only [planChecksGo]
    split
    · rename_i y hy
      rw [ih]
      have hc : chk r (c, x) = (y == x.toNat) := by simp only [chk, hs c y hy]
      simp only [List.all_cons, hc]
      by_cases hyx : y = x.toNat <;>
        cases skip <;> cases acc.toList.all (chk r) <;> cases cs.all (chk r) <;> simp [bne, hyx]
    · rw [ih]
      simp only [Array.toList_push, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
      cases skip <;> cases chk r (c, x) <;> cases acc.toList.all (chk r) <;> cases cs.all (chk r) <;> simp

/-- The checks and the named-graph test of a row of an admitted block, as
    `blockPlan` splits them: `skip`, the checks left, the named test left. -/
theorem blockPlan_keep (spec : ScanSpec) (b : BlockMeta) (r : Row)
    (hs : ∀ c y, colConst? b c = some y → rowCol r c = y) :
    ((!spec.named || r.g != 0) && spec.checks.toList.all (chk r)) =
      (!(blockPlan spec b).skip && (blockPlan spec b).checks.toList.all (chk r) &&
        (!(blockPlan spec b).named || r.g != 0)) := by
  have hp := planChecksGo_spec b r hs spec.checks.toList false #[]
  simp only [Bool.not_false, List.all_nil, Bool.true_and] at hp
  unfold blockPlan
  generalize planChecksGo b spec.checks.toList false #[] = res at hp
  obtain ⟨sk, ac⟩ := res
  simp only at hp ⊢
  by_cases hn : spec.named = true
  · rw [if_pos hn, hn]
    have hg : rowCol r 3 = r.g := rfl
    cases hc : colConst? b 3 with
    | none =>
      simp only
      rw [← hp]
      cases sk <;> cases ac.toList.all (chk r) <;> cases (r.g != 0) <;> simp
    | some y =>
      have hry := hs 3 y hc
      rw [hg] at hry
      cases y with
      | zero =>
        simp only [hry]
        simp
      | succ y =>
        simp only
        rw [← hp, hry]
        cases sk <;> cases ac.toList.all (chk r) <;> simp
  · rw [if_neg hn]
    simp only [Bool.not_eq_true] at hn
    rw [hn, ← hp]
    cases sk <;> cases ac.toList.all (chk r) <;> simp

/-! ## The row tests of `selectRows` -/

theorem foldl_modify (g : Nat → ByteArray → ByteArray) : ∀ (l : List Nat) (acc : Array ByteArray), l.Nodup →
    (l.foldl (fun a k => a.modify k (g k)) acc).size = acc.size ∧
    ∀ k (hk : k < acc.size), (l.foldl (fun a k => a.modify k (g k)) acc)[k]! =
      if k ∈ l then g k acc[k] else acc[k] := by
  intro l
  induction l with
  | nil => intro acc _; refine ⟨rfl, fun k hk => ?_⟩; simp [getElem!_pos acc k hk]
  | cons k0 ks ih =>
    intro acc hnd
    have hnd' := List.nodup_cons.mp hnd
    obtain ⟨h1, h2⟩ := ih (acc.modify k0 (g k0)) hnd'.2
    simp only [List.foldl_cons]
    refine ⟨by rw [h1, Array.size_modify], fun k hk => ?_⟩
    rw [h2 k (by rw [Array.size_modify]; exact hk)]
    by_cases hks : k ∈ ks
    · have hne : k0 ≠ k := fun h => hnd'.1 (h ▸ hks)
      rw [if_pos hks, if_pos (List.mem_cons_of_mem _ hks), Array.getElem_modify_of_ne hne]
    · rw [if_neg hks, Array.getElem_modify]
      by_cases hk0 : k0 = k
      · subst hk0; simp
      · rw [if_neg hk0, if_neg]
        intro hm
        rcases List.mem_cons.mp hm with h | h
        · exact hk0 h.symm
        · exact hks h

theorem side_put64_data (out : ByteArray) (x : UInt64) :
    (L4Factoidal.Qlvr.Side.put64 out x).data.toList = out.data.toList ++ Column.put64 x.toNat := by
  have := FrameWords.put64_data out x.toNat
  rw [show (x.toNat.toUInt64) = x from UInt64.ofNat_toNat] at this
  exact this

/-- The row test of `selectRows`. -/
def okRow (cols : Array ByteArray) (checks : Array (Nat × UInt64)) (named : Bool)
    (eqs : Array (Nat × Nat)) (i : Nat) : Bool :=
  checks.all (fun (c, x) => at64 cols[c]! i == x) &&
    (!named || at64 cols[3]! i != 0) &&
    eqs.all (fun (a, b) => at64 cols[a]! i == at64 cols[b]! i)

theorem selectRows_spec (cols : Array ByteArray) (checks : Array (Nat × UInt64)) (named : Bool)
    (eqs : Array (Nat × Nat)) (outCols : Array Nat) (hi : Nat) :
    ∀ fuel i (acc : Array ByteArray) n, hi - i ≤ fuel →
      (selectRows cols checks named eqs outCols hi fuel i acc n).1.size = acc.size ∧
      (selectRows cols checks named eqs outCols hi fuel i acc n).2 =
        n + ((List.range' i (hi - i)).filter (okRow cols checks named eqs)).length ∧
      ∀ k (hk : k < acc.size), k < outCols.size →
        ((selectRows cols checks named eqs outCols hi fuel i acc n).1[k]!).data.toList =
          acc[k].data.toList ++ (((List.range' i (hi - i)).filter (okRow cols checks named eqs)).map
            fun j => Column.put64 (at64 cols[outCols[k]!]! j).toNat).flatten := by
  intro fuel
  induction fuel with
  | zero =>
    intro i acc n hf
    have : hi - i = 0 := by omega
    simp only [selectRows, this, List.range'_zero, List.filter_nil, List.length_nil, Nat.add_zero,
      List.map_nil, List.flatten_nil, List.append_nil]
    exact ⟨trivial, trivial, fun k hk _ => by rw [getElem!_pos acc k hk]⟩
  | succ fuel ih =>
    intro i acc n hf
    simp only [selectRows]
    by_cases hge : i ≥ hi
    · rw [if_pos hge]
      have : hi - i = 0 := by omega
      simp only [this, List.range'_zero, List.filter_nil, List.length_nil, Nat.add_zero,
        List.map_nil, List.flatten_nil, List.append_nil]
      exact ⟨trivial, trivial, fun k hk _ => by rw [getElem!_pos acc k hk]⟩
    · rw [if_neg hge]
      have hr : List.range' i (hi - i) = i :: List.range' (i + 1) (hi - (i + 1)) := by
        rw [show hi - i = (hi - (i + 1)) + 1 by omega, List.range'_succ]
      rw [hr, List.filter_cons]
      by_cases hok : okRow cols checks named eqs i = true
      · have hok' : (checks.all (fun (c, x) => at64 cols[c]! i == x) &&
            (!named || at64 cols[3]! i != 0) &&
            eqs.all (fun (a, b) => at64 cols[a]! i == at64 cols[b]! i)) = true := hok
        rw [if_pos hok', if_pos hok]
        obtain ⟨fsz, fget⟩ := foldl_modify
          (fun k out => L4Factoidal.Qlvr.Side.put64 out (at64 cols[outCols[k]!]! i))
          (List.range outCols.size) acc List.nodup_range
        obtain ⟨i1, i2, i3⟩ := ih (i + 1)
          ((List.range outCols.size).foldl (fun a k => a.modify k
            (fun out => L4Factoidal.Qlvr.Side.put64 out (at64 cols[outCols[k]!]! i))) acc) (n + 1) (by omega)
        refine ⟨by rw [i1, fsz], by rw [i2, List.length_cons]; omega, fun k hk hko => ?_⟩
        rw [i3 k (by rw [fsz]; exact hk) hko]
        have := fget k hk
        rw [if_pos (List.mem_range.mpr hko)] at this
        rw [← getElem!_pos _ k (by rw [fsz]; exact hk), this, side_put64_data]
        simp only [List.map_cons, List.flatten_cons, List.append_assoc]
      · have hok' : (checks.all (fun (c, x) => at64 cols[c]! i == x) &&
            (!named || at64 cols[3]! i != 0) &&
            eqs.all (fun (a, b) => at64 cols[a]! i == at64 cols[b]! i)) = false :=
          (Bool.not_eq_true _).mp hok
        rw [if_neg (by simp [hok']), if_neg hok]
        obtain ⟨i1, i2, i3⟩ := ih (i + 1) acc n (by omega)
        exact ⟨i1, i2, i3⟩

/-! ## Reading the frames of a block -/

/-- The PRM1 length of frame `c`. -/
def lenOf (b : BlockMeta) : Nat → Nat
  | 0 => b.len0
  | 1 => b.len1
  | 2 => b.len2
  | _ => b.len3

theorem lens_getElem (b : BlockMeta) (c : Nat) (hc : c < 4) :
    (#[b.len0, b.len1, b.len2, b.len3] : Array Nat)[c]! = lenOf b c := by
  match c, hc with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

theorem frameStart_eq (b : BlockMeta) (base c : Nat) (hc : c < 4) :
    frameStart b base c = base + (frameStarts b)[c]! := by
  match c, hc with
  | 0, _ => rfl
  | 1, _ => simp [frameStart, frameStarts]
  | 2, _ => simp [frameStart, frameStarts]; omega
  | 3, _ => simp [frameStart, frameStarts]; omega

/-- The span of the needed frames covers each of them and lies inside the
    block. -/
theorem frameSpan_cover (b : BlockMeta) (need : Array Bool) (lo hi : Nat)
    (h : frameSpan b need = some (lo, hi)) :
    lo ≤ hi ∧ hi ≤ b.size ∧ ∀ c, c < 4 → need[c]! = true →
      lo ≤ (frameStarts b)[c]! ∧ (frameStarts b)[c]! + lenOf b c ≤ hi := by
  unfold frameSpan at h
  cases h0 : need[0]! <;> cases h1 : need[1]! <;> cases h2 : need[2]! <;> cases h3 : need[3]! <;>
    simp only [h0, h1, h2, h3, Bool.false_eq_true, if_false, if_true, Option.map_some, Option.map_none,
      Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    (try obtain ⟨rfl, rfl⟩ := h) <;>
    refine ⟨?_, ?_, fun c hc hn => ?_⟩
  all_goals first
    | omega
    | (simp only [BlockMeta.size]; omega)
    | (rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl <;>
        (try simp_all [frameStarts, lenOf]) <;> omega)

theorem frameSpan_none (b : BlockMeta) (need : Array Bool) (h : frameSpan b need = none) :
    ∀ c, c < 4 → need[c]! = false := by
  unfold frameSpan at h
  intro c hc
  cases h0 : need[0]! <;> cases h1 : need[1]! <;> cases h2 : need[2]! <;> cases h3 : need[3]! <;>
    simp only [h0, h1, h2, h3, Bool.false_eq_true, if_false, if_true, Option.map_some, Option.map_none,
      reduceCtorEq] at h <;>
    (match c, hc with
     | 0, _ => exact h0
     | 1, _ => exact h1
     | 2, _ => exact h2
     | 3, _ => exact h3)

/-- `readFrames` over a store that reads a PRB1 byte array in memory. -/
theorem readFrames_mem (st : Store Id) (prb : ByteArray) (perm : Nat)
    (hprb : ∀ off len, st.prb perm off len = pure (prb.extract off (off + len)))
    (b : BlockMeta) (need : Array Bool) (hsz : b.offset + b.size ≤ prb.size) :
    readFrames st perm b need = match frameSpan b need with
      | none => pure (.empty, frameStarts b, 0)
      | some (lo, hi) => pure (prb.extract (b.offset + lo) (b.offset + hi),
          (frameStarts b).map (· - lo), hi - lo) := by
  unfold readFrames
  cases hs : frameSpan b need with
  | none => rfl
  | some p =>
    obtain ⟨lo, hi⟩ := p
    obtain ⟨hlh, hhi, -⟩ := frameSpan_cover b need lo hi hs
    have hx : (prb.extract (b.offset + lo) (b.offset + lo + (hi - lo))).size = hi - lo := by
      simp only [ByteArray.size_extract]; omega
    have he : b.offset + lo + (hi - lo) = b.offset + hi := by omega
    simp only [hprb, he] at hx ⊢
    rw [pure_bind]
    simp [hx]

/-! ### The frames of an admitted block in a slice of PRB1 -/

/-- The word decoder on frame `c` of an admitted block. -/
theorem decodeWords_frame (prb : ByteArray) (b : BlockMeta) (cols : Cols)
    (h : decodeBlockAt prb b b.offset = .ok cols) (hrows : b.rows ≤ two64) (c : Nat) (hc : c < 4) :
    FrameWords.decodeWords prb b.rows (b.offset + (frameStarts b)[c]!) =
      some (words (colv cols c), b.offset + (frameStarts b)[c]! + lenOf b c) := by
  obtain ⟨d0, d1, d2, d3, -⟩ := decodeBlockAt_ok prb b b.offset cols h
  rw [FrameWords.decodeWords_eq _ _ _ hrows]
  unfold FrameWords.decodeWordsRef
  match c, hc with
  | 0, _ => simp only [frameStarts]; simp [d0, lenOf]; rfl
  | 1, _ => simp only [frameStarts]; simp [d1, lenOf]; rfl
  | 2, _ =>
    simp only [frameStarts]
    simp [show b.offset + (b.len0 + b.len1) = b.offset + b.len0 + b.len1 by omega, d2, lenOf]; rfl
  | 3, _ =>
    simp only [frameStarts]
    simp [show b.offset + (b.len0 + b.len1 + b.len2) = b.offset + b.len0 + b.len1 + b.len2 by omega, d3, lenOf]
    rfl

theorem decodeBlockAt_size (prb : ByteArray) (b : BlockMeta) (base : Nat) (cols : Cols)
    (h : decodeBlockAt prb b base = .ok cols) : base + b.size ≤ prb.size := by
  unfold decodeBlockAt at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · omega

theorem starts_map (b : BlockMeta) (lo c : Nat) (hc : c < 4) :
    ((frameStarts b).map (· - lo))[c]! = (frameStarts b)[c]! - lo := by
  match c, hc with
  | 0, _ => simp [frameStarts]
  | 1, _ => simp [frameStarts]
  | 2, _ => simp [frameStarts]
  | 3, _ => simp [frameStarts]

/-- On the bytes that `readFrames` returns, every needed frame decodes to
    the words of the column that activation checked, and ends at its PRM1
    length. -/
theorem frame_in_slice (prb : ByteArray) (b : BlockMeta) (cols : Cols)
    (h : decodeBlockAt prb b b.offset = .ok cols) (hrows : b.rows ≤ two64) (need : Array Bool)
    (lo hi : Nat) (hs : frameSpan b need = some (lo, hi)) (c : Nat) (hc : c < 4) (hn : need[c]! = true) :
    FrameWords.decodeWords (prb.extract (b.offset + lo) (b.offset + hi)) b.rows
        ((frameStarts b).map (· - lo))[c]! =
      some (words (colv cols c), ((frameStarts b).map (· - lo))[c]! + lenOf b c) := by
  obtain ⟨hlh, hhi, hcov⟩ := frameSpan_cover b need lo hi hs
  obtain ⟨c1, c2⟩ := hcov c hc hn
  have hsz := decodeBlockAt_size prb b b.offset cols h
  have := FrameWords.decodeWords_extract prb b.rows _ _ _ (b.offset + lo) (b.offset + hi) hrows
    (decodeWords_frame prb b cols h hrows c hc) (by omega) (by omega) (by omega)
  rw [starts_map b lo c hc]
  rw [show b.offset + (frameStarts b)[c]! - (b.offset + lo) = (frameStarts b)[c]! - lo by omega,
    show b.offset + (frameStarts b)[c]! + lenOf b c - (b.offset + lo) = (frameStarts b)[c]! - lo + lenOf b c by omega]
    at this
  exact this

/-- The frame bytes and starts of a block: each needed frame decodes to the
    words of the admitted column and ends at its PRM1 length. -/
def SliceOk (b : BlockMeta) (cols : Cols) (need : Array Bool) (bytes : ByteArray) (starts : Array Nat) : Prop :=
  ∀ c, c < 4 → need[c]! = true →
    FrameWords.decodeWords bytes b.rows starts[c]! = some (words (colv cols c), starts[c]! + lenOf b c)

/-- What `readFrames` returns over an in-memory PRB1 is such a slice. -/
theorem readFrames_slice (st : Store Id) (prb : ByteArray) (perm : Nat)
    (hprb : ∀ off len, st.prb perm off len = pure (prb.extract off (off + len)))
    (b : BlockMeta) (cols : Cols) (h : decodeBlockAt prb b b.offset = .ok cols) (hrows : b.rows ≤ two64)
    (need : Array Bool) :
    ∃ bytes starts nbytes, readFrames st perm b need = pure (bytes, starts, nbytes) ∧
      SliceOk b cols need bytes starts := by
  rw [readFrames_mem st prb perm hprb b need (decodeBlockAt_size prb b b.offset cols h)]
  cases hs : frameSpan b need with
  | none =>
    refine ⟨_, _, _, rfl, fun c hc hn => ?_⟩
    rw [frameSpan_none b need hs c hc] at hn; cases hn
  | some p =>
    obtain ⟨lo, hi⟩ := p
    exact ⟨_, _, _, rfl, fun c hc hn => frame_in_slice prb b cols h hrows need lo hi hs c hc hn⟩

theorem words_size' (xs : Array Nat) : (words xs).size = 8 * xs.size := by
  show (words xs).data.size = _
  rw [← Array.length_toList, FrameWords.words_data]
  have : ∀ l : List Nat, ((l.map Column.put64).flatten).length = 8 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append, ih, List.length_cons,
        FrameWords.put64_length]
      omega
  rw [this, Array.length_toList]

section slice
variable {b : BlockMeta} {cols : Cols} {need : Array Bool} {bytes : ByteArray} {starts : Array Nat}

theorem colAll_slice (hsl : SliceOk b cols need bytes starts) (hsz : ∀ c, c < 4 → (colv cols c).size = b.rows)
    (c : Nat) (hc : c < 4) (hn : need[c]! = true) : colAll b bytes starts c = .ok (words (colv cols c)) := by
  unfold colAll
  rw [hsl c hc hn]
  simp only [lens_getElem b c hc, words_size', hsz c hc, bne_self_eq_false, Bool.or_false]
  rfl

theorem colRange_slice (hsl : SliceOk b cols need bytes starts) (hrows : b.rows ≤ two64)
    (c : Nat) (hc : c < 4) (hn : need[c]! = true) (lo hi : Nat) (h1 : lo ≤ hi) (h2 : hi ≤ b.rows) :
    colRange b bytes starts c lo hi = .ok ((words (colv cols c)).extract (8 * lo) (8 * hi)) := by
  unfold colRange
  rw [FrameWords.decodeWordsRange_eq _ _ _ _ _ _ _ hrows h1 h2 (hsl c hc hn)]

theorem colsAllGo_slice (hsl : SliceOk b cols need bytes starts) (hsz : ∀ c, c < 4 → (colv cols c).size = b.rows) :
    ∀ k c0 (acc : Array ByteArray), c0 + k ≤ 4 → (∀ c, c0 ≤ c → c < c0 + k → need[c]! = true) →
      colsAllGo b bytes starts k c0 acc = .ok (acc ++ ((List.range' c0 k).map fun c => words (colv cols c)).toArray) := by
  intro k
  induction k with
  | zero => intro c0 acc _ _; simp [colsAllGo]
  | succ k ih =>
    intro c0 acc hk hn
    simp only [colsAllGo]
    rw [colAll_slice hsl hsz c0 (by omega) (hn c0 (by omega) (by omega))]
    simp only
    rw [ih (c0 + 1) _ (by omega) (fun c h1 h2 => hn c (by omega) (by omega))]
    simp [List.range'_succ]

theorem cutCol_slice (hsl : SliceOk b cols need bytes starts) (hrows : b.rows ≤ two64)
    (keyWords : Array ByteArray) (hkw : ∀ j (hj : j < keyWords.size), keyWords[j] = words (colv cols j))
    (lo hi : Nat) (h1 : lo ≤ hi) (h2 : hi ≤ b.rows) (c : Nat) (hc : c < 4) :
    cutCol b bytes starts need keyWords lo hi c =
      .ok (if need[c]! then (words (colv cols c)).extract (8 * lo) (8 * hi) else .empty) := by
  unfold cutCol
  by_cases hn : need[c]! = true
  · rw [if_pos hn, if_pos hn]
    by_cases hk : c < keyWords.size
    · rw [dif_pos hk, hkw c hk]
    · rw [dif_neg hk, colRange_slice hsl hrows c hc hn lo hi h1 h2]
  · rw [if_neg hn, if_neg hn]

end slice

/-- A word of a cut column is the id of the row. -/
theorem at64_cut (xs : Array Nat) (n : Nat) (hsz : xs.size = n) (hv : ∀ i, i < n → xs[i]! < two64)
    (lo hi j : Nat) (h : lo + j < hi) (hhi : hi ≤ n) :
    (at64 ((words xs).extract (8 * lo) (8 * hi)) j).toNat = xs[lo + j]! := by
  rw [at64_extract _ _ _ _ h (by rw [words_size', hsz]; omega), at64_words _ _ (by omega),
    ← getElem!_pos xs (lo + j) (by omega)]
  have := hv (lo + j) (by omega)
  simp only [Nat.toUInt64, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt this

/-! ## List helpers -/

theorem all_congr_mem {α : Type} (l : List α) (p q : α → Bool) (h : ∀ x ∈ l, p x = q x) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, h x (List.mem_cons_self), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem filter_congr_mem {α : Type} (l : List α) (p q : α → Bool) (h : ∀ x ∈ l, p x = q x) :
    l.filter p = l.filter q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons, h x (List.mem_cons_self), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem map_congr_mem {α β : Type} (l : List α) (f g : α → β) (h : ∀ x ∈ l, f x = g x) :
    l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, h x (List.mem_cons_self), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- Filtering `[0, n)` by a test that holds exactly on `[lo, hi)` and
    another test. -/
theorem filter_range_interval (n lo hi : Nat) (hlh : lo ≤ hi) (hhi : hi ≤ n) (A B : Nat → Bool)
    (hA : ∀ i, i < n → (A i = true ↔ (lo ≤ i ∧ i < hi))) :
    (List.range n).filter (fun i => A i && B i) =
      ((List.range (hi - lo)).filter (fun j => B (lo + j))).map (lo + ·) := by
  have hsplit : List.range n = List.range' 0 lo ++ List.range' lo (hi - lo) ++ List.range' hi (n - hi) := by
    rw [List.range_eq_range']
    have e1 := @List.range'_append 0 lo (hi - lo) 1
    have e2 := @List.range'_append 0 (lo + (hi - lo)) (n - hi) 1
    simp only [Nat.one_mul, Nat.zero_add] at e1 e2
    rw [← e1, show lo + (hi - lo) = hi by omega, show hi + (n - hi) = n by omega] at e2
    exact e2.symm
  rw [hsplit, List.filter_append, List.filter_append]
  have h1 : (List.range' 0 lo).filter (fun i => A i && B i) = [] := by
    rw [List.filter_eq_nil_iff]
    intro i hi'
    have := List.mem_range'_1.mp hi'
    have hA' := hA i (by omega)
    cases hAi : A i
    · simp
    · exact absurd (hA'.mp hAi).1 (by omega)
  have h3 : (List.range' hi (n - hi)).filter (fun i => A i && B i) = [] := by
    rw [List.filter_eq_nil_iff]
    intro i hi'
    have := List.mem_range'_1.mp hi'
    have hA' := hA i (by omega)
    cases hAi : A i
    · simp
    · exact absurd (hA'.mp hAi).2 (by omega)
  have h2 : (List.range' lo (hi - lo)).filter (fun i => A i && B i) = (List.range' lo (hi - lo)).filter B := by
    apply filter_congr_mem
    intro i hi'
    have := List.mem_range'_1.mp hi'
    rw [(hA i (by omega)).mpr ⟨by omega, by omega⟩, Bool.true_and]
  rw [h1, h2, h3, List.nil_append, List.append_nil, List.range'_eq_map_range, List.filter_map]
  rfl

/-- `(range l.length).map (f ∘ l[·]!) = l.map f`. -/
theorem map_range_getElem! {α β : Type} [Inhabited α] (l : List α) (f : α → β) :
    (List.range l.length).map (fun j => f l[j]!) = l.map f := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [getElem!_pos l j (by simpa using h1)]

theorem keyBound_le (cols : Array ByteArray) (key : Array UInt64) (strict : Bool) :
    ∀ f lo hi, lo ≤ hi → lo ≤ keyBound cols key strict f lo hi ∧ keyBound cols key strict f lo hi ≤ hi := by
  intro f
  induction f with
  | zero => intro lo hi h; simp [keyBound]; omega
  | succ f ih =>
    intro lo hi h
    simp only [keyBound]
    split
    · split
      · have := ih ((lo + hi) / 2 + 1) hi (by omega); omega
      · have := ih lo ((lo + hi) / 2) (by omega); omega
    · omega

/-! ## What the scan should return -/

/-- Repeated-variable test `e` (two columns) on row `r`. -/
def eqk (r : Row) (e : Nat × Nat) : Bool := rowCol r e.1 == rowCol r e.2

/-- The rows a scan of `spec` keeps: the key prefix, the named-graph test,
    the checks, the repeated-variable tests. -/
def keep (spec : ScanSpec) (r : Row) : Bool :=
  prefixCmp r spec.key == .eq && ((!spec.named || r.g != 0) && spec.checks.toList.all (chk r)) &&
    spec.eqs.toList.all (eqk r)

/-- The output tuple of a row: its output columns. -/
def proj (spec : ScanSpec) (r : Row) : List Nat :=
  (List.range spec.outCols.size).map fun k => rowCol r spec.outCols[k]!

/-- The tuples of a chunk: per row, per output column, the constant of the
    chunk (`consts`) or the word of the column. -/
def tuples (ch : Chunk) : List (List Nat) :=
  (List.range ch.table.rows).map fun i => (List.range ch.consts.size).map fun k =>
    match ch.consts[k]! with
    | some x => x.toNat
    | none => (at64 ch.table.cols[k]! i).toNat

/-- The scan specifications the planner builds (`mkSpec`): columns below 4,
    a key of at most four columns, one variable per output column. -/
structure SpecOk (spec : ScanSpec) : Prop where
  key : spec.key.size ≤ 4
  checks : ∀ ck ∈ spec.checks, ck.1 < 4
  eqs : ∀ e ∈ spec.eqs, e.1 < 4 ∧ e.2 < 4
  outCols : ∀ c ∈ spec.outCols, c < 4
  outVars : spec.outVars.size = spec.outCols.size

/-! ## Which columns a chunk reads -/

theorem planChecksGo_sub (b : BlockMeta) : ∀ (l : List (Nat × UInt64)) skip acc ck,
    ck ∈ (planChecksGo b l skip acc).2 → ck ∈ acc ∨ ck ∈ l := by
  intro l
  induction l with
  | nil => intro _ _ ck h; exact Or.inl h
  | cons x xs ih =>
    intro skip acc ck h
    obtain ⟨c, v⟩ := x
    simp only [planChecksGo] at h
    split at h
    · rcases ih _ _ ck h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases ih _ _ ck h with h | h
      · rcases Array.mem_push.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (h ▸ List.mem_cons_self)
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem blockPlan_checks_sub (spec : ScanSpec) (b : BlockMeta) (ck : Nat × UInt64)
    (h : ck ∈ (blockPlan spec b).checks) : ck ∈ spec.checks := by
  unfold blockPlan at h
  generalize hres : planChecksGo b spec.checks.toList false #[] = res at h
  obtain ⟨sk, ac⟩ := res
  have hs := planChecksGo_sub b spec.checks.toList false #[] ck
  rw [hres] at hs
  simp only at h
  rcases hs h with h' | h'
  · simp at h'
  · exact Array.mem_toList_iff.mp h'

theorem outNeedGo_true (outCols : Array Nat) (constOut : Array (Option Nat)) (perRow : Bool) (c : Nat) :
    ∀ f k k', k ≤ k' → k' < k + f → outCols[k']! = c → ((constOut[k']!).isNone || perRow) = true →
      outNeedGo outCols constOut perRow c f k = true := by
  intro f
  induction f with
  | zero => intro k k' _ h; omega
  | succ f ih =>
    intro k k' h1 h2 hc ho
    simp only [outNeedGo]
    split
    · rfl
    · rename_i hne
      by_cases hk : k = k'
      · subst hk; simp [hc, ho] at hne
      · exact ih (k + 1) k' (by omega) (by omega) hc ho

section need
variable (spec : ScanSpec) (bp : BlockPlan) (constOut : Array (Option Nat))

theorem needOf_getElem (c : Nat) (hc : c < 4) : (needOf spec bp constOut)[c]! = needCol spec bp constOut c := by
  match c, hc with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

theorem needCol_key (c : Nat) (hf : bp.full = false) (hc : c < spec.key.size) : needCol spec bp constOut c = true := by
  simp [needCol, hf, hc]

theorem needCol_check (ck : Nat × UInt64) (h : ck ∈ bp.checks) : needCol spec bp constOut ck.1 = true := by
  have : bp.checks.any (fun x => x.1 == ck.1) = true := Array.any_eq_true'.mpr ⟨ck, h, by simp⟩
  simp [needCol, this]

theorem needCol_named (h : bp.named = true) : needCol spec bp constOut 3 = true := by
  simp [needCol, h]

theorem needCol_eq (e : Nat × Nat) (h : e ∈ spec.eqs) :
    needCol spec bp constOut e.1 = true ∧ needCol spec bp constOut e.2 = true := by
  have h1 : spec.eqs.any (fun x => x.1 == e.1 || x.2 == e.1) = true := Array.any_eq_true'.mpr ⟨e, h, by simp⟩
  have h2 : spec.eqs.any (fun x => x.1 == e.2 || x.2 == e.2) = true := Array.any_eq_true'.mpr ⟨e, h, by simp⟩
  constructor
  · simp only [needCol, h1, Bool.or_true, Bool.true_or]
  · simp only [needCol, h2, Bool.or_true, Bool.true_or]

theorem needCol_out (k : Nat) (hk : k < spec.outCols.size)
    (h : ((constOut[k]!).isNone || bp.perRow spec) = true) : needCol spec bp constOut spec.outCols[k]! = true := by
  have := outNeedGo_true spec.outCols constOut (bp.perRow spec) spec.outCols[k]! spec.outCols.size 0 k
    (by omega) (by omega) rfl h
  simp [needCol, this]

end need

/-! ## The chunk from the cut columns -/

theorem uint64_beq_toNat (a b : UInt64) : (a == b) = (a.toNat == b.toNat) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, UInt64.toNat_inj]

theorem uint64_bne_zero (a : UInt64) : (a != 0) = (a.toNat != 0) := by
  rw [bne, bne, uint64_beq_toNat]
  rfl

theorem uint64_toNat_toUInt64 (x : Nat) (h : x < two64) : x.toUInt64.toNat = x := by
  simp only [Nat.toUInt64, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-- A chunk built from cut columns whose needed words are the values `val`
    (column, row of the chunk) holds, per row that passes the row tests left
    by `blockPlan`, the output values. -/
theorem chunkOfCols_tuples (spec : ScanSpec) (hspec : SpecOk spec) (fill : Bool) (sortVar : Option String)
    (bp : BlockPlan) (hbp : ∀ ck ∈ bp.checks, ck ∈ spec.checks)
    (constOut : Array (Option Nat)) (hco : constOut.size = spec.outCols.size)
    (cols : Array ByteArray) (n : Nat) (val : Nat → Nat → Nat)
    (hv : ∀ c j, c < 4 → j < n → val c j < two64)
    (hcol : ∀ c, c < 4 → needCol spec bp constOut c = true → ∀ j, j < n → (at64 cols[c]! j).toNat = val c j)
    (hconst : ∀ k, k < spec.outCols.size → ∀ x, constOut[k]! = some x → ∀ j, j < n → val spec.outCols[k]! j = x) :
    tuples (chunkOfCols spec fill sortVar bp constOut cols n) =
      ((List.range n).filter fun j => bp.checks.toList.all (fun ck => val ck.1 j == ck.2.toNat) &&
          (!bp.named || val 3 j != 0) && spec.eqs.toList.all (fun e => val e.1 j == val e.2 j)).map
        fun j => (List.range spec.outCols.size).map fun k => val spec.outCols[k]! j := by
  have houtlt : ∀ k, k < spec.outCols.size → spec.outCols[k]! < 4 := by
    intro k hk
    rw [getElem!_pos spec.outCols k hk]
    exact hspec.outCols _ (Array.getElem_mem hk)
  unfold chunkOfCols
  by_cases hp : bp.perRow spec = true
  · rw [if_pos hp]
    generalize hsel : selectRows cols bp.checks bp.named spec.eqs spec.outCols n (n + 1) 0
      (spec.outVars.map fun _ => ByteArray.emptyWithCapacity (8 * n)) 0 = res
    obtain ⟨out, k⟩ := res
    obtain ⟨s1, s2, s3⟩ := selectRows_spec cols bp.checks bp.named spec.eqs spec.outCols n (n + 1) 0
      (spec.outVars.map fun _ => ByteArray.emptyWithCapacity (8 * n)) 0 (by omega)
    rw [hsel] at s1 s2 s3
    dsimp only at s1 s2 s3
    rw [Nat.sub_zero, ← List.range_eq_range'] at s2 s3
    generalize hI : (List.range n).filter (okRow cols bp.checks bp.named spec.eqs) = I at s2 s3
    -- the row tests over the words are the tests over the values
    have hok : (List.range n).filter (okRow cols bp.checks bp.named spec.eqs) =
        (List.range n).filter fun j => bp.checks.toList.all (fun ck => val ck.1 j == ck.2.toNat) &&
          (!bp.named || val 3 j != 0) && spec.eqs.toList.all (fun e => val e.1 j == val e.2 j) := by
      apply filter_congr_mem
      intro j hj
      have hjn := List.mem_range.mp hj
      unfold okRow
      rw [← Array.all_toList, ← Array.all_toList]
      congr 1
      congr 1
      · apply all_congr_mem
        intro ck hck
        obtain ⟨c, x⟩ := ck
        have hm := Array.mem_toList_iff.mp hck
        have hc4 : c < 4 := hspec.checks _ (hbp _ hm)
        simp only
        rw [uint64_beq_toNat, hcol c hc4 (needCol_check spec bp constOut (c, x) hm) j hjn]
      · cases hn : bp.named
        · rfl
        · simp only [Bool.not_true, Bool.false_or]
          rw [uint64_bne_zero, hcol 3 (by omega) (needCol_named spec bp constOut hn) j hjn]
      · apply all_congr_mem
        intro e he
        obtain ⟨a, d⟩ := e
        have hm := Array.mem_toList_iff.mp he
        obtain ⟨ha, hd⟩ := hspec.eqs _ hm
        obtain ⟨na, nd⟩ := needCol_eq spec bp constOut (a, d) hm
        simp only
        rw [uint64_beq_toNat, hcol a ha na j hjn, hcol d hd nd j hjn]
    rw [hI] at hok
    rw [← hok]
    unfold tuples
    simp only
    rw [s2, Nat.zero_add]
    have hcs : (spec.outVars.map fun _ => (none : Option UInt64)).size = spec.outCols.size := by
      rw [Array.size_map, hspec.outVars]
    rw [hcs, ← map_range_getElem! I]
    apply map_congr_mem
    intro i hi
    have hiI := List.mem_range.mp hi
    apply map_congr_mem
    intro k' hk'
    have hk := List.mem_range.mp hk'
    have hnone : (spec.outVars.map fun _ => (none : Option UInt64))[k']! = none := by
      rw [getElem!_pos _ k' (by rw [hcs]; exact hk)]; simp
    rw [hnone]
    simp only
    -- the output column is the words of the kept rows
    have hA : k' < (spec.outVars.map fun _ => ByteArray.emptyWithCapacity (8 * n)).size := by
      rw [Array.size_map, hspec.outVars]; exact hk
    have hdata := s3 k' hA hk
    have hout : out[k']! = words ((I.map fun j => (at64 cols[spec.outCols[k']!]! j).toNat).toArray) := by
      apply ByteArray.ext
      apply Array.toList_inj.mp
      rw [hdata, FrameWords.words_data]
      simp [List.map_map, Function.comp_def]
      rfl
    rw [hout, at64_words _ _ (by simpa using hiI)]
    have hIi : I[i]! ∈ I := by rw [getElem!_pos I i hiI]; exact List.getElem_mem _
    have hsub : ∀ x ∈ I, x < n := by
      intro x hx; rw [← hI] at hx; exact List.mem_range.mp (List.mem_filter.mp hx).1
    have hIn : I[i]! < n := hsub _ hIi
    simp only [List.getElem_toArray, List.getElem_map]
    rw [uint64_toNat_toUInt64 _ (by
      have := UInt64.toNat_lt (at64 cols[spec.outCols[k']!]! I[i])
      simpa [two64] using this)]
    rw [← getElem!_pos I i hiI]
    exact hcol _ (houtlt k' hk) (needCol_out spec bp constOut k' hk (by simp [hp])) _ hIn
  · rw [if_neg hp]
    have hp' : bp.perRow spec = false := by simpa using hp
    unfold BlockPlan.perRow at hp'
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', Array.isEmpty_iff] at hp'
    obtain ⟨⟨hce, hne⟩, hee⟩ := hp'
    have hf : ((List.range n).filter fun j => bp.checks.toList.all (fun ck => val ck.1 j == ck.2.toNat) &&
          (!bp.named || val 3 j != 0) && spec.eqs.toList.all (fun e => val e.1 j == val e.2 j)) = List.range n := by
      rw [hce, hne, hee]
      simp
    rw [hf]
    unfold tuples
    simp only
    have hcs : (constOut.map (·.map Nat.toUInt64)).size = spec.outCols.size := by rw [Array.size_map, hco]
    rw [hcs]
    apply map_congr_mem
    intro j hj
    have hjn := List.mem_range.mp hj
    apply map_congr_mem
    intro k' hk'
    have hk := List.mem_range.mp hk'
    have hck : (constOut.map (·.map Nat.toUInt64))[k']! = (constOut[k']!).map Nat.toUInt64 := by
      rw [getElem!_pos _ k' (by rw [hcs]; exact hk), getElem!_pos _ k' (by rw [hco]; exact hk)]
      simp
    rw [hck]
    have hout : ((List.range spec.outCols.size).toArray.map fun k =>
        match constOut[k]! with
        | some x => if fill then constWords x.toUInt64 n else ByteArray.empty
        | none => cols[spec.outCols[k]!]!)[k']! =
        match constOut[k']! with
        | some x => if fill then constWords x.toUInt64 n else ByteArray.empty
        | none => cols[spec.outCols[k']!]! := by
      rw [getElem!_pos _ k' (by simp; exact hk)]
      simp
    cases hc : constOut[k']! with
    | none =>
      simp only [Option.map_none]
      erw [hout]
      rw [hc]
      exact hcol _ (houtlt k' hk) (needCol_out spec bp constOut k' hk (by simp [hc])) j hjn
    | some x =>
      simp only [Option.map_some]
      have hx := hconst k' hk x hc j hjn
      rw [← hx, uint64_toNat_toUInt64 _ (hv _ _ (houtlt k' hk) hjn)]

/-! ## One block (`blockChunk`) -/

/-- The rows `[lo, hi)` that `keyRange` gives are exactly the rows of the
    block whose key prefix equals the key. -/
theorem keyRange_spec (spec : ScanSpec) (hkey : spec.key.size ≤ 4) (prb : ByteArray) (b : BlockMeta)
    (cols : Cols) (h : decodeBlockAt prb b b.offset = .ok cols) (full : Bool) (hfull : full = fullFor b spec.key)
    (kw : Array ByteArray) (hkw : full = false → ∀ j, j < spec.key.size → kw[j]! = words (colv cols j)) :
    (keyRange spec b full kw).1 ≤ (keyRange spec b full kw).2 ∧ (keyRange spec b full kw).2 ≤ b.rows ∧
      ∀ i, i < b.rows → (((keyRange spec b full kw).1 ≤ i ∧ i < (keyRange spec b full kw).2) ↔
        prefixCmp (cols.row i) spec.key = .eq) := by
  unfold keyRange
  cases hf : full
  · simp only [Bool.false_eq_true, if_false]
    have b1 := keyBound_le kw spec.key false (Nat.log2 b.rows + 2) 0 b.rows (Nat.zero_le _)
    have b2 := keyBound_le kw spec.key true (Nat.log2 b.rows + 2)
      (keyBound kw spec.key false (Nat.log2 b.rows + 2) 0 b.rows) b.rows b1.2
    refine ⟨b2.1, b2.2, fun i hi => ?_⟩
    exact Block.scanRows_exact_of_decodeBlockAt prb b b.offset cols h spec.key hkey kw (hkw hf) i hi
  · simp only [if_true]
    refine ⟨Nat.zero_le _, Nat.le_refl _, fun i hi => ?_⟩
    have hff : fullFor b spec.key = true := by rw [← hfull, hf]
    obtain ⟨h1, h2⟩ := row_between prb b cols h i hi
    exact ⟨fun _ => ScanTheorems.fullFor_row b spec.key hff _ h1 h2, fun _ => ⟨Nat.zero_le _, hi⟩⟩

/-- The chunk of one admitted block that `blockPlan` does not skip holds the
    output tuples of the block's rows that the scan keeps, in row order. -/
theorem blockChunk_tuples (spec : ScanSpec) (hspec : SpecOk spec) (fill : Bool) (sortVar : Option String)
    (prb : ByteArray) (b : BlockMeta) (cols : Cols) (h : decodeBlockAt prb b b.offset = .ok cols)
    (hrows : b.rows ≤ two64) (hskip : (blockPlan spec b).skip = false) (bytes : ByteArray) (starts : Array Nat)
    (hsl : SliceOk b cols (needOf spec (blockPlan spec b) (constOutOf spec b (blockPlan spec b))) bytes starts) :
    ∃ ch, blockChunk spec fill sortVar b (blockPlan spec b) (constOutOf spec b (blockPlan spec b))
        (needOf spec (blockPlan spec b) (constOutOf spec b (blockPlan spec b))) bytes starts = .ok ch ∧
      tuples ch = ((List.range b.rows).filter fun i => keep spec (cols.row i)).map fun i => proj spec (cols.row i) := by
  obtain ⟨hsz, hv64, -, -, -, -⟩ := admitted_facts prb b cols h
  generalize hbp : blockPlan spec b = bp at hskip hsl ⊢
  generalize hco : constOutOf spec b bp = co at hsl ⊢
  have hneed : ∀ c, c < 4 → (needOf spec bp co)[c]! = needCol spec bp co c := fun c hc => needOf_getElem spec bp co c hc
  -- the key columns in full
  let kw : Array ByteArray := if bp.full then #[] else
    ((List.range' 0 spec.key.size).map fun c => words (colv cols c)).toArray
  have hkwEq : keyWordsOf b bytes starts bp.full spec.key.size = .ok kw := by
    unfold keyWordsOf
    cases hf : bp.full
    · simp only [Bool.false_eq_true, if_false, kw, hf]
      rw [colsAllGo_slice hsl hsz spec.key.size 0 #[] (by have := hspec.key; omega)
        (fun c _ hc => by
          rw [hneed c (by have := hspec.key; omega)]; exact needCol_key spec bp co c hf (by omega))]
      simp
    · simp only [if_true, kw, hf]
  have hkw : ∀ j (hj : j < kw.size), kw[j] = words (colv cols j) := by
    intro j hj
    cases hf : bp.full
    · simp only [kw, hf, Bool.false_eq_true, if_false, List.getElem_toArray, List.getElem_map,
        List.getElem_range'] at hj ⊢
      simp
    · simp [kw, hf] at hj
  have hkw' : bp.full = false → ∀ j, j < spec.key.size → kw[j]! = words (colv cols j) := by
    intro hf j hj
    have hj' : j < kw.size := by simp [kw, hf]; exact hj
    rw [getElem!_pos kw j hj', hkw j hj']
  have hfull : bp.full = fullFor b spec.key := by rw [← hbp]; rfl
  obtain ⟨hlh, hhi, hiff⟩ := keyRange_spec spec hspec.key prb b cols h bp.full hfull kw hkw'
  generalize hlhp : keyRange spec b bp.full kw = lh at hlh hhi hiff
  obtain ⟨lo, hi⟩ := lh
  simp only at hlh hhi hiff
  -- the cut columns
  have hcut : ∀ c, c < 4 → cutCol b bytes starts (needOf spec bp co) kw lo hi c =
      .ok (if (needOf spec bp co)[c]! then (words (colv cols c)).extract (8 * lo) (8 * hi) else .empty) :=
    fun c hc => cutCol_slice hsl hrows kw hkw lo hi hlh hhi c hc
  refine ⟨chunkOfCols spec fill sortVar bp co
    #[if (needOf spec bp co)[0]! then (words (colv cols 0)).extract (8 * lo) (8 * hi) else .empty,
      if (needOf spec bp co)[1]! then (words (colv cols 1)).extract (8 * lo) (8 * hi) else .empty,
      if (needOf spec bp co)[2]! then (words (colv cols 2)).extract (8 * lo) (8 * hi) else .empty,
      if (needOf spec bp co)[3]! then (words (colv cols 3)).extract (8 * lo) (8 * hi) else .empty] (hi - lo), ?_, ?_⟩
  · unfold blockChunk
    rw [hkwEq]
    simp only [bind, Except.bind, hlhp]
    rw [hcut 0 (by omega), hcut 1 (by omega), hcut 2 (by omega), hcut 3 (by omega)]
    rfl
  · rw [chunkOfCols_tuples spec hspec fill sortVar bp (fun ck hck => by rw [← hbp] at hck; exact blockPlan_checks_sub spec b ck hck)
      co (by rw [← hco]; simp [constOutOf]) _ (hi - lo) (fun c j => rowCol (cols.row (lo + j)) c)]
    · -- the rows the scan keeps, by the key range and the plan
      have hkeep : ∀ i, i < b.rows → keep spec (cols.row i) =
          ((prefixCmp (cols.row i) spec.key == .eq) &&
            (bp.checks.toList.all (chk (cols.row i)) && (!bp.named || (cols.row i).g != 0) &&
              spec.eqs.toList.all (eqk (cols.row i)))) := by
        intro i hi'
        have hk := blockPlan_keep spec b (cols.row i) (fun c y hc => colConst_sound prb b cols h c y hc i hi')
        rw [hbp, hskip] at hk
        unfold keep
        rw [hk]
        cases (prefixCmp (cols.row i) spec.key == .eq) <;> cases bp.checks.toList.all (chk (cols.row i)) <;>
          cases (!bp.named || (cols.row i).g != 0) <;> cases spec.eqs.toList.all (eqk (cols.row i)) <;> rfl
      rw [filter_congr_mem _ _ _ (fun i hi' => hkeep i (List.mem_range.mp hi'))]
      rw [filter_range_interval b.rows lo hi hlh hhi _ _ (fun i hi' => by
        rw [beq_iff_eq]; exact (hiff i hi').symm)]
      rw [List.map_map]
      rfl
    · intro c j hc hj
      rw [rowCol_row]
      exact hv64 c (lo + j) hc (by omega)
    · intro c hc hn j hj
      have hn' : (needOf spec bp co)[c]! = true := by rw [hneed c hc]; exact hn
      rw [rowCol_row]
      match c, hc with
      | 0, _ => simp only [hn', if_true]; exact at64_cut _ b.rows (hsz 0 (by omega)) (fun i hi => hv64 0 i (by omega) hi) lo hi j (by omega) hhi
      | 1, _ => simp only [hn', if_true]; exact at64_cut _ b.rows (hsz 1 (by omega)) (fun i hi => hv64 1 i (by omega) hi) lo hi j (by omega) hhi
      | 2, _ => simp only [hn', if_true]; exact at64_cut _ b.rows (hsz 2 (by omega)) (fun i hi => hv64 2 i (by omega) hi) lo hi j (by omega) hhi
      | 3, _ => simp only [hn', if_true]; exact at64_cut _ b.rows (hsz 3 (by omega)) (fun i hi => hv64 3 i (by omega) hi) lo hi j (by omega) hhi
    · intro k hk x hx j hj
      rw [← hco] at hx
      unfold constOutOf at hx
      rw [getElem!_pos _ k (by simp; exact hk)] at hx
      simp only [Array.getElem_map] at hx
      split at hx
      · rw [← getElem!_pos spec.outCols k hk] at hx
        exact colConst_sound prb b cols h _ x hx (lo + j) (by omega)
      · cases hx

/-! ## Blocks the scan reads no chunk from -/

/-- The rows of block `b` of a PRB1 byte array, as activation decodes them
    (none when activation refuses the block). -/
def blockRows (prb : ByteArray) (b : BlockMeta) : List Row :=
  match decodeBlockAt prb b b.offset with
  | .ok cols => (List.range b.rows).map cols.row
  | .error _ => []

/-- The output tuples a scan of `spec` should give for block `b`. -/
def blockOut (spec : ScanSpec) (prb : ByteArray) (b : BlockMeta) : List (List Nat) :=
  ((blockRows prb b).filter (keep spec)).map (proj spec)

theorem blockOut_eq (spec : ScanSpec) (prb : ByteArray) (b : BlockMeta) (cols : Cols)
    (h : decodeBlockAt prb b b.offset = .ok cols) :
    blockOut spec prb b = ((List.range b.rows).filter fun i => keep spec (cols.row i)).map fun i => proj spec (cols.row i) := by
  unfold blockOut blockRows
  rw [h]
  simp only [List.filter_map, List.map_map]
  rfl

/-- A row the scan keeps carries the key prefix, so its block is selected. -/
theorem keep_prefix (spec : ScanSpec) (r : Row) (h : keep spec r = true) : prefixCmp r spec.key = .eq := by
  unfold keep at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

theorem blockOut_unselected (spec : ScanSpec) (prb : ByteArray) (b : BlockMeta) (cols : Cols)
    (h : decodeBlockAt prb b b.offset = .ok cols) (hsel : selects b spec.key = false) :
    blockOut spec prb b = [] := by
  rw [blockOut_eq spec prb b cols h, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro i hi hk
  have hi' := List.mem_range.mp hi
  have hp := keep_prefix spec _ hk
  obtain ⟨h1, h2⟩ := row_between prb b cols h i hi'
  have hf : prefixCmp b.first spec.key ≠ .gt := by
    intro hc; have := ScanTheorems.prefixCmp_gt_of_le spec.key h1 hc; rw [hp] at this; cases this
  have hl : prefixCmp b.last spec.key ≠ .lt := by
    intro hc; have := ScanTheorems.prefixCmp_lt_of_le spec.key h2 hc; rw [hp] at this; cases this
  unfold selects at hsel
  cases hcf : prefixCmp b.first spec.key <;> cases hcl : prefixCmp b.last spec.key <;> simp_all

theorem blockOut_skipped (spec : ScanSpec) (prb : ByteArray) (b : BlockMeta) (cols : Cols)
    (h : decodeBlockAt prb b b.offset = .ok cols) (hskip : (blockPlan spec b).skip = true) :
    blockOut spec prb b = [] := by
  rw [blockOut_eq spec prb b cols h, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro i hi hk
  have hi' := List.mem_range.mp hi
  have hpk := blockPlan_keep spec b (cols.row i) (fun c y hc => colConst_sound prb b cols h c y hc i hi')
  rw [hskip] at hpk
  unfold keep at hk
  simp only [Bool.not_true, Bool.false_and] at hpk
  rw [hpk] at hk
  simp at hk

/-! ## The walk over the blocks -/

theorem blocksForGo_range (metas : Array BlockMeta) (key : Array UInt64) :
    ∀ f i (out : Array Nat), ∃ c, (blocksForGo metas key f i out).toList = out.toList ++ List.range' i c ∧
      (c = 0 ∨ i + c ≤ metas.size) := by
  intro f
  induction f with
  | zero => intro i out; exact ⟨0, by simp [blocksForGo], Or.inl rfl⟩
  | succ f ih =>
    intro i out
    simp only [blocksForGo]
    split
    · exact ⟨0, by simp, Or.inl rfl⟩
    · rename_i hi
      split
      · exact ⟨0, by simp, Or.inl rfl⟩
      · obtain ⟨c, hc, hb⟩ := ih (i + 1) (out.push i)
        refine ⟨c + 1, ?_, Or.inr (by omega)⟩
        rw [hc, Array.toList_push, List.range'_succ]
        simp

theorem flatMap_range_interval {β : Type} (n a c : Nat) (hac : a + c ≤ n) (E : Nat → List β)
    (hE : ∀ k, k < n → (k < a ∨ a + c ≤ k) → E k = []) :
    (List.range n).flatMap E = (List.range' a c).flatMap E := by
  have hsplit : List.range n = List.range' 0 a ++ List.range' a c ++ List.range' (a + c) (n - (a + c)) := by
    rw [List.range_eq_range']
    have e1 := @List.range'_append 0 a c 1
    have e2 := @List.range'_append 0 (a + c) (n - (a + c)) 1
    simp only [Nat.one_mul, Nat.zero_add] at e1 e2
    rw [← e1, show a + c + (n - (a + c)) = n by omega] at e2
    exact e2.symm
  rw [hsplit, List.flatMap_append, List.flatMap_append]
  have h1 : (List.range' 0 a).flatMap E = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro k hk
    have := List.mem_range'_1.mp hk
    exact hE k (by omega) (Or.inl (by omega))
  have h3 : (List.range' (a + c) (n - (a + c))).flatMap E = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro k hk
    have := List.mem_range'_1.mp hk
    exact hE k (by omega) (Or.inr (by omega))
  rw [h1, h3, List.nil_append, List.append_nil]

theorem flatMap_eq_range {α β : Type} [Inhabited α] (l : List α) (g : α → List β) :
    l.flatMap g = (List.range l.length).flatMap fun k => g l[k]! := by
  rw [List.flatMap, List.flatMap, map_range_getElem! l g]

theorem toArray_getElem! (ms : List BlockMeta) (i : Nat) (h : i < ms.length) : ms.toArray[i]! = ms[i] := by
  simp [getElem!_pos, h]

/-! ## Reading a chunk by its columns alone (`fill = true`) -/

/-- The tuples of a chunk read from its columns only (what the joins read
    when the scan fills constant columns, `fill = true`). -/
def colTuples (ch : Chunk) : List (List Nat) :=
  (List.range ch.table.rows).map fun i => (List.range ch.table.cols.size).map fun k =>
    (at64 ch.table.cols[k]! i).toNat

theorem constWordsGo_data (x : UInt64) : ∀ k (out : ByteArray),
    (constWordsGo x k out).data.toList = out.data.toList ++ ((List.replicate k x.toNat).map Column.put64).flatten := by
  intro k
  induction k with
  | zero => intro out; simp [constWordsGo]
  | succ k ih =>
    intro out
    simp only [constWordsGo]
    rw [ih, side_put64_data, List.replicate_succ, List.map_cons, List.flatten_cons, List.append_assoc]

theorem at64_constWords (x : UInt64) (n j : Nat) (hj : j < n) : at64 (constWords x n) j = x := by
  have hw : constWords x n = words (List.replicate n x.toNat).toArray := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [constWords, constWordsGo_data, FrameWords.words_data]
    simp
    rfl
  rw [hw, at64_words _ _ (by simpa using hj)]
  simp

/-- With `fill = true` the columns of a chunk hold what its tuples say. -/
theorem chunkOfCols_colTuples (spec : ScanSpec) (sortVar : Option String)
    (bp : BlockPlan) (constOut : Array (Option Nat)) (hco : constOut.size = spec.outCols.size)
    (cols : Array ByteArray) (n : Nat) :
    colTuples (chunkOfCols spec true sortVar bp constOut cols n) =
      tuples (chunkOfCols spec true sortVar bp constOut cols n) := by
  unfold chunkOfCols
  by_cases hp : bp.perRow spec = true
  · rw [if_pos hp]
    obtain ⟨s1, -, -⟩ := selectRows_spec cols bp.checks bp.named spec.eqs spec.outCols n (n + 1) 0
      (spec.outVars.map fun _ => ByteArray.emptyWithCapacity (8 * n)) 0 (by omega)
    generalize selectRows cols bp.checks bp.named spec.eqs spec.outCols n (n + 1) 0
      (spec.outVars.map fun _ => ByteArray.emptyWithCapacity (8 * n)) 0 = res at s1
    obtain ⟨out, k⟩ := res
    dsimp only at s1
    unfold colTuples tuples
    simp only [Array.size_map] at s1 ⊢
    rw [s1]
    apply map_congr_mem
    intro i _
    apply map_congr_mem
    intro k' hk'
    have hk := List.mem_range.mp hk'
    have hnone : (spec.outVars.map fun _ => (none : Option UInt64))[k']! = none := by
      rw [getElem!_pos _ k' (by simpa using hk)]; simp
    rw [hnone]
  · rw [if_neg hp]
    unfold colTuples tuples
    simp only [Array.size_map, List.size_toArray, List.length_range]
    rw [hco]
    apply map_congr_mem
    intro i hi
    have hin := List.mem_range.mp hi
    apply map_congr_mem
    intro k' hk'
    have hk := List.mem_range.mp hk'
    have hck : (constOut.map (·.map Nat.toUInt64))[k']! = (constOut[k']!).map Nat.toUInt64 := by
      rw [getElem!_pos _ k' (by simp [hco]; exact hk), getElem!_pos _ k' (by rw [hco]; exact hk)]
      simp
    have hout : ((List.range spec.outCols.size).toArray.map fun k =>
        match constOut[k]! with
        | some x => if true = true then constWords x.toUInt64 n else ByteArray.empty
        | none => cols[spec.outCols[k]!]!)[k']! =
        match constOut[k']! with
        | some x => if true = true then constWords x.toUInt64 n else ByteArray.empty
        | none => cols[spec.outCols[k']!]! := by
      rw [getElem!_pos _ k' (by simp; exact hk)]
      simp
    erw [hck, hout]
    cases hc : constOut[k']! with
    | none => rfl
    | some x =>
      simp only [Option.map_some, if_true]
      rw [at64_constWords _ _ _ hin]

/-- Every chunk `blockChunk` makes is a `chunkOfCols`. -/
theorem blockChunk_ok {spec : ScanSpec} {fill : Bool} (b : BlockMeta) (bytes : ByteArray) (starts : Array Nat)
    (ch : Chunk) (sortVar : Option String) {bp : BlockPlan} {constOut : Array (Option Nat)} {need : Array Bool}
    (h : blockChunk spec fill sortVar b bp constOut need bytes starts = .ok ch) :
    ∃ cs n, ch = chunkOfCols spec fill sortVar bp constOut cs n := by
  unfold blockChunk at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals (try (cases h; done))
  all_goals (try (exact ⟨_, _, rfl⟩))
  all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; exact ⟨_, _, h.symm⟩)

/-! ## The walk, for a chunk reading `den` -/

/-- The scan's `f` that appends every chunk's tuples (read by `den`) and never
    stops. -/
def collectWith (den : Chunk → List (List Nat)) (acc : List (List Nat)) (ch : Chunk) :
    ExceptT String Id (List (List Nat) × Bool) :=
  pure (acc ++ den ch, true)

/-- `den` reads every chunk that `blockChunk` makes as `tuples` does. -/
def DenOk (spec : ScanSpec) (fill : Bool) (den : Chunk → List (List Nat)) : Prop :=
  ∀ sortVar b bytes starts ch, blockChunk spec fill sortVar b (blockPlan spec b)
    (constOutOf spec b (blockPlan spec b)) (needOf spec (blockPlan spec b) (constOutOf spec b (blockPlan spec b)))
    bytes starts = .ok ch → den ch = tuples ch

/-- One block of a scan with no overlay over an in-memory store: the scan
    goes on, with the block's tuples appended. -/
theorem scanBlockM_step (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) (fill : Bool)
    (den : Chunk → List (List Nat)) (hden : DenOk spec fill den)
    (prb : ByteArray) (ms : List BlockMeta)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hfits : ∀ b ∈ ms, b.rows ≤ two64)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols)
    (sortVar : Option String) (ox : OvCtx) (hon : ox.on = false)
    (k : Nat) (hk : k < ms.length) (s : ScanState (List (List Nat))) :
    ∃ s1, scanBlockM st spec fill (collectWith den) ms.toArray sortVar ox k s = pure (.yield s1) ∧
      s1.acc = s.acc ++ blockOut spec prb ms[k] ∧ s1.stopped = s.stopped := by
  obtain ⟨cols, h⟩ := hblocks ms[k] (List.getElem_mem hk)
  have hrows := hfits ms[k] (List.getElem_mem hk)
  unfold scanBlockM
  rw [toArray_getElem! ms k hk]
  by_cases hsel : selects ms[k] spec.key = true
  · simp only [hsel, Bool.not_true, Bool.false_eq_true, if_false, hon]
    by_cases hskip : (blockPlan spec ms[k]).skip = true
    · simp only [hskip, if_true]
      exact ⟨s, rfl, by rw [blockOut_skipped spec prb ms[k] cols h hskip, List.append_nil], rfl⟩
    · have hskip' : (blockPlan spec ms[k]).skip = false := by simpa using hskip
      simp only [hskip', Bool.false_eq_true, if_false]
      obtain ⟨bytes, starts, nbytes, hrf, hsl⟩ := readFrames_slice st prb spec.perm hprb ms[k] cols h hrows
        (needOf spec (blockPlan spec ms[k]) (constOutOf spec ms[k] (blockPlan spec ms[k])))
      obtain ⟨ch, hch, ht⟩ := blockChunk_tuples spec hspec fill sortVar prb ms[k] cols h hrows hskip' bytes starts hsl
      rw [hrf]
      simp only [pure_bind, hch, ofExceptM, collectWith, stepOf, if_true]
      refine ⟨_, rfl, ?_, rfl⟩
      simp only
      rw [hden sortVar ms[k] bytes starts ch hch, ht, blockOut_eq spec prb ms[k] cols h]
  · have hsel' : selects ms[k] spec.key = false := by simpa using hsel
    simp only [hsel', Bool.not_false, if_true]
    exact ⟨s, rfl, by rw [blockOut_unselected spec prb ms[k] cols h hsel', List.append_nil], rfl⟩

theorem forIn_blocks (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) (fill : Bool)
    (den : Chunk → List (List Nat)) (hden : DenOk spec fill den)
    (prb : ByteArray) (ms : List BlockMeta)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hfits : ∀ b ∈ ms, b.rows ≤ two64)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols)
    (sortVar : Option String) (ox : OvCtx) (hon : ox.on = false) :
    ∀ (L : List Nat), (∀ k ∈ L, k < ms.length) → ∀ (s : ScanState (List (List Nat))),
      ∃ s', forIn L s (scanBlockM st spec fill (collectWith den) ms.toArray sortVar ox) = pure s' ∧
        s'.acc = s.acc ++ L.flatMap (fun k => blockOut spec prb ms[k]!) ∧ s'.stopped = s.stopped := by
  intro L
  induction L with
  | nil => intro _ s; exact ⟨s, rfl, by simp, rfl⟩
  | cons k ks ih =>
    intro hL s
    have hk := hL k List.mem_cons_self
    obtain ⟨s1, h1, a1, t1⟩ :=
      scanBlockM_step st spec hspec fill den hden prb ms hprb hfits hblocks sortVar ox hon k hk s
    obtain ⟨s', h2, a2, t2⟩ := ih (fun j hj => hL j (List.mem_cons_of_mem _ hj)) s1
    refine ⟨s', ?_, ?_, by rw [t2, t1]⟩
    · rw [List.forIn_cons, h1, pure_bind]
      exact h2
    · rw [a2, a1, List.flatMap_cons, List.append_assoc, getElem!_pos ms k hk]

/-- The scan with any chunk reading `den` that agrees with `tuples`. -/
theorem scanFoldM_den (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) (fill : Bool)
    (den : Chunk → List (List Nat)) (hden : DenOk spec fill den)
    (prb : ByteArray) (ms : List BlockMeta)
    (hmetas : st.metas spec.perm = pure ms.toArray)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hovl : (st.ovl spec.perm).isEmpty = true)
    (hadm : prmAdmitted spec.perm ms = true)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols) :
    ∃ stats, scanFoldM st spec fill [] (collectWith den) =
      pure (((ms.flatMap (blockRows prb)).filter (keep spec)).map (proj spec), stats) := by
  have hch : chainGo prbHeaderBytes ms = true := by
    simp only [prmAdmitted, Bool.and_eq_true] at hadm
    exact hadm.1.1.2
  have hfits : ∀ b ∈ ms, b.rows ≤ two64 := by
    intro b hb
    have := chainGo_fits ms _ hch b hb
    simp only [metaFits, Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, h32⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := this
    exact Nat.le_of_lt (Nat.lt_of_lt_of_le h32 (by decide))
  have hon : (ovCtx (st.ovl spec.perm) spec.key).on = false := by
    simp [ovCtx, hovl]
  have hLk : ∀ k ∈ (blocksFor ms.toArray spec.key).toList, k < ms.length := by
    intro k hk
    obtain ⟨c, hc, hb⟩ := blocksForGo_range ms.toArray spec.key ms.toArray.size
      (firstBlockGo ms.toArray spec.key (Nat.log2 ms.toArray.size + 2) 0 ms.toArray.size) #[]
    unfold blocksFor at hk
    rw [hc] at hk
    simp only [List.nil_append] at hk
    have := List.mem_range'_1.mp hk
    have hs : ms.toArray.size = ms.length := List.size_toArray
    rcases hb with hb | hb
    · omega
    · omega
  unfold scanFoldM
  rw [hmetas, pure_bind]
  obtain ⟨s', hfor, hacc, hstop⟩ := forIn_blocks st spec hspec fill den hden prb ms hprb hfits hblocks
    (match spec.outCols[0]? with
      | some c => if c == spec.key.size then spec.outVars[0]? else none
      | none => none) _ hon
    (blocksFor ms.toArray spec.key).toList hLk
    { acc := [], stats := { blocksTotal := ms.toArray.size }, insPos := 0, stopped := false }
  refine ⟨s'.stats, ?_⟩
  simp only []
  rw [← Array.forIn_toList]
  erw [hfor]
  rw [pure_bind]
  simp only [hon, Bool.false_and, Bool.false_eq_true, if_false]
  congr 2
  rw [hacc, List.nil_append]
  -- every block outside `blocksFor` gives no tuple
  rw [List.filter_flatMap, List.map_flatMap]
  show _ = ms.flatMap (blockOut spec prb)
  rw [flatMap_eq_range ms (blockOut spec prb)]
  have hE : ∀ k, k < ms.length → k ∉ (blocksFor ms.toArray spec.key).toList → blockOut spec prb ms[k]! = [] := by
    intro k hk hnot
    obtain ⟨cols, h⟩ := hblocks ms[k] (List.getElem_mem hk)
    rw [getElem!_pos ms k hk, blockOut_eq spec prb ms[k] cols h, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro i hi hkeep
    have hi' := List.mem_range.mp hi
    obtain ⟨h1, h2⟩ := row_between prb ms[k] cols h i hi'
    have := ScanTheorems.blocksFor_complete spec.perm ms hadm spec.key k hk _ h1 h2 (keep_prefix spec _ hkeep)
    exact hnot (Array.mem_toList_iff.mpr this.1)
  obtain ⟨c, hc, hb⟩ := blocksForGo_range ms.toArray spec.key ms.toArray.size
    (firstBlockGo ms.toArray spec.key (Nat.log2 ms.toArray.size + 2) 0 ms.toArray.size) #[]
  have hL : (blocksFor ms.toArray spec.key).toList =
      List.range' (firstBlockGo ms.toArray spec.key (Nat.log2 ms.toArray.size + 2) 0 ms.toArray.size) c := by
    unfold blocksFor; rw [hc]; simp
  rcases hb with hb | hb
  · subst hb
    rw [hL] at hE ⊢
    simp only [List.range'_zero, List.flatMap_nil]
    rw [eq_comm, List.flatMap_eq_nil_iff]
    intro k hk
    exact hE k (List.mem_range.mp hk) (by simp)
  · rw [hL] at hE ⊢
    have hs : ms.toArray.size = ms.length := List.size_toArray
    rw [flatMap_range_interval ms.length _ c (by omega) (fun k => blockOut spec prb ms[k]!)
      (fun k hk hout => hE k hk (fun hm => by have := List.mem_range'_1.mp hm; omega))]

/-! ## The scan (lemma L4e) -/

/-- **L4e.** A scan of an admitted permutation over a store that reads its
    PRM1 entries and PRB1 bytes from memory, with no delta overlay, gives the
    output tuples of exactly the rows of the permutation that carry the key
    prefix and pass the checks, the named-graph test and the repeated-variable
    tests, in row order (`tuples`: a chunk's constants, else its columns).
    The hypotheses are what activation checks: the PRM1 entries admitted
    (`prmAdmitted`: blocks sorted and contiguous) and every block admitted
    (`decodeBlockAt`). -/
theorem scanFoldM_tuples (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) (fill : Bool)
    (prb : ByteArray) (ms : List BlockMeta)
    (hmetas : st.metas spec.perm = pure ms.toArray)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hovl : (st.ovl spec.perm).isEmpty = true)
    (hadm : prmAdmitted spec.perm ms = true)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols) :
    ∃ stats, scanFoldM st spec fill [] (collectWith tuples) =
      pure (((ms.flatMap (blockRows prb)).filter (keep spec)).map (proj spec), stats) :=
  scanFoldM_den st spec hspec fill tuples (fun _ _ _ _ _ _ => rfl) prb ms hmetas hprb hovl hadm hblocks

/-- **L4e, columns.** With `fill = true` (the BGP and join path) the columns
    of the chunks alone hold the same tuples. -/
theorem scanFoldM_columns (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec)
    (prb : ByteArray) (ms : List BlockMeta)
    (hmetas : st.metas spec.perm = pure ms.toArray)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hovl : (st.ovl spec.perm).isEmpty = true)
    (hadm : prmAdmitted spec.perm ms = true)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols) :
    ∃ stats, scanFoldM st spec true [] (collectWith colTuples) =
      pure (((ms.flatMap (blockRows prb)).filter (keep spec)).map (proj spec), stats) := by
  apply scanFoldM_den st spec hspec true colTuples _ prb ms hmetas hprb hovl hadm hblocks
  intro sortVar b bytes starts ch hch
  obtain ⟨cs, n, rfl⟩ := blockChunk_ok b bytes starts ch sortVar hch
  exact chunkOfCols_colTuples spec sortVar _ _ (by simp [constOutOf]) cs n

#print axioms scanFoldM_tuples
#print axioms scanFoldM_columns
#print axioms blockChunk_tuples
#print axioms colConst_sound

end L4Factoidal.Storage.Sbm11.ScanFoldTheorems
