/-
L4Factoidal.Storage.Sbm11.SipScanTheorems — the scan with candidates as a
whole (sideways information passing,
https://github.com/danbri/factoidal/issues/809; lemma L4i of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

* `sipChunk_tuples`: the chunk `IdQuery.sipChunk` builds for one admitted
  block holds the output tuples of exactly the block's rows that the scan
  keeps (`ScanFoldTheorems.keep`) and whose column `key.size` holds a
  candidate, in row order.
* `sipSkip_none`: a block that `Sip.mayHold` rules out holds no such row.
* `scanFoldSipM_tuples`: over a store in memory (`m = Id`) of an admitted
  permutation with no overlay, and candidates in non-decreasing order, the
  scan with candidates returns the output tuples of exactly the rows of the
  permutation that the full scan keeps and whose column `key.size` holds a
  candidate.
* `scanFoldSipM_filter`: with the column `key.size` as the first output
  column (the sort variable of the scan, which the planner requires), the
  scan with candidates returns the full scan's tuples
  (`ScanFoldTheorems.scanFoldM_columns`) filtered by "the first value is a
  candidate".

The hypotheses are those of `scanFoldM_columns` (the activation checks and
the planner's scan shape), the key of at most three columns (so a column
follows it) and candidates in non-decreasing order (checked at run time
before a scan uses them, `IdQuery.sipCands`, `Sip.sorted_spec`).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.ScanFoldTheorems
import L4Factoidal.Storage.Sbm11.SipTheorems

namespace L4Factoidal.Storage.Sbm11.SipScanTheorems

open L4Factoidal (two64)
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.ScanFoldTheorems
open L4Factoidal.Storage.Sbm11.FrameWords (words)
open L4Factoidal.Storage.Sbm11.ScanTheorems (colOf rowOf at64_words)
open L4Factoidal.Codec.Zstd (word64)

/-! ## Rows with the key prefix -/

/-- A row with the key prefix holds the key in the key columns. -/
theorem prefixCmpGo_eq (r : Row) (key : Array UInt64) :
    ∀ f j, key.size - j ≤ f → prefixCmpGo r key f j = .eq →
      ∀ i, j ≤ i → i < key.size → rowCol r i = key[i]!.toNat := by
  intro f
  induction f with
  | zero => intro j hf _ i hji hi; omega
  | succ f ih =>
    intro j hf h i hji hi
    simp only [prefixCmpGo] at h
    rw [if_pos (by omega)] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i h1 h2
        rcases Nat.eq_or_lt_of_le hji with he | hlt
        · subst he; omega
        · exact ih (j + 1) (by omega) h i (by omega) hi

theorem prefixCmp_eq_cols (r : Row) (key : Array UInt64) (h : prefixCmp r key = .eq) :
    ∀ i, i < key.size → rowCol r i = key[i]!.toNat :=
  fun i hi => prefixCmpGo_eq r key key.size 0 (by omega) h i (Nat.zero_le _) hi

/-- In row order, the column after the columns two rows agree on is in
    order. -/
theorem col_le_of_le (a r : Row) (k : Nat) (h : a.le r = true) (hag : ∀ j, j < k → rowCol a j = rowCol r j) :
    rowCol a k ≤ rowCol r k := by
  rw [ScanTheorems.le_iff] at h
  rcases h with h | h
  · subst h; exact Nat.le_refl _
  · obtain ⟨d, hd1, hd2⟩ := ScanTheorems.lt_exists_diff h
    rcases Nat.lt_trichotomy d k with hlt | heq | hgt
    · have := hag d hlt; omega
    · subst heq; exact Nat.le_of_lt hd2
    · exact Nat.le_of_eq (hd1 k hgt)

theorem toUInt64_le (x y : Nat) (hx : x < two64) (hy : y < two64) (h : x ≤ y) : x.toUInt64 ≤ y.toUInt64 := by
  rw [UInt64.le_iff_toNat_le]
  simp only [Nat.toUInt64, UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  exact h

/-- Every row of an admitted block with the key prefix has its column
    `key.size` in the range `sipRange` gives. -/
theorem sipRange_bounds (prb : ByteArray) (b : BlockMeta) (cols : Cols)
    (h : decodeBlockAt prb b b.offset = .ok cols) (key : Array UInt64) (hk : key.size < 4)
    (i : Nat) (hi : i < b.rows) (hp : prefixCmp (cols.row i) key = .eq) :
    (sipRange b key key.size).1 ≤ (rowCol (cols.row i) key.size).toUInt64 ∧
      (rowCol (cols.row i) key.size).toUInt64 ≤ (sipRange b key key.size).2 := by
  obtain ⟨-, hv64, hpos, hf, hl, -⟩ := admitted_facts prb b cols h
  obtain ⟨h1, h2⟩ := row_between prb b cols h i hi
  have hvr : rowCol (cols.row i) key.size < two64 := by
    rw [rowCol_row]; exact hv64 _ i (by omega) hi
  unfold sipRange
  constructor
  · simp only
    split
    · rename_i hf'
      have hfe : prefixCmp b.first key = .eq := by simpa using hf'
      have hvf : rowCol b.first key.size < two64 := by
        rw [← hf, rowCol_row]; exact hv64 _ 0 (by omega) hpos
      apply toUInt64_le _ _ hvf hvr
      apply col_le_of_le _ _ _ h1
      intro j hj
      rw [prefixCmp_eq_cols _ key hfe j hj, prefixCmp_eq_cols _ key hp j hj]
    · exact UInt64.zero_le
  · simp only
    split
    · rename_i hl'
      have hle : prefixCmp b.last key = .eq := by simpa using hl'
      have hvl : rowCol b.last key.size < two64 := by
        rw [← hl, rowCol_row]; exact hv64 _ (b.rows - 1) (by omega) (by omega)
      apply toUInt64_le _ _ hvr hvl
      apply col_le_of_le _ _ _ h2
      intro j hj
      rw [prefixCmp_eq_cols _ key hp j hj, prefixCmp_eq_cols _ key hle j hj]
    · rw [UInt64.le_iff_toNat_le]
      have := UInt64.toNat_lt (rowCol (cols.row i) key.size).toUInt64
      show _ ≤ 18446744073709551615
      omega

/-- The candidate test of a row: its column `key.size` holds a
    candidate. -/
def candOf (spec : ScanSpec) (cands : Array UInt64) (r : Row) : Bool :=
  cands.contains (rowCol r spec.key.size).toUInt64

/-- A block that `mayHold` rules out has no kept row with a candidate. -/
theorem sipSkip_none (spec : ScanSpec) (hk : spec.key.size < 4) (cands : Array UInt64) (hs : Sip.Sorted cands)
    (prb : ByteArray) (b : BlockMeta) (cols : Cols) (h : decodeBlockAt prb b b.offset = .ok cols)
    (q : Nat) (hm : Sip.mayHold cands (sipRange b spec.key spec.key.size).1 (sipRange b spec.key spec.key.size).2 q = false)
    (i : Nat) (hi : i < b.rows) (hkeep : keep spec (cols.row i) = true) : candOf spec cands (cols.row i) = false := by
  have hp := keep_prefix spec _ hkeep
  obtain ⟨b1, b2⟩ := sipRange_bounds prb b cols h spec.key hk i hi hp
  unfold candOf
  cases hc : cands.contains (rowCol (cols.row i) spec.key.size).toUInt64
  · rfl
  · rcases Sip.mayHold_false cands hs _ _ q hm _ hc with h1 | h1
    · exact absurd b1 (UInt64.not_le.mpr h1)
    · exact absurd b2 (UInt64.not_le.mpr h1)

/-! ## One block (`sipChunk`) -/

/-- `needOf` with the join column set. -/
theorem needSet_getElem (spec : ScanSpec) (bp : BlockPlan) (co : Array (Option Nat)) (c : Nat) (hc : c < 4) :
    ((needOf spec bp co).set! spec.key.size true)[c]! = (if spec.key.size = c then true else needCol spec bp co c) := by
  have hsz : (needOf spec bp co).size = 4 := rfl
  have hs' : ((needOf spec bp co).set! spec.key.size true).size = 4 := by
    simp only [Array.set!, Array.size_setIfInBounds, hsz]
  rw [getElem!_pos _ c (by omega)]
  simp only [Array.set!]
  rw [Array.getElem_setIfInBounds (by omega)]
  split
  · rfl
  · rw [← getElem!_pos (needOf spec bp co) c (by omega), needOf_getElem spec bp co c hc]

/-- The row tests that `blockPlan` leaves to the chunk, on row `i` of the
    block. -/
def rowTests (bp : BlockPlan) (spec : ScanSpec) (cols : Cols) (i : Nat) : Bool :=
  bp.checks.toList.all (fun ck => rowCol (cols.row i) ck.1 == ck.2.toNat) &&
    (!bp.named || rowCol (cols.row i) 3 != 0) &&
    spec.eqs.toList.all (fun e => rowCol (cols.row i) e.1 == rowCol (cols.row i) e.2)

/-- A filter and map over the positions of a list, read through `l[j]!`. -/
theorem filter_map_pos {β : Type} (l : List Nat) (P : Nat → Bool) (F : Nat → β) :
    ((List.range l.length).filter (fun j => P l[j]!)).map (fun j => F l[j]!) = (l.filter P).map F := by
  have h1 : (List.range l.length).map (fun j => l[j]!) = l := by
    have := map_range_getElem! l id
    simpa using this
  have h2 : ((List.range l.length).filter (fun j => P l[j]!)).map (fun j => F l[j]!) =
      (((List.range l.length).map (fun j => l[j]!)).filter P).map F := by
    rw [List.filter_map, List.map_map]
    rfl
  rw [h2, h1]

theorem word64_words_u (a : Array Nat) (t : Nat) (ht : t < a.size) :
    word64 (words a) (8 * t) = (a[t]!).toUInt64 := by
  have := at64_words a t ht
  unfold at64 at this
  rw [this, getElem!_pos a t ht]

/-- A column of words whose data are the `put64` of the values at `pos`. -/
theorem words_of_data (X : ByteArray) (pos : List Nat) (val : Nat → Nat)
    (h : X.data.toList = (pos.map fun r => Column.put64 (val r)).flatten) :
    X = words (pos.map val).toArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [h, FrameWords.words_data]
  simp [List.map_map, Function.comp_def]

/-- **One block.** The chunk of one admitted block (not skipped by its plan)
    with candidates holds the output tuples of exactly the block's rows that
    the scan keeps and whose column `key.size` holds a candidate, in row
    order. -/
theorem sipChunk_tuples (spec : ScanSpec) (hspec : SpecOk spec) (hk : spec.key.size < 4)
    (cands : Array UInt64) (hs : Sip.Sorted cands) (sortVar : Option String)
    (prb : ByteArray) (b : BlockMeta) (cols : Cols) (h : decodeBlockAt prb b b.offset = .ok cols)
    (hskip : (blockPlan spec b).skip = false) (bytes : ByteArray) (starts : Array Nat)
    (hsl : SliceOk b cols ((needOf spec (blockPlan spec b) (constOutOf spec b (blockPlan spec b))).set!
      spec.key.size true) bytes starts) (p : Nat) :
    ∃ ch t g, sipChunk spec cands sortVar b (blockPlan spec b) (constOutOf spec b (blockPlan spec b))
        ((needOf spec (blockPlan spec b) (constOutOf spec b (blockPlan spec b))).set! spec.key.size true)
        bytes starts p = .ok (ch, t, g) ∧
      colTuples ch = ((List.range b.rows).filter fun i => keep spec (cols.row i) && candOf spec cands (cols.row i)).map
        (fun i => proj spec (cols.row i)) ∧
      ∃ cs n, ch = chunkOfCols spec true sortVar (blockPlan spec b) (constOutOf spec b (blockPlan spec b)) cs n ∧
        ∀ c, c < 4 → needCol spec (blockPlan spec b) (constOutOf spec b (blockPlan spec b)) c = true →
          cs[c]!.size = 8 * n := by
  obtain ⟨hsz, hv64, -, -, -, -⟩ := admitted_facts prb b cols h
  generalize hbp : blockPlan spec b = bp at hskip hsl ⊢
  generalize hco : constOutOf spec b bp = co at hsl ⊢
  generalize hnd : (needOf spec bp co).set! spec.key.size true = need' at hsl ⊢
  have hneed : ∀ c, c < 4 → need'[c]! = (if spec.key.size = c then true else needCol spec bp co c) := by
    intro c hc; rw [← hnd]; exact needSet_getElem spec bp co c hc
  -- the key columns in full
  let kw : Array ByteArray := if bp.full then #[] else
    ((List.range' 0 spec.key.size).map fun c => words (colv cols c)).toArray
  have hkwEq : keyWordsOf b bytes starts bp.full spec.key.size = .ok kw := by
    unfold keyWordsOf
    cases hf : bp.full
    · simp only [Bool.false_eq_true, if_false, kw, hf]
      rw [colsAllGo_slice hsl hsz spec.key.size 0 #[] (by omega)
        (fun c _ hc => by
          rw [hneed c (by omega), if_neg (by omega)]
          exact needCol_key spec bp co c hf (by omega))]
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
  -- the found rows
  have hjs := hsl spec.key.size hk (by rw [hneed _ hk, if_pos rfl])
  obtain ⟨pos, jw, hfind, hpos, hjw⟩ := Sip.findWords_spec bytes b.rows starts[spec.key.size]! lo hi cands hs p _ _
    hlh hhi hjs
  have hjsz := hsz spec.key.size hk
  have hposl : pos.toList = (List.range' lo (hi - lo)).filter (fun i => candOf spec cands (cols.row i)) := by
    rw [hpos]
    unfold Sip.foundIn
    apply List.filter_congr
    intro t ht
    have := List.mem_range'_1.mp ht
    unfold candOf
    rw [word64_words_u _ t (by omega), rowCol_row]
  have hmem : ∀ m, m < pos.size → lo ≤ pos[m]! ∧ pos[m]! < hi := by
    intro m hm
    have hin : pos[m]! ∈ pos.toList := by
      rw [getElem!_pos pos m hm]; exact Array.getElem_mem_toList hm
    rw [hposl] at hin
    have := List.mem_range'_1.mp (List.mem_filter.mp hin).1
    omega
  have hinc : ∀ m m', m < m' → m' < pos.size → pos[m]! < pos[m']! := by
    intro m m' hmm hm'
    have hpw : List.Pairwise (· < ·) pos.toList := by
      rw [hposl]; exact (List.pairwise_lt_range').filter _
    rw [List.pairwise_iff_getElem] at hpw
    have := hpw m m' (by simp; omega) (by simp; omega) hmm
    rw [getElem!_pos pos m (by omega), getElem!_pos pos m' hm']
    simpa using this
  -- the column of `c` at the found rows
  have hcol : ∀ c, c < 4 → ∃ X, sipCol b bytes starts need' kw spec.key.size jw pos c = .ok X ∧
      ((spec.key.size = c ∨ need'[c]! = true) → X = words (pos.toList.map fun r => (colv cols c)[r]!).toArray) := by
    intro c hc
    unfold sipCol
    by_cases hcj : (c == spec.key.size) = true
    · have hce : c = spec.key.size := by simpa using hcj
      refine ⟨jw, by rw [if_pos hcj], fun _ => ?_⟩
      apply words_of_data jw pos.toList (fun r => (colv cols c)[r]!)
      rw [hjw, ← hpos]
      congr 1
      apply List.map_congr_left
      intro r hr
      have hrm : r < hi := by
        rw [hposl] at hr; have := List.mem_range'_1.mp (List.mem_filter.mp hr).1; omega
      rw [word64_words_u _ r (by omega), hce]
      have := hv64 _ r hk (by omega)
      simp only [Nat.toUInt64, UInt64.toNat_ofNat']
      rw [Nat.mod_eq_of_lt this]
    · rw [if_neg hcj]
      have hcne : spec.key.size ≠ c := fun e => hcj (by simp [e])
      by_cases hn : need'[c]! = true
      · rw [if_pos hn]
        by_cases hkc : c < kw.size
        · rw [dif_pos hkc]
          refine ⟨_, rfl, fun _ => ?_⟩
          apply words_of_data _ pos.toList (fun r => (colv cols c)[r]!)
          rw [Sip.pickWords_data, hkw c hkc]
          congr 1
          apply List.map_congr_left
          intro r hr
          have hrm : r < hi := by
            rw [hposl] at hr; have := List.mem_range'_1.mp (List.mem_filter.mp hr).1; omega
          rw [Sip.word64_words _ r (by rw [hsz c hc]; omega)
            (fun x hx => by
              obtain ⟨i, hi', he⟩ := Array.mem_iff_getElem.mp hx
              rw [← he]
              have := hv64 c i hc (by rw [hsz c hc] at hi'; exact hi')
              rw [getElem!_pos _ i hi'] at this
              exact this)]
        · rw [dif_neg hkc]
          obtain ⟨X, hX, hXd⟩ := Sip.gatherWords_spec bytes b.rows starts[c]! pos _ _ (hsl c hc hn) hinc
            (fun m hm => by have := hmem m hm; omega)
          rw [hX]
          refine ⟨X, rfl, fun _ => ?_⟩
          apply words_of_data X pos.toList (fun r => (colv cols c)[r]!)
          rw [hXd]
          congr 1
          apply List.map_congr_left
          intro r hr
          have hrm : r < hi := by
            rw [hposl] at hr; have := List.mem_range'_1.mp (List.mem_filter.mp hr).1; omega
          rw [Sip.word64_words _ r (by rw [hsz c hc]; omega)
            (fun x hx => by
              obtain ⟨i, hi', he⟩ := Array.mem_iff_getElem.mp hx
              rw [← he]
              have := hv64 c i hc (by rw [hsz c hc] at hi'; exact hi')
              rw [getElem!_pos _ i hi'] at this
              exact this)]
      · rw [if_neg hn]
        refine ⟨_, rfl, fun hh => ?_⟩
        rcases hh with e | e
        · exact absurd e hcne
        · exact absurd e hn
  obtain ⟨X0, h0, e0⟩ := hcol 0 (by omega)
  obtain ⟨X1, h1, e1⟩ := hcol 1 (by omega)
  obtain ⟨X2, h2, e2⟩ := hcol 2 (by omega)
  obtain ⟨X3, h3, e3⟩ := hcol 3 (by omega)
  refine ⟨chunkOfCols spec true sortVar bp co #[X0, X1, X2, X3] pos.size, hi - lo, pos.size, ?_, ?_,
    #[X0, X1, X2, X3], pos.size, rfl, fun c hc hn => ?_⟩
  rotate_left 2
  · have hn' : spec.key.size = c ∨ need'[c]! = true := by
      rw [hneed c hc]
      by_cases e : spec.key.size = c
      · exact Or.inl e
      · right; rw [if_neg e]; exact hn
    have hX : (#[X0, X1, X2, X3] : Array ByteArray)[c]! = words (pos.toList.map fun r => (colv cols c)[r]!).toArray := by
      match c, hc with
      | 0, _ => exact e0 hn'
      | 1, _ => exact e1 hn'
      | 2, _ => exact e2 hn'
      | 3, _ => exact e3 hn'
    rw [hX, words_size']
    simp
  · unfold sipChunk
    rw [hkwEq]
    simp only [bind, Except.bind, hlhp, hfind]
    rw [h0, h1, h2, h3]
    rfl
  · rw [chunkOfCols_colTuples spec sortVar bp co (by rw [← hco]; simp [constOutOf])]
    rw [chunkOfCols_tuples spec hspec true sortVar bp
      (fun ck hck => by rw [← hbp] at hck; exact blockPlan_checks_sub spec b ck hck)
      co (by rw [← hco]; simp [constOutOf]) _ pos.size (fun c j => rowCol (cols.row pos[j]!) c)]
    · -- the tuples over the found rows
      have hpre : ((List.range pos.size).filter fun j =>
            (bp.checks.toList.all fun ck => rowCol (cols.row pos[j]!) ck.1 == ck.2.toNat) &&
              (!bp.named || rowCol (cols.row pos[j]!) 3 != 0) &&
              spec.eqs.toList.all fun e => rowCol (cols.row pos[j]!) e.1 == rowCol (cols.row pos[j]!) e.2).map
            (fun j => (List.range spec.outCols.size).map fun k => rowCol (cols.row pos[j]!) spec.outCols[k]!) =
          (pos.toList.filter (rowTests bp spec cols)).map fun i => proj spec (cols.row i) := by
        have := filter_map_pos pos.toList (rowTests bp spec cols) (fun i => proj spec (cols.row i))
        simp only [Array.length_toList, Array.getElem!_toList] at this
        rw [← this]
        rfl
      rw [hpre, hposl, List.filter_filter]
      -- the rows the scan keeps, by the key range and the plan
      have hkeep : ∀ i, i < b.rows → (keep spec (cols.row i) && candOf spec cands (cols.row i)) =
          ((prefixCmp (cols.row i) spec.key == .eq) &&
            (rowTests bp spec cols i && candOf spec cands (cols.row i))) := by
        intro i hi'
        have hk' := blockPlan_keep spec b (cols.row i) (fun c y hc => colConst_sound prb b cols h c y hc i hi')
        rw [hbp, hskip] at hk'
        unfold keep
        rw [hk']
        unfold rowTests
        have e1 : bp.checks.toList.all (chk (cols.row i)) =
            bp.checks.toList.all (fun ck => rowCol (cols.row i) ck.1 == ck.2.toNat) := rfl
        have e2 : spec.eqs.toList.all (eqk (cols.row i)) =
            spec.eqs.toList.all (fun e => rowCol (cols.row i) e.1 == rowCol (cols.row i) e.2) := rfl
        have e3 : (cols.row i).g = rowCol (cols.row i) 3 := rfl
        rw [e1, e2, e3]
        generalize (prefixCmp (cols.row i) spec.key == .eq) = x1
        generalize bp.checks.toList.all (fun ck => rowCol (cols.row i) ck.1 == ck.2.toNat) = x2
        generalize (!bp.named || rowCol (cols.row i) 3 != 0) = x3
        generalize spec.eqs.toList.all (fun e => rowCol (cols.row i) e.1 == rowCol (cols.row i) e.2) = x4
        generalize candOf spec cands (cols.row i) = x5
        cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;> cases x5 <;> rfl
      rw [filter_congr_mem _ _ _ (fun i hi' => hkeep i (List.mem_range.mp hi'))]
      rw [filter_range_interval b.rows lo hi hlh hhi _ _ (fun i hi' => by
        rw [beq_iff_eq]; exact (hiff i hi').symm)]
      rw [List.range'_eq_map_range, List.filter_map, List.map_map, List.map_map]
      rfl
    · intro c j hc hj
      rw [rowCol_row]
      exact hv64 c _ hc (by have := hmem j hj; omega)
    · intro c hc hn j hj
      have hX : (#[X0, X1, X2, X3] : Array ByteArray)[c]! = words (pos.toList.map fun r => (colv cols c)[r]!).toArray := by
        have hn' : spec.key.size = c ∨ need'[c]! = true := by
          rw [hneed c hc]
          by_cases e : spec.key.size = c
          · exact Or.inl e
          · right; rw [if_neg e]; exact hn
        match c, hc with
        | 0, _ => exact e0 hn'
        | 1, _ => exact e1 hn'
        | 2, _ => exact e2 hn'
        | 3, _ => exact e3 hn'
      rw [hX, at64_words _ _ (by simpa using hj)]
      simp only [List.getElem_toArray, List.getElem_map, Array.getElem_toList]
      rw [rowCol_row, ← getElem!_pos pos j (by simpa using hj)]
      have := hv64 c pos[j]! hc (by have := hmem j (by simpa using hj); omega)
      simp only [Nat.toUInt64, UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt this
    · intro k hk2 x hx j hj
      rw [← hco] at hx
      unfold constOutOf at hx
      rw [getElem!_pos _ k (by simp; exact hk2)] at hx
      simp only [Array.getElem_map] at hx
      split at hx
      · rw [← getElem!_pos spec.outCols k hk2] at hx
        exact colConst_sound prb b cols h _ x hx pos[j]! (by have := hmem j hj; omega)
      · cases hx

/-! ## The walk over the blocks -/

/-- The output tuples a scan of `spec` with candidates should give for block
    `b`: the rows the full scan keeps whose column `key.size` holds a
    candidate. -/
def blockOutSip (spec : ScanSpec) (cands : Array UInt64) (prb : ByteArray) (b : BlockMeta) : List (List Nat) :=
  ((blockRows prb b).filter fun r => keep spec r && candOf spec cands r).map (proj spec)

theorem blockOutSip_eq (spec : ScanSpec) (cands : Array UInt64) (prb : ByteArray) (b : BlockMeta) (cols : Cols)
    (h : decodeBlockAt prb b b.offset = .ok cols) :
    blockOutSip spec cands prb b = ((List.range b.rows).filter fun i => keep spec (cols.row i) &&
      candOf spec cands (cols.row i)).map fun i => proj spec (cols.row i) := by
  unfold blockOutSip blockRows
  rw [h]
  simp only [List.filter_map, List.map_map]
  rfl

/-- A block with no row the full scan keeps has none with a candidate
    either. -/
theorem blockOutSip_nil (spec : ScanSpec) (cands : Array UInt64) (prb : ByteArray) (b : BlockMeta)
    (hnil : blockOut spec prb b = []) : blockOutSip spec cands prb b = [] := by
  unfold blockOut at hnil
  unfold blockOutSip
  rw [List.map_eq_nil_iff] at hnil ⊢
  rw [List.filter_eq_nil_iff] at hnil ⊢
  intro r hr hk
  simp only [Bool.and_eq_true] at hk
  exact hnil r hr hk.1

/-- One block of a scan with candidates, with no overlay, over an in-memory
    store: the scan goes on, with the block's tuples appended. -/
theorem scanBlockSipM_step (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) (hk : spec.key.size < 4)
    (cands : Array UInt64) (hs : Sip.Sorted cands)
    (prb : ByteArray) (ms : List BlockMeta)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hfits : ∀ b ∈ ms, b.rows ≤ two64)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols)
    (sortVar : Option String) (ox : OvCtx) (hon : ox.on = false)
    (k : Nat) (hk' : k < ms.length) (s : ScanState (List (List Nat))) :
    ∃ s1, scanBlockSipM st spec cands (collectWith colTuples) ms.toArray sortVar ox k s = pure (.yield s1) ∧
      s1.acc = s.acc ++ blockOutSip spec cands prb ms[k] ∧ s1.stopped = s.stopped := by
  obtain ⟨cols, h⟩ := hblocks ms[k] (List.getElem_mem hk')
  have hrows := hfits ms[k] (List.getElem_mem hk')
  unfold scanBlockSipM
  rw [toArray_getElem! ms k hk']
  by_cases hsel : selects ms[k] spec.key = true
  · simp only [hsel, Bool.not_true, Bool.false_eq_true, if_false, hon]
    by_cases hskip : (blockPlan spec ms[k]).skip = true
    · simp only [hskip, if_true]
      exact ⟨s, rfl, by rw [blockOutSip_nil spec cands prb ms[k] (blockOut_skipped spec prb ms[k] cols h hskip),
        List.append_nil], rfl⟩
    · have hskip' : (blockPlan spec ms[k]).skip = false := by simpa using hskip
      simp only [hskip', Bool.false_eq_true, if_false]
      by_cases hmh : Sip.mayHold cands (sipRange ms[k] spec.key spec.key.size).1
          (sipRange ms[k] spec.key spec.key.size).2
          (Sip.lbHint cands (sipRange ms[k] spec.key spec.key.size).1) = true
      · simp only [hmh, Bool.not_true, Bool.false_eq_true, if_false]
        obtain ⟨bytes, starts, nbytes, hrf, hsl⟩ := readFrames_slice st prb spec.perm hprb ms[k] cols h hrows
          ((needOf spec (blockPlan spec ms[k]) (constOutOf spec ms[k] (blockPlan spec ms[k]))).set! spec.key.size true)
        obtain ⟨ch, t, g, hch, ht, -⟩ := sipChunk_tuples spec hspec hk cands hs sortVar prb ms[k] cols h hskip'
          bytes starts hsl (Sip.lbHint cands (sipRange ms[k] spec.key spec.key.size).1)
        rw [hrf]
        simp only [pure_bind, hch, ofExceptM, collectWith, stepOf, if_true]
        refine ⟨_, rfl, ?_, rfl⟩
        simp only
        rw [ht, blockOutSip_eq spec cands prb ms[k] cols h]
      · have hmh' : Sip.mayHold cands (sipRange ms[k] spec.key spec.key.size).1
            (sipRange ms[k] spec.key spec.key.size).2
            (Sip.lbHint cands (sipRange ms[k] spec.key spec.key.size).1) = false := by simpa using hmh
        simp only [hmh', Bool.not_false, if_true]
        refine ⟨_, rfl, ?_, rfl⟩
        simp only
        rw [blockOutSip_eq spec cands prb ms[k] cols h, List.map_eq_nil_iff.mpr, List.append_nil]
        rw [List.filter_eq_nil_iff]
        intro i hi hki
        simp only [Bool.and_eq_true] at hki
        have := sipSkip_none spec hk cands hs prb ms[k] cols h _ hmh' i (List.mem_range.mp hi) hki.1
        rw [this] at hki
        exact Bool.false_ne_true hki.2
  · have hsel' : selects ms[k] spec.key = false := by simpa using hsel
    simp only [hsel', Bool.not_false, if_true]
    exact ⟨s, rfl, by rw [blockOutSip_nil spec cands prb ms[k] (blockOut_unselected spec prb ms[k] cols h hsel'),
      List.append_nil], rfl⟩

theorem forIn_blocks_sip (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) (hk : spec.key.size < 4)
    (cands : Array UInt64) (hs : Sip.Sorted cands)
    (prb : ByteArray) (ms : List BlockMeta)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hfits : ∀ b ∈ ms, b.rows ≤ two64)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols)
    (sortVar : Option String) (ox : OvCtx) (hon : ox.on = false) :
    ∀ (L : List Nat), (∀ k ∈ L, k < ms.length) → ∀ (s : ScanState (List (List Nat))),
      ∃ s', forIn L s (scanBlockSipM st spec cands (collectWith colTuples) ms.toArray sortVar ox) = pure s' ∧
        s'.acc = s.acc ++ L.flatMap (fun k => blockOutSip spec cands prb ms[k]!) ∧ s'.stopped = s.stopped := by
  intro L
  induction L with
  | nil => intro _ s; exact ⟨s, rfl, by simp, rfl⟩
  | cons k ks ih =>
    intro hL s
    have hk' := hL k List.mem_cons_self
    obtain ⟨s1, h1, a1, t1⟩ :=
      scanBlockSipM_step st spec hspec hk cands hs prb ms hprb hfits hblocks sortVar ox hon k hk' s
    obtain ⟨s', h2, a2, t2⟩ := ih (fun j hj => hL j (List.mem_cons_of_mem _ hj)) s1
    refine ⟨s', ?_, ?_, by rw [t2, t1]⟩
    · rw [List.forIn_cons, h1, pure_bind]
      exact h2
    · rw [a2, a1, List.flatMap_cons, List.append_assoc, getElem!_pos ms k hk']

/-- The loop of `scanFoldSipM` over the entries `metasFor metas key` is the
    loop over the blocks `blocksFor metas key` (issue 805). -/
theorem forIn_metasFor_sip {m : Type → Type} [Monad m] [LawfulMonad m] {σ : Type} (st : Store m)
    (spec : ScanSpec) (cands : Array UInt64) (f : σ → Chunk → ExceptT String m (σ × Bool))
    (sortVar : Option String) (ox : OvCtx) (metas : Array BlockMeta) (key : Array UInt64) (s : ScanState σ) :
    forIn (List.range (metasFor metas key).size) s (scanBlockSipM st spec cands f (metasFor metas key) sortVar ox) =
      forIn (blocksFor metas key).toList s (scanBlockSipM st spec cands f metas sortVar ox) :=
  forIn_metasFor_of (fun a i => scanBlockSipM st spec cands f a sortVar ox i)
    (fun a a' i i' h => by funext s; unfold scanBlockSipM; rw [h]) metas key s

/-! ## The scan with candidates (lemma L4i) -/

/-- **L4i.** A scan with candidates (in non-decreasing order) of an admitted
    permutation, over a store that reads its PRM1 entries and PRB1 bytes from
    memory, with no delta overlay, gives the output tuples of exactly the
    rows of the permutation that the full scan keeps (`keep`: the key prefix,
    the checks, the named-graph test, the repeated-variable tests) and whose
    column `key.size` holds a candidate, in row order. -/
theorem scanFoldSipM_tuples (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) (hk : spec.key.size < 4)
    (cands : Array UInt64) (hs : Sip.Sorted cands)
    (prb : ByteArray) (ms : List BlockMeta)
    (hrange : st.blocksForRange spec.perm spec.key = pure (metasFor ms.toArray spec.key))
    (hcount : st.blockCount spec.perm = pure ms.length)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hovl : (st.ovl spec.perm).isEmpty = true)
    (hadm : prmAdmitted spec.perm ms = true)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols) :
    ∃ stats, scanFoldSipM st spec cands [] (collectWith colTuples) =
      pure (((ms.flatMap (blockRows prb)).filter fun r => keep spec r && candOf spec cands r).map (proj spec),
        stats) := by
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
  unfold scanFoldSipM
  rw [hrange, pure_bind, hcount, pure_bind]
  obtain ⟨s', hfor, hacc, hstop⟩ := forIn_blocks_sip st spec hspec hk cands hs prb ms hprb hfits hblocks
    (match spec.outCols[0]? with
      | some c => if c == spec.key.size then spec.outVars[0]? else none
      | none => none) _ hon
    (blocksFor ms.toArray spec.key).toList hLk
    { acc := [], stats := { blocksTotal := ms.length }, insPos := 0, stopped := false }
  refine ⟨s'.stats, ?_⟩
  simp only []
  rw [forIn_metasFor_sip]
  erw [hfor]
  rw [pure_bind]
  simp only [hon, Bool.false_and, Bool.false_eq_true, if_false]
  congr 2
  rw [hacc, List.nil_append]
  rw [List.filter_flatMap, List.map_flatMap]
  show _ = ms.flatMap (blockOutSip spec cands prb)
  rw [flatMap_eq_range ms (blockOutSip spec cands prb)]
  have hE : ∀ k, k < ms.length → k ∉ (blocksFor ms.toArray spec.key).toList →
      blockOutSip spec cands prb ms[k]! = [] := by
    intro k hk2 hnot
    obtain ⟨cols, h⟩ := hblocks ms[k] (List.getElem_mem hk2)
    apply blockOutSip_nil
    rw [getElem!_pos ms k hk2, blockOut_eq spec prb ms[k] cols h, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro i hi hkeep
    have hi' := List.mem_range.mp hi
    obtain ⟨h1, h2⟩ := row_between prb ms[k] cols h i hi'
    have := ScanTheorems.blocksFor_complete spec.perm ms hadm spec.key k hk2 _ h1 h2 (keep_prefix spec _ hkeep)
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
    intro k hk2
    exact hE k (List.mem_range.mp hk2) (by simp)
  · rw [hL] at hE ⊢
    have hs' : ms.toArray.size = ms.length := List.size_toArray
    rw [flatMap_range_interval ms.length _ c (by omega) (fun k => blockOutSip spec cands prb ms[k]!)
      (fun k hk2 hout => hE k hk2 (fun hm => by have := List.mem_range'_1.mp hm; omega))]

/-- **The reduced scan is a filter of the full scan.** When the column
    `key.size` is the first output column (the scan's sort variable, which
    the planner requires before it passes candidates), the scan with
    candidates returns the tuples of the full scan (`scanFoldM` with
    `fill = true`, lemma L4e) whose first value is a candidate. -/
theorem scanFoldSipM_filter (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) (hk : spec.key.size < 4)
    (hout : spec.outCols[0]? = some spec.key.size)
    (cands : Array UInt64) (hs : Sip.Sorted cands)
    (prb : ByteArray) (ms : List BlockMeta)
    (hrange : st.blocksForRange spec.perm spec.key = pure (metasFor ms.toArray spec.key))
    (hcount : st.blockCount spec.perm = pure ms.length)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hovl : (st.ovl spec.perm).isEmpty = true)
    (hadm : prmAdmitted spec.perm ms = true)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols) :
    ∃ T s1 s2, scanFoldM st spec true [] (collectWith colTuples) = pure (T, s1) ∧
      scanFoldSipM st spec cands [] (collectWith colTuples) =
        pure (T.filter (fun t => cands.contains (t.headD 0).toUInt64), s2) := by
  obtain ⟨s1, h1⟩ := scanFoldM_columns st spec hspec prb ms hrange hcount hprb hovl hadm hblocks
  obtain ⟨s2, h2⟩ := scanFoldSipM_tuples st spec hspec hk cands hs prb ms hrange hcount hprb hovl hadm hblocks
  refine ⟨_, s1, s2, h1, ?_⟩
  rw [h2]
  have hsz : 0 < spec.outCols.size := by
    rcases Nat.eq_zero_or_pos spec.outCols.size with e | e
    · simp [Array.getElem?_eq_none (by omega : spec.outCols.size ≤ 0)] at hout
    · exact e
  have h0 : spec.outCols[0]! = spec.key.size := by
    rw [getElem!_pos spec.outCols 0 hsz]
    rw [Array.getElem?_eq_getElem hsz] at hout
    simpa using hout
  have hhead : ∀ r, (proj spec r).headD 0 = rowCol r spec.key.size := by
    intro r
    unfold proj
    rw [List.range_eq_range', show spec.outCols.size = (spec.outCols.size - 1) + 1 by omega, List.range'_succ]
    simp [h0]
  congr 2
  rw [List.filter_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro r _
  simp only [Function.comp, hhead, candOf]
  rw [Bool.and_comm]

#print axioms sipRange_bounds
#print axioms sipSkip_none
#print axioms sipChunk_tuples
#print axioms scanBlockSipM_step
#print axioms scanFoldSipM_tuples
#print axioms scanFoldSipM_filter

/-! ## The candidates the planner passes (`sipCands`) -/

theorem allMemGo_spec (t : L4Factoidal.Qlvr.Table) (c : Nat) (cands : Array UInt64) :
    ∀ f i, t.rows - i ≤ f → allMemGo t c cands f i = true →
      ∀ k, i ≤ k → k < t.rows → sipMem cands (t.at c k) = true := by
  intro f
  induction f with
  | zero => intro i hf _ k hik hk; omega
  | succ f ih =>
    intro i hf h k hik hk
    simp only [allMemGo] at h
    rw [if_pos (by omega)] at h
    split at h
    · rename_i hm
      rcases Nat.eq_or_lt_of_le hik with e | l
      · subst e; exact hm
      · exact ih (i + 1) (by omega) h k (by omega) hk
    · cases h

/-- **What the planner's candidates satisfy.** When `sipCands` gives
    candidates for the variable `v` of a table, they are in non-decreasing
    order and every value of the table's column `v` is a candidate: the two
    hypotheses that `scanFoldSipM_filter` and the semi-join theorems
    (`SemiJoinTheorems`) need. Both come from the run-time checks of
    `sipCheck`, not from the sort. -/
theorem sipCands_sound (t : L4Factoidal.Qlvr.Table) (v : String) (cands : Array UInt64)
    (h : sipCands t v = some cands) :
    Sip.Sorted cands ∧ ∃ c, t.idx v = some c ∧ ∀ i, i < t.rows → cands.contains (t.at c i) = true := by
  unfold sipCands at h
  cases hc : t.idx v with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    simp only at h
    unfold sipCheck at h
    split at h
    · rename_i hok
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hok
      have hs := Sip.sorted_spec _ hok.1
      refine ⟨hs, c, rfl, fun i hi => ?_⟩
      have := allMemGo_spec t c _ t.rows 0 (by omega) hok.2 i (Nat.zero_le _) hi
      unfold sipMem at this
      rw [Sip.probe_mem _ hs] at this
      exact this
    · cases h

#print axioms sipCands_sound

end L4Factoidal.Storage.Sbm11.SipScanTheorems
