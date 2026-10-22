/-
L4Factoidal.Storage.Sbm11.WindowTheorems — the FILTER window of a scan
(https://github.com/danbri/factoidal/issues/929): the blocks that
`IdQuery.windowSkip` rules out hold no row that passes the STRSTARTS id
test, so a scan that does not read them gives the same rows after the
FILTER.

* `strRangeFast?_of_span`: every id between two ids for which `spanRejects`
  holds is decided `false` by `strRangeFast?` (the test that
  `IdQuery.applyFilters` applies to a `strRange` conjunct; `some false`
  removes the row).
* `windowSkip_row`: every row with the key prefix of an admitted block that
  `windowSkip` rules out has its column `key.size` rejected by
  `windowRejects`.
* `scanFoldM_window`: over a store in memory (`m = Id`) of an admitted
  permutation with no overlay, the scan over the window store
  (`IdQuery.windowStore`, the store `windowStoreM` gives the streamed path)
  and the scan over the store itself return tuple lists that are equal
  after the removal of the tuples whose first value `windowRejects`
  rejects. With the column `key.size` as the first output column (the sort
  variable, which `windowSkip` requires), the first value of a tuple is the
  id that the `strRange` conjunct tests, so the rows that the FILTER keeps
  are the same. The full scan's tuples are `ScanFoldTheorems.scanFoldM_columns`.

The step from "the tuples are equal after `windowRejects`" to "the emitted
rows are equal" is `applyFilters`, which decides each row by its own ids and
removes a row whose `strRange` conjunct gets `strRangeFast? = some false`;
that loop is not modelled here, the W3C census and the gate fixture
(`tests/sbm11/run.sh` parts (d) and (l), `ids-strstarts-window`) check it.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.SipScanTheorems

namespace L4Factoidal.Storage.Sbm11.WindowTheorems

open L4Factoidal (two64)
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.ScanFoldTheorems
open L4Factoidal.Storage.Sbm11.SipScanTheorems (sipRange_bounds)

/-! ## The id test -/

theorem tagOf_eq (x : UInt64) : tagOf x = x.toNat / 1152921504606846976 := by
  unfold tagOf
  rw [UInt64.toNat_shiftRight]
  simp [Nat.shiftRight_eq_div_pow]

theorem rank_eq (x : UInt64) : (x &&& 0x0FFFFFFFFFFFFFFF).toNat = x.toNat % 1152921504606846976 := by
  rw [UInt64.toNat_and]
  have : (0x0FFFFFFFFFFFFFFF : UInt64).toNat = 2 ^ 60 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

/-- Every id between `vlo` and `vhi` is decided `false` when `spanRejects`
    holds of them. -/
theorem strRangeFast?_of_span (ranges : Array (Nat × Nat)) (classLo classHi : Nat) (vlo vhi x : UInt64)
    (h : spanRejects ranges classLo classHi vlo vhi = true) (h1 : vlo ≤ x) (h2 : x ≤ vhi) :
    strRangeFast? ranges classLo classHi x = some false := by
  unfold spanRejects at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.all_eq_true] at h
  obtain ⟨⟨⟨⟨ht1, ht2⟩, hlo⟩, hhi⟩, hall⟩ := h
  rw [UInt64.le_iff_toNat_le] at h1 h2
  rw [tagOf_eq] at ht1 ht2
  rw [rank_eq] at hlo hhi
  have htx : x.toNat / 1152921504606846976 = 3 := by omega
  have hr1 : vlo.toNat % 1152921504606846976 ≤ x.toNat % 1152921504606846976 := by omega
  have hr2 : x.toNat % 1152921504606846976 ≤ vhi.toNat % 1152921504606846976 := by omega
  unfold strRangeFast?
  simp only [tagOf_eq, rank_eq, htx]
  rw [if_pos (by simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega)]
  congr 1
  rw [Bool.eq_false_iff]
  intro hany
  rw [Array.any_eq_true] at hany
  obtain ⟨j, hj, hp⟩ := hany
  have hq := hall j hj
  rw [rank_eq, rank_eq] at hq
  obtain ⟨lo, hi⟩ := ranges[j]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hp hq
  omega

/-! ## One block -/

/-- A row with the key prefix of an admitted block that `windowSkip` rules
    out has its column `key.size` rejected. -/
theorem windowSkip_row (fs : Array FKind) (spec : ScanSpec) (v : String) (hv : sortVarOf spec = some v)
    (hk : spec.key.size < 4) (prb : ByteArray) (b : BlockMeta) (cols : Cols)
    (h : decodeBlockAt prb b b.offset = .ok cols) (hs : windowSkip fs spec b = true)
    (i : Nat) (hi : i < b.rows) (hp : prefixCmp (cols.row i) spec.key = .eq) :
    windowRejects fs v (rowCol (cols.row i) spec.key.size).toUInt64 = true := by
  obtain ⟨b1, b2⟩ := sipRange_bounds prb b cols h spec.key hk i hi hp
  unfold windowSkip at hs
  rw [hv] at hs
  simp only at hs
  unfold windowRejects
  rw [Array.any_eq_true] at hs ⊢
  obtain ⟨j, hj, hf⟩ := hs
  refine ⟨j, hj, ?_⟩
  cases hfj : fs[j] with
  | strRange w ranges lo hi e =>
    rw [hfj] at hf
    simp only [Bool.and_eq_true] at hf ⊢
    refine ⟨hf.1, ?_⟩
    rw [strRangeFast?_of_span ranges lo hi _ _ _ hf.2 b1 b2]
    rfl
  | _ => rw [hfj] at hf; simp at hf

/-! ## The scan -/

/-- Dropping lists whose elements all fail `P` does not change the filter by
    `P` of the concatenation. -/
theorem filter_flatMap_drop {α : Type} (B : Nat → List α) (P : α → Bool) (q : Nat → Bool) :
    ∀ (L : List Nat), (∀ k ∈ L, q k = false → ∀ t ∈ B k, P t = false) →
      ((L.filter q).flatMap B).filter P = (L.flatMap B).filter P := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons k ks ih =>
    intro hL
    have ih' := ih (fun j hj => hL j (List.mem_cons_of_mem _ hj))
    by_cases hq : q k = true
    · simp only [List.filter_cons, hq, if_true, List.flatMap_cons, List.filter_append, ih']
    · have hq' : q k = false := by simpa using hq
      simp only [List.filter_cons, hq', Bool.false_eq_true, if_false, List.flatMap_cons,
        List.filter_append, ih']
      have : (B k).filter P = [] := by
        rw [List.filter_eq_nil_iff]
        intro t ht hpt
        rw [hL k List.mem_cons_self hq' t ht] at hpt
        cases hpt
      rw [this, List.nil_append]

/-- The head of a projected row is its column `key.size` when that is the
    first output column. -/
theorem proj_head (spec : ScanSpec) (hout : spec.outCols[0]? = some spec.key.size) (r : Row) :
    (proj spec r).headD 0 = rowCol r spec.key.size := by
  have hsz : 0 < spec.outCols.size := by
    rcases Nat.eq_zero_or_pos spec.outCols.size with e | e
    · simp [Array.getElem?_eq_none (by omega : spec.outCols.size ≤ 0)] at hout
    · exact e
  have h0 : spec.outCols[0]! = spec.key.size := by
    rw [getElem!_pos spec.outCols 0 hsz]
    rw [Array.getElem?_eq_getElem hsz] at hout
    simpa using hout
  unfold proj
  rw [List.range_eq_range', show spec.outCols.size = (spec.outCols.size - 1) + 1 by omega, List.range'_succ]
  simp [h0]

/-- The tuples a scan keeps after the window conjuncts. -/
def windowPass (fs : Array FKind) (v : String) (t : List Nat) : Bool :=
  !windowRejects fs v (t.headD 0).toUInt64

/-- The block positions of `blocksFor` are positions of `ms`. -/
theorem blocksFor_lt (ms : List BlockMeta) (key : Array UInt64) :
    ∀ k ∈ (blocksFor ms.toArray key).toList, k < ms.length := by
  intro k hk
  obtain ⟨c, hc, hb⟩ := blocksForGo_range ms.toArray key ms.toArray.size
    (firstBlockGo ms.toArray key (Nat.log2 ms.toArray.size + 2) 0 ms.toArray.size) #[]
  unfold blocksFor at hk
  rw [hc] at hk
  simp only [List.nil_append] at hk
  have := List.mem_range'_1.mp hk
  have hs : ms.toArray.size = ms.length := List.size_toArray
  rcases hb with hb | hb
  · omega
  · omega

theorem fits_of_admitted (perm : Nat) (ms : List BlockMeta) (hadm : prmAdmitted perm ms = true) :
    ∀ b ∈ ms, b.rows ≤ two64 := by
  have hch : chainGo prbHeaderBytes ms = true := by
    simp only [prmAdmitted, Bool.and_eq_true] at hadm
    exact hadm.1.1.2
  intro b hb
  have := chainGo_fits ms _ hch b hb
  simp only [metaFits, Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, h32⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := this
  exact Nat.le_of_lt (Nat.lt_of_lt_of_le h32 (by decide))

theorem denOk_colTuples (spec : ScanSpec) : DenOk spec true colTuples := by
  intro sortVar b bytes starts ch hch
  obtain ⟨cs, n, rfl⟩ := blockChunk_ok b bytes starts ch sortVar hch
  exact chunkOfCols_colTuples spec sortVar _ _ (by simp [constOutOf]) cs n

/-- The scan of a store over the block positions `idx` of `ms` (the PRM1
    entries it answers are `ms` at those positions): the tuples of those
    blocks. -/
theorem scanFoldM_idx (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec)
    (prb : ByteArray) (ms : List BlockMeta) (idx : List Nat) (hidx : ∀ k ∈ idx, k < ms.length)
    (hrange : st.blocksForRange spec.perm spec.key = pure (idx.map (ms.toArray[·]!)).toArray)
    (n : Nat) (hcount : st.blockCount spec.perm = pure n)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hovl : (st.ovl spec.perm).isEmpty = true)
    (hfits : ∀ b ∈ ms, b.rows ≤ two64)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols) :
    ∃ stats, scanFoldM st spec true [] (collectWith colTuples) =
      pure (idx.flatMap (fun k => blockOut spec prb ms[k]!), stats) := by
  have hon : (ovCtx (st.ovl spec.perm) spec.key).on = false := by
    simp [ovCtx, hovl]
  unfold scanFoldM
  rw [hrange, pure_bind]
  rw [hcount, pure_bind]
  have hsz : (idx.map (ms.toArray[·]!)).toArray.size = idx.length := by simp
  obtain ⟨s', hfor, hacc, hstop⟩ := forIn_blocks st spec hspec true colTuples (denOk_colTuples spec) prb ms
    hprb hfits hblocks
    (match spec.outCols[0]? with
      | some c => if c == spec.key.size then spec.outVars[0]? else none
      | none => none) _ hon idx hidx
    { acc := [], stats := { blocksTotal := n }, insPos := 0, stopped := false }
  refine ⟨s'.stats, ?_⟩
  simp only []
  rw [hsz]
  rw [forIn_range_idx (scanBlockM st spec true (collectWith colTuples) ms.toArray _ (ovCtx (st.ovl spec.perm) spec.key))
    idx _ (fun j hj => scanBlockM_congr _ _ _ _ _ _ _ _ _ _ (by
      rw [getElem!_pos _ j (by simp; exact hj)]
      simp [List.getElem_map, List.getElem?_eq_getElem hj]))]
  erw [hfor]
  rw [pure_bind]
  simp only [hon, Bool.false_and, Bool.false_eq_true, if_false]
  rw [hacc, List.nil_append]

/-- **The window.** Over a store in memory of an admitted permutation with
    no overlay, with the column `key.size` as the first output column, the
    scan over the window store and the scan over the store return tuple
    lists that are equal after the removal of the tuples whose first value
    `windowRejects` rejects. -/
theorem scanFoldM_window (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) (hk : spec.key.size < 4)
    (hout : spec.outCols[0]? = some spec.key.size) (v : String) (hv : sortVarOf spec = some v)
    (fs : Array FKind) (prb : ByteArray) (ms : List BlockMeta)
    (hrange : st.blocksForRange spec.perm spec.key = pure (metasFor ms.toArray spec.key))
    (hcount : st.blockCount spec.perm = pure ms.length)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hovl : (st.ovl spec.perm).isEmpty = true)
    (hadm : prmAdmitted spec.perm ms = true)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols) :
    ∃ T T' s1 s2, scanFoldM st spec true [] (collectWith colTuples) = pure (T, s1) ∧
      scanFoldM (windowStore st spec fs (metasFor ms.toArray spec.key)) spec true [] (collectWith colTuples) =
        pure (T', s2) ∧
      T'.filter (windowPass fs v) = T.filter (windowPass fs v) := by
  have hfits := fits_of_admitted spec.perm ms hadm
  let L := (blocksFor ms.toArray spec.key).toList
  let q : Nat → Bool := fun k => !windowSkip fs spec ms.toArray[k]!
  have hL : ∀ k ∈ L, k < ms.length := blocksFor_lt ms spec.key
  have hLq : ∀ k ∈ L.filter q, k < ms.length := fun k hk => hL k (List.mem_filter.mp hk).1
  have hmeta : metasFor ms.toArray spec.key = (L.map (ms.toArray[·]!)).toArray := by
    apply Array.toList_inj.mp
    simp [metasFor, L]
  have hr1 : st.blocksForRange spec.perm spec.key = pure (L.map (ms.toArray[·]!)).toArray := by
    rw [hrange, hmeta]
  have hr2 : (windowStore st spec fs (metasFor ms.toArray spec.key)).blocksForRange spec.perm spec.key =
      pure ((L.filter q).map (ms.toArray[·]!)).toArray := by
    simp only [windowStore, beq_self_eq_true, Bool.and_self, if_true]
    congr 1
    rw [hmeta]
    apply Array.toList_inj.mp
    simp only [Array.toList_filter, List.filter_map]
    rfl
  obtain ⟨s1, h1⟩ := scanFoldM_idx st spec hspec prb ms L hL hr1 ms.length hcount hprb hovl hfits hblocks
  obtain ⟨s2, h2⟩ := scanFoldM_idx (windowStore st spec fs (metasFor ms.toArray spec.key)) spec hspec prb ms
    (L.filter q) hLq hr2 ms.length hcount hprb hovl hfits hblocks
  refine ⟨_, _, s1, s2, h1, h2, ?_⟩
  apply filter_flatMap_drop
  intro k hkL hqk t ht
  have hkl := hL k hkL
  have hskip : windowSkip fs spec ms[k] = true := by
    have : q k = false := hqk
    simp only [q, Bool.not_eq_false', getElem!_pos ms.toArray k (by simpa using hkl)] at this
    simpa using this
  obtain ⟨cols, h⟩ := hblocks ms[k] (List.getElem_mem hkl)
  rw [getElem!_pos ms k hkl, blockOut_eq spec prb ms[k] cols h] at ht
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
  obtain ⟨hi', hkeep⟩ := List.mem_filter.mp hi
  have hrow := windowSkip_row fs spec v hv hk prb ms[k] cols h hskip i (List.mem_range.mp hi')
    (keep_prefix spec _ hkeep)
  unfold windowPass
  rw [proj_head spec hout, hrow]
  rfl

#print axioms strRangeFast?_of_span
#print axioms windowSkip_row
#print axioms scanFoldM_idx
#print axioms scanFoldM_window

end L4Factoidal.Storage.Sbm11.WindowTheorems
