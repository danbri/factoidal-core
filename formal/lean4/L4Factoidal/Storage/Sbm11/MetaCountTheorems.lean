/-
L4Factoidal.Storage.Sbm11.MetaCountTheorems — the count of a scan from its
PRM1 entries (https://github.com/danbri/factoidal/issues/932).

`IdQuery.metaCountM` gives the number of rows a scan keeps: for a block that
its PRM1 entry decides (`metaDecided`), `metaRows`; for every other block,
the rows of the chunk that `scanBlockM` makes.

* `metaRows_eq`: on an admitted block that its entry decides, `metaRows` is
  the number of output tuples of the block (`ScanFoldTheorems.blockOut`).
* `scanBlockM_count_step`, `forIn_count`: the scan of a list of blocks with
  the count accumulator `countAdd` adds the number of output tuples of each.
* `metaSplitGo_sum`: the decided sum plus the tuples of the other blocks is
  the number of output tuples of all blocks.
* `metaCountM_eq_scan`: over a store in memory (`m = Id`) of an admitted
  permutation with no overlay, `metaCountM` gives the length of the tuple list
  that `scanFoldM` gives (`ScanFoldTheorems.scanFoldM_tuples`), the rows of the
  permutation that carry the key prefix and pass the checks, the named-graph
  test and the repeated-variable tests.

Not covered, as in `ScanFoldTheorems`: the delta overlay (the caller uses
`metaCountM` only when the overlay is empty) and a store in `IO`.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.ScanFoldTheorems

namespace L4Factoidal.Storage.Sbm11.MetaCountTheorems

open L4Factoidal (two64)
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.ScanFoldTheorems

/-! ## One block -/

theorem tuples_length (ch : Chunk) : (tuples ch).length = ch.table.rows := by
  simp [tuples]

/-- On an admitted block, the number that `metaStep` gives is the number of
    output tuples of the block. -/
theorem metaStep_sound (spec : ScanSpec) (prb : ByteArray) (b : BlockMeta) (cols : Cols)
    (h : decodeBlockAt prb b b.offset = .ok cols) (r : Nat) (hm : metaStep spec b = some r) :
    r = (blockOut spec prb b).length := by
  unfold metaStep at hm
  by_cases h1 : (!selects b spec.key || spec.checks.any (checkFails b)) = true
  · rw [if_pos h1] at hm
    cases hm
    by_cases hsel : selects b spec.key = true
    · simp only [hsel, Bool.not_true, Bool.false_or, Array.any_eq_true] at h1
      obtain ⟨j, hj, hf⟩ := h1
      rw [blockOut_eq spec prb b cols h]
      symm
      rw [List.length_eq_zero_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff]
      intro i hi hk
      have hi' := List.mem_range.mp hi
      unfold checkFails at hf
      cases hc : colConst? b spec.checks[j].1 with
      | none => rw [hc] at hf; cases hf
      | some y =>
        rw [hc] at hf
        have hy := colConst_sound prb b cols h _ y hc i hi'
        unfold keep at hk
        simp only [Bool.and_eq_true, List.all_eq_true] at hk
        have := hk.1.2.2 spec.checks[j] (Array.mem_toList_iff.mpr (Array.getElem_mem hj))
        simp only [chk, hy, beq_iff_eq] at this
        simp [this] at hf
    · have hsel' : selects b spec.key = false := by simpa using hsel
      rw [blockOut_unselected spec prb b cols h hsel']
      rfl
  · rw [if_neg h1] at hm
    by_cases h2 : (fullFor b spec.key && spec.checks.all (fun ck => (colConst? b ck.1).isSome) &&
        spec.eqs.isEmpty && !spec.named) = true
    · rw [if_pos h2] at hm
      cases hm
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h2
      obtain ⟨⟨⟨hfull, hall⟩, heq⟩, hnamed⟩ := h2
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_true, Array.any_eq_true,
        not_exists] at h1
      obtain ⟨-, hnf⟩ := h1
      rw [blockOut_eq spec prb b cols h, List.length_map]
      rw [List.filter_eq_self.mpr, List.length_range]
      intro i hi
      have hi' := List.mem_range.mp hi
      obtain ⟨hb1, hb2⟩ := row_between prb b cols h i hi'
      unfold keep
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
      refine ⟨⟨ScanTheorems.fullFor_row b spec.key hfull _ hb1 hb2, ?_, ?_⟩, ?_⟩
      · simp [hnamed]
      · intro ck hck
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hck
        have hj' : j < spec.checks.size := by simpa using hj
        have hsome := (Array.all_eq_true.mp hall) j hj'
        have hnot := hnf j hj'
        simp only [Array.getElem_toList]
        unfold checkFails at hnot
        cases hc : colConst? b spec.checks[j].1 with
        | none => rw [hc] at hsome; cases hsome
        | some y =>
          rw [hc] at hnot
          have hy := colConst_sound prb b cols h _ y hc i hi'
          have hyx : y = spec.checks[j].snd.toNat := by simpa [bne] using hnot
          simp [chk, hy, hyx]
      · intro e he
        have : spec.eqs.toList = [] := by simpa using heq
        rw [this] at he
        cases he
    · rw [if_neg h2] at hm
      cases hm

/-! ## The scan of the other blocks with a count -/

theorem scanBlockM_count_step (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec)
    (prb : ByteArray) (ms : List BlockMeta)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hfits : ∀ b ∈ ms, b.rows ≤ two64)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols)
    (sortVar : Option String) (ox : OvCtx) (hon : ox.on = false)
    (k : Nat) (hk : k < ms.length) (s : ScanState Nat) :
    ∃ s1, scanBlockM st spec false countAdd ms.toArray sortVar ox k s = pure (.yield s1) ∧
      s1.acc = s.acc + (blockOut spec prb ms[k]).length := by
  obtain ⟨cols, h⟩ := hblocks ms[k] (List.getElem_mem hk)
  have hrows := hfits ms[k] (List.getElem_mem hk)
  unfold scanBlockM
  rw [toArray_getElem! ms k hk]
  by_cases hsel : selects ms[k] spec.key = true
  · simp only [hsel, Bool.not_true, Bool.false_eq_true, if_false, hon]
    by_cases hskip : (blockPlan spec ms[k]).skip = true
    · simp only [hskip, if_true]
      exact ⟨s, rfl, by rw [blockOut_skipped spec prb ms[k] cols h hskip]; rfl⟩
    · have hskip' : (blockPlan spec ms[k]).skip = false := by simpa using hskip
      simp only [hskip', Bool.false_eq_true, if_false]
      obtain ⟨bytes, starts, nbytes, hrf, hsl⟩ := readFrames_slice st prb spec.perm hprb ms[k] cols h hrows
        (needOf spec (blockPlan spec ms[k]) (constOutOf spec ms[k] (blockPlan spec ms[k])))
      obtain ⟨ch, hch, ht⟩ := blockChunk_tuples spec hspec false sortVar prb ms[k] cols h hrows hskip' bytes starts hsl
      rw [hrf]
      simp only [pure_bind, hch, ofExceptM, countAdd, stepOf, if_true]
      refine ⟨_, rfl, ?_⟩
      simp only
      rw [blockOut_eq spec prb ms[k] cols h, ← ht, tuples_length]
  · have hsel' : selects ms[k] spec.key = false := by simpa using hsel
    simp only [hsel', Bool.not_false, if_true]
    exact ⟨s, rfl, by rw [blockOut_unselected spec prb ms[k] cols h hsel']; rfl⟩

/-- The number of output tuples of block `k` of `ms`. -/
def tupleCount (spec : ScanSpec) (prb : ByteArray) (ms : List BlockMeta) (k : Nat) : Nat :=
  (blockOut spec prb ms[k]!).length

theorem forIn_count (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec)
    (prb : ByteArray) (ms : List BlockMeta)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hfits : ∀ b ∈ ms, b.rows ≤ two64)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols)
    (sortVar : Option String) (ox : OvCtx) (hon : ox.on = false) :
    ∀ (L : List Nat), (∀ k ∈ L, k < ms.length) → ∀ (s : ScanState Nat),
      ∃ s', forIn L s (scanBlockM st spec false countAdd ms.toArray sortVar ox) = pure s' ∧
        s'.acc = s.acc + (L.map (tupleCount spec prb ms)).sum := by
  intro L
  induction L with
  | nil => intro _ s; exact ⟨s, rfl, by simp⟩
  | cons k ks ih =>
    intro hL s
    have hk := hL k List.mem_cons_self
    obtain ⟨s1, h1, a1⟩ := scanBlockM_count_step st spec hspec prb ms hprb hfits hblocks sortVar ox hon k hk s
    obtain ⟨s', h2, a2⟩ := ih (fun j hj => hL j (List.mem_cons_of_mem _ hj)) s1
    refine ⟨s', ?_, ?_⟩
    · rw [List.forIn_cons, h1, pure_bind]
      exact h2
    · rw [a2, a1, List.map_cons, List.sum_cons, tupleCount, getElem!_pos ms k hk]
      omega

/-! ## The split of the entries -/

/-- `metaSplitGo` from position `i` with enough fuel: its sum plus the tuples
    of the blocks it leaves is the start plus the tuples of the blocks from
    `i`; every block it leaves is in `rest` or a block of `ms`. -/
theorem metaSplitGo_sum (spec : ScanSpec) (prb : ByteArray) (ms : List BlockMeta)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols) :
    ∀ f i n (rest : Array Nat), ms.length ≤ i + f →
      (∀ k ∈ (metaSplitGo spec ms.toArray f i n rest).2.toList, k ∈ rest.toList ∨ k < ms.length) ∧
      (metaSplitGo spec ms.toArray f i n rest).1 +
          ((metaSplitGo spec ms.toArray f i n rest).2.toList.map (tupleCount spec prb ms)).sum =
        n + (rest.toList.map (tupleCount spec prb ms)).sum +
          ((List.range' i (ms.length - i)).map (tupleCount spec prb ms)).sum := by
  intro f
  induction f with
  | zero =>
    intro i n rest hf
    have : ms.length - i = 0 := by omega
    exact ⟨fun k hk => Or.inl (by simpa [metaSplitGo] using hk), by simp [metaSplitGo, this]⟩
  | succ f ih =>
    intro i n rest hf
    have hsz : ms.toArray.size = ms.length := List.size_toArray
    by_cases hi : i < ms.length
    · have hr : List.range' i (ms.length - i) = i :: List.range' (i + 1) (ms.length - (i + 1)) := by
        rw [show ms.length - i = (ms.length - (i + 1)) + 1 by omega, List.range'_succ]
      have hb : ms.toArray[i]! = ms[i] := toArray_getElem! ms i hi
      have htc : tupleCount spec prb ms i = (blockOut spec prb ms[i]).length := by
        rw [tupleCount, getElem!_pos ms i hi]
      obtain ⟨cols, h⟩ := hblocks ms[i] (List.getElem_mem hi)
      cases hm : metaStep spec ms[i] with
      | some r =>
        have hs : metaSplitGo spec ms.toArray (f + 1) i n rest =
            metaSplitGo spec ms.toArray f (i + 1) (n + r) rest := by
          simp [metaSplitGo, hsz, hi, hm]
        obtain ⟨h1, h2⟩ := ih (i + 1) (n + r) rest (by omega)
        rw [hs]
        refine ⟨h1, ?_⟩
        rw [h2, hr, List.map_cons, List.sum_cons, htc, ← metaStep_sound spec prb ms[i] cols h r hm]
        omega
      | none =>
        have hs : metaSplitGo spec ms.toArray (f + 1) i n rest =
            metaSplitGo spec ms.toArray f (i + 1) n (rest.push i) := by
          simp [metaSplitGo, hsz, hi, hm]
        obtain ⟨h1, h2⟩ := ih (i + 1) n (rest.push i) (by omega)
        rw [hs]
        refine ⟨fun k hk => ?_, ?_⟩
        · rcases h1 k hk with hk | hk
          · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hk
            rcases hk with hk | hk
            · exact Or.inl hk
            · exact Or.inr (hk ▸ hi)
          · exact Or.inr hk
        · rw [h2, hr]
          simp only [Array.toList_push, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
            List.map_nil, List.sum_nil]
          omega
    · have hs : metaSplitGo spec ms.toArray (f + 1) i n rest = (n, rest) := by
        simp [metaSplitGo, hsz, hi]
      have : ms.length - i = 0 := by omega
      rw [hs]
      exact ⟨fun k hk => Or.inl hk, by simp [this]⟩

/-! ## The count -/

theorem mem_metasFor (ms : List BlockMeta) (key : Array UInt64) (b : BlockMeta)
    (hb : b ∈ (metasFor ms.toArray key).toList) : b ∈ ms := by
  unfold metasFor at hb
  simp only [Array.toList_map, List.mem_map] at hb
  obtain ⟨k, hk, rfl⟩ := hb
  obtain ⟨c, hc, hcb⟩ := blocksForGo_range ms.toArray key ms.toArray.size
    (firstBlockGo ms.toArray key (Nat.log2 ms.toArray.size + 2) 0 ms.toArray.size) #[]
  unfold blocksFor at hk
  rw [hc] at hk
  simp only [List.nil_append] at hk
  have := List.mem_range'_1.mp hk
  have hs : ms.toArray.size = ms.length := List.size_toArray
  have hk' : k < ms.length := by rcases hcb with hcb | hcb <;> omega
  rw [toArray_getElem! ms k hk']
  exact List.getElem_mem hk'

/-- **Issue 932.** Over a store in memory of an admitted permutation with no
    overlay (the hypotheses of `ScanFoldTheorems.scanFoldM_tuples`, which are
    the activation checks), the count that `metaCountM` gives from the PRM1
    entries and the scan of the other blocks is the number of tuples that the
    scan gives: the rows of the permutation that carry the key prefix and pass
    the checks, the named-graph test and the repeated-variable tests. -/
theorem metaCountM_eq_scan (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec)
    (prb : ByteArray) (ms : List BlockMeta)
    (hrange : st.blocksForRange spec.perm spec.key = pure (metasFor ms.toArray spec.key))
    (hcount : st.blockCount spec.perm = pure ms.length)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hovl : (st.ovl spec.perm).isEmpty = true)
    (hadm : prmAdmitted spec.perm ms = true)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols) :
    ∃ d stats, metaCountM st spec =
      pure ((((ms.flatMap (blockRows prb)).filter (keep spec)).map (proj spec)).length, d, stats) := by
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
  -- the selected entries, as a list of blocks of `ms`
  generalize hsel : metasFor ms.toArray spec.key = sel at hrange
  have hsl : sel.toList.toArray = sel := Array.toArray_toList
  have hmem : ∀ b ∈ sel.toList, b ∈ ms := fun b hb => mem_metasFor ms spec.key b (hsel ▸ hb)
  have hfits' : ∀ b ∈ sel.toList, b.rows ≤ two64 := fun b hb => hfits b (hmem b hb)
  have hblocks' : ∀ b ∈ sel.toList, ∃ cols, decodeBlockAt prb b b.offset = .ok cols :=
    fun b hb => hblocks b (hmem b hb)
  have hlen : sel.toList.length = sel.size := Array.length_toList
  -- the scan's tuple list over the selected entries
  obtain ⟨stats0, hscan⟩ := scanFoldM_tuples st spec hspec false prb ms (hsel ▸ hrange) hcount hprb hovl
    hadm hblocks
  obtain ⟨s0, hfor0, hacc0, -⟩ := forIn_blocks st spec hspec false tuples (fun _ _ _ _ _ _ => rfl) prb
    sel.toList hprb hfits' hblocks' (sortVarOf spec) (ovCtx (st.ovl spec.perm) spec.key) hon
    (List.range sel.size) (fun k hk => by rw [hlen]; exact List.mem_range.mp hk)
    { acc := [], stats := { blocksTotal := ms.length }, insPos := 0, stopped := false }
  rw [hsl] at hfor0
  have hL : ((ms.flatMap (blockRows prb)).filter (keep spec)).map (proj spec) =
      (List.range sel.size).flatMap (fun k => blockOut spec prb sel.toList[k]!) := by
    unfold scanFoldM at hscan
    rw [hrange, pure_bind, hcount, pure_bind] at hscan
    have hfor0' := hfor0
    unfold sortVarOf at hfor0'
    simp only [] at hscan
    erw [hfor0'] at hscan
    rw [pure_bind] at hscan
    simp only [hon, Bool.false_and, Bool.false_eq_true, if_false] at hscan
    have hx := congrArg (fun e : ExceptT String Id (List (List Nat) × ScanStats) =>
      match e.run with | .ok p => p.1 | .error _ => []) hscan
    simp only [pure, ExceptT.pure, ExceptT.run, ExceptT.mk] at hx
    rw [← hx, hacc0, List.nil_append]
  -- the split and the count
  obtain ⟨hrest, hsum⟩ := metaSplitGo_sum spec prb sel.toList hblocks' sel.toList.length 0 0 #[] (by omega)
  rw [hsl, hlen] at hrest hsum
  have hrest' : ∀ k ∈ (metaSplitGo spec sel sel.size 0 0 #[]).2.toList, k < sel.toList.length := by
    intro k hk
    rcases hrest k hk with hk | hk
    · simp at hk
    · rw [hlen]; exact hk
  obtain ⟨s1, hfor1, hacc1⟩ := forIn_count st spec hspec prb sel.toList hprb hfits' hblocks' (sortVarOf spec)
    (ovCtx (st.ovl spec.perm) spec.key) hon (metaSplitGo spec sel sel.size 0 0 #[]).2.toList hrest'
    { acc := (metaSplitGo spec sel sel.size 0 0 #[]).1, stats := { blocksTotal := ms.length },
      insPos := 0, stopped := false }
  rw [hsl] at hfor1
  refine ⟨sel.size - (metaSplitGo spec sel sel.size 0 0 #[]).2.size, s1.stats, ?_⟩
  unfold metaCountM
  rw [hrange, pure_bind, hcount, pure_bind]
  simp only []
  erw [hfor1]
  rw [pure_bind]
  rw [hacc1, hsum, hL, List.length_flatMap]
  simp only [List.map_nil, List.sum_nil, Nat.zero_add, Nat.sub_zero, List.range_eq_range']
  rfl

#print axioms metaStep_sound
#print axioms forIn_count
#print axioms metaSplitGo_sum
#print axioms metaCountM_eq_scan

end L4Factoidal.Storage.Sbm11.MetaCountTheorems
