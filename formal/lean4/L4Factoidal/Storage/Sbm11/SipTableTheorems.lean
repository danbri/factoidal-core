/-
L4Factoidal.Storage.Sbm11.SipTableTheorems — the table of a scan with
candidates (https://github.com/danbri/factoidal/issues/776 and
https://github.com/danbri/factoidal/issues/809; part of lemma L4l of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

`SipScanTheorems.scanFoldSipM_tuples` (L4i) is stated with a list
accumulator. `IdQuery.scanSipTableM` appends the chunks to a `Table`.

* `scanFoldSipM_R`: L4i for any accumulator that appends well-formed chunks
  (as `ScanTableTheorems.scanFoldM_R` for the full scan; the chunk's form
  from `SipScanTheorems.sipChunk_tuples`).
* `scanSipTableM_spec`: the table has the scan's variables, one column of
  `8 * rows` bytes per variable, the scan's sort variable, and the tuples of
  the rows the full scan keeps whose column `key.size` holds a candidate
  (`ScanTableTheorems.TableOf`).

The hypotheses are those of L4i: an in-memory store of an admitted
permutation with no overlay, the planner's scan shape, a key of at most
three columns, candidates in non-decreasing order.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.ScanTableTheorems
import L4Factoidal.Storage.Sbm11.SipScanTheorems

namespace L4Factoidal.Storage.Sbm11.SipTableTheorems

open L4Factoidal (two64)
open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.ScanFoldTheorems
open L4Factoidal.Storage.Sbm11.SipScanTheorems
open L4Factoidal.Storage.Sbm11.ScanTableTheorems (ChunkWF liftG chunkOfCols_wf TableOf tableOf_append ewc_size
  blocksFor_lt)

/-- One block of a scan with candidates, with no overlay, over an in-memory
    store, for an accumulator related to the list of tuples by `R`. -/
theorem scanBlockSipM_stepR (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) (hk : spec.key.size < 4)
    (cands : Array UInt64) (hs : Sip.Sorted cands) {σ : Type}
    (g : σ → Chunk → σ) (R : σ → List (List Nat) → Prop)
    (hR : ∀ a l ch, ChunkWF spec ch → R a l → R (g a ch) (l ++ colTuples ch))
    (prb : ByteArray) (ms : List BlockMeta)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hfits : ∀ b ∈ ms, b.rows ≤ two64)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols)
    (sortVar : Option String) (ox : OvCtx) (hon : ox.on = false)
    (k : Nat) (hk' : k < ms.length) (s : ScanState σ) (l : List (List Nat)) (hsl0 : R s.acc l) :
    ∃ s1, scanBlockSipM st spec cands (liftG g) ms.toArray sortVar ox k s = pure (.yield s1) ∧
      R s1.acc (l ++ blockOutSip spec cands prb ms[k]) ∧ s1.stopped = s.stopped := by
  obtain ⟨cols, h⟩ := hblocks ms[k] (List.getElem_mem hk')
  have hrows := hfits ms[k] (List.getElem_mem hk')
  unfold scanBlockSipM
  rw [toArray_getElem! ms k hk']
  by_cases hsel : selects ms[k] spec.key = true
  · simp only [hsel, Bool.not_true, Bool.false_eq_true, if_false, hon]
    by_cases hskip : (blockPlan spec ms[k]).skip = true
    · simp only [hskip, if_true]
      refine ⟨s, rfl, ?_, rfl⟩
      rw [blockOutSip_nil spec cands prb ms[k] (blockOut_skipped spec prb ms[k] cols h hskip), List.append_nil]
      exact hsl0
    · have hskip' : (blockPlan spec ms[k]).skip = false := by simpa using hskip
      simp only [hskip', Bool.false_eq_true, if_false]
      by_cases hmh : Sip.mayHold cands (sipRange ms[k] spec.key spec.key.size).1
          (sipRange ms[k] spec.key spec.key.size).2
          (Sip.lbHint cands (sipRange ms[k] spec.key spec.key.size).1) = true
      · simp only [hmh, Bool.not_true, Bool.false_eq_true, if_false]
        obtain ⟨bytes, starts, nbytes, hrf, hsl⟩ := readFrames_slice st prb spec.perm hprb ms[k] cols h hrows
          ((needOf spec (blockPlan spec ms[k]) (constOutOf spec ms[k] (blockPlan spec ms[k]))).set! spec.key.size true)
        obtain ⟨ch, t, g', hch, ht, cs, n, hform, hsz⟩ := sipChunk_tuples spec hspec hk cands hs sortVar prb ms[k] cols h
          hskip' bytes starts hsl (Sip.lbHint cands (sipRange ms[k] spec.key spec.key.size).1)
        rw [hrf]
        simp only [pure_bind, hch, ofExceptM, liftG, stepOf, if_true]
        refine ⟨_, rfl, ?_, rfl⟩
        simp only
        have hwf : ChunkWF spec ch := by
          rw [hform]; exact chunkOfCols_wf spec hspec sortVar _ _ cs n hsz
        have := hR s.acc l ch hwf hsl0
        rw [ht, ← blockOutSip_eq spec cands prb ms[k] cols h] at this
        exact this
      · have hmh' : Sip.mayHold cands (sipRange ms[k] spec.key spec.key.size).1
            (sipRange ms[k] spec.key spec.key.size).2
            (Sip.lbHint cands (sipRange ms[k] spec.key spec.key.size).1) = false := by simpa using hmh
        simp only [hmh', Bool.not_false, if_true]
        refine ⟨_, rfl, ?_, rfl⟩
        simp only
        have hnil : blockOutSip spec cands prb ms[k] = [] := by
          rw [blockOutSip_eq spec cands prb ms[k] cols h, List.map_eq_nil_iff.mpr]
          rw [List.filter_eq_nil_iff]
          intro i hi hki
          simp only [Bool.and_eq_true] at hki
          have := sipSkip_none spec hk cands hs prb ms[k] cols h _ hmh' i (List.mem_range.mp hi) hki.1
          rw [this] at hki
          exact Bool.false_ne_true hki.2
        rw [hnil, List.append_nil]
        exact hsl0
  · have hsel' : selects ms[k] spec.key = false := by simpa using hsel
    simp only [hsel', Bool.not_false, if_true]
    refine ⟨s, rfl, ?_, rfl⟩
    rw [blockOutSip_nil spec cands prb ms[k] (blockOut_unselected spec prb ms[k] cols h hsel'), List.append_nil]
    exact hsl0

theorem forIn_blocks_sipR (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) (hk : spec.key.size < 4)
    (cands : Array UInt64) (hs : Sip.Sorted cands) {σ : Type}
    (g : σ → Chunk → σ) (R : σ → List (List Nat) → Prop)
    (hR : ∀ a l ch, ChunkWF spec ch → R a l → R (g a ch) (l ++ colTuples ch))
    (prb : ByteArray) (ms : List BlockMeta)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hfits : ∀ b ∈ ms, b.rows ≤ two64)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols)
    (sortVar : Option String) (ox : OvCtx) (hon : ox.on = false) :
    ∀ (L : List Nat), (∀ k ∈ L, k < ms.length) → ∀ (s : ScanState σ) (l : List (List Nat)), R s.acc l →
      ∃ s', forIn L s (scanBlockSipM st spec cands (liftG g) ms.toArray sortVar ox) = pure s' ∧
        R s'.acc (l ++ L.flatMap (fun k => blockOutSip spec cands prb ms[k]!)) ∧ s'.stopped = s.stopped := by
  intro L
  induction L with
  | nil => intro _ s l hs0; exact ⟨s, rfl, by simpa using hs0, rfl⟩
  | cons k ks ih =>
    intro hL s l hs0
    have hk' := hL k List.mem_cons_self
    obtain ⟨s1, h1, a1, t1⟩ :=
      scanBlockSipM_stepR st spec hspec hk cands hs g R hR prb ms hprb hfits hblocks sortVar ox hon k hk' s l hs0
    obtain ⟨s', h2, a2, t2⟩ := ih (fun j hj => hL j (List.mem_cons_of_mem _ hj)) s1 _ a1
    refine ⟨s', ?_, ?_, by rw [t2, t1]⟩
    · rw [List.forIn_cons, h1, pure_bind]
      exact h2
    · rw [List.flatMap_cons, ← List.append_assoc, getElem!_pos ms k hk']
      exact a2

/-- The blocks outside `blocksFor` give no tuple with candidates. -/
theorem blocksFor_outSip (spec : ScanSpec) (cands : Array UInt64) (prb : ByteArray) (ms : List BlockMeta)
    (hadm : prmAdmitted spec.perm ms = true)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols) :
    (blocksFor ms.toArray spec.key).toList.flatMap (fun k => blockOutSip spec cands prb ms[k]!) =
      ((ms.flatMap (blockRows prb)).filter fun r => keep spec r && candOf spec cands r).map (proj spec) := by
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
    intro k hk
    exact hE k (List.mem_range.mp hk) (by simp)
  · rw [hL] at hE ⊢
    have hs : ms.toArray.size = ms.length := List.size_toArray
    rw [flatMap_range_interval ms.length _ c (by omega) (fun k => blockOutSip spec cands prb ms[k]!)
      (fun k hk hout => hE k hk (fun hm => by have := List.mem_range'_1.mp hm; omega))]

/-- **The scan with candidates with an accumulator** (L4i). -/
theorem scanFoldSipM_R (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) (hk : spec.key.size < 4)
    (cands : Array UInt64) (hs : Sip.Sorted cands) {σ : Type}
    (g : σ → Chunk → σ) (R : σ → List (List Nat) → Prop)
    (hR : ∀ a l ch, ChunkWF spec ch → R a l → R (g a ch) (l ++ colTuples ch))
    (init : σ) (hinit : R init [])
    (prb : ByteArray) (ms : List BlockMeta)
    (hrange : st.blocksForRange spec.perm spec.key = pure (metasFor ms.toArray spec.key))
    (hcount : st.blockCount spec.perm = pure ms.length)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hovl : (st.ovl spec.perm).isEmpty = true)
    (hadm : prmAdmitted spec.perm ms = true)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols) :
    ∃ acc stats, scanFoldSipM st spec cands init (liftG g) = pure (acc, stats) ∧
      R acc (((ms.flatMap (blockRows prb)).filter fun r => keep spec r && candOf spec cands r).map (proj spec)) := by
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
  unfold scanFoldSipM
  rw [hrange, pure_bind, hcount, pure_bind]
  obtain ⟨s', hfor, hacc, hstop⟩ := forIn_blocks_sipR st spec hspec hk cands hs g R hR prb ms hprb hfits hblocks
    (match spec.outCols[0]? with
      | some c => if c == spec.key.size then spec.outVars[0]? else none
      | none => none) _ hon
    (blocksFor ms.toArray spec.key).toList (blocksFor_lt spec ms)
    { acc := init, stats := { blocksTotal := ms.length }, insPos := 0, stopped := false } [] hinit
  refine ⟨s'.acc, s'.stats, ?_, ?_⟩
  · simp only []
    rw [forIn_metasFor_sip]
    erw [hfor]
    rw [pure_bind]
    simp only [hon, Bool.false_and, Bool.false_eq_true, if_false]
  · rw [List.nil_append, blocksFor_outSip spec cands prb ms hadm hblocks] at hacc
    exact hacc

/-- **The table of a scan with candidates.** -/
theorem scanSipTableM_spec (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) (hk : spec.key.size < 4)
    (cands : Array UInt64) (hs : Sip.Sorted cands)
    (prb : ByteArray) (ms : List BlockMeta)
    (hrange : st.blocksForRange spec.perm spec.key = pure (metasFor ms.toArray spec.key))
    (hcount : st.blockCount spec.perm = pure ms.length)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hovl : (st.ovl spec.perm).isEmpty = true)
    (hadm : prmAdmitted spec.perm ms = true)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols) :
    ∃ T stats, scanSipTableM st spec cands = pure (T, stats) ∧
      TableOf spec T (((ms.flatMap (blockRows prb)).filter fun r => keep spec r && candOf spec cands r).map
        (proj spec)) := by
  unfold scanSipTableM
  have hinit : TableOf spec (Table.mk spec.outVars (spec.outVars.map (fun _ => ByteArray.empty)) 0
      (sortVarOf spec)) [] := by
    refine ⟨rfl, by simp, fun k h => ?_, rfl, rfl⟩
    simp
  obtain ⟨acc, stats, he, hR⟩ := scanFoldSipM_R st spec hspec hk cands hs (fun acc ch => acc.append ch.table)
    (TableOf spec) (tableOf_append spec) _ hinit prb ms hrange hcount hprb hovl hadm hblocks
  exact ⟨acc, stats, he, hR⟩

end L4Factoidal.Storage.Sbm11.SipTableTheorems

#print axioms L4Factoidal.Storage.Sbm11.SipTableTheorems.scanSipTableM_spec
