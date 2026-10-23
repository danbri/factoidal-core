/-
L4Factoidal.Storage.Sbm11.ScanTableTheorems — the table of one triple
pattern scan against the model of the leaves
(https://github.com/danbri/factoidal/issues/776; lemma L4k of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md, the first step of
the leaf scans of section 3).

`IdLeafTheorems.storeLeaves` models a basic graph pattern as the scan of each
triple pattern alone (`IdLeaf.scanRows` over a listing of the store's id
triples), joined with `IdJoin.idJoin`. The id path runs `IdQuery.scanTableM`
of the planner's scan specification (`IdQuery.mkSpec`) and gets a `Table`.
This file proves that the table denotes the model's scan.

## Steps

* `scanFoldM_R`: lemma L4e (`ScanFoldTheorems.scanFoldM_tuples`) for any
  accumulator that appends chunks: over an in-memory store of an admitted
  permutation with no overlay, the accumulator is related to the output
  tuples of the rows the scan keeps, when a well-formed chunk (`ChunkWF`,
  from `blockChunk_form` and `chunkOfCols_wf`) extends the relation by its
  column tuples.
* `scanTableM_spec`: with `Table.append` as the accumulator (`append_fields`,
  `tabTuples_append`), the table has the scan's variables, one column of
  `8 * rows` bytes per variable, the scan's sort variable, and the tuples of
  L4e (`TableOf`).
* `mkSpec_eq`, `specInv_step`, `specInv_four`: `mkSpec` is a fold over the
  four columns; its state (`SpecAcc`) satisfies an invariant (`SpecInv`):
  the key, checks and repeated-variable tests of the scan pass on a row
  exactly when `IdLeaf.matchSlots` of the row's columns succeeds, and the
  solution mapping of the row (`seenRow`) is the match, up to `RowEq`.
* `colSl_perm`, `row_opt`: the four columns are the subject, predicate,
  object and graph positions in another order (`matchSlots_perm`), so a row
  is kept exactly when the model matches its triple (`tripleOf`) in the
  graph `gid`.
* `idRows_eq`, `rows_sorted`, `scanTable_sortOk`: the rows of the table are
  the `seenRow`s of the rows kept, no column holds id 0, and the table is in
  the order its sort variable says.
* `scanTable_model` (L4k): `scanTableM` of `mkSpec t perm (fun _ => true)`
  over a permutation of an in-memory store (`PermMem`) returns a table that
  is well formed (`Table.WF`), has no id 0 (`NoUnbound`), is `SortOk`, and
  whose rows are row for row (`Pw RowEq`) `IdLeaf.scanRows (ipatOf t)` over
  the permutation's listing of the graph `gid` (`permListing`).

## Hypotheses

`PermMem`: the store answers the PRM1 range queries and PRB1 reads from
arrays (the in-memory store; `PrmRangeTheorems.rangeM_array` gives the range
answer), the permutation has no delta overlay, activation admitted the PRM1
entries and every block, and no subject, predicate or object id of a row is
0. The pattern: a constant graph slot (`GCtx.dflt` without a dataset clause,
or `GCtx.named`), `named = false`, no constant without an id. Not covered:
the overlay (L7e), the `IO` store, `GRAPH ?g` as one scan, FROM / FROM
NAMED patterns.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.TableOuterTheorems
import L4Factoidal.Storage.Sbm11.IdLeafTheorems

namespace L4Factoidal.Storage.Sbm11.ScanTableTheorems

open L4Factoidal (two64)
open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.ScanFoldTheorems
open L4Factoidal.Storage.Sbm11.FrameWords (words)
open L4Factoidal.Codec.Zstd (word64)

/-! ## The chunk of one block, explicitly -/

/-- The cut column `c` of a block (`cutCol` over an admitted block). -/
def cutOf (cols : Cols) (need : Array Bool) (lo hi c : Nat) : ByteArray :=
  if need[c]! then (words (colv cols c)).extract (8 * lo) (8 * hi) else .empty

/-- The chunk `blockChunk` builds for an admitted block: `chunkOfCols` of the
    four cut columns over the key range `[lo, hi)`. -/
theorem blockChunk_form (spec : ScanSpec) (hspec : SpecOk spec) (fill : Bool) (sortVar : Option String)
    (prb : ByteArray) (b : BlockMeta) (cols : Cols) (h : decodeBlockAt prb b b.offset = .ok cols)
    (hrows : b.rows ≤ two64) (bytes : ByteArray) (starts : Array Nat)
    (hsl : SliceOk b cols (needOf spec (blockPlan spec b) (constOutOf spec b (blockPlan spec b))) bytes starts) :
    ∃ lo hi, lo ≤ hi ∧ hi ≤ b.rows ∧
      blockChunk spec fill sortVar b (blockPlan spec b) (constOutOf spec b (blockPlan spec b))
        (needOf spec (blockPlan spec b) (constOutOf spec b (blockPlan spec b))) bytes starts =
      .ok (chunkOfCols spec fill sortVar (blockPlan spec b) (constOutOf spec b (blockPlan spec b))
        #[cutOf cols (needOf spec (blockPlan spec b) (constOutOf spec b (blockPlan spec b))) lo hi 0,
          cutOf cols (needOf spec (blockPlan spec b) (constOutOf spec b (blockPlan spec b))) lo hi 1,
          cutOf cols (needOf spec (blockPlan spec b) (constOutOf spec b (blockPlan spec b))) lo hi 2,
          cutOf cols (needOf spec (blockPlan spec b) (constOutOf spec b (blockPlan spec b))) lo hi 3] (hi - lo)) := by
  obtain ⟨hsz, -, -, -, -, -⟩ := admitted_facts prb b cols h
  generalize hbp : blockPlan spec b = bp at hsl ⊢
  generalize hco : constOutOf spec b bp = co at hsl ⊢
  have hneed : ∀ c, c < 4 → (needOf spec bp co)[c]! = needCol spec bp co c := fun c hc => needOf_getElem spec bp co c hc
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
  obtain ⟨hlh, hhi, -⟩ := keyRange_spec spec hspec.key prb b cols h bp.full hfull kw hkw'
  generalize hlhp : keyRange spec b bp.full kw = lh at hlh hhi
  obtain ⟨lo, hi⟩ := lh
  simp only at hlh hhi
  have hcut : ∀ c, c < 4 → cutCol b bytes starts (needOf spec bp co) kw lo hi c =
      .ok (cutOf cols (needOf spec bp co) lo hi c) :=
    fun c hc => cutCol_slice hsl hrows kw hkw lo hi hlh hhi c hc
  refine ⟨lo, hi, hlh, hhi, ?_⟩
  unfold blockChunk
  rw [hkwEq]
  simp only [bind, Except.bind, hlhp]
  rw [hcut 0 (by omega), hcut 1 (by omega), hcut 2 (by omega), hcut 3 (by omega)]
  rfl

/-- A chunk whose table has the scan's variables, one column per variable,
    each of `8 * rows` bytes. -/
structure ChunkWF (spec : ScanSpec) (ch : Chunk) : Prop where
  vars : ch.table.vars = spec.outVars
  size : ch.table.cols.size = spec.outVars.size
  bytes : ∀ k (h : k < ch.table.cols.size), ch.table.cols[k].size = 8 * ch.table.rows

theorem flatten_put64_length {α : Type} (f : α → Nat) (l : List α) :
    ((l.map fun a => Column.put64 (f a)).flatten).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, ih, List.length_cons,
      FrameWords.put64_length]
    omega

theorem ewc_data (c : Nat) : (ByteArray.emptyWithCapacity c).data.toList = [] := rfl
theorem ewc_size (c : Nat) : (ByteArray.emptyWithCapacity c).size = 0 := rfl

theorem constWords_size (x : UInt64) (n : Nat) : (constWords x n).size = 8 * n := by
  rw [TableTheorems.size_eq_length]
  unfold constWords
  rw [constWordsGo_data]
  have := flatten_put64_length id (List.replicate n x.toNat)
  simp only [id] at this
  rw [List.length_append, ewc_data, this]
  simp

/-- `chunkOfCols` with `fill = true` gives a well-formed chunk when every
    column it needs has `8 * n` bytes. -/
theorem chunkOfCols_wf (spec : ScanSpec) (hspec : SpecOk spec) (sortVar : Option String)
    (bp : BlockPlan) (constOut : Array (Option Nat))
    (cols : Array ByteArray) (n : Nat)
    (hcols : ∀ c, c < 4 → needCol spec bp constOut c = true → cols[c]!.size = 8 * n) :
    ChunkWF spec (chunkOfCols spec true sortVar bp constOut cols n) := by
  have houtlt : ∀ k, k < spec.outCols.size → spec.outCols[k]! < 4 := by
    intro k hk
    rw [getElem!_pos spec.outCols k hk]
    exact hspec.outCols _ (Array.getElem_mem hk)
  unfold chunkOfCols
  by_cases hp : bp.perRow spec = true
  · rw [if_pos hp]
    obtain ⟨s1, s2, s3⟩ := selectRows_spec cols bp.checks bp.named spec.eqs spec.outCols n (n + 1) 0
      (spec.outVars.map fun _ => ByteArray.emptyWithCapacity (8 * n)) 0 (by omega)
    generalize selectRows cols bp.checks bp.named spec.eqs spec.outCols n (n + 1) 0
      (spec.outVars.map fun _ => ByteArray.emptyWithCapacity (8 * n)) 0 = res at s1 s2 s3
    obtain ⟨out, k⟩ := res
    dsimp only at s1 s2 s3
    simp only [Array.size_map] at s1 s3
    refine ⟨rfl, s1, fun j hj => ?_⟩
    have hj' : j < spec.outVars.size := by rw [← s1]; exact hj
    have := s3 j (by simpa using hj') (by rw [← hspec.outVars]; exact hj')
    rw [← getElem!_pos out j hj, TableTheorems.size_eq_length, this, List.length_append,
      flatten_put64_length (fun j_1 => (at64 cols[spec.outCols[j]!]! j_1).toNat), s2]
    simp [ewc_data]
  · rw [if_neg hp]
    refine ⟨rfl, by simp [hspec.outVars], fun j hj => ?_⟩
    simp only [Array.size_map, List.size_toArray, List.length_range] at hj
    simp only [Array.getElem_map, List.getElem_toArray, List.getElem_range]
    cases hc : constOut[j]! with
    | some x => simp [constWords_size]
    | none =>
      simp only
      apply hcols _ (houtlt j hj)
      apply needCol_out spec bp constOut j hj
      simp [hc]

/-- The chunk of an admitted block, with `fill = true`, is well formed. -/
theorem blockChunk_wf (spec : ScanSpec) (hspec : SpecOk spec) (sortVar : Option String)
    (prb : ByteArray) (b : BlockMeta) (cols : Cols) (h : decodeBlockAt prb b b.offset = .ok cols)
    (lo hi : Nat) (hlh : lo ≤ hi) (hhi : hi ≤ b.rows) :
    ChunkWF spec (chunkOfCols spec true sortVar (blockPlan spec b) (constOutOf spec b (blockPlan spec b))
        #[cutOf cols (needOf spec (blockPlan spec b) (constOutOf spec b (blockPlan spec b))) lo hi 0,
          cutOf cols (needOf spec (blockPlan spec b) (constOutOf spec b (blockPlan spec b))) lo hi 1,
          cutOf cols (needOf spec (blockPlan spec b) (constOutOf spec b (blockPlan spec b))) lo hi 2,
          cutOf cols (needOf spec (blockPlan spec b) (constOutOf spec b (blockPlan spec b))) lo hi 3] (hi - lo)) := by
  obtain ⟨hsz, -, -, -, -, -⟩ := admitted_facts prb b cols h
  apply chunkOfCols_wf spec hspec sortVar _ _
  intro c hc hn
  have hn' : (needOf spec (blockPlan spec b) (constOutOf spec b (blockPlan spec b)))[c]! = true := by
    rw [needOf_getElem _ _ _ c hc]; exact hn
  have hw : (cutOf cols (needOf spec (blockPlan spec b) (constOutOf spec b (blockPlan spec b)))
      lo hi c).size = 8 * (hi - lo) := by
    unfold cutOf
    rw [if_pos hn']
    simp only [ByteArray.size_extract, words_size', hsz c hc]
    omega
  match c, hc with
  | 0, _ => exact hw
  | 1, _ => exact hw
  | 2, _ => exact hw
  | 3, _ => exact hw

/-! ## The scan with any accumulator that appends chunks -/

/-- The scan's `f` from a pure step that never stops. -/
def liftG {σ : Type} (g : σ → Chunk → σ) (acc : σ) (ch : Chunk) : ExceptT String Id (σ × Bool) :=
  pure (g acc ch, true)

/-- One block of a scan with no overlay over an in-memory store, for an
    accumulator related to the list of tuples by `R`, which every well-formed
    chunk extends by its column tuples. -/
theorem scanBlockM_stepR (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) {σ : Type}
    (g : σ → Chunk → σ) (R : σ → List (List Nat) → Prop)
    (hR : ∀ a l ch, ChunkWF spec ch → R a l → R (g a ch) (l ++ colTuples ch))
    (prb : ByteArray) (ms : List BlockMeta)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hfits : ∀ b ∈ ms, b.rows ≤ two64)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols)
    (sortVar : Option String) (ox : OvCtx) (hon : ox.on = false)
    (k : Nat) (hk : k < ms.length) (s : ScanState σ) (l : List (List Nat)) (hs : R s.acc l) :
    ∃ s1, scanBlockM st spec true (liftG g) ms.toArray sortVar ox k s = pure (.yield s1) ∧
      R s1.acc (l ++ blockOut spec prb ms[k]) ∧ s1.stopped = s.stopped := by
  obtain ⟨cols, h⟩ := hblocks ms[k] (List.getElem_mem hk)
  have hrows := hfits ms[k] (List.getElem_mem hk)
  unfold scanBlockM
  rw [toArray_getElem! ms k hk]
  by_cases hsel : selects ms[k] spec.key = true
  · simp only [hsel, Bool.not_true, Bool.false_eq_true, if_false, hon]
    by_cases hskip : (blockPlan spec ms[k]).skip = true
    · simp only [hskip, if_true]
      exact ⟨s, rfl, by rw [blockOut_skipped spec prb ms[k] cols h hskip, List.append_nil]; exact hs, rfl⟩
    · have hskip' : (blockPlan spec ms[k]).skip = false := by simpa using hskip
      simp only [hskip', Bool.false_eq_true, if_false]
      obtain ⟨bytes, starts, nbytes, hrf, hsl⟩ := readFrames_slice st prb spec.perm hprb ms[k] cols h hrows
        (needOf spec (blockPlan spec ms[k]) (constOutOf spec ms[k] (blockPlan spec ms[k])))
      obtain ⟨ch, hch, ht⟩ := blockChunk_tuples spec hspec true sortVar prb ms[k] cols h hrows hskip' bytes starts hsl
      obtain ⟨lo, hi, hlh, hhi, hform⟩ := blockChunk_form spec hspec true sortVar prb ms[k] cols h hrows bytes starts hsl
      rw [hform] at hch
      cases hch
      rw [hrf]
      simp only [pure_bind, hform, ofExceptM, liftG, stepOf, if_true]
      refine ⟨_, rfl, ?_, rfl⟩
      simp only
      have hct := chunkOfCols_colTuples spec sortVar (blockPlan spec ms[k]) (constOutOf spec ms[k] (blockPlan spec ms[k]))
        (by simp [constOutOf])
        #[cutOf cols (needOf spec (blockPlan spec ms[k]) (constOutOf spec ms[k] (blockPlan spec ms[k]))) lo hi 0,
          cutOf cols (needOf spec (blockPlan spec ms[k]) (constOutOf spec ms[k] (blockPlan spec ms[k]))) lo hi 1,
          cutOf cols (needOf spec (blockPlan spec ms[k]) (constOutOf spec ms[k] (blockPlan spec ms[k]))) lo hi 2,
          cutOf cols (needOf spec (blockPlan spec ms[k]) (constOutOf spec ms[k] (blockPlan spec ms[k]))) lo hi 3]
        (hi - lo)
      have := hR s.acc l _ (blockChunk_wf spec hspec sortVar prb ms[k] cols h lo hi hlh hhi) hs
      rw [hct, ht, ← blockOut_eq spec prb ms[k] cols h] at this
      exact this
  · have hsel' : selects ms[k] spec.key = false := by simpa using hsel
    simp only [hsel', Bool.not_false, if_true]
    exact ⟨s, rfl, by rw [blockOut_unselected spec prb ms[k] cols h hsel', List.append_nil]; exact hs, rfl⟩

theorem forIn_blocksR (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) {σ : Type}
    (g : σ → Chunk → σ) (R : σ → List (List Nat) → Prop)
    (hR : ∀ a l ch, ChunkWF spec ch → R a l → R (g a ch) (l ++ colTuples ch))
    (prb : ByteArray) (ms : List BlockMeta)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hfits : ∀ b ∈ ms, b.rows ≤ two64)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols)
    (sortVar : Option String) (ox : OvCtx) (hon : ox.on = false) :
    ∀ (L : List Nat), (∀ k ∈ L, k < ms.length) → ∀ (s : ScanState σ) (l : List (List Nat)), R s.acc l →
      ∃ s', forIn L s (scanBlockM st spec true (liftG g) ms.toArray sortVar ox) = pure s' ∧
        R s'.acc (l ++ L.flatMap (fun k => blockOut spec prb ms[k]!)) ∧ s'.stopped = s.stopped := by
  intro L
  induction L with
  | nil => intro _ s l hs; exact ⟨s, rfl, by simpa using hs, rfl⟩
  | cons k ks ih =>
    intro hL s l hs
    have hk := hL k List.mem_cons_self
    obtain ⟨s1, h1, a1, t1⟩ :=
      scanBlockM_stepR st spec hspec g R hR prb ms hprb hfits hblocks sortVar ox hon k hk s l hs
    obtain ⟨s', h2, a2, t2⟩ := ih (fun j hj => hL j (List.mem_cons_of_mem _ hj)) s1 _ a1
    refine ⟨s', ?_, ?_, by rw [t2, t1]⟩
    · rw [List.forIn_cons, h1, pure_bind]
      exact h2
    · rw [List.flatMap_cons, ← List.append_assoc, getElem!_pos ms k hk]
      exact a2

/-- The blocks outside `blocksFor` give no tuple: the tuples of the selected
    blocks are those of the whole permutation. -/
theorem blocksFor_out (spec : ScanSpec) (prb : ByteArray) (ms : List BlockMeta)
    (hadm : prmAdmitted spec.perm ms = true)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols) :
    (blocksFor ms.toArray spec.key).toList.flatMap (fun k => blockOut spec prb ms[k]!) =
      ((ms.flatMap (blockRows prb)).filter (keep spec)).map (proj spec) := by
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

theorem blocksFor_lt (spec : ScanSpec) (ms : List BlockMeta) :
    ∀ k ∈ (blocksFor ms.toArray spec.key).toList, k < ms.length := by
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

/-- **The scan with an accumulator.** Over an in-memory store of an admitted
    permutation with no overlay, `scanFoldM` with `fill = true` and a pure
    step `g` that never stops ends in an accumulator related by `R` to the
    output tuples of the rows the scan keeps, when `R` relates the initial
    accumulator to no tuple and every well-formed chunk extends it by its
    column tuples. -/
theorem scanFoldM_R (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) {σ : Type}
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
    ∃ acc stats, scanFoldM st spec true init (liftG g) = pure (acc, stats) ∧
      R acc (((ms.flatMap (blockRows prb)).filter (keep spec)).map (proj spec)) := by
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
  unfold scanFoldM
  rw [hrange, pure_bind, hcount, pure_bind]
  obtain ⟨s', hfor, hacc, hstop⟩ := forIn_blocksR st spec hspec g R hR prb ms hprb hfits hblocks
    (match spec.outCols[0]? with
      | some c => if c == spec.key.size then spec.outVars[0]? else none
      | none => none) _ hon
    (blocksFor ms.toArray spec.key).toList (blocksFor_lt spec ms)
    { acc := init, stats := { blocksTotal := ms.length }, insPos := 0, stopped := false } [] hinit
  refine ⟨s'.acc, s'.stats, ?_, ?_⟩
  · simp only []
    rw [forIn_metasFor]
    erw [hfor]
    rw [pure_bind]
    simp only [hon, Bool.false_and, Bool.false_eq_true, if_false]
  · rw [List.nil_append, blocksFor_out spec prb ms hadm hblocks] at hacc
    exact hacc

/-! ## `Table.append` -/

theorem append_fields (a b : Table) :
    (a.append b).vars = a.vars ∧ (a.append b).rows = a.rows + b.rows ∧ (a.append b).sortVar = a.sortVar ∧
      (a.append b).cols.size = a.cols.size ∧
      ∀ k, k < a.cols.size → (a.append b).cols[k]! = a.cols[k]! ++ b.cols[k]! := by
  unfold Table.append
  simp only [_root_.Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [List.forIn_pure_yield_eq_foldl]
  obtain ⟨h1, h2⟩ := foldl_modify (fun k c => c ++ b.cols[k]!) (List.range' 0 a.cols.size) a.cols
    List.nodup_range'
  refine ⟨rfl, rfl, rfl, h1, fun k hk => ?_⟩
  have := h2 k hk
  rw [if_pos (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)] at this
  rw [getElem!_pos a.cols k hk]
  exact this

/-- The tuples of a table: per row, per column, the id. -/
def tabTuples (t : Table) : List (List Nat) :=
  (List.range t.rows).map fun i => (List.range t.cols.size).map fun k => (t.at k i).toNat

theorem colTuples_eq (ch : Chunk) : colTuples ch = tabTuples ch.table := rfl

theorem word64_append_left (A B : ByteArray) (i : Nat) (h : i + 8 ≤ A.size) :
    word64 (A ++ B) i = word64 A i := by
  apply TableTheorems.word64_congr
  intro t ht
  rw [ByteArray.data_append, Array.toList_append, List.getElem?_append_left
    (by rw [← TableTheorems.size_eq_length]; omega)]

theorem word64_append_right (A B : ByteArray) (j : Nat) :
    word64 (A ++ B) (A.size + j) = word64 B j := by
  apply TableTheorems.word64_congr
  intro t ht
  rw [ByteArray.data_append, Array.toList_append, List.getElem?_append_right
    (by rw [← TableTheorems.size_eq_length]; omega), ← TableTheorems.size_eq_length]
  congr 1; omega

theorem tabTuples_append (a b : Table) (hsz : b.cols.size = a.cols.size)
    (ha : ∀ k (h : k < a.cols.size), a.cols[k].size = 8 * a.rows) :
    tabTuples (a.append b) = tabTuples a ++ tabTuples b := by
  obtain ⟨_, hr, _, hc, hk⟩ := append_fields a b
  unfold tabTuples
  rw [hr, hc, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply map_congr_mem
    intro i hi
    have hi' := List.mem_range.mp hi
    apply map_congr_mem
    intro k hk'
    have hk'' := List.mem_range.mp hk'
    unfold Table.at
    rw [hk k hk'', word64_append_left _ _ _ (by rw [getElem!_pos a.cols k hk'', ha k hk'']; omega)]
  · rw [hsz]
    apply map_congr_mem
    intro j _
    apply map_congr_mem
    intro k hk'
    have hk'' := List.mem_range.mp hk'
    unfold Table.at
    rw [hk k hk'', show 8 * (a.rows + j) = a.cols[k]!.size + 8 * j by
      rw [getElem!_pos a.cols k hk'', ha k hk'']; omega, word64_append_right]

/-! ## The table of one scan -/

/-- What the table of a scan of `spec` holds: the scan's variables, one
    column of `8 * rows` bytes per variable, the scan's sort variable, and
    the tuples `l`. -/
structure TableOf (spec : ScanSpec) (t : Table) (l : List (List Nat)) : Prop where
  vars : t.vars = spec.outVars
  size : t.cols.size = spec.outVars.size
  bytes : ∀ k (h : k < t.cols.size), t.cols[k].size = 8 * t.rows
  sortVar : t.sortVar = sortVarOf spec
  tuples : tabTuples t = l

theorem tableOf_append (spec : ScanSpec) (a : Table) (l : List (List Nat)) (ch : Chunk)
    (hch : ChunkWF spec ch) (ha : TableOf spec a l) :
    TableOf spec (a.append ch.table) (l ++ colTuples ch) := by
  obtain ⟨hv, hr, hs, hc, hk⟩ := append_fields a ch.table
  have hsz : ch.table.cols.size = a.cols.size := by rw [hch.size, ha.size]
  refine ⟨by rw [hv, ha.vars], by rw [hc, ha.size], fun k h => ?_, by rw [hs, ha.sortVar], ?_⟩
  · rw [hc] at h
    rw [← getElem!_pos _ k (by rw [hc]; exact h), hk k h, ByteArray.size_append,
      getElem!_pos a.cols k h, getElem!_pos ch.table.cols k (by rw [hsz]; exact h), ha.bytes k h,
      hch.bytes k (by rw [hsz]; exact h), hr]
    omega
  · rw [tabTuples_append a ch.table hsz ha.bytes, ha.tuples, colTuples_eq]

/-- **The table of one triple pattern scan.** Over an in-memory store of an
    admitted permutation with no overlay, `scanTableM` returns a table with
    the scan's output variables, one column of `8 * rows` bytes per
    variable, the scan's sort variable, whose tuples are the output tuples of
    exactly the rows of the permutation the scan keeps, in row order. -/
theorem scanTableM_spec (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec)
    (prb : ByteArray) (ms : List BlockMeta)
    (hrange : st.blocksForRange spec.perm spec.key = pure (metasFor ms.toArray spec.key))
    (hcount : st.blockCount spec.perm = pure ms.length)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hovl : (st.ovl spec.perm).isEmpty = true)
    (hadm : prmAdmitted spec.perm ms = true)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols) :
    ∃ T stats, scanTableM st spec = pure (T, stats) ∧
      TableOf spec T (((ms.flatMap (blockRows prb)).filter (keep spec)).map (proj spec)) := by
  unfold scanTableM
  rw [hrange, pure_bind]
  have hinit : ∀ cap, TableOf spec (Table.mk spec.outVars
      (spec.outVars.map (fun _ => ByteArray.emptyWithCapacity cap)) 0 (sortVarOf spec)) [] := by
    intro cap
    refine ⟨rfl, by simp, fun k h => ?_, rfl, rfl⟩
    simp [ewc_size]
  obtain ⟨acc, stats, he, hR⟩ := scanFoldM_R st spec hspec (fun acc ch => acc.append ch.table) (TableOf spec)
    (tableOf_append spec) _ (hinit (8 * selRows (metasFor ms.toArray spec.key))) prb ms hrange hcount hprb hovl
    hadm hblocks
  exact ⟨acc, stats, he, hR⟩

/-! ## `mkSpec` as a fold over the four columns -/

/-- The state of the loop of `mkSpec`. -/
structure SpecAcc where
  key : Array UInt64
  checks : Array (Nat × UInt64)
  outVars : Array String
  outCols : Array Nat
  eqs : Array (Nat × Nat)
  seen : Array (String × Nat)
  leading : Bool

/-- One column of the loop of `mkSpec`. -/
def specStep (t : Pat) (perm : Nat) (need : String → Bool) (a : SpecAcc) (c : Nat) : SpecAcc :=
  match t.slot (ScanSpec.colPos perm c) with
  | .const x => if a.leading then { a with key := a.key.push x } else { a with checks := a.checks.push (c, x) }
  | .missing => if a.leading then { a with key := a.key.push 0 } else { a with checks := a.checks.push (c, 0) }
  | .var v =>
    match a.seen.find? (·.1 == v) with
    | some (_, c0) => { a with leading := false, eqs := a.eqs.push (c0, c) }
    | none =>
      if need v then
        { a with leading := false, seen := a.seen.push (v, c), outVars := a.outVars.push v,
                 outCols := a.outCols.push c }
      else { a with leading := false, seen := a.seen.push (v, c) }

def specInit : SpecAcc := ⟨#[], #[], #[], #[], #[], #[], true⟩

abbrev SpecT := Array UInt64 × Array (Nat × UInt64) × Array String × Array Nat × Array (Nat × Nat) ×
  Array (String × Nat) × Bool

def toT (a : SpecAcc) : SpecT := (a.key, a.checks, a.outVars, a.outCols, a.eqs, a.seen, a.leading)

theorem forIn_tuple (t : Pat) (perm : Nat) (need : String → Bool) (f : Nat → SpecT → _root_.Id (ForInStep SpecT))
    (h : ∀ c a, f c (toT a) = pure (.yield (toT (specStep t perm need a c)))) :
    ∀ (l : List Nat) (a : SpecAcc), forIn l (toT a) f = pure (toT (l.foldl (specStep t perm need) a)) := by
  intro l
  induction l with
  | nil => intro a; rfl
  | cons c l ih => intro a; rw [List.forIn_cons, h c a, pure_bind]; exact ih _

/-- The scan specification of a final loop state. -/
def specOf (perm : Nat) (named : Bool) (a : SpecAcc) : ScanSpec :=
  { perm, key := a.key, checks := a.checks, named, outVars := a.outVars, outCols := a.outCols, eqs := a.eqs }

/-- The final state of the loop of `mkSpec`. -/
def specAcc (t : Pat) (perm : Nat) (need : String → Bool) : SpecAcc :=
  [0, 1, 2, 3].foldl (specStep t perm need) specInit

/-- `mkSpec` is the fold of `specStep` over the columns 0 to 3. -/
theorem mkSpec_eq (t : Pat) (perm : Nat) (need : String → Bool) :
    mkSpec t perm need = specOf perm t.named (specAcc t perm need) := by
  unfold mkSpec
  simp only [_root_.Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [show ((#[], #[], #[], #[], #[], #[], true) : SpecT) = toT specInit from rfl]
  rw [forIn_tuple t perm need _ (fun c a => ?_)]
  · rfl
  · simp only [specStep, toT]
    cases hs : t.slot (ScanSpec.colPos perm c) with
    | const x => by_cases hl : a.leading = true <;> simp [hl]
    | missing => by_cases hl : a.leading = true <;> simp [hl]
    | var v =>
      cases hf : Array.find? (fun x => x.fst == v) a.seen with
      | some p => obtain ⟨_, c0⟩ := p; simp [hf]
      | none => by_cases hn : need v = true <;> simp [hf, hn]

/-! ## What the scan of one pattern keeps: the match of its slots -/

open L4Factoidal.Storage.Sbm11.IdLeaf (ISlot slotMatch matchSlots OptRowEq IPat idTpMatch scanRows)
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup)
open L4Factoidal.Storage.Sbm11.TableTheorems (RowEq)

/-- A slot of a pattern over ids, as the model reads it. -/
def islot : Slot → ISlot
  | .var v => .var v
  | .const x => .const x
  | .missing => .missing

/-- The slots of the columns `cs` of a scan of `t` from permutation `perm`
    against row `r`. -/
def colSl (t : Pat) (perm : Nat) (r : Row) (cs : List Nat) : List (ISlot × UInt64) :=
  cs.map fun c => (islot (t.slot (ScanSpec.colPos perm c)), (rowCol r c).toUInt64)

/-- The tests of the loop state on a row: the key, the checks, the repeated
    variables. -/
def testF (key : Array UInt64) (checks : Array (Nat × UInt64)) (eqs : Array (Nat × Nat)) (r : Row) : Bool :=
  (List.range key.size).all (fun j => rowCol r j == key[j]!.toNat) && checks.toList.all (chk r) &&
    eqs.toList.all (eqk r)

def test (a : SpecAcc) (r : Row) : Bool := testF a.key a.checks a.eqs r

/-- The solution mapping of a row: each variable seen, with the id of its
    first column. -/
def seenRow (a : SpecAcc) (r : Row) : IdRow := a.seen.toList.map fun p => (p.1, (rowCol r p.2).toUInt64)

/-- Every column below 4 of a row holds a word. -/
def Fits (r : Row) : Prop := ∀ c, c < 4 → rowCol r c < two64

/-- The invariant of the loop of `mkSpec` (every variable needed) after the
    columns `0 .. n - 1`. -/
structure SpecInv (t : Pat) (perm n : Nat) (a : SpecAcc) : Prop where
  keyLe : a.key.size ≤ n
  lead : a.leading = true → a.key.size = n
  checks : ∀ ck ∈ a.checks.toList, ck.1 < n
  eqs : ∀ e ∈ a.eqs.toList, e.1 < n ∧ e.2 < n
  seenLt : ∀ p ∈ a.seen.toList, p.2 < n
  seenVar : ∀ p ∈ a.seen.toList, t.slot (ScanSpec.colPos perm p.2) = .var p.1
  outVars : a.outVars = a.seen.map (·.1)
  outCols : a.outCols = a.seen.map (·.2)
  nodup : (a.seen.toList.map (·.1)).Nodup
  test_eq : ∀ r, Fits r → test a r = (matchSlots (colSl t perm r (List.range n)) []).isSome
  row_eq : ∀ r, Fits r → ∀ m, matchSlots (colSl t perm r (List.range n)) [] = some m → RowEq m (seenRow a r)

theorem specInv_init (t : Pat) (perm : Nat) : SpecInv t perm 0 specInit := by
  refine ⟨by simp [specInit], fun _ => rfl, by simp [specInit], by simp [specInit], by simp [specInit],
    by simp [specInit], by simp [specInit], by simp [specInit], by simp [specInit], fun r _ => rfl,
    fun r _ m hm => ?_⟩
  simp only [colSl, List.range_zero, List.map_nil, matchSlots, Option.some.injEq] at hm
  subst hm
  exact RowEq.refl _

theorem lookup_map_seen (g : Nat → UInt64) (v : String) :
    ∀ (l : List (String × Nat)), idLookup v (l.map fun p => (p.1, g p.2)) = (l.find? (·.1 == v)).map (g ·.2)
  | [] => rfl
  | (w, c) :: l => by
    simp only [List.map_cons, List.find?_cons]
    unfold idLookup
    by_cases h : w = v
    · simp [h]
    · rw [if_neg h, lookup_map_seen g v l, beq_eq_false_iff_ne.mpr h]

theorem toUInt64_beq (x y : Nat) (hx : x < two64) (hy : y < two64) : (x.toUInt64 == y.toUInt64) = (x == y) := by
  rw [ScanFoldTheorems.uint64_beq_toNat, ScanFoldTheorems.uint64_toNat_toUInt64 x hx,
    ScanFoldTheorems.uint64_toNat_toUInt64 y hy]

theorem const_beq (x : UInt64) (y : Nat) (hy : y < two64) : (x == y.toUInt64) = (y == x.toNat) := by
  rw [ScanFoldTheorems.uint64_beq_toNat, ScanFoldTheorems.uint64_toNat_toUInt64 y hy]
  by_cases hxy : x.toNat = y
  · simp [hxy]
  · have : y ≠ x.toNat := fun e => hxy e.symm
    rw [beq_eq_false_iff_ne.mpr hxy, beq_eq_false_iff_ne.mpr this]

theorem all_range_push (key : Array UInt64) (x : UInt64) (f : Nat → UInt64 → Bool) :
    (List.range (key.push x).size).all (fun j => f j (key.push x)[j]!) =
      ((List.range key.size).all (fun j => f j key[j]!) && f key.size x) := by
  rw [Array.size_push, List.range_succ, List.all_append]
  congr 1
  · apply ScanFoldTheorems.all_congr_mem
    intro j hj
    have hj' := List.mem_range.mp hj
    rw [getElem!_pos (key.push x) j (by simp; omega), getElem!_pos key j hj', Array.getElem_push,
      dif_pos hj']
  · simp

theorem matchSlots_snoc (S : List (ISlot × UInt64)) (s : ISlot) (y : UInt64) :
    matchSlots (S ++ [(s, y)]) [] = (matchSlots S []).bind (slotMatch s y) := by
  rw [IdLeaf.matchSlots_append]
  cases matchSlots S [] with
  | none => rfl
  | some m => simp only [Option.bind_some, matchSlots]; cases slotMatch s y m <;> rfl

theorem colSl_succ (t : Pat) (perm : Nat) (r : Row) (n : Nat) :
    colSl t perm r (List.range (n + 1)) =
      colSl t perm r (List.range n) ++ [(islot (t.slot (ScanSpec.colPos perm n)), (rowCol r n).toUInt64)] := by
  simp [colSl, List.range_succ]

theorem test_key (key : Array UInt64) (checks : Array (Nat × UInt64)) (eqs : Array (Nat × Nat)) (x : UInt64)
    (r : Row) : testF (key.push x) checks eqs r = (testF key checks eqs r && (rowCol r key.size == x.toNat)) := by
  unfold testF
  rw [all_range_push key x (fun j y => rowCol r j == y.toNat)]
  cases (List.range key.size).all (fun j => rowCol r j == key[j]!.toNat) <;>
    cases checks.toList.all (chk r) <;> cases eqs.toList.all (eqk r) <;> simp

theorem test_check (key : Array UInt64) (checks : Array (Nat × UInt64)) (eqs : Array (Nat × Nat))
    (ck : Nat × UInt64) (r : Row) : testF key (checks.push ck) eqs r = (testF key checks eqs r && chk r ck) := by
  unfold testF
  simp only [Array.toList_push, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
  cases (List.range key.size).all (fun j => rowCol r j == key[j]!.toNat) <;>
    cases checks.toList.all (chk r) <;> cases eqs.toList.all (eqk r) <;> simp

theorem test_eqs (key : Array UInt64) (checks : Array (Nat × UInt64)) (eqs : Array (Nat × Nat))
    (e : Nat × Nat) (r : Row) : testF key checks (eqs.push e) r = (testF key checks eqs r && eqk r e) := by
  unfold testF
  simp only [Array.toList_push, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
  cases (List.range key.size).all (fun j => rowCol r j == key[j]!.toNat) <;>
    cases checks.toList.all (chk r) <;> cases eqs.toList.all (eqk r) <;> simp

/-- A constant slot keeps the row or drops it. -/
theorem bind_const (M : Option IdRow) (x y : UInt64) :
    (M.bind (slotMatch (.const x) y)) = if x == y then M else none := by
  cases M with
  | none => simp
  | some m => simp only [Option.bind_some, slotMatch]

theorem lookup_append (w : String) : ∀ (A B : IdRow), idLookup w (A ++ B) =
    match idLookup w A with
    | some x => some x
    | none => idLookup w B
  | [], B => rfl
  | (u, x) :: A, B => by
    rw [List.cons_append, show idLookup w ((u, x) :: (A ++ B)) = if u = w then some x else idLookup w (A ++ B) from rfl,
      show idLookup w ((u, x) :: A) = if u = w then some x else idLookup w A from rfl]
    by_cases h : u = w
    · simp [h]
    · simp only [h, if_false]; exact lookup_append w A B

theorem isSome_ite (c : Bool) (M : Option IdRow) : (if c = true then M else none).isSome = (M.isSome && c) := by
  cases c <;> cases M <;> rfl

theorem find?_mem {l : Array (String × Nat)} {v w : String} {c0 : Nat} (h : l.find? (·.1 == v) = some (w, c0)) :
    w = v ∧ (w, c0) ∈ l.toList := by
  have h1 := Array.find?_some h
  have h2 := Array.mem_of_find?_eq_some h
  simp only [beq_iff_eq] at h1
  exact ⟨h1, Array.mem_toList_iff.mpr h2⟩

theorem find?_none {l : Array (String × Nat)} {v : String} (h : l.find? (·.1 == v) = none) :
    ∀ p ∈ l.toList, p.1 ≠ v := by
  intro p hp he
  rw [← Array.find?_toList, List.find?_eq_none] at h
  exact h p hp (by simp [he])

/-- One column of `mkSpec` keeps the invariant (every variable needed, no
    missing constant). -/
theorem specInv_step (t : Pat) (perm n : Nat) (hn : n < 4) (a : SpecAcc) (h : SpecInv t perm n a)
    (hmiss : t.slot (ScanSpec.colPos perm n) ≠ .missing) :
    SpecInv t perm (n + 1) (specStep t perm (fun _ => true) a n) := by
  have hM : ∀ r, matchSlots (colSl t perm r (List.range (n + 1))) [] =
      (matchSlots (colSl t perm r (List.range n)) []).bind
        (slotMatch (islot (t.slot (ScanSpec.colPos perm n))) (rowCol r n).toUInt64) := fun r => by
    rw [colSl_succ, matchSlots_snoc]
  unfold specStep
  cases hs : t.slot (ScanSpec.colPos perm n) with
  | missing => exact absurd hs hmiss
  | const x =>
    simp only [hs, islot] at hM
    have hT : ∀ r, Fits r → (matchSlots (colSl t perm r (List.range (n + 1))) []).isSome =
        (test a r && (rowCol r n == x.toNat)) := by
      intro r hr
      rw [hM r, bind_const, const_beq x _ (hr n hn), isSome_ite, h.test_eq r hr]
    have hR : ∀ r, Fits r → ∀ m, matchSlots (colSl t perm r (List.range (n + 1))) [] = some m →
        RowEq m (seenRow a r) := by
      intro r hr m hm
      rw [hM r, bind_const] at hm
      split at hm
      · exact h.row_eq r hr m hm
      · cases hm
    by_cases hl : a.leading = true
    · simp only [hl, if_true]
      refine ⟨by simp; have := h.keyLe; omega, fun _ => by simp [h.lead hl],
        fun ck hck => Nat.lt_succ_of_lt (h.checks ck hck), fun e he => ⟨Nat.lt_succ_of_lt (h.eqs e he).1,
          Nat.lt_succ_of_lt (h.eqs e he).2⟩, fun p hp => Nat.lt_succ_of_lt (h.seenLt p hp), h.seenVar, h.outVars,
        h.outCols, h.nodup, fun r hr => ?_, fun r hr m hm => hR r hr m hm⟩
      show testF (a.key.push x) a.checks a.eqs r = _
      rw [test_key, hT r hr, h.lead hl]
      rfl
    · simp only [hl, Bool.false_eq_true, if_false]
      refine ⟨Nat.le_succ_of_le h.keyLe, (fun h' => by cases h'),
        fun ck hck => ?_, fun e he => ⟨Nat.lt_succ_of_lt (h.eqs e he).1,
          Nat.lt_succ_of_lt (h.eqs e he).2⟩, fun p hp => Nat.lt_succ_of_lt (h.seenLt p hp), h.seenVar, h.outVars,
        h.outCols, h.nodup, fun r hr => ?_, fun r hr m hm => hR r hr m hm⟩
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hck
        rcases hck with hck | hck
        · exact Nat.lt_succ_of_lt (h.checks ck hck)
        · subst hck; exact Nat.lt_succ_self n
      · show testF a.key (a.checks.push (n, x)) a.eqs r = _
        rw [test_check, hT r hr]
        rfl
  | var v =>
    simp only [hs, islot] at hM
    cases hf : Array.find? (fun x => x.fst == v) a.seen with
    | some p =>
      obtain ⟨w, c0⟩ := p
      obtain ⟨hwv, hmem⟩ := find?_mem hf
      subst hwv
      have hc0 : c0 < n := h.seenLt _ hmem
      have hlk : ∀ r, idLookup w (seenRow a r) = some (rowCol r c0).toUInt64 := by
        intro r
        unfold seenRow
        rw [lookup_map_seen (fun c => (rowCol r c).toUInt64) w, Array.find?_toList, hf]
        rfl
      have hstep : ∀ r, Fits r → ∀ m, RowEq m (seenRow a r) →
          slotMatch (.var w) (rowCol r n).toUInt64 m = if rowCol r c0 == rowCol r n then some m else none := by
        intro r hr m hm
        simp only [slotMatch]
        rw [hm w, hlk r]
        dsimp only
        rw [toUInt64_beq _ _ (hr c0 (by omega)) (hr n hn)]
      simp only [hf]
      refine ⟨Nat.le_succ_of_le h.keyLe, (fun h' => by cases h'),
        fun ck hck => Nat.lt_succ_of_lt (h.checks ck hck), fun e he => ?_,
        fun p hp => Nat.lt_succ_of_lt (h.seenLt p hp), h.seenVar, h.outVars,
        h.outCols, h.nodup, fun r hr => ?_, fun r hr m hm => ?_⟩
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at he
        rcases he with he | he
        · exact ⟨Nat.lt_succ_of_lt (h.eqs e he).1, Nat.lt_succ_of_lt (h.eqs e he).2⟩
        · subst he; exact ⟨by simp; omega, by simp⟩
      · show testF a.key a.checks (a.eqs.push (c0, n)) r = _
        rw [test_eqs, hM r]
        rw [show testF a.key a.checks a.eqs r = test a r from rfl, h.test_eq r hr]
        cases hm : matchSlots (colSl t perm r (List.range n)) [] with
        | none => rfl
        | some m =>
          simp only [Option.bind_some, Option.isSome_some, Bool.true_and]
          rw [hstep r hr m (h.row_eq r hr m hm)]
          unfold eqk
          cases rowCol r c0 == rowCol r n <;> rfl
      · rw [hM r] at hm
        cases hm0 : matchSlots (colSl t perm r (List.range n)) [] with
        | none => rw [hm0] at hm; cases hm
        | some m0 =>
          rw [hm0, Option.bind_some, hstep r hr m0 (h.row_eq r hr m0 hm0)] at hm
          split at hm
          · rw [Option.some.injEq] at hm; rw [← hm]; exact h.row_eq r hr m0 hm0
          · cases hm
    | none =>
      have hnot := find?_none hf
      have hlk : ∀ r, idLookup v (seenRow a r) = none := by
        intro r
        unfold seenRow
        rw [lookup_map_seen (fun c => (rowCol r c).toUInt64) v, Array.find?_toList, hf]
        rfl
      simp only [hf, ↓reduceIte]
      refine ⟨Nat.le_succ_of_le h.keyLe, (fun h' => by cases h'),
        fun ck hck => Nat.lt_succ_of_lt (h.checks ck hck), fun e he => ⟨Nat.lt_succ_of_lt (h.eqs e he).1,
          Nat.lt_succ_of_lt (h.eqs e he).2⟩, fun p hp => ?_, fun p hp => ?_, ?_, ?_, ?_,
        fun r hr => ?_, fun r hr m hm => ?_⟩
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | hp
        · exact Nat.lt_succ_of_lt (h.seenLt p hp)
        · subst hp; exact Nat.lt_succ_self n
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | hp
        · exact h.seenVar p hp
        · subst hp; exact hs
      · rw [h.outVars, Array.map_push]
      · rw [h.outCols, Array.map_push]
      · rw [Array.toList_push, List.map_append, List.nodup_append]
        refine ⟨h.nodup, by simp, ?_⟩
        intro x hx y hy
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
        subst hy
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        exact hnot p hp
      · show test a r = _
        rw [hM r, h.test_eq r hr]
        cases hm : matchSlots (colSl t perm r (List.range n)) [] with
        | none => rfl
        | some m =>
          simp only [Option.bind_some, Option.isSome_some, slotMatch]
          rw [h.row_eq r hr m hm v, hlk r]
          rfl
      · rw [hM r] at hm
        cases hm0 : matchSlots (colSl t perm r (List.range n)) [] with
        | none => rw [hm0] at hm; cases hm
        | some m0 =>
          have hrow := h.row_eq r hr m0 hm0
          rw [hm0, Option.bind_some] at hm
          simp only [slotMatch] at hm
          rw [hrow v, hlk r] at hm
          cases hm
          intro w
          have hlk' := hlk r
          unfold seenRow at hlk' hrow ⊢
          simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
          rw [lookup_append]
          have e1 : idLookup w ((v, (rowCol r n).toUInt64) :: m0) =
              if v = w then some (rowCol r n).toUInt64 else idLookup w m0 := rfl
          have e2 : idLookup w [(v, (rowCol r n).toUInt64)] =
              if v = w then some (rowCol r n).toUInt64 else none := rfl
          rw [e1]
          by_cases hvw : v = w
          · subst hvw
            rw [hlk', if_pos rfl]
            show _ = idLookup v [(v, (rowCol r n).toUInt64)]
            rw [e2, if_pos rfl]
          · rw [if_neg hvw, hrow w]
            cases idLookup w (a.seen.toList.map fun p => (p.1, (rowCol r p.2).toUInt64)) with
            | some x => rfl
            | none => exact (e2.trans (if_neg hvw)).symm

/-- The invariant after the four columns. -/
theorem specInv_four (t : Pat) (perm : Nat) (hmiss : t.hasMissing = false) :
    SpecInv t perm 4 (specAcc t perm (fun _ => true)) := by
  have hm : ∀ c, c < 4 → t.slot (ScanSpec.colPos perm c) ≠ .missing := by
    intro c _ he
    unfold Pat.hasMissing at hmiss
    simp only [Bool.or_eq_false_iff] at hmiss
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hmiss
    generalize ScanSpec.colPos perm c = q at he
    match q with
    | 0 => rw [Pat.slot] at he; rw [he] at h1; exact absurd h1 (by decide)
    | 1 => rw [Pat.slot] at he; rw [he] at h2; exact absurd h2 (by decide)
    | 2 => rw [Pat.slot] at he; rw [he] at h3; exact absurd h3 (by decide)
    | _ + 3 => rw [show t.slot (_ + 3) = t.g from rfl] at he; rw [he] at h4; exact absurd h4 (by decide)
  simp only [specAcc, List.foldl_cons, List.foldl_nil]
  exact specInv_step t perm 3 (by omega) _ (specInv_step t perm 2 (by omega) _
    (specInv_step t perm 1 (by omega) _ (specInv_step t perm 0 (by omega) _ (specInv_init t perm)
      (hm 0 (by omega))) (hm 1 (by omega))) (hm 2 (by omega))) (hm 3 (by omega))

/-- The planner's scan of a pattern with no missing constant has the shape
    the scan theorems assume. -/
theorem specOk_mkSpec (t : Pat) (perm : Nat) (hmiss : t.hasMissing = false) :
    SpecOk (mkSpec t perm (fun _ => true)) := by
  have h := specInv_four t perm hmiss
  rw [mkSpec_eq]
  generalize specAcc t perm (fun _ => true) = A at h ⊢
  refine ⟨h.keyLe, fun ck hck => h.checks ck (Array.mem_toList_iff.mpr hck),
    fun e he => h.eqs e (Array.mem_toList_iff.mpr he), fun c hc => ?_, ?_⟩
  · simp only [specOf, h.outCols] at hc
    obtain ⟨p, hp, rfl⟩ := Array.mem_map.mp hc
    exact h.seenLt p (Array.mem_toList_iff.mpr hp)
  · simp [specOf, h.outVars, h.outCols]

theorem prefixCmpGo_iff (r : Row) (key : Array UInt64) :
    ∀ f j, key.size - j ≤ f →
      (prefixCmpGo r key f j = .eq ↔ ∀ i, j ≤ i → i < key.size → rowCol r i = key[i]!.toNat) := by
  intro f
  induction f with
  | zero => intro j hf; simp only [prefixCmpGo, true_iff]; intro i h1 h2; omega
  | succ f ih =>
    intro j hf
    simp only [prefixCmpGo]
    by_cases hj : j < key.size
    · rw [if_pos hj]
      by_cases h1 : rowCol r j < key[j]!.toNat
      · rw [if_pos h1]
        simp only [reduceCtorEq, false_iff]
        intro hall
        have := hall j (Nat.le_refl _) hj
        omega
      · rw [if_neg h1]
        by_cases h2 : key[j]!.toNat < rowCol r j
        · rw [if_pos h2]
          simp only [reduceCtorEq, false_iff]
          intro hall
          have := hall j (Nat.le_refl _) hj
          omega
        · rw [if_neg h2, ih (j + 1) (by omega)]
          constructor
          · intro hall i hji hi
            by_cases hij : i = j
            · subst hij; omega
            · exact hall i (by omega) hi
          · intro hall i hji hi
            exact hall i (by omega) hi
    · rw [if_neg hj]
      simp only [true_iff]
      intro i h1 h2; omega

theorem prefixCmp_iff (r : Row) (key : Array UInt64) :
    (prefixCmp r key == .eq) = (List.range key.size).all (fun j => rowCol r j == key[j]!.toNat) := by
  have := prefixCmpGo_iff r key key.size 0 (by omega)
  unfold prefixCmp
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, this, List.all_eq_true]
  constructor
  · intro h j hj
    exact beq_iff_eq.mpr (h j (Nat.zero_le _) (List.mem_range.mp hj))
  · intro h i _ hi
    exact beq_iff_eq.mp (h i (List.mem_range.mpr hi))

/-- The scan keeps a row exactly when the loop's tests pass on it. -/
theorem keep_eq_test (t : Pat) (perm : Nat) (hnamed : t.named = false) (r : Row) :
    keep (mkSpec t perm (fun _ => true)) r = test (specAcc t perm (fun _ => true)) r := by
  rw [mkSpec_eq]
  unfold keep test testF specOf
  simp only [hnamed, Bool.not_false, Bool.true_or, Bool.true_and]
  rw [prefixCmp_iff]

/-! ## A row of a permutation as a triple, and the model's match -/

open L4Factoidal.Storage.Sbm11.IdPath (IdTriple)

/-- The triple (subject, predicate, object) of a row of permutation `perm`
    (`permOrder`: 0 PSO, 1 POS, 2 SPO, 3 OSP). -/
def tripleOf (perm : Nat) (r : Row) : IdTriple :=
  match perm with
  | 0 => (r.c1.toUInt64, r.c0.toUInt64, r.c2.toUInt64)
  | 1 => (r.c2.toUInt64, r.c0.toUInt64, r.c1.toUInt64)
  | 2 => (r.c0.toUInt64, r.c1.toUInt64, r.c2.toUInt64)
  | _ => (r.c1.toUInt64, r.c2.toUInt64, r.c0.toUInt64)

/-- A triple pattern of the id path as the model's pattern. -/
def ipatOf (t : Pat) : IPat := ⟨islot t.s, islot t.p, islot t.o⟩

/-- The listing of the triples of the graph `gid` in the row order of a
    permutation's rows. -/
def permListing (perm : Nat) (gid : UInt64) (R : List Row) : List IdTriple :=
  (R.filter fun r => r.g == gid.toNat).map (tripleOf perm)

/-- The four columns of a scan are the subject, predicate and object
    positions and the graph, in another order. -/
theorem colSl_perm (t : Pat) (perm : Nat) (hperm : perm < 4) (r : Row) :
    (colSl t perm r (List.range 4)).Perm
      ((ipatOf t).slots (tripleOf perm r) ++ [(islot t.g, r.g.toUInt64)]) := by
  match perm, hperm with
  | 0, _ =>
    show List.Perm [(islot t.p, r.c0.toUInt64), (islot t.s, r.c1.toUInt64), (islot t.o, r.c2.toUInt64),
      (islot t.g, r.g.toUInt64)] [(islot t.s, r.c1.toUInt64), (islot t.p, r.c0.toUInt64),
      (islot t.o, r.c2.toUInt64), (islot t.g, r.g.toUInt64)]
    exact List.Perm.swap _ _ _
  | 1, _ =>
    show List.Perm [(islot t.p, r.c0.toUInt64), (islot t.o, r.c1.toUInt64), (islot t.s, r.c2.toUInt64),
      (islot t.g, r.g.toUInt64)] [(islot t.s, r.c2.toUInt64), (islot t.p, r.c0.toUInt64),
      (islot t.o, r.c1.toUInt64), (islot t.g, r.g.toUInt64)]
    exact List.perm_middle (l₁ := [(islot t.p, r.c0.toUInt64), (islot t.o, r.c1.toUInt64)])
  | 2, _ => exact List.Perm.refl _
  | 3, _ =>
    show List.Perm [(islot t.o, r.c0.toUInt64), (islot t.s, r.c1.toUInt64), (islot t.p, r.c2.toUInt64),
      (islot t.g, r.g.toUInt64)] [(islot t.s, r.c1.toUInt64), (islot t.p, r.c2.toUInt64),
      (islot t.o, r.c0.toUInt64), (islot t.g, r.g.toUInt64)]
    exact (List.perm_middle (l₁ := [(islot t.s, r.c1.toUInt64), (islot t.p, r.c2.toUInt64)])).symm

/-- **One row.** For a pattern of the graph `gid` (no missing constant, not
    over the named graphs), the scan keeps a row exactly when the model
    matches the row's triple in that graph, and the scan's solution mapping
    of the row is the model's, up to `RowEq`. -/
theorem row_opt (t : Pat) (perm : Nat) (hperm : perm < 4) (gid : UInt64) (htg : t.g = .const gid)
    (hnamed : t.named = false) (hmiss : t.hasMissing = false) (r : Row) (hr : Fits r) :
    OptRowEq (if keep (mkSpec t perm (fun _ => true)) r then some (seenRow (specAcc t perm (fun _ => true)) r) else none)
      (if r.g == gid.toNat then idTpMatch (ipatOf t) (tripleOf perm r) [] else none) := by
  have hI := specInv_four t perm hmiss
  rw [keep_eq_test t perm hnamed, hI.test_eq r hr]
  have hP := IdLeaf.matchSlots_perm (colSl_perm t perm hperm r) []
  rw [matchSlots_snoc, htg, islot, bind_const, const_beq gid r.g (hr 3 (by omega))] at hP
  have hR := hI.row_eq r hr
  cases hm : matchSlots (colSl t perm r (List.range 4)) [] with
  | none =>
    rw [hm] at hP
    simp only [Option.isSome_none, Bool.false_eq_true, if_false]
    unfold idTpMatch
    revert hP
    cases (r.g == gid.toNat) <;> cases matchSlots ((ipatOf t).slots (tripleOf perm r)) [] <;>
      simp [OptRowEq]
  | some m =>
    rw [hm] at hP
    simp only [Option.isSome_some, if_true]
    unfold idTpMatch
    revert hP
    cases (r.g == gid.toNat) <;> cases matchSlots ((ipatOf t).slots (tripleOf perm r)) [] <;>
      simp only [OptRowEq, if_true, Bool.false_eq_true, if_false, imp_self]
    intro h
    exact TableTheorems.RowEq.trans (TableTheorems.RowEq.symm (hR m hm)) h

/-! ## The table of one triple pattern against the model -/

open L4Factoidal.Storage.Sbm11.TableTheorems (NoUnbound)
open L4Factoidal.Storage.Sbm11.IdGroup (Pw)

theorem filter_map_eq_filterMap {α β : Type} (p : α → Bool) (f : α → β) :
    ∀ (l : List α), (l.filter p).map f = l.filterMap fun x => if p x then some (f x) else none
  | [] => rfl
  | x :: l => by
    simp only [List.filter_cons, List.filterMap_cons]
    cases p x <;> simp [filter_map_eq_filterMap p f l]

theorem filterMap_map_eq {α β γ : Type} (f : α → β) (g : β → Option γ) (l : List α) :
    (l.map f).filterMap g = l.filterMap (g ∘ f) := by
  rw [List.filterMap_map]

theorem filterMap_filter_eq {α γ : Type} (p : α → Bool) (g : α → Option γ) :
    ∀ (l : List α), (l.filter p).filterMap g = l.filterMap fun x => if p x then g x else none
  | [] => rfl
  | x :: l => by
    simp only [List.filter_cons]
    cases h : p x
    · simp [h, filterMap_filter_eq p g l]
    · simp only [if_true]
      rw [List.filterMap_cons, List.filterMap_cons, if_pos h, filterMap_filter_eq p g l]

/-- The rows of the permutation of an admitted store fit in words. -/
theorem rows_fit (prb : ByteArray) (ms : List BlockMeta) :
    ∀ r ∈ ms.flatMap (blockRows prb), Fits r := by
  intro r hr c hc
  obtain ⟨b, _, hrb⟩ := List.mem_flatMap.mp hr
  unfold blockRows at hrb
  split at hrb
  · rename_i cols h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrb
    obtain ⟨-, hv, -⟩ := admitted_facts prb b cols h
    rw [rowCol_row]
    exact hv c i hc (List.mem_range.mp hi)
  · simp at hrb

theorem filterMap_some {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ (l : List α), (∀ x ∈ l, f x = some (g x)) → l.filterMap f = l.map g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.filterMap_cons, h x List.mem_cons_self, List.map_cons,
      filterMap_some f g l (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem tabTuples_at (T : Table) (L : List (List Nat)) (h : tabTuples T = L) :
    T.rows = L.length ∧ ∀ i, i < T.rows → ∀ c, c < T.cols.size → (T.at c i).toNat = L[i]![c]! := by
  subst h
  refine ⟨by simp [tabTuples], fun i hi c hc => ?_⟩
  unfold tabTuples
  rw [getElem!_pos _ i (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range]
  rw [getElem!_pos _ c (by simpa using hc)]
  simp

theorem toUInt64_of_toNat (x : UInt64) (n : Nat) (h : x.toNat = n) : x = n.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [h]
  have := x.toNat_lt
  rw [← h]
  simp

/-- The rows of the table, as solution mappings, are the solution mappings
    `seenRow` of the rows the scan keeps. -/
theorem idRows_eq (t : Pat) (perm : Nat) (hmiss : t.hasMissing = false) (gid : UInt64) (htg : t.g = .const gid)
    (T : Table) (K : List Row) (hT : TableOf (mkSpec t perm (fun _ => true)) T (K.map (proj (mkSpec t perm (fun _ => true)))))
    (hfit : ∀ r ∈ K, Fits r) (hnz : ∀ r ∈ K, ∀ c, c < 3 → rowCol r c ≠ 0) :
    T.idRows = K.map (seenRow (specAcc t perm (fun _ => true))) ∧ NoUnbound T := by
  have hI := specInv_four t perm hmiss
  have hspec := mkSpec_eq t perm (fun _ => true)
  generalize hA : specAcc t perm (fun _ => true) = A at hI hspec
  obtain ⟨hrows, hat⟩ := tabTuples_at T _ hT.tuples
  rw [List.length_map] at hrows
  have hvars : T.vars = A.seen.map (·.1) := by rw [hT.vars, hspec]; exact hI.outVars
  have hsz : T.cols.size = A.seen.size := by rw [hT.size, hspec]; simp [specOf, hI.outVars]
  have hvsz : T.vars.size = A.seen.size := by rw [hvars]; simp
  -- the seen columns are subject, predicate or object columns
  have hlt3 : ∀ c, c < A.seen.size → A.seen[c]!.2 < 3 := by
    intro c hc
    have hm : A.seen[c]! ∈ A.seen.toList := by rw [getElem!_pos A.seen c hc]; simp
    have hv := hI.seenVar _ hm
    have hl := hI.seenLt _ hm
    by_cases h3 : A.seen[c]!.2 = 3
    · rw [h3, show ScanSpec.colPos perm 3 = 3 from rfl, show t.slot 3 = t.g from rfl, htg] at hv
      cases hv
    · omega
  have hval : ∀ i, i < K.length → ∀ c, c < A.seen.size →
      T.at c i = (rowCol K[i]! A.seen[c]!.2).toUInt64 := by
    intro i hi c hc
    apply toUInt64_of_toNat
    rw [hat i (by omega) c (by omega), getElem!_pos _ i (by simpa using hi), List.getElem_map]
    unfold proj
    rw [hspec]
    simp only [specOf]
    rw [hI.outCols]
    rw [getElem!_pos _ c (by simp; exact hc)]
    simp only [List.getElem_map, List.getElem_range, Array.size_map]
    rw [getElem!_pos _ i hi, getElem!_pos (A.seen.map (·.2)) c (by simp; exact hc),
      getElem!_pos A.seen c hc]
    simp
  have hne : ∀ i, i < K.length → ∀ c, c < A.seen.size → T.at c i ≠ OptJoin.unbound := by
    intro i hi c hc he
    rw [hval i hi c hc] at he
    have hK : K[i]! ∈ K := by rw [getElem!_pos K i hi]; exact List.getElem_mem hi
    have h1 := hnz _ hK _ (hlt3 c hc)
    have h2 := hfit _ hK (A.seen[c]!.2) (by have := hlt3 c hc; omega)
    have : (rowCol K[i]! A.seen[c]!.2).toUInt64.toNat = 0 := by rw [he]; rfl
    rw [ScanFoldTheorems.uint64_toNat_toUInt64 _ h2] at this
    exact h1 this
  refine ⟨?_, fun c i hc hi => hne i (by omega) c (by omega)⟩
  unfold Table.idRows
  apply List.ext_getElem
  · simp [hrows]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have hi : i < K.length := by simpa using h2
    unfold Table.idRow seenRow
    rw [filterMap_some _ (fun c => (T.vars[c]!, T.at c i)) _ ?_]
    · apply List.ext_getElem
      · simp [hvsz]
      · intro c hc1 hc2
        simp only [List.getElem_map, List.getElem_range]
        have hc : c < A.seen.size := by simpa using hc2
        rw [hval i hi c hc, getElem!_pos K i hi, hvars, getElem!_pos _ c (by simpa using hc),
          getElem!_pos A.seen c hc]
        simp
    · intro c hc
      have hc' : c < A.seen.size := by rw [← hvsz]; exact List.mem_range.mp hc
      rw [if_neg (by rw [beq_iff_eq]; exact hne i hi c hc')]

/-! ## The order of the table -/

/-- The rows of an admitted permutation are strictly increasing. -/
theorem rows_sorted (prb : ByteArray) (ms : List BlockMeta) (hadm : prmAdmitted perm ms = true)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols) :
    (ms.flatMap (blockRows prb)).Pairwise (fun a b => a.lt b = true) := by
  have hch : chainGo prbHeaderBytes ms = true := by
    simp only [prmAdmitted, Bool.and_eq_true] at hadm
    exact hadm.1.1.2
  have hbw : ∀ b ∈ ms, ∀ x ∈ blockRows prb b, b.first.le x = true ∧ x.le b.last = true := by
    intro b hb x hx
    obtain ⟨cols, h⟩ := hblocks b hb
    unfold blockRows at hx
    rw [h] at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact row_between prb b cols h i (List.mem_range.mp hi)
  rw [List.pairwise_flatMap]
  constructor
  · intro b hb
    obtain ⟨cols, h⟩ := hblocks b hb
    unfold blockRows
    rw [h]
    obtain ⟨-, -, -, -, -, hs⟩ := admitted_facts prb b cols h
    rw [List.pairwise_map]
    apply List.Pairwise.imp_of_mem _ (List.pairwise_lt_range (n := b.rows))
    intro i j _ hj hij
    exact hs i j hij (List.mem_range.mp hj)
  · apply (ScanTheorems.chainGo_pairwise ms _ hch).imp_of_mem
    intro a b ha hb hab x hx y hy
    exact ScanTheorems.lt_of_lt_of_le (ScanTheorems.lt_of_le_of_lt (hbw a ha x hx).2 hab) (hbw b hb y hy).1

/-- Of two rows in order that agree on the columns before `k`, column `k` is
    in order. -/
theorem lt_col_le (a b : Row) (h : a.lt b = true) (k : Nat) (hk : k < 4)
    (heq : ∀ j, j < k → rowCol a j = rowCol b j) : rowCol a k ≤ rowCol b k := by
  rw [ScanTheorems.lt_iff] at h
  match k, hk with
  | 0, _ => show a.c0 ≤ b.c0; omega
  | 1, _ =>
    have e0 := heq 0 (by omega)
    show a.c1 ≤ b.c1
    simp only [rowCol] at e0; omega
  | 2, _ =>
    have e0 := heq 0 (by omega)
    have e1 := heq 1 (by omega)
    show a.c2 ≤ b.c2
    simp only [rowCol] at e0 e1; omega
  | 3, _ =>
    have e0 := heq 0 (by omega)
    have e1 := heq 1 (by omega)
    have e2 := heq 2 (by omega)
    show a.g ≤ b.g
    simp only [rowCol] at e0 e1 e2; omega

/-- A row the scan keeps holds the key in the key columns. -/
theorem keep_key (spec : ScanSpec) (r : Row) (h : keep spec r = true) :
    ∀ j, j < spec.key.size → rowCol r j = spec.key[j]!.toNat := by
  have hp := ScanFoldTheorems.keep_prefix spec r h
  have := (prefixCmpGo_iff r spec.key spec.key.size 0 (by omega)).mp hp
  exact fun j hj => this j (Nat.zero_le _) hj

/-- The table of a scan is in the order its sort variable says. -/
theorem scanTable_sortOk (t : Pat) (perm : Nat) (hmiss : t.hasMissing = false)
    (T : Table) (K : List Row) (hT : TableOf (mkSpec t perm (fun _ => true)) T (K.map (proj (mkSpec t perm (fun _ => true)))))
    (hK : K.Pairwise (fun a b => a.lt b = true)) (hkeep : ∀ r ∈ K, keep (mkSpec t perm (fun _ => true)) r = true)
    (hnd : T.vars.toList.Nodup) :
    TableTheorems.SortOk T := by
  generalize hS : mkSpec t perm (fun _ => true) = spec at hT hkeep
  have hspec : SpecOk spec := by rw [← hS]; exact specOk_mkSpec t perm hmiss
  intro v c hsv hidx x y hxy hy
  obtain ⟨hrows, hat⟩ := tabTuples_at T _ hT.tuples
  rw [List.length_map] at hrows
  rw [hT.sortVar] at hsv
  unfold sortVarOf at hsv
  cases ho : spec.outCols[0]? with
  | none => rw [ho] at hsv; cases hsv
  | some c0 =>
    rw [ho] at hsv
    simp only at hsv
    split at hsv
    · rename_i hc0
      have hc0' : c0 = spec.key.size := by simpa using hc0
      have hout0 : spec.outVars[0]? = some v := hsv
      have hvsz : 0 < spec.outVars.size := by
        cases hh : spec.outVars[0]? with
        | none => rw [hh] at hout0; cases hout0
        | some _ => exact (Array.getElem?_eq_some_iff.mp hh).1
      -- the column of `v` is column 0
      have hv0 : T.vars[0]! = v := by
        rw [hT.vars, getElem!_pos spec.outVars 0 hvsz]
        exact (Array.getElem?_eq_some_iff.mp hout0).2
      obtain ⟨hc, hcv⟩ := TableTheorems.idx_some hidx
      have hceq : c = 0 := TableTheorems.nodup_idx hnd hc (by rw [hT.vars]; exact hvsz) (by rw [hcv, hv0])
      subst hceq
      have hcols : 0 < T.cols.size := by rw [hT.size]; exact hvsz
      rw [hat x (by omega) 0 hcols, hat y hy 0 hcols]
      have hxK : x < K.length := by omega
      have hyK : y < K.length := by omega
      rw [getElem!_pos _ x (by simpa using hxK), getElem!_pos _ y (by simpa using hyK)]
      simp only [List.getElem_map]
      unfold proj
      have hoc : 0 < spec.outCols.size := by rw [← hspec.outVars]; exact hvsz
      rw [getElem!_pos _ 0 (by simpa using hoc), getElem!_pos _ 0 (by simpa using hoc)]
      simp only [List.getElem_map, List.getElem_range]
      have hc0e : spec.outCols[0]! = c0 := by
        rw [getElem!_pos spec.outCols 0 hoc]
        exact (Array.getElem?_eq_some_iff.mp ho).2
      rw [hc0e, hc0']
      have hk4 : spec.key.size < 4 := by
        have := hspec.outCols spec.outCols[0] (Array.getElem_mem hoc)
        rw [← getElem!_pos spec.outCols 0 hoc, hc0e, hc0'] at this
        exact this
      rcases Nat.lt_or_eq_of_le hxy with hlt | heq
      · apply lt_col_le K[x] K[y] (List.pairwise_iff_getElem.mp hK x y hxK hyK hlt) _ hk4
        intro j hj
        rw [keep_key spec _ (hkeep _ (List.getElem_mem hxK)) j hj,
          keep_key spec _ (hkeep _ (List.getElem_mem hyK)) j hj]
      · subst heq; exact Nat.le_refl _
    · cases hsv

/-- The solution mappings of the rows a scan keeps are, row for row, the
    model's scan of the pattern over the permutation's listing. -/
theorem keptRows_pw (t : Pat) (perm : Nat) (hperm : perm < 4) (gid : UInt64) (htg : t.g = .const gid)
    (hnamed : t.named = false) (hmiss : t.hasMissing = false) (R : List Row) (hfit : ∀ r ∈ R, Fits r) :
    Pw RowEq ((R.filter (keep (mkSpec t perm (fun _ => true)))).map (seenRow (specAcc t perm (fun _ => true))))
      (scanRows (ipatOf t) (permListing perm gid R)) := by
  rw [filter_map_eq_filterMap]
  unfold scanRows IdLeaf.idEvalTP permListing
  rw [List.filterMap_map, filterMap_filter_eq]
  apply IdLeaf.pw_filterMap
  intro r hr
  exact row_opt t perm hperm gid htg hnamed hmiss r (hfit r hr)

/-- The sort variable of a scan is bound, in the solution mapping of a row,
    to the row's column `key.size`. -/
theorem seen_sortVar (t : Pat) (perm : Nat) (hmiss : t.hasMissing = false) (v : String)
    (hv : sortVarOf (mkSpec t perm (fun _ => true)) = some v) (r : Row) :
    idLookup v (seenRow (specAcc t perm (fun _ => true)) r) =
      some (rowCol r (mkSpec t perm (fun _ => true)).key.size).toUInt64 := by
  have hI := specInv_four t perm hmiss
  have hspec := mkSpec_eq t perm (fun _ => true)
  generalize specAcc t perm (fun _ => true) = A at hI hspec ⊢
  rw [hspec] at hv ⊢
  unfold sortVarOf at hv
  rw [show (specOf perm t.named A).outCols = A.outCols from rfl,
    show (specOf perm t.named A).outVars = A.outVars from rfl,
    show (specOf perm t.named A).key = A.key from rfl] at hv
  rw [show (specOf perm t.named A).key = A.key from rfl]
  rw [hI.outCols, hI.outVars] at hv
  cases hs : A.seen.toList with
  | nil =>
    have : A.seen = #[] := by
      apply Array.ext'; exact hs
    rw [this] at hv; simp at hv
  | cons p rest =>
    have h0 : A.seen[0]? = some p := by
      rw [← Array.getElem?_toList, hs]; rfl
    rw [Array.getElem?_map, h0] at hv
    simp only [Option.map_some] at hv
    by_cases hc : (p.snd == A.key.size) = true
    · rw [if_pos hc] at hv
      rw [Array.getElem?_map, h0] at hv
      simp only [Option.map_some, Option.some.injEq] at hv
      subst hv
      unfold seenRow
      rw [hs]
      have hc' : p.2 = A.key.size := by simpa using hc
      show (if p.1 = p.1 then some (rowCol r p.2).toUInt64 else _) = _
      rw [if_pos rfl, hc']
    · rw [if_neg hc] at hv; cases hv

/-- A permutation of an in-memory store (`m = Id`): the store answers the
    PRM1 range queries and the PRB1 reads from the arrays `ms` and `prb`
    (`PrmRangeTheorems.rangeM_array` for the range), the permutation has no
    delta overlay, activation admitted its PRM1 entries and every block, and
    no subject, predicate or object id of a row is 0 (`OptJoin.unbound`, the
    id of no term). -/
structure PermMem (st : Store Id) (perm : Nat) (prb : ByteArray) (ms : List BlockMeta) : Prop where
  range : ∀ key, st.blocksForRange perm key = pure (metasFor ms.toArray key)
  count : st.blockCount perm = pure ms.length
  bytes : ∀ off len, st.prb perm off len = pure (prb.extract off (off + len))
  ovl : (st.ovl perm).isEmpty = true
  adm : prmAdmitted perm ms = true
  blocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols
  nz : ∀ r ∈ ms.flatMap (blockRows prb), ∀ c, c < 3 → rowCol r c ≠ 0

/-- **The table of one triple pattern (lemma L4k).** For a triple pattern of
    the id path over one graph `gid` (a constant graph slot, not over the
    named graphs, no constant without an id), the scan `scanTableM` of the
    planner's specification (`mkSpec`, every variable kept) from any of the
    four permutations of an in-memory store returns a well-formed table with
    no id 0, whose sort variable is the scan's, and whose rows, as solution
    mappings, are row for row (`RowEq`) the model's scan of the pattern
    (`IdLeaf.scanRows`) over the listing of the graph's triples in that
    permutation's row order (`permListing`). -/
theorem scanTable_model (st : Store Id) (t : Pat) (perm : Nat) (hperm : perm < 4) (gid : UInt64)
    (htg : t.g = .const gid) (hnamed : t.named = false) (hmiss : t.hasMissing = false)
    (prb : ByteArray) (ms : List BlockMeta) (hst : PermMem st perm prb ms) :
    ∃ T stats, scanTableM st (mkSpec t perm (fun _ => true)) = pure (T, stats) ∧ T.WF ∧ NoUnbound T ∧
      T.vars = (mkSpec t perm (fun _ => true)).outVars ∧
      T.sortVar = sortVarOf (mkSpec t perm (fun _ => true)) ∧ TableTheorems.SortOk T ∧
      Pw RowEq T.idRows (scanRows (ipatOf t) (permListing perm gid (ms.flatMap (blockRows prb)))) := by
  have hspec := specOk_mkSpec t perm hmiss
  have hperm' : (mkSpec t perm (fun _ => true)).perm = perm := by rw [mkSpec_eq]; rfl
  obtain ⟨T, stats, he, hT⟩ := scanTableM_spec st (mkSpec t perm (fun _ => true)) hspec prb ms
    (by rw [hperm']; exact hst.range _) (by rw [hperm']; exact hst.count) (by rw [hperm']; exact hst.bytes)
    (by rw [hperm']; exact hst.ovl) (by rw [hperm']; exact hst.adm) hst.blocks
  generalize hR : ms.flatMap (blockRows prb) = R at hT ⊢
  have hfitR : ∀ r ∈ R, Fits r := by rw [← hR]; exact rows_fit prb ms
  have hsorted : R.Pairwise (fun a b => a.lt b = true) := by rw [← hR]; exact rows_sorted prb ms hst.adm hst.blocks
  have hnzR : ∀ r ∈ R, ∀ c, c < 3 → rowCol r c ≠ 0 := by rw [← hR]; exact hst.nz
  obtain ⟨hrows, hnu⟩ := idRows_eq t perm hmiss gid htg T (R.filter (keep (mkSpec t perm (fun _ => true)))) hT
    (fun r hr => hfitR r ((List.mem_filter.mp hr).1)) (fun r hr => hnzR r ((List.mem_filter.mp hr).1))
  have hI := specInv_four t perm hmiss
  have hnd : T.vars.toList.Nodup := by
    rw [hT.vars, mkSpec_eq]
    simp only [specOf, hI.outVars]
    simpa using hI.nodup
  refine ⟨T, stats, he, ⟨by rw [hT.size, hT.vars], hT.bytes, hnd⟩, hnu, hT.vars, hT.sortVar,
    scanTable_sortOk t perm hmiss T _ hT (hsorted.filter _) (fun r hr => (List.mem_filter.mp hr).2) hnd, ?_⟩
  · rw [hrows]
    exact keptRows_pw t perm hperm gid htg hnamed hmiss R hfitR

end L4Factoidal.Storage.Sbm11.ScanTableTheorems

#print axioms L4Factoidal.Storage.Sbm11.ScanTableTheorems.scanTable_model
#print axioms L4Factoidal.Storage.Sbm11.ScanTableTheorems.scanTableM_spec
#print axioms L4Factoidal.Storage.Sbm11.ScanTableTheorems.scanFoldM_R
#print axioms L4Factoidal.Storage.Sbm11.ScanTableTheorems.row_opt