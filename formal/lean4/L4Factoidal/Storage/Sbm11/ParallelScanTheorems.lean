/-
L4Factoidal.Storage.Sbm11.ParallelScanTheorems — the parallel block scan
gives the single scan's answer (stage 1 of issue 799; record
docs/designissues/2026-10-12-parallel-block-scans.md).

`parallel_acc_eq`: a selected-block list `L` cut into chunks by
`ParallelScan.chunksOf` and scanned chunk by chunk, each from an empty
accumulator (the loop `IdQuery.scanListM` runs, one per task), gives the
concatenation of the chunk results in chunk order, and that equals the
single scan of `L` (`ScanFoldTheorems.forIn_blocks`, which is lemma L4e's
loop for any list of selected blocks). The statement is over lists of rows
(`blockOut`: the output tuples of one block). No hypothesis states the
conclusion: the hypotheses are the activation checks of L4e and the bound
`hL` that the selected blocks lie in the permutation.

The theorem is over `Store Id`, as L4e is. The native driver runs the same
generic code in `IO`; the equality of that instance with `Id` is not proved
here (the answer tests in `tests/sbm11/` check it on the native binary).

Table form (the production accumulator is `Table.append`, not lists): see
the record, section "What is open".
-/
import L4Factoidal.Storage.Sbm11.ParallelScan
import L4Factoidal.Storage.Sbm11.ScanFoldTheorems

namespace L4Factoidal.Storage.Sbm11.ParallelScanTheorems

open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.ScanFoldTheorems
open L4Factoidal.Storage.Sbm11.ParallelScan (chunksOf chunksOf_flatten mem_of_mem_chunksOf)

/-- The state a chunk scan starts from (`scanListM` with `init = []`). -/
def chunkInit : ScanState (List (List Nat)) :=
  { acc := [], stats := {}, insPos := 0, stopped := false }

/-- A `flatMap` of per-chunk `flatMap`s is the `flatMap` of the flattened
    chunks. -/
theorem flatMap_flatMap_flatten {α β : Type} (xss : List (List α)) (F : α → List β) :
    xss.flatMap (fun X => X.flatMap F) = xss.flatten.flatMap F := by
  induction xss with
  | nil => rfl
  | cons X xs ih => simp [List.flatten_cons, List.flatMap_append, ih]

/-- Pointwise equal functions give equal `flatMap`s over a list whose members
    all satisfy the equation. -/
theorem flatMap_congr_mem {α β : Type} (xss : List (List α)) (f g : List α → List β)
    (h : ∀ X ∈ xss, f X = g X) : xss.flatMap f = xss.flatMap g := by
  induction xss with
  | nil => rfl
  | cons X xs ih =>
    simp only [List.flatMap_cons]
    rw [h X (by simp), ih (fun Y hY => h Y (by simp [hY]))]

/-- The accumulator of the scan of the selected blocks `X`, from `chunkInit`,
    as an `Except` value (the loop of `IdQuery.scanListM` in the `Id` store). -/
def scanAccOf (st : Store Id) (spec : ScanSpec) (fill : Bool) (den : Chunk → List (List Nat))
    (ms : List BlockMeta) (sortVar : Option String) (ox : OvCtx) (X : List Nat) :
    Except String (List (List Nat)) :=
  (Id.run (ExceptT.run (forIn X chunkInit
    (scanBlockM st spec fill (collectWith den) ms.toArray sortVar ox)))).map (·.acc)

/-- `mapM` in `Except` of a total function with `.ok` values. -/
theorem mapM_except_ok {α β ε : Type} (f : α → Except ε β) (g : α → β) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = .ok (g x)) → xs.mapM f = .ok (xs.map g)
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons, h x (by simp), List.map_cons]
    rw [mapM_except_ok f g xs (fun y hy => h y (by simp [hy]))]
    rfl

/-- **Parallel scan equals single scan (list form).** For a list `L` of
    selected blocks of an admitted permutation, split into chunks of at most
    `c` blocks, the chunk scans (each from an empty accumulator, in chunk
    order) concatenate to the single scan's accumulator over `L`. -/
theorem parallel_acc_eq (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) (fill : Bool)
    (den : Chunk → List (List Nat)) (hden : DenOk spec fill den)
    (prb : ByteArray) (ms : List BlockMeta)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hadm : prmAdmitted spec.perm ms = true)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols)
    (sortVar : Option String) (ox : OvCtx) (hon : ox.on = false)
    (L : List Nat) (hL : ∀ k ∈ L, k < ms.length) (c : Nat) :
    ((chunksOf c L).mapM (scanAccOf st spec fill den ms sortVar ox)).map List.flatten
      = scanAccOf st spec fill den ms sortVar ox L := by
  have hch : chainGo prbHeaderBytes ms = true := by
    simp only [prmAdmitted, Bool.and_eq_true] at hadm
    exact hadm.1.1.2
  have hfits : ∀ b ∈ ms, b.rows ≤ two64 := by
    intro b hb
    have := chainGo_fits ms _ hch b hb
    simp only [metaFits, Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, h32⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := this
    exact Nat.le_of_lt (Nat.lt_of_lt_of_le h32 (by decide))
  -- every chunk is a sub-list of L
  have hsub : ∀ X ∈ chunksOf c L, ∀ k ∈ X, k < ms.length :=
    fun X hX k hk => hL k (mem_of_mem_chunksOf c L hX hk)
  have hchunk : ∀ X ∈ chunksOf c L,
      scanAccOf st spec fill den ms sortVar ox X
        = .ok (X.flatMap (fun k => blockOut spec prb ms[k]!)) := by
    intro X hX
    obtain ⟨s', h1, h2, _⟩ := forIn_blocks st spec hspec fill den hden prb ms hprb hfits hblocks
      sortVar ox hon X (hsub X hX) chunkInit
    have h2' : s'.acc = X.flatMap (fun k => blockOut spec prb ms[k]!) := by
      rw [h2]; rfl
    unfold scanAccOf
    rw [h1]
    show Except.ok s'.acc = _
    rw [h2']
  obtain ⟨s', h1, h2, _⟩ := forIn_blocks st spec hspec fill den hden prb ms hprb hfits hblocks
    sortVar ox hon L hL chunkInit
  have h2' : s'.acc = L.flatMap (fun k => blockOut spec prb ms[k]!) := by
    rw [h2]; rfl
  have hwhole : scanAccOf st spec fill den ms sortVar ox L
      = .ok (L.flatMap (fun k => blockOut spec prb ms[k]!)) := by
    unfold scanAccOf
    rw [h1]
    show Except.ok s'.acc = _
    rw [h2']
  rw [hwhole, mapM_except_ok _ (fun X => X.flatMap (fun k => blockOut spec prb ms[k]!)) _ hchunk]
  show Except.ok ((chunksOf c L).map (fun X => X.flatMap (fun k => blockOut spec prb ms[k]!))).flatten
    = Except.ok (L.flatMap (fun k => blockOut spec prb ms[k]!))
  congr 1
  calc ((chunksOf c L).map (fun X => X.flatMap (fun k => blockOut spec prb ms[k]!))).flatten
      = (chunksOf c L).flatMap (fun X => X.flatMap (fun k => blockOut spec prb ms[k]!)) := rfl
    _ = (chunksOf c L).flatten.flatMap (fun k => blockOut spec prb ms[k]!) :=
        flatMap_flatMap_flatten _ _
    _ = L.flatMap (fun k => blockOut spec prb ms[k]!) := by rw [chunksOf_flatten]

#print axioms parallel_acc_eq

end L4Factoidal.Storage.Sbm11.ParallelScanTheorems
