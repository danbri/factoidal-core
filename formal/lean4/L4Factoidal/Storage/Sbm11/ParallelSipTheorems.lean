/-
L4Factoidal.Storage.Sbm11.ParallelSipTheorems — the parallel scan with
candidates gives the single scan's answer (issue 799, OKR batch 3 KR 1.2;
record docs/designissues/2026-10-12-parallel-block-scans.md).

`parallel_sip_acc_eq` is `ParallelScanTheorems.parallel_acc_eq` for
`IdQuery.scanBlockSipM`: a selected-block list `L` cut into chunks by
`ParallelScan.chunksOf` and scanned chunk by chunk with the candidates, each
from an empty accumulator (the loop `IdQuery.scanListSipM` runs, one per
task), gives the concatenation of the chunk results in chunk order, and that
equals the single scan of `L` (`SipScanTheorems.forIn_blocks_sip`). The
statement is over lists of rows (`blockOutSip`). No hypothesis states the
conclusion: the hypotheses are those of `forIn_blocks_sip` (the activation
checks, the candidates in non-decreasing order, no delta overlay) and the
bound `hL` that the selected blocks lie in the permutation. As for stage 1,
the theorem is over `Store Id`; the `Table` accumulator and the `IO`
instance are checked by the answer tests of `tests/sbm11/threads.sh`.
-/
import L4Factoidal.Storage.Sbm11.ParallelScanTheorems
import L4Factoidal.Storage.Sbm11.SipScanTheorems

namespace L4Factoidal.Storage.Sbm11.ParallelSipTheorems

open L4Factoidal (two64)
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.ScanFoldTheorems
open L4Factoidal.Storage.Sbm11.SipScanTheorems
open L4Factoidal.Storage.Sbm11.ParallelScanTheorems (chunkInit flatMap_flatMap_flatten mapM_except_ok)
open L4Factoidal.Storage.Sbm11.ParallelScan (chunksOf chunksOf_flatten mem_of_mem_chunksOf)

/-- The accumulator of the scan with candidates of the selected blocks `X`,
    from `chunkInit` (the loop of `IdQuery.scanListSipM` in the `Id` store). -/
def scanAccSipOf (st : Store Id) (spec : ScanSpec) (cands : Array UInt64)
    (ms : List BlockMeta) (sortVar : Option String) (ox : OvCtx) (X : List Nat) :
    Except String (List (List Nat)) :=
  (Id.run (ExceptT.run (forIn X chunkInit
    (scanBlockSipM st spec cands (collectWith colTuples) ms.toArray sortVar ox)))).map (·.acc)

/-- **Parallel scan with candidates equals the single scan (list form).** -/
theorem parallel_sip_acc_eq (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec)
    (hk : spec.key.size < 4) (cands : Array UInt64) (hs : Sip.Sorted cands)
    (prb : ByteArray) (ms : List BlockMeta)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hfits : ∀ b ∈ ms, b.rows ≤ two64)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols)
    (sortVar : Option String) (ox : OvCtx) (hon : ox.on = false)
    (L : List Nat) (hL : ∀ k ∈ L, k < ms.length) (c : Nat) :
    ((chunksOf c L).mapM (scanAccSipOf st spec cands ms sortVar ox)).map List.flatten
      = scanAccSipOf st spec cands ms sortVar ox L := by
  have hsub : ∀ X ∈ chunksOf c L, ∀ k ∈ X, k < ms.length :=
    fun X hX k hk => hL k (mem_of_mem_chunksOf c L hX hk)
  have hchunk : ∀ X ∈ chunksOf c L,
      scanAccSipOf st spec cands ms sortVar ox X
        = .ok (X.flatMap (fun k => blockOutSip spec cands prb ms[k]!)) := by
    intro X hX
    obtain ⟨s', h1, h2, _⟩ := forIn_blocks_sip st spec hspec hk cands hs prb ms hprb hfits hblocks
      sortVar ox hon X (hsub X hX) chunkInit
    have h2' : s'.acc = X.flatMap (fun k => blockOutSip spec cands prb ms[k]!) := by
      rw [h2]; rfl
    unfold scanAccSipOf
    rw [h1]
    show Except.ok s'.acc = _
    rw [h2']
  obtain ⟨s', h1, h2, _⟩ := forIn_blocks_sip st spec hspec hk cands hs prb ms hprb hfits hblocks
    sortVar ox hon L hL chunkInit
  have h2' : s'.acc = L.flatMap (fun k => blockOutSip spec cands prb ms[k]!) := by
    rw [h2]; rfl
  have hwhole : scanAccSipOf st spec cands ms sortVar ox L
      = .ok (L.flatMap (fun k => blockOutSip spec cands prb ms[k]!)) := by
    unfold scanAccSipOf
    rw [h1]
    show Except.ok s'.acc = _
    rw [h2']
  rw [hwhole, mapM_except_ok _ (fun X => X.flatMap (fun k => blockOutSip spec cands prb ms[k]!)) _ hchunk]
  show Except.ok ((chunksOf c L).map (fun X => X.flatMap (fun k => blockOutSip spec cands prb ms[k]!))).flatten
    = Except.ok (L.flatMap (fun k => blockOutSip spec cands prb ms[k]!))
  congr 1
  calc ((chunksOf c L).map (fun X => X.flatMap (fun k => blockOutSip spec cands prb ms[k]!))).flatten
      = (chunksOf c L).flatMap (fun X => X.flatMap (fun k => blockOutSip spec cands prb ms[k]!)) := rfl
    _ = (chunksOf c L).flatten.flatMap (fun k => blockOutSip spec cands prb ms[k]!) :=
        flatMap_flatMap_flatten _ _
    _ = L.flatMap (fun k => blockOutSip spec cands prb ms[k]!) := by rw [chunksOf_flatten]

#print axioms parallel_sip_acc_eq

end L4Factoidal.Storage.Sbm11.ParallelSipTheorems
