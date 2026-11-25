/-
Copyright (c) 2026 Dan Brickley. All rights reserved.
Released under the Apache 2.0 license.
-/
import L4Factoidal.Paralliverse.Ordered
import L4Factoidal.Storage.Sbm11.MetaCountTheorems
import L4Factoidal.Storage.Sbm11.ParallelScanTheorems

namespace L4Factoidal.Storage.Sbm11.ParallelScanTheorems

open Block IdQuery ScanFoldTheorems ParallelScan
open L4Factoidal.Paralliverse.Ordered (collect? mapM_eq_of_collect?)

/-- Kind: refinement.
Says: select metadata for the actual key, partition it using the native driver's
bounds and check replies against each range's list scan. Appending the collected
rows gives the single scan of the selected metadata, including interior slices.
Does not say: that native IO, table memory, overlays, statistics or remote workers
implement the Id-store semantics or eventually produce a reply. -/
theorem scan_rangeBounds_eq_collected
    (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) (fill : Bool)
    (den : Chunk → List (List Nat)) (hden : DenOk spec fill den)
    (prb : ByteArray) (fullMetadata : List BlockMeta)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hadm : prmAdmitted spec.perm fullMetadata = true)
    (hblocks : ∀ b ∈ fullMetadata, ∃ cols, decodeBlockAt prb b b.offset = .ok cols)
    (sortVar : Option String) (ox : OvCtx) (hon : ox.on = false)
    (c : Nat) (replies : List (Nat × List (List Nat))) (parts : List (List (List Nat))) :
    let ms := (metasFor fullMetadata.toArray spec.key).toList
    let bounds := rangeBounds c ms.length
    collect? bounds.length replies = some parts →
    (∀ i b rows, bounds[i]? = some b → (i, rows) ∈ replies →
      scanAccOf st spec fill den ms sortVar ox (boundsList b) = .ok rows) →
    scanAccOf st spec fill den ms sortVar ox (List.range ms.length) = .ok parts.flatten := by
  let ms := (metasFor fullMetadata.toArray spec.key).toList
  dsimp only
  intro hcollected hvalid
  have hmember (b : BlockMeta) (hb : b ∈ ms) : b ∈ fullMetadata :=
    MetaCountTheorems.mem_metasFor fullMetadata spec.key b hb
  let scan := scanAccOf st spec fill den ms sortVar ox
  have hparts := mapM_eq_of_collect? (rangeBounds c ms.length) (scan ∘ boundsList)
    replies parts hcollected hvalid
  rw [← List.mapM_map, rangeBounds_map, rangeChunks_eq] at hparts
  have hwhole := parallel_acc_eq_of_selected st spec hspec fill den hden prb fullMetadata ms
    hprb hadm hmember hblocks
    sortVar ox hon (List.range ms.length) (fun _ hi => List.mem_range.mp hi) c
  exact hwhole.symm.trans (congrArg
    (fun r : Except String (List (List (List Nat))) => r.map List.flatten) hparts)

#print axioms scan_rangeBounds_eq_collected

end L4Factoidal.Storage.Sbm11.ParallelScanTheorems
