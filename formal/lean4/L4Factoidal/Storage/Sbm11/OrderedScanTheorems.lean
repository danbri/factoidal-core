/-
Copyright (c) 2026 Dan Brickley. All rights reserved.
Released under the Apache 2.0 license.
-/
import L4Factoidal.Paralliverse.Ordered
import L4Factoidal.Storage.Sbm11.ParallelScanTheorems

namespace L4Factoidal.Storage.Sbm11.ParallelScanTheorems

open Block IdQuery ScanFoldTheorems ParallelScan
open L4Factoidal.Paralliverse.Ordered (collect? mapM_eq_of_collect?)

/-- Kind: refinement.
Says: if each indexed reply is the successful list scan of its assigned native-driver
range, collecting the replies and appending their rows gives the single scan.
Does not say: that native IO, table memory, overlays, statistics or remote workers
implement the Id-store semantics or eventually produce a reply. -/
theorem scan_rangeBounds_eq_collected
    (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) (fill : Bool)
    (den : Chunk → List (List Nat)) (hden : DenOk spec fill den)
    (prb : ByteArray) (ms : List BlockMeta)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hadm : prmAdmitted spec.perm ms = true)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols)
    (sortVar : Option String) (ox : OvCtx) (hon : ox.on = false)
    (c : Nat) (replies : List (Nat × List (List Nat))) (parts : List (List (List Nat)))
    (hcollected : collect? (rangeBounds c ms.length).length replies = some parts)
    (hvalid : ∀ i b rows, (rangeBounds c ms.length)[i]? = some b → (i, rows) ∈ replies →
      scanAccOf st spec fill den ms sortVar ox (boundsList b) = .ok rows) :
    scanAccOf st spec fill den ms sortVar ox (List.range ms.length) = .ok parts.flatten := by
  let scan := scanAccOf st spec fill den ms sortVar ox
  have hparts := mapM_eq_of_collect? (rangeBounds c ms.length) (scan ∘ boundsList)
    replies parts hcollected hvalid
  rw [← List.mapM_map, rangeBounds_map, rangeChunks_eq] at hparts
  have hwhole := parallel_acc_eq st spec hspec fill den hden prb ms hprb hadm hblocks
    sortVar ox hon (List.range ms.length) (fun _ hi => List.mem_range.mp hi) c
  exact hwhole.symm.trans (congrArg
    (fun r : Except String (List (List (List Nat))) => r.map List.flatten) hparts)

#print axioms scan_rangeBounds_eq_collected

end L4Factoidal.Storage.Sbm11.ParallelScanTheorems
