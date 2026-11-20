/-
Copyright (c) 2026 Dan Brickley. All rights reserved.
Released under the Apache 2.0 license.
-/
import L4Factoidal.Par.Chunked
import L4Factoidal.Paralliverse.Ordered
import L4Factoidal.Paralliverse.StaticPack

namespace L4Factoidal.Paralliverse.StaticPack

/-- Kind: refinement.
Says: collect the indexed results of the CPU task map in any delivery order.
Their concatenation is exactly the stable pack of all parts in source order.
Does not say: a worker, transport, GPU or host supplied the right indexed answers. -/
theorem collect_mapChunks_pack (workers : Nat) (parts : Array Rows) (prior : Buffer)
    (replies : List (Nat × List UInt32))
    (hdelivered : replies.Perm ((List.range parts.size).zip
      (Par.mapChunks workers (fun part => packParallel part prior) parts).toList)) :
    (Ordered.collect? parts.size replies).map List.flatten = some (packSpec parts.toList.flatten) := by
  rw [Par.mapChunks_eq, Array.toList_map] at hdelivered
  have hordered := (Ordered.collect?_eq_some_iff parts.size replies
    (parts.toList.map (fun part => packParallel part prior))).2
    ⟨by simp, hdelivered⟩
  rw [hordered]
  simp only [Option.map_some, packParallel_eq_packSpec, packSpec, List.flatten_flatten]

#print axioms collect_mapChunks_pack

end L4Factoidal.Paralliverse.StaticPack
