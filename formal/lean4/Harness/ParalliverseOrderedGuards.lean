import L4Factoidal.Paralliverse.Ordered
import L4Factoidal.Paralliverse.StaticPack
import L4Factoidal.Par.Chunked
import L4Factoidal.Storage.Sbm11.ParallelScan

open L4Factoidal.Paralliverse.Ordered

-- Executable examples of the collector, independent of the general proofs.
#guard collect? (α := Nat) 0 [] == some []
#guard collect? 0 [(0, 23)] == none
#guard collect? 1 [(0, 23)] == some [23]
#guard collect? 2 [(1, 23)] == none
#guard collect? 2 [(0, 23), (0, 23)] == none
#guard collect? 2 [(2, 99), (0, 23)] == none
#guard collect? 3 [(2, [7]), (0, [7]), (1, [])] == some [[7], [], [7]]

-- Deliver the actual CPU pack results in reverse, with an entirely empty part.
open L4Factoidal.Paralliverse.StaticPack in
#guard
  let parts : Array Rows := #[[[2, 2], []], [], [[5], [2]]]
  let packed := L4Factoidal.Par.mapChunks 4 (fun part => packParallel part (fun _ => 91)) parts
  let replies := ((List.range parts.size).zip packed.toList).reverse
  (collect? parts.size replies).map List.flatten == some [2, 2, 5, 2]

-- The scan driver's three bounds cover five positions in order after reverse delivery.
open L4Factoidal.Storage.Sbm11.ParallelScan in
#guard
  let bounds := rangeBounds 2 5
  let replies := ((List.range bounds.length).zip (bounds.map boundsList)).reverse
  bounds.length == 3 && (collect? bounds.length replies).map List.flatten == some [0, 1, 2, 3, 4]
