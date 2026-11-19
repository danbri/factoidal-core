import L4Factoidal.Paralliverse.Ordered
import L4Factoidal.Storage.Sbm11.ParallelScan
import L4Factoidal.Storage.Sbm11.ScanFoldTests
import L4Factoidal.Storage.Sbm11.ScanFoldTheorems

open L4Factoidal.Paralliverse.Ordered
open L4Factoidal.Storage.Sbm11

-- Decode the actual eleven-block PRB1 fixture and select key 3, strictly inside the file.
-- Return the four ranges backwards and check all sixteen rows, including repeated tuples.
#guard
  let (metadata, bytes) := ScanFoldTests.sample
  let spec : IdQuery.ScanSpec :=
    { perm := 2, key := #[3], checks := #[], named := false,
      outVars := #["y", "g"], outCols := #[1, 3], eqs := #[] }
  let selected := IdQuery.metasFor metadata spec.key
  let bounds := ParallelScan.rangeBounds 1 selected.size
  let rows := bounds.map fun bound =>
    (ParallelScan.boundsList bound).flatMap fun i =>
      ScanFoldTheorems.blockOut spec bytes selected[i]!
  let replies := ((List.range bounds.length).zip rows).reverse
  let expected := [[1, 0], [1, 0], [1, 5], [1, 0],
    [2, 0], [2, 5], [2, 0], [2, 0], [3, 0], [3, 0], [3, 0], [3, 5],
    [4, 0], [4, 0], [4, 5], [4, 0]]
  metadata.size == 11 && selected.size == 4 &&
    selected[0]!.offset > Block.prbHeaderBytes && selected.back!.offset < metadata.back!.offset &&
    (collect? bounds.length replies).map List.flatten == some expected
