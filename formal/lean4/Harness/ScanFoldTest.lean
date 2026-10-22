import L4Factoidal.Storage.Sbm11.ScanFoldTests

/-! The checks of `L4Factoidal.Storage.Sbm11.ScanFoldTests` that run the scan
(`scanDifferential`, `scanSeesData`), as a compiled program: the scan reaches
`Prim.Bytes.pushU64LE`, an extern the build-time interpreter cannot run.
`tests/sbm11/run.sh` runs it; exit 0 when both hold. -/

open L4Factoidal.Storage.Sbm11.ScanFoldTests
open L4Factoidal.Storage.Sbm11.IdQuery

/-- A table of `rows` rows and `ncols` columns of small ids with runs (a
    linear congruential generator, `seed`). -/
def sampleTable (seed rows ncols : Nat) : L4Factoidal.Qlvr.Table := Id.run do
  let mut cols : Array ByteArray := Array.replicate ncols ByteArray.empty
  let mut st := seed
  let mut cur : Array UInt64 := Array.replicate ncols 0
  for _ in [0:rows] do
    for c in [0:ncols] do
      st := (st * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
      if (st >>> 33) % (3 + c) == 0 then cur := cur.set! c (UInt64.ofNat ((st >>> 40) % 4))
      cols := cols.modify c fun b => L4Factoidal.Storage.Sbm11.FrameWords.put64 b cur[c]!
  return { vars := (List.range ncols).toArray.map fun c => s!"v{c}", cols, rows }

/-- `countChunk` (one key list per run) against `countChunkRef` (one per row):
    the same groups and counts in the same first-seen order, for 0 to 3 group
    variables, with and without a constant column. -/
def countChunkDifferential : Bool :=
  [0, 1, 2, 7, 64, 300].all fun rows => [1, 2, 3].all fun ncols => [1, 2, 3].all fun seed =>
    let t := sampleTable seed rows ncols
    [#[], #["v0"], #["v1"], #["v0", "v1"], #["v1", "v0", "v2"], #["v2"]].all fun gv =>
      [(fun _ => (none : Option UInt64)), (fun c => if c == 0 then some 7 else none)].all fun cf =>
        let ch : Chunk := { table := t, consts := t.vars.mapIdx fun c _ => cf c }
        let a := countChunk gv ch {}
        let b := countChunkRef gv ch {}
        a.keys == b.keys && a.keys.all fun k => a.counts.getD k 0 == b.counts.getD k 0

def main : IO UInt32 := do
  let a := scanDifferential
  let b := scanSeesData
  let c := countChunkDifferential
  IO.println s!"scanfold: differential {if a then "pass" else "FAIL"}, sees data {if b then "pass" else "FAIL"}, countChunk {if c then "pass" else "FAIL"}"
  return if a && b && c then 0 else 1
