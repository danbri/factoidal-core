/-
Harness/Sbm11PermCheck — the exact check of activation that the four
permutations of an SBM11 generation hold one quad set (lemma L3b,
`docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md`;
https://github.com/danbri/factoidal/issues/776). The check as a function of
the rows, and the theorem that it gives equal quad multisets, are
`L4Factoidal.Storage.Sbm11.PermSet` (`sameQuads`, `perms_same`).

Method (disk-resident, memory bounded):

  1. The PSO blocks are cut into groups of at most `groupRows` rows (a group
     holds at least one block). The first row of every group after the first
     is a bound; the bucket of a PSO row is `PermSet.bucketOf bounds`.
  2. While activation decodes the blocks of POS, SPO and OSP, each row is
     re-keyed to the PSO row of its quad (`PermSet.rekey`) and appended (32
     bytes) to the file of its bucket, through a buffer per bucket that is
     written out at `flushBytes nb` bytes (64 KiB, less when there are many
     buckets, at least 4 KiB).
  3. Then, per permutation and bucket: a bucket whose row count differs
     from its group's is refused without being read; else its file is read,
     sorted (`PermSet.sortRows`) and compared row by row with the PSO rows
     of the group, decoded block by block; every PSO row must be in the
     bucket of its group.

Memory (measured on olympics in
`docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md` section 9): one
bucket of at most `G + b` rows (`G = groupRows`, `b` the rows of the largest
PSO block) as file bytes (32 per row) and as rows, the sort's arrays, one
decoded PSO block; and the buffers, `3 nb` of them (`nb ≤ N / G + 1` for `N`
quads), each written out at `flushBytes nb ≤ max(4 KiB, 16 MiB / 3 nb)`
bytes, so at most `max(32 MiB, 24 KiB × nb)` in all. With `G = 262,144`
that is about 25 MB for the bucket and, for a billion quads (`nb` about
3,815), about 90 MB of buffers. Disk: 32 bytes per row of the three
permutations, in a directory next to the generation, removed at the end.

`SBM11_VERIFY_GROUP_ROWS` sets `groupRows` (default 262,144; the tests use
a small value to have many buckets). `SBM11_VERIFY_DIGEST=0` leaves out the
digest comparison of `Sbm11Cli.verifyGen` (test support: it shows that this
check alone refuses a permutation with another quad set).
-/
import Harness.Sbm11Gen
import L4Factoidal.Storage.Sbm11.PermSet
import L4Factoidal.Qlvr.Side
import L4Factoidal.Codec.Zstd

namespace Harness.Sbm11PermCheck

open L4Factoidal.Storage.Sbm11
open L4Factoidal.Storage.Sbm11.Block
open Harness.Sbm11Gen

def defaultGroupRows : Nat := 262144

def groupRowsOf : IO Nat := do
  pure (((← IO.getEnv "SBM11_VERIFY_GROUP_ROWS").bind String.toNat?).getD defaultGroupRows |>.max 1)

/-- The groups of PSO blocks: the bounds (first row of every group after the
    first), and per group its block range and its row count. -/
structure Plan where
  bounds : Array Row
  groups : Array (Nat × Nat)
  rows : Array Nat

def planGroups (metas : Array BlockMeta) (groupRows : Nat) : Plan := Id.run do
  let mut bounds : Array Row := #[]
  let mut groups : Array (Nat × Nat) := #[]
  let mut rows : Array Nat := #[]
  let mut start := 0
  let mut acc := 0
  for i in [0:metas.size] do
    let b := metas[i]!
    if acc > 0 && acc + b.rows > groupRows then
      groups := groups.push (start, i)
      rows := rows.push acc
      bounds := bounds.push b.first
      start := i
      acc := 0
    acc := acc + b.rows
  groups := groups.push (start, metas.size)
  rows := rows.push acc
  return { bounds, groups, rows }

@[inline] def put64 (b : ByteArray) (x : Nat) : ByteArray :=
  L4Factoidal.Qlvr.Side.put64 b x.toUInt64

def putRow (b : ByteArray) (r : Row) : ByteArray :=
  put64 (put64 (put64 (put64 b r.c0) r.c1) r.c2) r.g

def rowAt (b : ByteArray) (i : Nat) : Row :=
  let w (k : Nat) : Nat := (L4Factoidal.Codec.Zstd.word64 b (32 * i + 8 * k)).toNat
  ⟨w 0, w 1, w 2, w 3⟩

def bucketPath (dir : String) (p j : Nat) : String := s!"{dir}/p{p}-b{j}.rows"

/-- Create the bucket files (empty) of permutations 1 to 3. -/
def createBuckets (dir : String) (nb : Nat) : IO Unit := do
  IO.FS.createDirAll dir
  for p in [1:4] do
    for j in [0:nb] do
      IO.FS.writeBinFile (bucketPath dir p j) ByteArray.empty

def appendFile (path : String) (b : ByteArray) : IO Unit := do
  if b.isEmpty then return
  let h ← IO.FS.Handle.mk path .append
  h.write b

/-- The buffers and row counts of the buckets, flat: index `(p - 1) * nb + j`.
    The caller keeps them in `let mut` variables so that every append is in
    place (`Array.modify` takes the buffer out before the push). -/
def slot (nb p j : Nat) : Nat := (p - 1) * nb + j

/-- The size at which a bucket buffer is written out: 64 KiB, less when
    there are many buckets (16 MiB over the `3 nb` buffers), at least 4 KiB. -/
def flushBytes (nb : Nat) : Nat := max 4096 (min 65536 (16777216 / (3 * nb)))

/-- Append a re-keyed row; write the buffer out at `flush` bytes. -/
def addRow (dir : String) (nb flush : Nat) (bufs : Array ByteArray) (counts : Array Nat) (p j : Nat) (r : Row) :
    IO (Array ByteArray × Array Nat) := do
  let k := slot nb p j
  let bufs := bufs.modify k (putRow · r)
  let counts := counts.modify k (· + 1)
  if (bufs[k]!).size ≥ flush then
    appendFile (bucketPath dir p j) bufs[k]!
    pure (bufs.set! k ByteArray.empty, counts)
  else pure (bufs, counts)

def flushAll (dir : String) (nb : Nat) (bufs : Array ByteArray) : IO Unit := do
  for p in [1:4] do
    for j in [0:nb] do
      appendFile (bucketPath dir p j) bufs[slot nb p j]!

/-- Compare bucket `j` of permutation `p` with PSO group `j`. Returns the
    failure, if any. -/
def compareBucket (g : Gen) (plan : Plan) (dir : String) (counts : Array Nat) (p j : Nat) :
    IO (Option String) := do
  let nb := plan.rows.size
  let n := counts[slot nb p j]!
  let want := plan.rows[j]!
  if n != want then
    return some s!"{permNamesArr[p]!} holds {n} rows in bucket {j}, pso {want}"
  let bytes ← IO.FS.readBinFile (bucketPath dir p j)
  if bytes.size != 32 * n then
    return some s!"{permNamesArr[p]!} bucket {j}: {bytes.size} bytes for {n} rows"
  let mut rows : Array Row := Array.mkEmpty n
  for i in [0:n] do
    rows := rows.push (rowAt bytes i)
  let sorted := PermSet.sortRows rows
  let some ps := g.perms[0]? | return some "no pso permutation"
  let (a, e) := plan.groups[j]!
  let mut idx := 0
  for bi in [a:e] do
    let c ← readBlock g ps bi
    for i in [0:c.size] do
      let r := c.row i
      if PermSet.bucketOf plan.bounds r != j then
        return some s!"pso block {bi} row {i}: not in bucket {j}"
      if idx ≥ sorted.size || sorted[idx]! != r then
        return some s!"{permNamesArr[p]!} holds other quads than pso (bucket {j}, pso row {idx})"
      idx := idx + 1
  if idx != sorted.size then
    return some s!"{permNamesArr[p]!} bucket {j}: {sorted.size} rows, pso group {idx}"
  return none

end Harness.Sbm11PermCheck
