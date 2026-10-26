/-
Harness/Sbm11PermCheck — the exact check of activation that the four
permutations of an SBM11 generation hold one quad set (lemma L3b,
`docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md` section 9;
https://github.com/danbri/factoidal/issues/776). The check as a function of
the rows, and the theorem that it gives equal quad multisets, are
`L4Factoidal.Storage.Sbm11.PermSet` (`segmentsSame`, `perms_same`).

Method (disk-resident, memory bounded; https://github.com/danbri/factoidal/issues/810):

  1. While activation decodes the blocks of POS, SPO and OSP for its other
     checks, each row is re-keyed to the PSO row of its quad
     (`PermSet.rekeyCols`, equal to `PermSet.rekey` by `rekeyCols_eq`) and
     appended to the segment of its permutation, in
     memory.
  2. A segment ends where the predicate changes (POS only: POS and PSO both
     start with the predicate, so one POS predicate is one contiguous range
     of PSO) and at the end of the permutation (SPO and OSP are one segment).
  3. At its end a segment is sorted (`PermSet.sortRows`) and compared row by
     row with the next rows of PSO, read block by block through a cursor. At
     the end of the permutation the cursor must be at the end of PSO.
  4. A segment that reaches `limit` rows (`SBM11_VERIFY_GROUP_ROWS`, default
     131,072) is sorted and written to disk as a run: chunks of at most
     4,096 rows, each the four column frames of the packer's encoder
     (`encodeColumnFast`), so a run takes about the bytes of a PSO block per
     row. At the end of the segment the runs are merged (a binary heap; more
     than 128 runs are first merged 128 at a time into longer runs) and the
     merged rows are compared with PSO as in 3. The run files of a segment
     are removed when the segment is done.

The sorting of runs and the comparison of segments run in background tasks
(`IO.asTask`): at most `SBM11_VERIFY_SPILLS` (default 6) runs are sorted at
once, the comparing jobs of a permutation are chained in segment order (so
the PSO cursor advances as in a sequential run), and the main thread waits
for the chain when more than `(spills + 1) * limit` rows are in flight. The
jobs of one permutation go on while the next permutation is decoded.

Memory: at most `spills + 1` buffers of `limit` rows and their sorts, one
decoded PSO block per job, and in a merge at most 128 decoded run chunks of
4,096 rows. Disk: the compressed runs of the segments not yet compared (of
at most two permutations at once); none when every segment fits in memory. The check reports the bytes it wrote and
the peak bytes in its directory (`temp-written-bytes`, `temp-peak-bytes`).

`SBM11_VERIFY_DIGEST=0` leaves out the digest comparison of
`Sbm11Cli.verifyGen` (test support: it shows that this check alone refuses a
permutation with another quad set).
-/
import Harness.Sbm11Gen
import L4Factoidal.Storage.Sbm11.PermSet
import L4Factoidal.Qlvr.Side
import L4Factoidal.Codec.Zstd

namespace Harness.Sbm11PermCheck

open L4Factoidal.Storage.Sbm11
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.Column
open Harness.Sbm11Gen

def defaultGroupRows : Nat := 131072

/-- The rows of a segment held in memory before a run goes to disk. -/
def groupRowsOf : IO Nat := do
  pure (((← IO.getEnv "SBM11_VERIFY_GROUP_ROWS").bind String.toNat?).getD defaultGroupRows |>.max 1)

/-- Rows per chunk of a run file. -/
def chunkRows : Nat := 4096

/-- Runs merged at once. -/
def fanIn : Nat := 128

@[inline] def put64 (b : ByteArray) (x : Nat) : ByteArray :=
  L4Factoidal.Qlvr.Side.put64 b x.toUInt64

@[inline] def get64 (b : ByteArray) (i : Nat) : Nat :=
  (L4Factoidal.Codec.Zstd.word64 b i).toNat

/-! ## The PSO cursor -/

/-- The PSO rows, block by block: `blk` the next block to read, `cols` the
    decoded block, `i` its next row, `idx` the rows consumed. -/
structure Cursor where
  blk : Nat := 0
  cols : Cols := default
  i : Nat := 0
  idx : Nat := 0

/-- Compare `r` with the next PSO row; false when PSO is at its end or its
    next row differs. -/
def Cursor.step (g : Gen) (ps : PermSrc) (c : Cursor) (r : Row) : IO (Bool × Cursor) := do
  let mut c := c
  if c.i ≥ c.cols.size then
    -- every block holds at least one row (`decodeBlockAt`)
    if c.blk ≥ ps.metas.size then return (false, c)
    let cols ← readBlock g ps c.blk
    c := { c with blk := c.blk + 1, cols, i := 0 }
  let i := c.i
  let same := c.cols.c0[i]! == r.c0 && c.cols.c1[i]! == r.c1 && c.cols.c2[i]! == r.c2 && c.cols.g[i]! == r.g
  return (same, { c with i := i + 1, idx := c.idx + 1 })

/-! ## Run files -/

/-- One chunk: a header of five 64-bit words (rows, then the four frame
    lengths) and the four frames. -/
def encodeChunk (rows : Array Row) (a e : Nat) : ByteArray := Id.run do
  let n := e - a
  let mut c0 : Array Nat := Array.mkEmpty n
  let mut c1 : Array Nat := Array.mkEmpty n
  let mut c2 : Array Nat := Array.mkEmpty n
  let mut cg : Array Nat := Array.mkEmpty n
  for i in [a:e] do
    let r := rows[i]!
    c0 := c0.push r.c0; c1 := c1.push r.c1; c2 := c2.push r.c2; cg := cg.push r.g
  let f0 := encodeColumnFast c0
  let f1 := encodeColumnFast c1
  let f2 := encodeColumnFast c2
  let f3 := encodeColumnFast cg
  let hdr := put64 (put64 (put64 (put64 (put64 ByteArray.empty n) f0.size) f1.size) f2.size) f3.size
  return hdr ++ f0 ++ f1 ++ f2 ++ f3

/-- Read up to `n` bytes (fewer only at the end of the file). -/
def readExact (h : IO.FS.Handle) (n : Nat) : IO ByteArray := do
  let mut out := ByteArray.empty
  for _ in [0:n + 1] do
    if out.size ≥ n then break
    let b ← h.read (n - out.size).toUSize
    if b.isEmpty then break
    out := out ++ b
  return out

/-- The next chunk of a run file, or none at its end. -/
def readChunk (path : String) (h : IO.FS.Handle) : IO (Option Cols) := do
  let hdr ← readExact h 40
  if hdr.isEmpty then return none
  if hdr.size != 40 then throw (IO.userError s!"{path}: a chunk header of {hdr.size} bytes")
  let n := get64 hdr 0
  let l0 := get64 hdr 8
  let l1 := get64 hdr 16
  let l2 := get64 hdr 24
  let l3 := get64 hdr 32
  let b ← readExact h (l0 + l1 + l2 + l3)
  if b.size != l0 + l1 + l2 + l3 then throw (IO.userError s!"{path}: a chunk of {b.size} bytes, the header says {l0 + l1 + l2 + l3}")
  let frame (k off len : Nat) : IO (Array Nat) :=
    match decodeColumnAt b n off with
    | some (c, j) =>
      if j == off + len && c.size == n then pure c
      else throw (IO.userError s!"{path}: frame {k} does not end at its length")
    | none => throw (IO.userError s!"{path}: frame {k} does not decode")
  let c0 ← frame 0 0 l0
  let c1 ← frame 1 l0 l1
  let c2 ← frame 2 (l0 + l1) l2
  let cg ← frame 3 (l0 + l1 + l2) l3
  if n == 0 then throw (IO.userError s!"{path}: a chunk with no row")
  return some ⟨c0, c1, c2, cg⟩

/-- A run being read: its current chunk and next row. -/
structure Reader where
  path : String
  h : IO.FS.Handle
  cols : Cols
  i : Nat

def Reader.open (path : String) : IO (Option Reader) := do
  let h ← IO.FS.Handle.mk path .read
  match ← readChunk path h with
  | some cols => pure (some { path, h, cols, i := 0 })
  | none => pure none

/-- The row of a reader, and the reader advanced (none at the end of the run). -/
def Reader.next (r : Reader) : IO (Row × Option Reader) := do
  let row := r.cols.row r.i
  if r.i + 1 < r.cols.size then return (row, some { r with i := r.i + 1 })
  match ← readChunk r.path r.h with
  | some cols => return (row, some { r with cols, i := 0 })
  | none => return (row, none)

/-! ## The merge heap: entries (row, reader index), least row at the root -/

@[inline] def entryLt (a b : Row × Nat) : Bool := a.1.lt b.1 || (a.1 == b.1 && a.2 < b.2)

def siftUp (hp : Array (Row × Nat)) (k : Nat) : Array (Row × Nat) := Id.run do
  let mut hp := hp
  let mut k := k
  for _ in [0:Nat.log2 hp.size + 2] do
    if k == 0 then break
    let p := (k - 1) / 2
    if entryLt hp[k]! hp[p]! then
      hp := hp.swapIfInBounds k p
      k := p
    else break
  return hp

def siftDown (hp : Array (Row × Nat)) (k : Nat) : Array (Row × Nat) := Id.run do
  let mut hp := hp
  let mut k := k
  for _ in [0:Nat.log2 hp.size + 2] do
    let l := 2 * k + 1
    if l ≥ hp.size then break
    let m := if l + 1 < hp.size && entryLt hp[l + 1]! hp[l]! then l + 1 else l
    if entryLt hp[m]! hp[k]! then
      hp := hp.swapIfInBounds k m
      k := m
    else break
  return hp

/-- Merge the runs `paths`; `emit` takes each row in order and returns
    false to stop. Returns false when `emit` stopped. -/
def mergeRuns (paths : Array String) (emit : Row → IO Bool) : IO Bool := do
  let mut readers : Array (Option Reader) := #[]
  let mut hp : Array (Row × Nat) := #[]
  for p in paths do
    match ← Reader.open p with
    | some r =>
      let (row, r') ← r.next
      hp := siftUp (hp.push (row, readers.size)) readers.size
      readers := readers.push r'
    | none => readers := readers.push none
  let mut more := true
  while more do
    match hp[0]? with
    | none => more := false
    | some (row, k) =>
      if !(← emit row) then return false
      match readers[k]! with
      | some r =>
        let (row', r') ← r.next
        readers := readers.set! k r'
        hp := siftDown (hp.set! 0 (row', k)) 0
      | none =>
        let last := hp.back!
        hp := hp.pop
        if hp.size > 0 then hp := siftDown (hp.set! 0 last) 0
  return true

/-! ## The check of one permutation

The main thread cuts the segments while it decodes the permutation; the
sorting of runs and the comparison of each segment with PSO run in
background tasks (`IO.asTask`), the segments one after the other in order
(each job is bound to the end of the previous one), so the cursor over PSO
advances as in a sequential run. -/

/-- Bytes the check wrote, the bytes now in its directory, and their peak:
    shared by the three permutations and the tasks. -/
structure Disk where
  written : Nat := 0
  now : Nat := 0
  peak : Nat := 0

def Disk.add (d : Disk) (n : Nat) : Disk :=
  let now := d.now + n
  { written := d.written + n, now, peak := max d.peak now }

/-- Write sorted rows as a run file in chunks of `chunkRows`; count its bytes. -/
def writeRun (disk : IO.Ref Disk) (path : String) (rows : Array Row) : IO Unit := do
  let h ← IO.FS.Handle.mk path .write
  let mut a := 0
  for _ in [0:rows.size / chunkRows + 1] do
    if a ≥ rows.size then break
    let e := min rows.size (a + chunkRows)
    let b := encodeChunk rows a e
    h.write b
    disk.modify (·.add b.size)
    a := e
  h.flush

def removeRun (disk : IO.Ref Disk) (path : String) : IO Unit := do
  let n := (← System.FilePath.metadata path).byteSize.toNat
  IO.FS.removeFile path
  disk.modify fun d => { d with now := d.now - n }

/-- The comparing side: the cursor over PSO, the first failure, the
    segments done, and the runs written by merges. -/
structure W where
  cursor : Cursor := {}
  fail : Option String := none
  segments : Nat := 0
  merged : Nat := 0

/-- Merge runs `fanIn` at a time into longer runs until at most `fanIn`
    remain; new runs are named `pre-m{k}.run`. -/
def reduceRuns (disk : IO.Ref Disk) (pre : String) (runs : Array String) : IO (Array String × Nat) := do
  let mut runs := runs
  let mut made := 0
  for _ in [0:runs.size + 1] do
    if runs.size ≤ fanIn then break
    let mut next : Array String := #[]
    let mut a := 0
    for _ in [0:runs.size / fanIn + 1] do
      if a ≥ runs.size then break
      let e := min runs.size (a + fanIn)
      let group := runs.extract a e
      let path := s!"{pre}-m{made}.run"
      made := made + 1
      let h ← IO.FS.Handle.mk path .write
      let out ← IO.mkRef (Array.mkEmpty chunkRows : Array Row)
      let flushOut : IO Unit := do
        let rows ← out.get
        if rows.isEmpty then return
        let b := encodeChunk rows 0 rows.size
        h.write b
        disk.modify (·.add b.size)
        out.set (Array.mkEmpty chunkRows)
      let _ ← mergeRuns group fun r => do
        out.modify (·.push r)
        if (← out.get).size ≥ chunkRows then flushOut
        pure true
      flushOut
      h.flush
      for p in group do removeRun disk p
      next := next.push path
      a := e
    runs := next
  return (runs, made)

/-- Compare sorted rows (in memory) with the next rows of PSO. -/
def W.memSeg (g : Gen) (pso : PermSrc) (name : String) (buf : Array Row) (w : W) : IO W := do
  if w.fail.isSome then return w
  let sorted := PermSet.sortRows buf
  let mut c := w.cursor
  for r in sorted do
    let (same, c') ← c.step g pso r
    if !same then
      return { w with cursor := c', fail := some s!"{name} holds other quads than pso (pso row {c.idx})" }
    c := c'
  return { w with cursor := c, segments := w.segments + 1 }

/-- Wait for the runs of a segment, merge them, compare the merged rows
    with the next rows of PSO, and remove the runs. -/
def W.runSeg (g : Gen) (pso : PermSrc) (name : String) (disk : IO.Ref Disk) (pre : String)
    (runs : Array String) (spills : Array (Task (Except IO.Error Unit))) (w : W) : IO W := do
  for t in spills do IO.ofExcept (← IO.wait t)
  if w.fail.isSome then
    for p in runs do removeRun disk p
    return w
  let (runs, made) ← reduceRuns disk pre runs
  let cur ← IO.mkRef w.cursor
  let bad ← IO.mkRef (none : Option Nat)
  let _ ← mergeRuns runs fun r => do
    let c ← cur.get
    let (same, c') ← c.step g pso r
    cur.set c'
    if same then pure true else do bad.set (some c.idx); pure false
  for p in runs do removeRun disk p
  let w := { w with cursor := ← cur.get, segments := w.segments + 1, merged := w.merged + made }
  match ← bad.get with
  | some i => return { w with fail := some s!"{name} holds other quads than pso (pso row {i})" }
  | none => return w

/-- The cutting side, on the main thread. -/
structure St where
  perm : Nat
  limit : Nat
  dir : String
  maxSpills : Nat := 6
  /-- the re-keyed rows of the current segment not yet in a run -/
  buf : Array Row := #[]
  /-- the runs of the current segment and the tasks that write them -/
  runs : Array String := #[]
  spills : Array (Task (Except IO.Error Unit)) := #[]
  key : Nat := 0
  seg : Nat := 0
  runsWritten : Nat := 0
  /-- the comparing jobs, chained in segment order -/
  chain : Task (Except IO.Error W) := .pure (.ok {})
  /-- rows handed to tasks since the last wait for the chain -/
  inflight : Nat := 0

/-- Spills sorted and written at once by tasks for the current segment
    (`SBM11_VERIFY_SPILLS`, default 6). -/
def maxSpillsOf : IO Nat := do
  pure (((← IO.getEnv "SBM11_VERIFY_SPILLS").bind String.toNat?).getD 6 |>.max 1)

/-- Sort the buffer and write it as a run of the current segment, in a task. -/
def St.spill (st : St) (disk : IO.Ref Disk) : IO St := do
  if st.buf.isEmpty then return st
  IO.FS.createDirAll st.dir
  let path := s!"{st.dir}/p{st.perm}-s{st.seg}-r{st.runs.size}.run"
  let buf := st.buf
  let st := { st with buf := #[] }
  -- the sort runs in the task (a `do` block is a function of the world)
  let t ← IO.asTask (do
    let sorted := PermSet.sortRows buf
    writeRun disk path sorted)
  let mut st := { st with spills := st.spills.push t, runs := st.runs.push path,
                          runsWritten := st.runsWritten + 1, inflight := st.inflight + buf.size }
  -- at most `st.maxSpills` running: wait for the oldest (it stays in the list; the job waits again)
  if st.spills.size > st.maxSpills then
    let _ ← IO.wait st.spills[st.spills.size - 1 - st.maxSpills]!
  return st

/-- Wait for every job so far. -/
def St.sync (st : St) : IO (St × W) := do
  let w ← IO.ofExcept (← IO.wait st.chain)
  return ({ st with chain := .pure (.ok w), inflight := 0 }, w)

/-- Hand the current segment to the comparing side. -/
def St.submit (st : St) (g : Gen) (pso : PermSrc) (disk : IO.Ref Disk) : IO St := do
  if st.buf.isEmpty && st.runs.isEmpty then return st
  let name := permNamesArr[st.perm]!
  let mut st := st
  let job : W → IO W ←
    if st.runs.isEmpty then
      let buf := st.buf
      st := { st with buf := #[], inflight := st.inflight + buf.size }
      pure (W.memSeg g pso name buf)
    else do
      st ← st.spill disk
      let pre := s!"{st.dir}/p{st.perm}-s{st.seg}"
      let runs := st.runs
      let spills := st.spills
      st := { st with runs := #[], spills := #[] }
      pure (W.runSeg g pso name disk pre runs spills)
  let chain ← IO.bindTask st.chain fun r => match r with
    | .ok w => IO.asTask (job w)
    | .error e => pure (.pure (.error e))
  st := { st with chain, seg := st.seg + 1 }
  if st.inflight ≥ (st.maxSpills + 1) * st.limit then
    let (st', _) ← st.sync
    st := st'
  return st

/-- Add the re-keyed row `r` of the permutation. -/
def St.add (st : St) (g : Gen) (pso : PermSrc) (disk : IO.Ref Disk) (r : Row) : IO St := do
  let mut st := st
  if st.perm == 1 && r.c0 != st.key && !(st.buf.isEmpty && st.runs.isEmpty) then
    st ← st.submit g pso disk
  st := { st with key := r.c0, buf := st.buf.push r }
  if st.buf.size ≥ st.limit then st ← st.spill disk
  return st

/-- End the permutation's pass: hand over the last segment. Its jobs go on
    in the background while the next permutation is decoded. -/
def St.close (st : St) (g : Gen) (pso : PermSrc) (disk : IO.Ref Disk) : IO St :=
  st.submit g pso disk

/-- Wait for every job of the permutation; then PSO must be at its end.
    Returns the comparing side's result. -/
def St.finish (st : St) (pso : PermSrc) : IO W := do
  let (st, w) ← st.sync
  if w.fail.isSome then return w
  if w.cursor.idx != pso.rows then
    return { w with fail := some s!"{permNamesArr[st.perm]!} holds other quads than pso ({w.cursor.idx} rows, pso {pso.rows})" }
  return w

end Harness.Sbm11PermCheck
