/-
L4Factoidal.Storage.Sbm11.ScanFoldTests — `IdQuery.scanFoldM` before and
after it was cut into per-block functions (2026-10-12, lemma L4e of
`docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md`;
https://github.com/danbri/factoidal/issues/776).

`scanFoldMOld` is the scan as it was: one `for` loop over the blocks with
eight mutable variables and early `continue` and `break`. The `#guard`s run
the old and the new scan over an in-memory store of a sample permutation
(several block shapes: constant and varying graph frames, a block of nine
rows or more with a constant graph, a block whose rows all have graph 0) and
compare every chunk (columns, rows, constants, variables, sort variable) and
the statistics, for key prefixes of length 0 to 4, checks, the named-graph
test, repeated variables, `fill` true and false, an early stop, and with a
delta overlay (inserts, deletes, a cleared graph).
`ScanFoldTheorems.scanFoldM_tuples` is the theorem about the new form.
-/
import L4Factoidal.Storage.Sbm11.IdQuery
import L4Factoidal.Storage.Sbm11.PrmRange

namespace L4Factoidal.Storage.Sbm11.ScanFoldTests

open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.Overlay (PermOverlay)

namespace OldForms

def constWordsOld (x : UInt64) (rows : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (8 * rows)
  for _ in [0:rows] do
    out := L4Factoidal.Qlvr.Side.put64 out x
  return out


/-- The bytes of the frames `need` of block `b`: one positioned read of the
    contiguous frames from the first to the last needed one. Returns the
    bytes, the start of each frame in them, and the bytes read. -/
def readFramesOld {m : Type → Type} [Monad m] (st : Store m) (perm : Nat) (b : BlockMeta)
    (need : Array Bool) : ExceptT String m (ByteArray × Array Nat × Nat) := do
  let lens : Array Nat := #[b.len0, b.len1, b.len2, b.len3]
  let starts : Array Nat := #[0, b.len0, b.len0 + b.len1, b.len0 + b.len1 + b.len2]
  let mut lo : Option Nat := none
  let mut hi := 0
  for c in [0:4] do
    if need[c]! then
      if lo.isNone then lo := some starts[c]!
      hi := starts[c]! + lens[c]!
  let some lo0 := lo | return (.empty, starts, 0)
  let bytes ← st.prb perm (b.offset + lo0) (hi - lo0)
  if bytes.size != hi - lo0 then throw s!"block at {b.offset}: short read"
  return (bytes, starts.map (· - lo0), hi - lo0)


/-- A block with overlay rows in its range: all four frames are read and
    decoded, the rows with the key prefix are merged with the deletes, the
    cleared graphs and the inserts (`Overlay.mergeRows`, proved:
    `OverlayTheorems.mergeRows_spec`), and the checks run per row. Returns
    the chunk and the bytes read. -/
def overlayChunkMOld {m : Type → Type} [Monad m] (st : Store m) (spec : ScanSpec) (b : BlockMeta)
    (ins del : List Row) (cleared : Array Nat) (sortVar : Option String) :
    ExceptT String m (Chunk × Nat) := do
  let (bytes, starts, nbytes) ← readFramesOld st spec.perm b #[true, true, true, true]
  let mut cols : Array ByteArray := #[]
  for c in [0:4] do
    match colAll b bytes starts c with
    | .ok w => cols := cols.push w
    | .error e => throw e
  let fuel := Nat.log2 b.rows + 2
  let lo := keyBound cols spec.key false fuel 0 b.rows
  let hi := keyBound cols spec.key true fuel lo b.rows
  let base := rowsOfColsGo cols lo (hi - lo) []
  let merged := L4Factoidal.Storage.Sbm11.Overlay.mergeRows (fun g => cleared.contains g) base del ins
  return (chunkOfRows spec merged sortVar, nbytes)

/-- Scan block by block; `f` gets each block's rows and says whether to go
    on. With `fill = false` a column that is constant over a chunk is left
    empty and given in `consts` (the aggregate path counts it so). -/
def scanFoldMOld {m : Type → Type} [Monad m] {σ : Type} (st : Store m) (spec : ScanSpec) (fill : Bool)
    (init : σ) (f : σ → Chunk → ExceptT String m (σ × Bool)) (metas : Array BlockMeta) :
    ExceptT String m (σ × ScanStats) := do
  -- the old form took the whole PRM1 array from the store (`st.metas`,
  -- before issue 805); it is given here
  let mut acc := init
  let mut stats : ScanStats := { blocksTotal := metas.size }
  let sortVar := match spec.outCols[0]? with
    | some c => if c == spec.key.size then spec.outVars[0]? else none
    | none => none
  -- the delta overlay (stage 5): the inserts with the key prefix, in row
  -- order; each is merged into the first selected block whose last row is
  -- not below it, or into a last chunk after the blocks
  let ov := st.ovl spec.perm
  let ovOn := !ov.isEmpty
  let insK : Array Row := if ovOn then ov.ins.filter (fun r => prefixCmp r spec.key == .eq) else #[]
  let insFuel := Nat.log2 insK.size + 2
  let delFuel := Nat.log2 ov.del.size + 2
  let mut insPos := 0
  let mut stopped := false
  for i in blocksFor metas spec.key do
    let b := metas[i]!
    if !selects b spec.key then continue
    let full := fullFor b spec.key
    -- checks decided by the metadata
    let mut skip := false
    let mut checks : Array (Nat × UInt64) := #[]
    for (c, x) in spec.checks do
      match colConst? b c with
      | some y => if y != x.toNat then skip := true
      | none => checks := checks.push (c, x)
    let mut named := spec.named
    if named then
      match colConst? b 3 with
      | some 0 => skip := true
      | some _ => named := false
      | none => pure ()
    if ovOn then
      let insEnd := L4Factoidal.Storage.Sbm11.Overlay.upperIdx insK b.last insFuel insPos insK.size
      let dLo := L4Factoidal.Storage.Sbm11.Overlay.lowerIdx ov.del b.first delFuel 0 ov.del.size
      let dHi := L4Factoidal.Storage.Sbm11.Overlay.upperIdx ov.del b.last delFuel dLo ov.del.size
      let clHit := !ov.cleared.isEmpty && (match colConst? b 3 with
        | some g => ov.cleared.contains g
        | none => true)
      if insEnd > insPos || (!skip && (dHi > dLo || clHit)) then
        let insL := L4Factoidal.Storage.Sbm11.Overlay.sliceList insK insPos (insEnd - insPos) []
        let delL := L4Factoidal.Storage.Sbm11.Overlay.sliceList ov.del dLo (dHi - dLo) []
        let (chunk, nbytes) ← overlayChunkMOld st spec b insL delL ov.cleared sortVar
        insPos := insEnd
        stats := { stats with blocksSelected := stats.blocksSelected + 1, blocksRead := stats.blocksRead + 1,
                              framesRead := stats.framesRead + 4, bytesRead := stats.bytesRead + nbytes,
                              rowsOut := stats.rowsOut + chunk.table.rows }
        let (acc', more) ← f acc chunk
        acc := acc'
        if !more then
          stopped := true
          break
        continue
    if skip then continue
    stats := { stats with blocksSelected := stats.blocksSelected + 1 }
    -- the columns to decode
    let constOut : Array (Option Nat) := spec.outCols.map fun c => if full then colConst? b c else none
    let keyCols : Array Nat := if full then #[] else (List.range spec.key.size).toArray
    let perRow := !checks.isEmpty || named || !spec.eqs.isEmpty
    let mut need : Array Bool := #[false, false, false, false]
    for c in keyCols do need := need.set! c true
    for (c, _) in checks do need := need.set! c true
    if named then need := need.set! 3 true
    for (a, c) in spec.eqs do
      need := (need.set! a true).set! c true
    for k in [0:spec.outCols.size] do
      if constOut[k]!.isNone || perRow then need := need.set! spec.outCols[k]! true
    let (bytes, starts, nbytes) ← readFramesOld st spec.perm b need
    if need.any id then
      stats := { stats with blocksRead := stats.blocksRead + 1,
                            framesRead := stats.framesRead + (need.filter id).size,
                            bytesRead := stats.bytesRead + nbytes }
    -- the key columns in full (to find the rows with the key prefix), then
    -- every other needed column for those rows only
    let mut keyWords : Array ByteArray := #[]
    for c in keyCols do
      match colAll b bytes starts c with
      | .ok w => keyWords := keyWords.push w
      | .error e => throw e
    let (lo, hi) :=
      if full then (0, b.rows)
      else
        let fuel := Nat.log2 b.rows + 2
        let lo := keyBound keyWords spec.key false fuel 0 b.rows
        (lo, keyBound keyWords spec.key true fuel lo b.rows)
    -- columns cut to rows [lo, hi): row r of the chunk is row lo + r
    let mut cols : Array ByteArray := #[.empty, .empty, .empty, .empty]
    for c in [0:4] do
      if need[c]! then
        if h : c < keyWords.size then
          cols := cols.set! c (keyWords[c].extract (8 * lo) (8 * hi))
        else
          match colRange b bytes starts c lo hi with
          | .ok w => cols := cols.set! c w
          | .error e => throw e
    let n := hi - lo
    let chunk : Chunk :=
      if perRow then
        let (out, k) := selectRows cols checks named spec.eqs spec.outCols n (n + 1) 0
          (spec.outVars.map fun _ => ByteArray.emptyWithCapacity (8 * n)) 0
        { table := { vars := spec.outVars, cols := out, rows := k, sortVar },
          consts := spec.outVars.map fun _ => none }
      else
        let outs := (List.range spec.outCols.size).toArray.map fun k =>
          match constOut[k]! with
          | some x => if fill then constWordsOld x.toUInt64 n else ByteArray.empty
          | none => cols[spec.outCols[k]!]!
        { table := { vars := spec.outVars, cols := outs, rows := n, sortVar },
          consts := constOut.map (·.map Nat.toUInt64) }
    stats := { stats with rowsOut := stats.rowsOut + chunk.table.rows }
    let (acc', more) ← f acc chunk
    acc := acc'
    if !more then
      stopped := true
      break
  if ovOn && !stopped && insPos < insK.size then
    let chunk := chunkOfRows spec (L4Factoidal.Storage.Sbm11.Overlay.sliceList insK insPos (insK.size - insPos) []) sortVar
    stats := { stats with rowsOut := stats.rowsOut + chunk.table.rows }
    let (acc', _) ← f acc chunk
    acc := acc'
  return (acc, stats)


end OldForms

/-! ## A sample permutation -/

/-- Rows in `Row.lt` order: varying graphs; a run of 10 rows with graph 7
    (a 9-byte constant graph frame); a run of rows all in graph 0. -/
def sampleRows : List Row :=
  let a := (List.range 3).flatMap fun x => (List.range 4).flatMap fun y => (List.range 3).flatMap fun z =>
    let r : Row := ⟨x + 1, y + 1, z + 1, 0⟩
    if (x + y + z) % 3 == 0 then [r, { r with g := 5 }] else [r]
  let b := (List.range 10).map fun y => (⟨4, y + 1, 1, 7⟩ : Row)
  let c := (List.range 6).map fun y => (⟨5, 1, y + 1, 0⟩ : Row)
  a ++ b ++ c

/-- Cut a list into pieces of the given sizes (the last piece takes the rest). -/
def cutGo : List Nat → List Row → List (List Row) → List (List Row)
  | _, [], acc => acc.reverse
  | [], rs, acc => (rs :: acc).reverse
  | n :: ns, rs, acc => cutGo ns (rs.drop (max n 1)) (rs.take (max n 1) :: acc)

/-- Blocks from byte 6 on, and the PRB1 bytes. -/
def buildGo : List (List Row) → Nat → Array BlockMeta → ByteArray → Array BlockMeta × ByteArray
  | [], _, ms, bs => (ms, bs)
  | rs :: rest, off, ms, bs =>
    match encodeBlock? off rs with
    | some (m, b) => buildGo rest (off + b.length) (ms.push m) (bs ++ ⟨b.toArray⟩)
    | none => buildGo rest off ms bs

def sample : Array BlockMeta × ByteArray :=
  buildGo (cutGo [3, 5, 1, 9, 12, 4, 2, 7, 10, 3] sampleRows []) 6 #[] ⟨(prbHeader 2).toArray⟩

def memStore (ov : PermOverlay) : Store Id where
  blockCount _ := pure sample.1.size
  blocksForRange _ key := L4Factoidal.Storage.Sbm11.PrmRange.rangeM (L4Factoidal.Storage.Sbm11.PrmRange.arrayReader sample.1) key
  prb _ off len := pure (sample.2.extract off (off + len))
  idOf _ := pure none
  keyOf _ := pure .empty
  keySlice _ := pure (.empty, 0, 0)
  termOf _ := throw "no terms"
  lowerBound _ := pure 0
  ovl _ := ov

#guard prmAdmitted 2 sample.1.toList
#guard sample.1.size == 11
#guard sample.1.toList.all fun m => (decodeBlockAt sample.2 m m.offset).toOption.isSome

abbrev ChunkKey := Array String × List (List UInt8) × Nat × Option String × Array (Option UInt64)

/-- What a chunk is, for comparison. -/
def chunkKey (ch : Chunk) : ChunkKey :=
  (ch.table.vars, ch.table.cols.toList.map (·.data.toList), ch.table.rows, ch.table.sortVar, ch.consts)

def statsKey (s : ScanStats) : List Nat :=
  [s.blocksRead, s.blocksSelected, s.blocksTotal, s.framesRead, s.bytesRead, s.rowsOut]

/-- Every chunk, and the statistics; stop after `stopAt` chunks. -/
def runNew (ov : PermOverlay) (spec : ScanSpec) (fill : Bool) (stopAt : Nat) :
    Except String (List ChunkKey × List Nat) :=
  match (scanFoldM (memStore ov) spec fill #[] fun acc ch => pure (acc.push (chunkKey ch), acc.size + 1 < stopAt)).run with
  | .ok (acc, st) => .ok (acc.toList, statsKey st)
  | .error e => .error e

def runOld (ov : PermOverlay) (spec : ScanSpec) (fill : Bool) (stopAt : Nat) :
    Except String (List ChunkKey × List Nat) :=
  match (OldForms.scanFoldMOld (memStore ov) spec fill #[] (fun acc ch =>
      pure (acc.push (chunkKey ch), acc.size + 1 < stopAt)) sample.1).run with
  | .ok (acc, st) => .ok (acc.toList, statsKey st)
  | .error e => .error e

def sameRun (a b : Except String (List ChunkKey × List Nat)) : Bool :=
  match a, b with
  | .ok x, .ok y => x == y
  | .error e, .error f => e == f
  | _, _ => false

/-- Scan specifications over permutation 2: every key prefix length, checks
    on each column, the named-graph test, repeated variables, constant and
    varying outputs. -/
def sampleSpecs : List ScanSpec :=
  let mk (key : Array UInt64) (checks : Array (Nat × UInt64)) (named : Bool) (outCols : Array Nat)
      (eqs : Array (Nat × Nat)) : ScanSpec :=
    { perm := 2, key, checks, named, outVars := outCols.map (fun c => s!"v{c}"), outCols, eqs }
  [mk #[] #[] false #[0, 1, 2, 3] #[], mk #[1] #[] false #[1, 2] #[], mk #[2] #[] false #[1, 2, 3] #[],
   mk #[2, 3] #[] false #[2] #[], mk #[2, 3, 1] #[] false #[3] #[], mk #[2, 3, 1, 5] #[] false #[] #[],
   mk #[4] #[] false #[1, 3] #[], mk #[4] #[] true #[1, 3] #[], mk #[5] #[] true #[2] #[],
   mk #[] #[(3, 7)] false #[0, 1] #[], mk #[4] #[(3, 7)] false #[1] #[], mk #[4] #[(3, 6)] false #[1] #[],
   mk #[] #[(1, 2)] false #[0, 2] #[], mk #[] #[(2, 1)] true #[0, 1] #[], mk #[1] #[] false #[1] #[(1, 2)],
   mk #[] #[] false #[0] #[(0, 2)], mk #[3] #[(2, 2)] true #[1, 3] #[(1, 2)], mk #[9] #[] false #[0] #[],
   mk #[0] #[] false #[1] #[], mk #[5, 1] #[] false #[2, 3] #[], mk #[] #[] true #[0, 3] #[],
   mk #[4, 2] #[] false #[0, 2, 3] #[], mk #[5, 1] #[(3, 0)] false #[2] #[]]

def sampleOverlays : List PermOverlay :=
  [{}, { ins := #[⟨1, 1, 1, 9⟩, ⟨4, 5, 1, 0⟩, ⟨9, 9, 9, 0⟩] },
   { del := #[⟨1, 1, 1, 0⟩, ⟨4, 3, 1, 7⟩] }, { cleared := #[5] },
   { ins := #[⟨2, 2, 2, 2⟩, ⟨6, 1, 1, 0⟩], del := #[⟨5, 1, 3, 0⟩], cleared := #[7] }]

/-- The old and the new scan agree on every sample (overlay, spec, `fill`,
    stop). Run by `Harness/ScanFoldTest.lean`, not by a `#guard`: the scan decodes
    its frames with `FrameWords.decodeWordsF`, which reaches the extern
    `Prim.Bytes.pushU64LE`, and the interpreter cannot run an extern
    declaration (issue 799, KR 1.2). -/
def scanDifferential : Bool := sampleOverlays.all fun ov => sampleSpecs.all fun spec => [true, false].all fun fill =>
  [100, 1, 2].all fun stopAt => sameRun (runNew ov spec fill stopAt) (runOld ov spec fill stopAt)

-- the comparison sees the data: every block is a chunk, every row is out
def scanSeesData : Bool := match runNew {} (sampleSpecs[0]!) true 100 with
  | .ok (chs, st) => chs.length == 11 && st[5]! == sampleRows.length
  | .error _ => false

-- `constWords` as a tail call against the old `for` loop
#guard [0, 1, 2, 7, 33].all fun n => [0, 5, 0xFFFFFFFFFFFFFFFF].all fun (x : UInt64) =>
  (constWords x n).data == (OldForms.constWordsOld x n).data

end L4Factoidal.Storage.Sbm11.ScanFoldTests
