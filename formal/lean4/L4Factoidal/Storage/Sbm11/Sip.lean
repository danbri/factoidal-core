/-
L4Factoidal.Storage.Sbm11.Sip — sideways information passing into an SBM11
scan, frame by frame (https://github.com/danbri/factoidal/issues/809; record
docs/designissues/2026-10-12-sbm11-stage4.md section 11).

A merge join whose left input is much smaller than its right scan passes the
sorted distinct left values of the join variable (the candidates) into the
right scan (Neumann and Weikum, "Scalable join processing on very large RDF
graphs", SIGMOD 2009). The scan column of the join variable is the column
after the key (`IdQuery.ScanSpec`: column `key.size`). In each block the scan
then

  1. decodes only that column (`findWords`), and finds the rows whose value
     is a candidate: a merge of the decoded values against the candidates,
     with a candidate pointer that moves forward. A delta frame (the codec
     of a sorted id column) is decoded value by value and nothing is written
     for a row that does not match;
  2. decodes the other needed columns at those rows only (`gatherWords`): a
     delta frame by one sequential pass that stops after the last such row
     and writes nothing for the other rows; a raw or constant frame through
     `FrameWords.decodeWords` (a copy of the raw bytes, or the constant
     repeated), then by index; key columns, already decoded, by index
     (`pickWords`).

No `Table` of all the rows of the block is built.

## The candidate pointer

`probeFrom cands w p` is the first index `q ≥ p0` whose candidate is not
below `w`, where `p0` is `p` when the candidate before `p` is below `w`, else
0. When `cands` is in non-decreasing order, every candidate before `p0` is
below `w`, so `w` is a candidate exactly when `q < cands.size` and
`cands[q] = w` (`SipTheorems.probe_mem`). The pointer is a hint: any start
value gives the same answer, a good one (the previous row's `q`, or the
binary search `lbHint` of the block's least value) gives it in few steps.
Rows of the key range are in non-decreasing order of this column, so in a
block the pointer only moves forward.

## Loops

`deltaFindGo`, `wordsFindGo`, `deltaGatherGo`, `advGo`, `lbHintGo` and
`sortedGo` are tail calls with fuel; `pickWords` is an `Array.foldl` (a
loop). Nothing recurses once per row.
-/
import L4Factoidal.Storage.Sbm11.FrameWords
import L4Factoidal.Codec.Zstd

namespace L4Factoidal.Storage.Sbm11.Sip

open L4Factoidal (two64)
open L4Factoidal.Storage.Sbm11.Column (tagConst tagRaw tagDelta)
open L4Factoidal.Storage.Sbm11.FrameWords (put64 repeatWords)
open L4Factoidal.Codec.Zstd (word64)

/-! ## Candidates -/

/-- Entries `i..` in non-decreasing order (a tail call with fuel). -/
def sortedGo (cands : Array UInt64) : Nat → Nat → Bool
  | 0, _ => true
  | f + 1, i =>
    if i + 1 < cands.size then
      if cands[i]! ≤ cands[i + 1]! then sortedGo cands f (i + 1) else false
    else true

/-- The candidates are in non-decreasing order (the precondition of every
    candidate test; checked before a scan uses them). -/
def sorted (cands : Array UInt64) : Bool := sortedGo cands cands.size 0

/-- From `p`, the first index whose candidate is not below `w` (a tail call
    with fuel). -/
def advGo (cands : Array UInt64) (w : UInt64) : Nat → Nat → Nat
  | 0, p => p
  | f + 1, p => if p < cands.size && cands[p]! < w then advGo cands w f (p + 1) else p

/-- The pointer to start from for `w`: `p` when the candidate before it is
    below `w`, else 0. -/
@[inline] def startFor (cands : Array UInt64) (w : UInt64) (p : Nat) : Nat :=
  if p ≤ cands.size && (p == 0 || cands[p - 1]! < w) then p else 0

/-- The first index from `startFor cands w p` whose candidate is not below
    `w`. -/
@[inline] def probeFrom (cands : Array UInt64) (w : UInt64) (p : Nat) : Nat :=
  let p0 := startFor cands w p
  advGo cands w (cands.size - p0) p0

/-- Binary search in `[lo, hi)` for the first candidate not below `w` (a
    hint: nothing depends on it being exact). -/
def lbHintGo (cands : Array UInt64) (w : UInt64) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if cands[mid]! < w then lbHintGo cands w f (mid + 1) hi else lbHintGo cands w f lo mid
    else lo

def lbHint (cands : Array UInt64) (w : UInt64) : Nat :=
  lbHintGo cands w (Nat.log2 cands.size + 2) 0 cands.size

/-- Whether a candidate can lie in `[vlo, vhi]`, from the hint `q`: `false`
    only when the candidate before `q` is below `vlo` and the candidate at
    `q` (if any) is above `vhi`. With `cands` in non-decreasing order,
    `false` means that no candidate lies in `[vlo, vhi]`
    (`SipTheorems.mayHold_false`). -/
def mayHold (cands : Array UInt64) (vlo vhi : UInt64) (q : Nat) : Bool :=
  if q ≤ cands.size && (q == 0 || cands[q - 1]! < vlo) then
    q < cands.size && cands[q]! ≤ vhi
  else true

/-! ## Finding the rows (the join-key column) -/

/-- The delta loop of `FrameWords.deltaRangeGo` that writes nothing for a
    row whose value is not a candidate: rows below `lo` are decoded and
    passed over; each row `idx` in `[lo, hi)` whose value is a candidate is
    appended to `pos` and its value to `out` (as a word). `p` is the
    candidate pointer. -/
def deltaFindGo (b : ByteArray) (lo hi : Nat) (cands : Array UInt64) :
    Nat → Nat → Nat → Nat → Nat → Nat → Array Nat → ByteArray → Option (Array Nat × ByteArray)
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, idx, prev, i, acc, p, pos, out =>
    if idx ≥ hi then some (pos, out)
    else if i < b.size then
      let x := (b.get! i).toNat
      if x < 128 then
        let z := acc * 128 + x
        let v? : Option Nat :=
          if z % 2 == 0 then (if prev + z / 2 < two64 then some (prev + z / 2) else none)
          else if (z + 1) / 2 ≤ prev then some (prev - (z + 1) / 2) else none
        match v? with
        | some v =>
          if idx ≥ lo then
            let w := v.toUInt64
            let q := probeFrom cands w p
            if q < cands.size && cands[q]! == w then
              deltaFindGo b lo hi cands fuel (idx + 1) v (i + 1) 0 q (pos.push idx) (put64 out w)
            else deltaFindGo b lo hi cands fuel (idx + 1) v (i + 1) 0 q pos out
          else deltaFindGo b lo hi cands fuel (idx + 1) v (i + 1) 0 p pos out
        | none => none
      else deltaFindGo b lo hi cands fuel idx prev (i + 1) (acc * 128 + (x - 128)) p pos out
    else none

/-- Rows `r..hi-1` of a column of words: each row whose word is a candidate
    is appended (a tail call with fuel). The constant and raw frames are
    read through `FrameWords.decodeWords` (a raw frame is a copy of its
    bytes, a constant frame its word repeated) and then by this loop. -/
def wordsFindGo (ws : ByteArray) (hi : Nat) (cands : Array UInt64) :
    Nat → Nat → Nat → Array Nat → ByteArray → Array Nat × ByteArray
  | 0, _, _, pos, out => (pos, out)
  | f + 1, r, p, pos, out =>
    if r < hi then
      let w := word64 ws (8 * r)
      let q := probeFrom cands w p
      if q < cands.size && cands[q]! == w then wordsFindGo ws hi cands f (r + 1) q (pos.push r) (put64 out w)
      else wordsFindGo ws hi cands f (r + 1) q pos out
    else (pos, out)

/-- The rows in `[lo, hi)` of the frame of `n` rows at `i` whose value is a
    candidate, and their values as words; `p` is the first candidate
    pointer. For a frame that decodes (`FrameWords.decodeWords b n i =
    some (ws, j)`) and candidates in non-decreasing order, the rows are
    `(List.range' lo (hi - lo)).filter` of the candidate test on the words
    (`SipTheorems.findWords_spec`). -/
def findWords (b : ByteArray) (n i lo hi : Nat) (cands : Array UInt64) (p : Nat) :
    Option (Array Nat × ByteArray) :=
  if hi > n || lo > hi then none
  else if i < b.size && b.get! i == tagDelta then
    deltaFindGo b lo hi cands (b.size - i + 2) 0 0 (i + 1) 0 p #[] .empty
  else match FrameWords.decodeWords b n i with
    | some (ws, _) => some (wordsFindGo ws hi cands (hi - lo) lo p #[] .empty)
    | none => none

/-! ## Gathering the other columns at the found rows -/

/-- The delta loop that writes only the rows `pos[k], pos[k + 1], ...`
    (strictly increasing) and stops after the last of them. -/
def deltaGatherGo (b : ByteArray) (pos : Array Nat) :
    Nat → Nat → Nat → Nat → Nat → Nat → ByteArray → Option ByteArray
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, idx, prev, i, acc, k, out =>
    if k ≥ pos.size then some out
    else if i < b.size then
      let x := (b.get! i).toNat
      if x < 128 then
        let z := acc * 128 + x
        let v? : Option Nat :=
          if z % 2 == 0 then (if prev + z / 2 < two64 then some (prev + z / 2) else none)
          else if (z + 1) / 2 ≤ prev then some (prev - (z + 1) / 2) else none
        match v? with
        | some v =>
          if idx == pos[k]! then deltaGatherGo b pos fuel (idx + 1) v (i + 1) 0 (k + 1) (put64 out v.toUInt64)
          else deltaGatherGo b pos fuel (idx + 1) v (i + 1) 0 k out
        | none => none
      else deltaGatherGo b pos fuel idx prev (i + 1) (acc * 128 + (x - 128)) k out
    else none

/-- The words at rows `pos` of a column of words. -/
def pickWords (ws : ByteArray) (pos : Array Nat) : ByteArray :=
  pos.foldl (fun out r => put64 out (word64 ws (8 * r))) (ByteArray.emptyWithCapacity (8 * pos.size))

/-- The words at rows `pos` (strictly increasing, below `n`) of the frame of
    `n` rows at `i` (`SipTheorems.gatherWords_spec`). -/
def gatherWords (b : ByteArray) (n i : Nat) (pos : Array Nat) : Option ByteArray :=
  if i < b.size && b.get! i == tagDelta then
    deltaGatherGo b pos (b.size - i + 2) 0 0 (i + 1) 0 0 (ByteArray.emptyWithCapacity (8 * pos.size))
  else match FrameWords.decodeWords b n i with
    | some (ws, _) => some (pickWords ws pos)
    | none => none

/-! ## Tests against the reference: decode the frame, then filter -/

private def frameOf (xs : List Nat) : ByteArray := ⟨(Column.frameBytes xs).toArray⟩

private def at64 (ws : ByteArray) (r : Nat) : UInt64 := word64 ws (8 * r)

/-- The reference of `findWords`: the whole frame's words, then the rows of
    `[lo, hi)` whose word is a candidate. -/
private def findRef (b : ByteArray) (n i lo hi : Nat) (cands : Array UInt64) : Option (List Nat × List UInt64) :=
  match FrameWords.decodeWords b n i with
  | some (ws, _) =>
    let pos := (List.range' lo (hi - lo)).filter fun r => cands.contains (at64 ws r)
    some (pos, pos.map (at64 ws))
  | none => none

private def findSame (b : ByteArray) (n i lo hi : Nat) (cands : Array UInt64) (p : Nat) : Bool :=
  match findWords b n i lo hi cands p, findRef b n i lo hi cands with
  | some (pos, out), some (pos', vals) =>
    pos.toList == pos' && out.size == 8 * pos'.length && (List.range pos'.length).all fun k => at64 out k == vals.getD k 0
  | _, _ => false

private def gatherSame (b : ByteArray) (n i : Nat) (pos : Array Nat) : Bool :=
  match gatherWords b n i pos, FrameWords.decodeWords b n i with
  | some out, some (ws, _) =>
    out.size == 8 * pos.size && (List.range pos.size).all fun k => at64 out k == at64 ws pos[k]!
  | _, _ => false

private def testCols : List (List Nat) :=
  [[7], [5, 5, 5, 5], [1, 2, 3, 4, 1000, 3, 0], [0, 2 ^ 63, 2 ^ 64 - 1, 1, 2 ^ 62],
   (List.range 300).map (· * 7919 % 1000), (List.range 200).map (fun i => 3 * i + 1),
   (List.range 20).map (fun i => 2 ^ 60 * 4 + i), [2 ^ 64 - 1, 0, 2 ^ 64 - 1]]

private def testCands : List (Array UInt64) :=
  [#[], #[5], #[1, 3, 1000], #[0, 1, 2, 3, 4, 5, 6, 7], #[7, 100, 301, 598, 2 ^ 63],
   (List.range 50).toArray.map (fun i => (6 * i + 1).toUInt64), #[2 ^ 64 - 1]]

-- every range of every column against every candidate set, with good and bad pointer hints
#guard testCols.all fun xs =>
  let f := frameOf xs
  let n := xs.length
  testCands.all fun cs =>
    [(0, n), (0, n / 2), (n / 3, n), (n / 3, 2 * n / 3), (n, n)].all fun (lo, hi) =>
      [0, 1, cs.size, cs.size + 3, lbHint cs 4].all fun p => findSame f n 0 lo hi cs p
-- the raw codec (frameBytes picks delta for small gaps; a raw frame of the same values)
#guard testCols.all fun xs =>
  let n := xs.length
  let f : ByteArray := ⟨((tagRaw :: (xs.map Column.put64).flatten)).toArray⟩
  testCands.all fun cs => [(0, n), (n / 3, 2 * n / 3)].all fun (lo, hi) => findSame f n 0 lo hi cs 0
-- gather: every column, several position sets
#guard testCols.all fun xs =>
  let f := frameOf xs
  let n := xs.length
  let raw : ByteArray := ⟨((tagRaw :: (xs.map Column.put64).flatten)).toArray⟩
  [(List.range n).toArray, ((List.range n).filter (· % 3 == 1)).toArray, #[], #[n - 1], #[0]].all fun pos =>
    gatherSame f n 0 pos && gatherSame raw n 0 pos
-- a frame cut short is refused by both
#guard findWords ((frameOf [1, 2, 3, 4]).extract 0 3) 4 0 0 4 #[2] 0 == none
-- `mayHold`
#guard mayHold #[3, 9, 20] 10 19 (lbHint #[3, 9, 20] 10) == false
#guard mayHold #[3, 9, 20] 10 20 (lbHint #[3, 9, 20] 10) == true
#guard mayHold #[3, 9, 20] 10 19 0 == true
#guard sorted #[1, 1, 2] && !sorted #[2, 1]

end L4Factoidal.Storage.Sbm11.Sip
