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
import L4Factoidal.Prim.Bytes
import L4Factoidal.Storage.Sbm11.VarintWord

namespace L4Factoidal.Storage.Sbm11.Sip

open L4Factoidal (two64)
open L4Factoidal.Storage.Sbm11.Column (tagConst tagRaw tagDelta)
open L4Factoidal.Storage.Sbm11.FrameWords (put64 repeatWords)
open L4Factoidal.Codec.Zstd (word64)
open L4Factoidal.Storage.Sbm11.VarintWord (C7 allOnes lenMask vVal vLen zzV zzOk)

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

/-- `probeFrom` with its most frequent case first: when the candidate at
    `p` is not below `w` and the candidate before it (if any) is below `w`,
    the answer is `p`, with no call (`SipFastTheorems.probeFast_eq`). The
    reads are guarded by `h`, not by `[]!`: the compiled default of
    `cands[q]!` at a `UInt64` element is a boxed word, one allocation per
    call. -/
@[inline] def probeFast (cands : Array UInt64) (w : UInt64) (p : Nat) : Nat :=
  if h : p < cands.size then
    if !(cands[p] < w) && (p == 0 || cands[p - 1] < w) then p
    else probeFrom cands w p
  else probeFrom cands w p

/-- `q < cands.size && cands[q]! == w`, with a guarded read for the reason
    of `probeFast` (`SipFastTheorems.candAt_eq`). -/
@[inline] def candAt (cands : Array UInt64) (q : Nat) (w : UInt64) : Bool :=
  if h : q < cands.size then cands[q] == w else false

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


/-! ## The delta loops on machine words

`deltaFindGoW` and `deltaGatherGoW` are `deltaFindGo` and `deltaGatherGo`
with the byte position as a `USize`, the previous value and the varint
accumulator as `UInt64`, and no fuel (each call reads one byte: the
measure is `b.size - i`). The `Nat` loops spend most of their time on
`Nat` bookkeeping: a term id is near `2 ^ 61`, the test
`prev + z / 2 < two64` compares with a number above the scalar range on
every row, and every byte position, row number and fuel step is a tagged
`Nat` (issue 930: d14 tested 593,920 join-key values per query in these
loops).

While the accumulator is below `accCap = 2 ^ 57`, `acc * 128 + x` (with
`x < 128`) is below `2 ^ 64`, so the word operations give the `Nat`
results: `prev ≤ prev + h` is `prev + h < 2 ^ 64`, and `h ≤ prev` makes
`prev - h` exact. When the accumulator reaches `accCap` (a varint of more
than eight bytes: a jump of `2 ^ 63` or more between two ids), the loop
continues as the `Nat` loop from the same state. The callers use these
loops only when the bytes are fewer than `2 ^ 31`, so that `USize`
positions are exact on 32-bit targets too.

`SipFastTheorems.deltaFindGoW_eq` and `deltaGatherGoW_eq`: each equals its
`Nat` loop, started with the fuel the callers give it. -/

/-- `2 ^ 57`. -/
@[inline] def accCap : UInt64 := 144115188075855872

/-- `2 ^ 31`: below it a byte position is an exact `USize` on every target. -/
@[inline] def smallBytes : Nat := 2147483648

/-- `deltaFindGo` on machine words (see above). -/
def deltaFindGoW (b : ByteArray) (lo hi : Nat) (cands : Array UInt64)
    (idx : Nat) (prev : UInt64) (i : USize) (acc : UInt64) (p : Nat) (pos : Array Nat) (out : ByteArray) :
    Option (Array Nat × ByteArray) :=
  if idx ≥ hi then some (pos, out)
  else if h : i < b.usize then
    if acc < accCap then
      let x := b.uget i (L4Factoidal.Prim.Bytes.usize_lt_size h)
      if x < 128 then
        let z := acc * 128 + x.toUInt64
        if z % 2 == 0 then
          let v := prev + z / 2
          if prev ≤ v then
            if idx ≥ lo then
              let q := probeFast cands v p
              if candAt cands q v then
                deltaFindGoW b lo hi cands (idx + 1) v (i + 1) 0 q (pos.push idx) (put64 out v)
              else deltaFindGoW b lo hi cands (idx + 1) v (i + 1) 0 q pos out
            else deltaFindGoW b lo hi cands (idx + 1) v (i + 1) 0 p pos out
          else none
        else
          let hz := z / 2 + 1
          if hz ≤ prev then
            let v := prev - hz
            if idx ≥ lo then
              let q := probeFast cands v p
              if candAt cands q v then
                deltaFindGoW b lo hi cands (idx + 1) v (i + 1) 0 q (pos.push idx) (put64 out v)
              else deltaFindGoW b lo hi cands (idx + 1) v (i + 1) 0 q pos out
            else deltaFindGoW b lo hi cands (idx + 1) v (i + 1) 0 p pos out
          else none
      else deltaFindGoW b lo hi cands idx prev (i + 1) (acc * 128 + (x - 128).toUInt64) p pos out
    else deltaFindGo b lo hi cands (b.size - i.toNat + 3) idx prev.toNat i.toNat acc.toNat p pos out
  else none
termination_by b.size - i.toNat
decreasing_by
  all_goals
    have h1 := L4Factoidal.Prim.Bytes.usize_lt_size h
    rw [L4Factoidal.Prim.Bytes.usize_succ_toNat h]
    omega

/-! ### The find loop with the current candidate in the loop state

`deltaFindGoW` reads `cands[p]` and `cands[p - 1]` for every row; an
`Array UInt64` holds boxed words, so each read is two dependent loads (issue
930: a third of the samples of the find loop). `deltaFindGoC` carries
`c = cAt cands p` and `lc = lAt cands p` as `UInt64` loop variables. The
pointer stays at `p` when `p < cands.size`, `c` is not below the value, and
`lc` (the candidate before `p`) is below it (`isFast`); then no array is read.
Otherwise the pointer is `probeFrom`, and `c`, `lc` are read for it.
`SipFastTheorems.deltaFindGoC_eq`: with the invariants `c = cAt cands p`,
`lc = lAt cands p`, it equals `deltaFindGoW`. -/

/-- `cands[q]` when `q < cands.size`, else 0 (a guarded read). -/
@[inline] def cAt (cands : Array UInt64) (q : Nat) : UInt64 :=
  if h : q < cands.size then cands[q] else 0

/-- `cands[q - 1]` when `q ≠ 0` and `q - 1 < cands.size`, else 0. -/
@[inline] def lAt (cands : Array UInt64) (q : Nat) : UInt64 :=
  if q = 0 then 0 else if h : q - 1 < cands.size then cands[q - 1] else 0

/-- The pointer `p` is the answer for `w`: it is inside the array, its
    candidate `c` is not below `w`, and the candidate before it `lc` (if
    any) is below `w`. -/
@[inline] def isFast (cands : Array UInt64) (w : UInt64) (p : Nat) (c lc : UInt64) : Bool :=
  p < cands.size && !(c < w) && (p == 0 || lc < w)

/-- `deltaFindGoW` with `c` and `lc` in the loop state (see above). -/
def deltaFindGoC (b : ByteArray) (lo hi : Nat) (cands : Array UInt64)
    (idx : Nat) (prev : UInt64) (i : USize) (acc : UInt64) (p : Nat) (c lc : UInt64)
    (pos : Array Nat) (out : ByteArray) : Option (Array Nat × ByteArray) :=
  if idx ≥ hi then some (pos, out)
  else if h : i < b.usize then
    if acc < accCap then
      let x := b.uget i (L4Factoidal.Prim.Bytes.usize_lt_size h)
      if x < 128 then
        let z := acc * 128 + x.toUInt64
        let h2 := if z % 2 == 0 then z / 2 else z / 2 + 1
        let v := if z % 2 == 0 then prev + h2 else prev - h2
        let ok := if z % 2 == 0 then prev ≤ v else h2 ≤ prev
        if ok then
          if idx ≥ lo then
            let fast := isFast cands v p c lc
            let q := if fast then p else probeFrom cands v p
            let c' := if fast then c else cAt cands q
            let lc' := if fast then lc else lAt cands q
            if q < cands.size && c' == v then
              deltaFindGoC b lo hi cands (idx + 1) v (i + 1) 0 q c' lc' (pos.push idx) (put64 out v)
            else deltaFindGoC b lo hi cands (idx + 1) v (i + 1) 0 q c' lc' pos out
          else deltaFindGoC b lo hi cands (idx + 1) v (i + 1) 0 p c lc pos out
        else none
      else deltaFindGoC b lo hi cands idx prev (i + 1) (acc * 128 + (x - 128).toUInt64) p c lc pos out
    else deltaFindGo b lo hi cands (b.size - i.toNat + 3) idx prev.toNat i.toNat acc.toNat p pos out
  else none
termination_by b.size - i.toNat
decreasing_by
  all_goals
    have h1 := L4Factoidal.Prim.Bytes.usize_lt_size h
    rw [L4Factoidal.Prim.Bytes.usize_succ_toNat h]
    omega

/-! ### The find loop on machine words for the row numbers

`deltaFindGoY` is `deltaFindGoC` with the row number, the bounds `lo` and `hi`
and the candidate pointer as `USize`, and the zigzag step without a branch on
the sign (`VarintWord.zzV`). The compiled `deltaFindGoC` spends most of its
instructions on `Nat` bookkeeping (74 instructions per row, DBpedia query d14,
`valgrind --tool=cachegrind`; record section 11.16). The callers use it only
when the bytes, the bound `hi`, the candidates and the first pointer are all
fewer than `smallBytes` (`deltaFindStart`), so that no `USize` value wraps.
`SipFastTheorems.deltaFindGoY_eq`: it equals `deltaFindGoC`. -/
def deltaFindGoY (b : ByteArray) (cands : Array UInt64) (csz lo hi : USize)
    (idx : USize) (prev : UInt64) (i : USize) (acc : UInt64) (p : USize) (c lc : UInt64)
    (pos : Array Nat) (out : ByteArray) : Option (Array Nat × ByteArray) :=
  if hi ≤ idx then some (pos, out)
  else if h : i < b.usize then
    if acc < accCap then
      let x := b.uget i (L4Factoidal.Prim.Bytes.usize_lt_size h)
      if x < 128 then
        let z := acc * 128 + x.toUInt64
        let v := zzV prev z
        if zzOk prev z v then
          if lo ≤ idx then
            let fast := p < csz && !(c < v) && (p == 0 || lc < v)
            let q := if fast then p else (probeFrom cands v p.toNat).toUSize
            let c' := if fast then c else cAt cands q.toNat
            let lc' := if fast then lc else lAt cands q.toNat
            if q < csz && c' == v then
              deltaFindGoY b cands csz lo hi (idx + 1) v (i + 1) 0 q c' lc' (pos.push idx.toNat) (put64 out v)
            else deltaFindGoY b cands csz lo hi (idx + 1) v (i + 1) 0 q c' lc' pos out
          else deltaFindGoY b cands csz lo hi (idx + 1) v (i + 1) 0 p c lc pos out
        else none
      else deltaFindGoY b cands csz lo hi idx prev (i + 1) (acc * 128 + (x - 128).toUInt64) p c lc pos out
    else deltaFindGo b lo.toNat hi.toNat cands (b.size - i.toNat + 3) idx.toNat prev.toNat i.toNat acc.toNat p.toNat pos out
  else none
termination_by b.size - i.toNat
decreasing_by
  all_goals
    have h1 := L4Factoidal.Prim.Bytes.usize_lt_size h
    rw [L4Factoidal.Prim.Bytes.usize_succ_toNat h]
    omega

/-- All the inputs of `deltaFindGoY` fit a `USize` on every target. -/
@[inline] def findFits (b : ByteArray) (lo hi : Nat) (cands : Array UInt64) (p : Nat) : Bool :=
  decide (b.size < smallBytes) && decide (lo < smallBytes) && decide (hi < smallBytes) && decide (cands.size < smallBytes) &&
    decide (p < smallBytes)

/-- The start of `findWords` on a delta frame whose tag is at `i`: the word
    loop when the bytes are fewer than `smallBytes`, else the `Nat` loop
    (`SipFastTheorems.deltaFindStartNat_eq`). -/
def deltaFindStartNat (b : ByteArray) (lo hi : Nat) (cands : Array UInt64) (i p : Nat) :
    Option (Array Nat × ByteArray) :=
  if b.size < smallBytes then
    deltaFindGoC b lo hi cands 0 0 (i + 1).toUSize 0 p (cAt cands p) (lAt cands p) #[] .empty
  else deltaFindGo b lo hi cands (b.size - i + 2) 0 0 (i + 1) 0 p #[] .empty

/-- The start of `findWords` on a delta frame whose tag is at `i`: the loop on
    machine words for the row numbers when every input fits (`findFits`),
    else the loops of `deltaFindStartNat`
    (`SipWordTheorems.deltaFindStart_eq`). -/
def deltaFindStart (b : ByteArray) (lo hi : Nat) (cands : Array UInt64) (i p : Nat) :
    Option (Array Nat × ByteArray) :=
  if findFits b lo hi cands p then
    deltaFindGoY b cands cands.usize lo.toUSize hi.toUSize 0 0 (i + 1).toUSize 0 p.toUSize
      (cAt cands p) (lAt cands p) #[] .empty
  else deltaFindStartNat b lo hi cands i p

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
    deltaFindStart b lo hi cands i p
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


/-- `deltaGatherGo` on machine words (see `deltaFindGoW`). -/
def deltaGatherGoW (b : ByteArray) (pos : Array Nat)
    (idx : Nat) (prev : UInt64) (i : USize) (acc : UInt64) (k : Nat) (out : ByteArray) : Option ByteArray :=
  if k ≥ pos.size then some out
  else if h : i < b.usize then
    if acc < accCap then
      let x := b.uget i (L4Factoidal.Prim.Bytes.usize_lt_size h)
      if x < 128 then
        let z := acc * 128 + x.toUInt64
        if z % 2 == 0 then
          let v := prev + z / 2
          if prev ≤ v then
            if idx == pos[k]! then deltaGatherGoW b pos (idx + 1) v (i + 1) 0 (k + 1) (put64 out v)
            else deltaGatherGoW b pos (idx + 1) v (i + 1) 0 k out
          else none
        else
          let hz := z / 2 + 1
          if hz ≤ prev then
            let v := prev - hz
            if idx == pos[k]! then deltaGatherGoW b pos (idx + 1) v (i + 1) 0 (k + 1) (put64 out v)
            else deltaGatherGoW b pos (idx + 1) v (i + 1) 0 k out
          else none
      else deltaGatherGoW b pos idx prev (i + 1) (acc * 128 + (x - 128).toUInt64) k out
    else deltaGatherGo b pos (b.size - i.toNat + 3) idx prev.toNat i.toNat acc.toNat k out
  else none
termination_by b.size - i.toNat
decreasing_by
  all_goals
    have h1 := L4Factoidal.Prim.Bytes.usize_lt_size h
    rw [L4Factoidal.Prim.Bytes.usize_succ_toNat h]
    omega

/-- `pos[k]` when `k < pos.size`, else 0 (the guarded read of the next
    wanted row). -/
@[inline] def posAt (pos : Array Nat) (k : Nat) : Nat :=
  if h : k < pos.size then pos[k] else 0

/-- `deltaGatherGoW` with the next wanted row `nk = posAt pos k` in the loop
    state: the row test compares `idx` with a loop variable, and `pos` is read
    once per found row (`SipFastTheorems.deltaGatherGoK_eq`). -/
def deltaGatherGoK (b : ByteArray) (pos : Array Nat)
    (idx : Nat) (prev : UInt64) (i : USize) (acc : UInt64) (k nk : Nat) (out : ByteArray) : Option ByteArray :=
  if k ≥ pos.size then some out
  else if h : i < b.usize then
    if acc < accCap then
      let x := b.uget i (L4Factoidal.Prim.Bytes.usize_lt_size h)
      if x < 128 then
        let z := acc * 128 + x.toUInt64
        let h2 := if z % 2 == 0 then z / 2 else z / 2 + 1
        let v := if z % 2 == 0 then prev + h2 else prev - h2
        let ok := if z % 2 == 0 then prev ≤ v else h2 ≤ prev
        if ok then
          if idx == nk then deltaGatherGoK b pos (idx + 1) v (i + 1) 0 (k + 1) (posAt pos (k + 1)) (put64 out v)
          else deltaGatherGoK b pos (idx + 1) v (i + 1) 0 k nk out
        else none
      else deltaGatherGoK b pos idx prev (i + 1) (acc * 128 + (x - 128).toUInt64) k nk out
    else deltaGatherGo b pos (b.size - i.toNat + 3) idx prev.toNat i.toNat acc.toNat k out
  else none
termination_by b.size - i.toNat
decreasing_by
  all_goals
    have h1 := L4Factoidal.Prim.Bytes.usize_lt_size h
    rw [L4Factoidal.Prim.Bytes.usize_succ_toNat h]
    omega

/-- `pos[k]` as a `USize` when `k < pos.size`, else 0. -/
@[inline] def posAtU (pos : Array Nat) (k : USize) : USize :=
  if h : k.toNat < pos.size then pos[k.toNat].toUSize else 0

/-! ### The gather loop on machine words, with the varint read of `VarintWord`

`deltaGatherGoY` is `deltaGatherGoK` with the row number, the index into `pos`
and the next wanted row as `USize`, the zigzag step without a branch on the
sign, and, at the start of a varint (`acc = 0`) with eight bytes in the
window, the varint read without a branch per byte (`VarintWord.lenMask`,
`vVal`, `vLen`). The window with no varint end, a window past the end of the
array and a varint inside a partial row fall back to the byte step of
`deltaGatherGoK`. The loop takes fuel because the length that `vLen` gives is
known to be positive only through `VarintWordTheorems.fastRead_spec`; the
callers give `b.size + 1`. `SipFastTheorems.deltaGatherGoY_eq`: it equals
`deltaGatherGoK`. -/
def deltaGatherGoY (b : ByteArray) (pos : Array Nat) (psz : USize) :
    Nat → USize → UInt64 → USize → UInt64 → USize → USize → ByteArray → Option ByteArray
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, idx, prev, i, acc, k, nk, out =>
  if psz ≤ k then some out
  else if h : i < b.usize then
    if acc < accCap then
      let w := L4Factoidal.Prim.Bytes.ldU64LE b i
      let y := w ||| C7
      if acc == 0 && i + 8 ≤ b.usize && i < i + 8 && y != allOnes then
        let m := lenMask y
        let z := vVal w m
        let i' := i + (vLen m).toUSize
        let v := zzV prev z
        if zzOk prev z v then
          if idx == nk then deltaGatherGoY b pos psz fuel (idx + 1) v i' 0 (k + 1) (posAtU pos (k + 1)) (put64 out v)
          else deltaGatherGoY b pos psz fuel (idx + 1) v i' 0 k nk out
        else none
      else
      let x := b.uget i (L4Factoidal.Prim.Bytes.usize_lt_size h)
      if x < 128 then
        let z := acc * 128 + x.toUInt64
        let v := zzV prev z
        if zzOk prev z v then
          if idx == nk then deltaGatherGoY b pos psz fuel (idx + 1) v (i + 1) 0 (k + 1) (posAtU pos (k + 1)) (put64 out v)
          else deltaGatherGoY b pos psz fuel (idx + 1) v (i + 1) 0 k nk out
        else none
      else deltaGatherGoY b pos psz fuel idx prev (i + 1) (acc * 128 + (x - 128).toUInt64) k nk out
    else deltaGatherGo b pos (b.size - i.toNat + 3) idx.toNat prev.toNat i.toNat acc.toNat k.toNat out
  else none

/-- All the inputs of `deltaGatherGoY` fit a `USize` on every target. -/
@[inline] def gatherFits (b : ByteArray) (pos : Array Nat) : Bool :=
  decide (b.size < smallBytes) && decide (pos.size < smallBytes) && pos.all (fun r => decide (r < smallBytes))

/-- The start of `gatherWords` on a delta frame whose tag is at `i`
    (`SipFastTheorems.deltaGatherStartNat_eq`). -/
def deltaGatherStartNat (b : ByteArray) (pos : Array Nat) (i : Nat) : Option ByteArray :=
  if b.size < smallBytes then
    deltaGatherGoK b pos 0 0 (i + 1).toUSize 0 0 (posAt pos 0) (ByteArray.emptyWithCapacity (8 * pos.size))
  else deltaGatherGo b pos (b.size - i + 2) 0 0 (i + 1) 0 0 (ByteArray.emptyWithCapacity (8 * pos.size))

/-- The start of `gatherWords` on a delta frame whose tag is at `i`: the loop
    on machine words with the varint read of `VarintWord` when every input
    fits (`gatherFits`), else the loops of `deltaGatherStartNat`
    (`SipWordTheorems.deltaGatherStart_eq`). -/
def deltaGatherStart (b : ByteArray) (pos : Array Nat) (i : Nat) : Option ByteArray :=
  if gatherFits b pos then
    deltaGatherGoY b pos pos.usize (b.size + 1) 0 0 (i + 1).toUSize 0 0 (posAtU pos 0)
      (ByteArray.emptyWithCapacity (8 * pos.size))
  else deltaGatherStartNat b pos i

/-- The words at rows `pos` of a column of words. -/
def pickWords (ws : ByteArray) (pos : Array Nat) : ByteArray :=
  pos.foldl (fun out r => put64 out (word64 ws (8 * r))) (ByteArray.emptyWithCapacity (8 * pos.size))

/-- The words at rows `pos` (strictly increasing, below `n`) of the frame of
    `n` rows at `i` (`SipTheorems.gatherWords_spec`). -/
def gatherWords (b : ByteArray) (n i : Nat) (pos : Array Nat) : Option ByteArray :=
  if i < b.size && b.get! i == tagDelta then
    deltaGatherStart b pos i
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
   (List.range 20).map (fun i => 2 ^ 60 * 4 + i), [2 ^ 64 - 1, 0, 2 ^ 64 - 1],
   -- deltas of 1 to 9 bytes, up then down (the varint read of `VarintWord` at every length)
   [0, 1, 129, 16513, 2113665, 270549121, 34630287489, 4432676798593, 567382630219905,
    72624976668147841, 567382630219905, 4432676798593, 34630287489, 270549121, 2113665, 16513, 129, 1, 0],
   -- varying lengths of 1 to 5 bytes in one column, more than eight bytes per window
   (List.range 300).map (fun i => i * 104729 % 2 ^ (7 * (1 + i % 5)))]

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
