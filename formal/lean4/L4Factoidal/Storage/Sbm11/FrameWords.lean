/-
L4Factoidal.Storage.Sbm11.FrameWords — a column frame decoded straight into
8-byte little-endian words, for the query path (stage 4,
https://github.com/danbri/factoidal/issues/790).

`Column.decodeColumnAt` (equal to the specification decoder,
`ColumnTheorems.decodeColumnAt_eq`) builds an `Array Nat` and allocates an
`Option` pair per varint; the query path then wrote each value as 8 bytes.
`decodeWords` gives the same bytes in one pass: a raw frame IS the words (a
copy), a constant frame is its 8 bytes repeated, a delta frame is decoded by a
loop with no allocation per value.

`decodeWords b n i = (decodeColumnAt b n i).map (fun (xs, j) => (words xs, j))`
is not proved. The `#guard`s below compare the two on encoded columns of every
codec and on refused frames; `l4sbm11 frame-check GEN` compares them on every
frame of every block of a generation.
-/
import L4Factoidal.Storage.Sbm11.Column

namespace L4Factoidal.Storage.Sbm11.FrameWords

open L4Factoidal.Storage.Sbm11.Column
open L4Factoidal (two64)

/-- Append `x` as 8 little-endian bytes. -/
@[inline] def put64 (b : ByteArray) (x : UInt64) : ByteArray :=
  b.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 24).toUInt8
   |>.push (x >>> 32).toUInt8 |>.push (x >>> 40).toUInt8 |>.push (x >>> 48).toUInt8
   |>.push (x >>> 56).toUInt8

/-- The words of a column of values below `2^64`. -/
def words (xs : Array Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (8 * xs.size)
  for x in xs do
    out := put64 out x.toUInt64
  return out

/-- `n` copies of the 8 bytes `v8`, by doubling. -/
def repeatWords (v8 : ByteArray) (n : Nat) : ByteArray := Id.run do
  if n == 0 then return ByteArray.empty
  let total := 8 * n
  let mut out := ByteArray.emptyWithCapacity total
  out := out ++ v8
  for _ in [0:64] do
    if out.size ≥ total then break
    let take := min out.size (total - out.size)
    out := out.copySlice 0 out out.size take
  return out

/-- The delta loop, one byte per step (a tail call with every value an
    argument, so nothing is allocated per value): `rows` values still to
    read, `prev` the last value, `acc` the varint read so far. A varint ends
    at a byte below 128; `unzz` and the bound `< 2^64` refuse as in
    `deltaAtGo`. -/
def deltaGo (b : ByteArray) : Nat → Nat → Nat → Nat → Nat → ByteArray → Option (ByteArray × Nat)
  | 0, _, _, _, _, _ => none
  | fuel + 1, rows, prev, i, acc, out =>
    if rows == 0 then some (out, i)
    else if i < b.size then
      let x := (b.get! i).toNat
      if x < 128 then
        let z := acc * 128 + x
        if z % 2 == 0 then
          let v := prev + z / 2
          if v < two64 then deltaGo b fuel (rows - 1) v (i + 1) 0 (put64 out v.toUInt64) else none
        else if (z + 1) / 2 ≤ prev then
          let v := prev - (z + 1) / 2
          deltaGo b fuel (rows - 1) v (i + 1) 0 (put64 out v.toUInt64)
        else none
      else deltaGo b fuel rows prev (i + 1) (acc * 128 + (x - 128)) out
    else none

/-- A delta frame of `n` values from byte `i0`: the words and the position
    after the frame. -/
def deltaWords (b : ByteArray) (n i0 : Nat) : Option (ByteArray × Nat) :=
  deltaGo b (b.size - i0 + 2) n 0 i0 0 (ByteArray.emptyWithCapacity (8 * n))

/-- `decodeColumnAt` as words. -/
def decodeWords (b : ByteArray) (n i : Nat) : Option (ByteArray × Nat) :=
  if i < b.size then
    let t := b.get! i
    if t == tagConst then
      if i + 9 ≤ b.size then some (repeatWords (b.extract (i + 1) (i + 9)) n, i + 9) else none
    else if t == tagRaw then
      if i + 1 + 8 * n ≤ b.size then some (b.extract (i + 1) (i + 1 + 8 * n), i + 1 + 8 * n) else none
    else if t == tagDelta then deltaWords b n (i + 1)
    else none
  else none

/-- Rows `[lo, hi)` of a delta frame: the loop of `deltaGo`, writing only
    the rows from `lo` and stopping after row `hi - 1` (the rest of the frame
    is not read). -/
def deltaRangeGo (b : ByteArray) (lo hi : Nat) : Nat → Nat → Nat → Nat → Nat → ByteArray → Option ByteArray
  | 0, _, _, _, _, _ => none
  | fuel + 1, idx, prev, i, acc, out =>
    if idx ≥ hi then some out
    else if i < b.size then
      let x := (b.get! i).toNat
      if x < 128 then
        let z := acc * 128 + x
        let v? : Option Nat :=
          if z % 2 == 0 then (if prev + z / 2 < two64 then some (prev + z / 2) else none)
          else if (z + 1) / 2 ≤ prev then some (prev - (z + 1) / 2) else none
        match v? with
        | some v =>
          deltaRangeGo b lo hi fuel (idx + 1) v (i + 1) 0 (if idx ≥ lo then put64 out v.toUInt64 else out)
        | none => none
      else deltaRangeGo b lo hi fuel idx prev (i + 1) (acc * 128 + (x - 128)) out
    else none

/-- Rows `[lo, hi)` (with `lo ≤ hi ≤ n`) of the frame of `n` rows at `i`, as
    words: the same bytes as `(decodeWords b n i)` cut to those rows, when the
    frame decodes. Only the bytes up to row `hi - 1` are read. -/
def decodeWordsRange (b : ByteArray) (n i lo hi : Nat) : Option ByteArray :=
  if hi > n || lo > hi then none
  else if i < b.size then
    let t := b.get! i
    if t == tagConst then
      if i + 9 ≤ b.size then some (repeatWords (b.extract (i + 1) (i + 9)) (hi - lo)) else none
    else if t == tagRaw then
      if i + 1 + 8 * n ≤ b.size then some (b.extract (i + 1 + 8 * lo) (i + 1 + 8 * hi)) else none
    else if t == tagDelta then
      deltaRangeGo b lo hi (b.size - i + 2) 0 0 (i + 1) 0 (ByteArray.emptyWithCapacity (8 * (hi - lo)))
    else none
  else none

/-- The reference: `decodeColumnAt`, then `words`. -/
def decodeWordsRef (b : ByteArray) (n i : Nat) : Option (ByteArray × Nat) :=
  (decodeColumnAt b n i).map fun (xs, j) => (words xs, j)

def same (a b : Option (ByteArray × Nat)) : Bool :=
  match a, b with
  | some (x, i), some (y, j) => x.data == y.data && i == j
  | none, none => true
  | _, _ => false

private def frame (xs : List Nat) : ByteArray := ⟨(frameBytes xs).toArray⟩

private def cols : List (List Nat) :=
  [[], [7], [5, 5, 5, 5], [1, 2, 3, 4, 1000, 3, 0], [0, 2 ^ 63, 2 ^ 64 - 1, 1, 2 ^ 62],
   (List.range 300).map (· * 7919 % 1000), (List.range 20).map (fun i => 2 ^ 60 * 4 + i),
   [2 ^ 64 - 1, 0, 2 ^ 64 - 1]]

#guard cols.all fun xs =>
  let f := frame xs
  same (decodeWords f xs.length 0) (decodeWordsRef f xs.length 0) &&
    -- with bytes before and after the frame
    same (decodeWords (ByteArray.mk #[9, 9] ++ f ++ ByteArray.mk #[1]) xs.length 2)
      (decodeWordsRef (ByteArray.mk #[9, 9] ++ f ++ ByteArray.mk #[1]) xs.length 2) &&
    -- a frame cut short, and one asked for more rows
    same (decodeWords (f.extract 0 (f.size - 1)) xs.length 0) (decodeWordsRef (f.extract 0 (f.size - 1)) xs.length 0) &&
    same (decodeWords f (xs.length + 1) 0) (decodeWordsRef f (xs.length + 1) 0)
-- every row range of every column: the range decoder against the cut words
#guard cols.all fun xs =>
  let f := frame xs
  let n := xs.length
  match decodeWords f n 0 with
  | some (ws, _) =>
    (List.range (n + 1)).all fun lo => (List.range (n + 1 - lo)).all fun d =>
      n > 25 && (lo % 17 != 0 || d % 19 != 0) ||
      match decodeWordsRange f n 0 lo (lo + d) with
      | some r => r.data == (ws.extract (8 * lo) (8 * (lo + d))).data
      | none => false
  | none => n == 0 && false
-- an unknown tag, a zstd tag, a delta that goes below zero
#guard same (decodeWords (ByteArray.mk #[3, 0, 0]) 1 0) none
#guard same (decodeWords (ByteArray.mk #[9]) 1 0) none
#guard same (decodeWords (ByteArray.mk #[2, 1]) 1 0) (decodeWordsRef (ByteArray.mk #[2, 1]) 1 0)

end L4Factoidal.Storage.Sbm11.FrameWords
