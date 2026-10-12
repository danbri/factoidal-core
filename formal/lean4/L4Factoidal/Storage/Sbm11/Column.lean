/-
L4Factoidal.Storage.Sbm11.Column — the column frames of an SBM11 block
(PRB1), wire version 11 (`docs/designissues/2026-10-11-shardborough-vs-qlever.md`
section 6.4; https://github.com/danbri/factoidal/issues/789).

A column is the list of the ids of one position (`col0`, `col1`, `col2` or
the graph id) of the rows of one block, each a natural number below `2^64`.
A frame is one codec byte and the column's bytes. The row count is not in
the frame: it is in the block's PRM1 entry, and every decoder takes it.

## Bytes

    tag 0  constant  value u64 LE                 every row has this value
    tag 1  raw       value u64 LE, once per row
    tag 2  delta     varint(zz(prev, v)) per row,  prev = 0 before the first row
    tag 3  zstd      reserved: an RFC 8878 frame of the raw column. Stage 3
                     does not write it and the decoder refuses it (see the
                     stage 3 record for the sizes that made zstd unnecessary
                     for the stage 3 size target).

`zz prev v` is the zig-zag map of the difference: `2 (v - prev)` when
`prev ≤ v`, else `2 (prev - v) - 1`. A varint is the value in groups of 7
bits, the most significant group first; every byte but the last has bit 7
set (`putVar`). The encoder writes tag 0 when every value is equal, else tag
2 when the delta bytes are fewer than `8 × rows`, else tag 1
(`frameBytes`). The choice is part of the bytes: activation re-encodes every
decoded column and compares.

## Admission

`encodeColumn? xs` is `some` exactly when every value is below `2^64`. The
delta decoder refuses a value at or above `2^64` and a negative value. The
round trip `ColumnTheorems.decodeColumn_encodeColumn?` has
`encodeColumn? xs = some bs` as its only hypothesis.

## Runtime path

The spec decoders work over `List UInt8`. The scan and activation run
`decodeColumnAt`, which reads a `ByteArray` by position into an `Array Nat`
(an id below `2^63` is a scalar `Nat`, no allocation per value);
`ColumnTheorems.decodeColumnAt_eq` proves it equal to `decodeColumn`.
`encodeColumnFast` is the packer's encoder over `Array Nat`. It is not
proved equal to `frameBytes`; the packer decodes every frame it writes and
activation re-encodes every frame it reads, and both compare.

## Loops

Every recursive function here is a tail call with a fuel or count `Nat`
first, or an accumulator. The encoders of the specification use `List.map`,
`List.zipWith` and `List.flatten` (each has a tail-recursive `@[csimp]`
implementation in Lean core). No `sorry`, no user `axiom`, no
`native_decide`, no `partial`.
-/
import L4Factoidal.NatBounds

namespace L4Factoidal.Storage.Sbm11.Column

open L4Factoidal (two64)

def tagConst : UInt8 := 0
def tagRaw : UInt8 := 1
def tagDelta : UInt8 := 2
/-- Reserved for zstd frames; refused by `decodeColumn` in stage 3. -/
def tagZstd : UInt8 := 3

/-! ## Fixed-width fields over `Nat` -/

/-- A value below `2^64`, 8 bytes little-endian. -/
def put64 (v : Nat) : List UInt8 :=
  [v.toUInt8, (v / 256).toUInt8, (v / 65536).toUInt8, (v / 16777216).toUInt8,
   (v / 4294967296).toUInt8, (v / 1099511627776).toUInt8, (v / 281474976710656).toUInt8,
   (v / 72057594037927936).toUInt8]

def get64 : List UInt8 → Option (Nat × List UInt8)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    some (b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216 +
      b4.toNat * 4294967296 + b5.toNat * 1099511627776 + b6.toNat * 281474976710656 +
      b7.toNat * 72057594037927936, rest)
  | _ => none

/-- A value below `2^32`, 4 bytes little-endian. -/
def put32 (v : Nat) : List UInt8 :=
  [v.toUInt8, (v / 256).toUInt8, (v / 65536).toUInt8, (v / 16777216).toUInt8]

def get32 : List UInt8 → Option (Nat × List UInt8)
  | b0 :: b1 :: b2 :: b3 :: rest =>
    some (b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216, rest)
  | _ => none

/-! ## Varints, most significant group first -/

/-- Prepend the continuation groups of `n` (from the least significant up)
    to `acc`. `fuel ≥ n` is enough. -/
def vbeGo : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | f + 1, n, acc => if n = 0 then acc else vbeGo f (n / 128) ((n % 128 + 128).toUInt8 :: acc)

/-- The varint of `n` in front of `rest`. -/
def putVar (n : Nat) (rest : List UInt8) : List UInt8 :=
  vbeGo n (n / 128) ((n % 128).toUInt8 :: rest)

def getVarGo : Nat → Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | f + 1, acc, b :: rest =>
    if b.toNat < 128 then some (acc * 128 + b.toNat, rest)
    else getVarGo f (acc * 128 + (b.toNat - 128)) rest

def getVar (bs : List UInt8) : Option (Nat × List UInt8) := getVarGo bs.length 0 bs

/-! ## Zig-zag differences -/

def zz (prev v : Nat) : Nat := if prev ≤ v then 2 * (v - prev) else 2 * (prev - v) - 1

def unzz (prev z : Nat) : Option Nat :=
  if z % 2 = 0 then some (prev + z / 2)
  else if (z + 1) / 2 ≤ prev then some (prev - (z + 1) / 2) else none

/-! ## The specification codec -/

def rawBytes (xs : List Nat) : List UInt8 := (xs.map put64).flatten

def deltaBytes (xs : List Nat) : List UInt8 :=
  (List.zipWith (fun p x => putVar (zz p x) []) (0 :: xs) xs).flatten

/-- The frame of a column: the codec choice is part of the format. -/
def frameBytes : List Nat → List UInt8
  | [] => [tagRaw]
  | x :: rest =>
    if rest.all (· == x) then tagConst :: put64 x
    else if (deltaBytes (x :: rest)).length < 8 * (rest.length + 1) then
      tagDelta :: deltaBytes (x :: rest)
    else tagRaw :: rawBytes (x :: rest)

def columnAdmitted (xs : List Nat) : Bool := xs.all (· < two64)

def encodeColumn? (xs : List Nat) : Option (List UInt8) :=
  if columnAdmitted xs then some (frameBytes xs) else none

def getRawGo : Nat → List UInt8 → List Nat → Option (List Nat × List UInt8)
  | 0, bs, acc => some (acc.reverse, bs)
  | n + 1, bs, acc =>
    match get64 bs with
    | none => none
    | some (v, rest) => getRawGo n rest (v :: acc)

def getDeltaGo : Nat → Nat → List UInt8 → List Nat → Option (List Nat × List UInt8)
  | 0, _, bs, acc => some (acc.reverse, bs)
  | n + 1, prev, bs, acc =>
    match getVar bs with
    | none => none
    | some (z, rest) =>
      match unzz prev z with
      | none => none
      | some v => if v < two64 then getDeltaGo n v rest (v :: acc) else none

/-- A frame of `n` rows at the front of `bs`: the column and the bytes after
    the frame. -/
def decodeColumn (n : Nat) : List UInt8 → Option (List Nat × List UInt8)
  | [] => none
  | t :: bs =>
    if t == tagConst then
      match get64 bs with
      | some (v, rest) => some (List.replicate n v, rest)
      | none => none
    else if t == tagRaw then getRawGo n bs []
    else if t == tagDelta then getDeltaGo n 0 bs []
    else none

/-! ## The byte-array decoder (runtime) -/

def get64At (b : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  if h : i + 8 ≤ b.size then
    some (b[i].toNat + b[i + 1].toNat * 256 + b[i + 2].toNat * 65536 +
      b[i + 3].toNat * 16777216 + b[i + 4].toNat * 4294967296 +
      b[i + 5].toNat * 1099511627776 + b[i + 6].toNat * 281474976710656 +
      b[i + 7].toNat * 72057594037927936, i + 8)
  else none

def get32At (b : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  if h : i + 4 ≤ b.size then
    some (b[i].toNat + b[i + 1].toNat * 256 + b[i + 2].toNat * 65536 +
      b[i + 3].toNat * 16777216, i + 4)
  else none

def getVarAtGo (b : ByteArray) : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _ => none
  | f + 1, acc, i =>
    if h : i < b.size then
      if b[i].toNat < 128 then some (acc * 128 + b[i].toNat, i + 1)
      else getVarAtGo b f (acc * 128 + (b[i].toNat - 128)) (i + 1)
    else none

def getVarAt (b : ByteArray) (i : Nat) : Option (Nat × Nat) := getVarAtGo b (b.size - i) 0 i

def rawAtGo (b : ByteArray) : Nat → Nat → Array Nat → Option (Array Nat × Nat)
  | 0, i, acc => some (acc, i)
  | n + 1, i, acc =>
    match get64At b i with
    | none => none
    | some (v, j) => rawAtGo b n j (acc.push v)

def deltaAtGo (b : ByteArray) : Nat → Nat → Nat → Array Nat → Option (Array Nat × Nat)
  | 0, _, i, acc => some (acc, i)
  | n + 1, prev, i, acc =>
    match getVarAt b i with
    | none => none
    | some (z, j) =>
      match unzz prev z with
      | none => none
      | some v => if v < two64 then deltaAtGo b n v j (acc.push v) else none

/-- `decodeColumn` over a byte array from position `i`: the column and the
    position after the frame (`ColumnTheorems.decodeColumnAt_eq`). -/
def decodeColumnAt (b : ByteArray) (n i : Nat) : Option (Array Nat × Nat) :=
  if h : i < b.size then
    let t := b[i]
    if t == tagConst then
      match get64At b (i + 1) with
      | some (v, j) => some (Array.replicate n v, j)
      | none => none
    else if t == tagRaw then rawAtGo b n (i + 1) (Array.mkEmpty n)
    else if t == tagDelta then deltaAtGo b n 0 (i + 1) (Array.mkEmpty n)
    else none
  else none

/-! ## The byte-array encoder (packer) -/

def pushU64 (out : ByteArray) (v : Nat) : ByteArray :=
  out.push v.toUInt8 |>.push (v / 256).toUInt8 |>.push (v / 65536).toUInt8
    |>.push (v / 16777216).toUInt8 |>.push (v / 4294967296).toUInt8
    |>.push (v / 1099511627776).toUInt8 |>.push (v / 281474976710656).toUInt8
    |>.push (v / 72057594037927936).toUInt8

def pushU32 (out : ByteArray) (v : Nat) : ByteArray :=
  out.push v.toUInt8 |>.push (v / 256).toUInt8 |>.push (v / 65536).toUInt8
    |>.push (v / 16777216).toUInt8

/-- The number of continuation groups of `n` (groups after the first). -/
def varExtraGo : Nat → Nat → Nat → Nat
  | 0, _, c => c
  | f + 1, n, c => if n < 128 then c else varExtraGo f (n / 128) (c + 1)

/-- Push group `j`, then groups `j-1 .. 0` of `n`, most significant first. -/
def pushVarGo (n : Nat) : Nat → ByteArray → ByteArray
  | 0, out => out.push (n % 128).toUInt8
  | j + 1, out => pushVarGo n j (out.push ((n >>> (7 * (j + 1))) % 128 + 128).toUInt8)

def pushVar (out : ByteArray) (n : Nat) : ByteArray :=
  pushVarGo n (varExtraGo n n 0) out

def allSameGo (xs : Array Nat) (x : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | f + 1, i => if h : i < xs.size then (xs[i] == x && allSameGo xs x f (i + 1)) else true

def rawFastGo (xs : Array Nat) : Nat → Nat → ByteArray → ByteArray
  | 0, _, out => out
  | f + 1, i, out => if h : i < xs.size then rawFastGo xs f (i + 1) (pushU64 out xs[i]) else out

def deltaFastGo (xs : Array Nat) : Nat → Nat → Nat → ByteArray → ByteArray
  | 0, _, _, out => out
  | f + 1, i, prev, out =>
    if h : i < xs.size then deltaFastGo xs f (i + 1) xs[i] (pushVar out (zz prev xs[i])) else out

/-- The packer's frame encoder: the same choice as `frameBytes`. -/
def encodeColumnFast (xs : Array Nat) : ByteArray :=
  if h : 0 < xs.size then
    let x := xs[0]
    if allSameGo xs x xs.size 1 then pushU64 (ByteArray.mk #[tagConst]) x
    else
      let d := deltaFastGo xs xs.size 0 0 (ByteArray.emptyWithCapacity (2 * xs.size + 8) |>.push tagDelta)
      if d.size - 1 < 8 * xs.size then d
      else rawFastGo xs xs.size 0 (ByteArray.emptyWithCapacity (8 * xs.size + 1) |>.push tagRaw)
  else ByteArray.mk #[tagRaw]

/-! ## Unit tests -/

private def enc (xs : List Nat) : List UInt8 := (encodeColumn? xs).getD []

#guard getVar (putVar 0 [9]) == some (0, [9])
#guard getVar (putVar 127 [9]) == some (127, [9])
#guard getVar (putVar 128 [9]) == some (128, [9])
#guard getVar (putVar 300 []) == some (300, [])
#guard getVar (putVar 18446744073709551615 [1]) == some (18446744073709551615, [1])
#guard putVar 300 [] == [130, 44]
#guard (putVar 18446744073709551615 []).length == 10
#guard get64 (put64 18446744073709551615 ++ [5]) == some (18446744073709551615, [5])
#guard get32 (put32 4294967295 ++ [5]) == some (4294967295, [5])
#guard unzz 10 (zz 10 3) == some 3
#guard unzz 3 (zz 3 10) == some 10
#guard unzz 0 1 == none
#guard enc [7, 7, 7] == [0, 7, 0, 0, 0, 0, 0, 0, 0]
#guard enc [] == [1]
#guard (enc [1, 2, 3, 500]).head? == some 2
#guard (enc [9223372036854775808, 0, 9223372036854775808]).head? == some 1
#guard encodeColumn? [18446744073709551616] == none
#guard [[7, 7, 7], [], [1, 2, 3, 500], [0, 18446744073709551615, 0], [9223372036854775808, 0, 9223372036854775808], [5], [9, 3, 9, 3],
        [2305843009213693952, 2305843009213693953, 2305843009213693960]].all fun xs =>
  decodeColumn xs.length (enc xs ++ [42]) == some (xs, [42]) &&
  (encodeColumnFast xs.toArray).data.toList == enc xs &&
  (decodeColumnAt ⟨(enc xs ++ [42]).toArray⟩ xs.length 0).map (fun r => (r.1.toList, r.2)) ==
    some (xs, (enc xs).length)
#guard decodeColumn 2 [3, 0, 0] == none
#guard decodeColumn 2 [1, 0, 0] == none
#guard decodeColumnAt ⟨#[3, 0, 0]⟩ 1 0 == none
-- a delta value at or above 2^64 is refused
#guard decodeColumn 1 (tagDelta :: putVar (2 * 18446744073709551616) []) == none

end L4Factoidal.Storage.Sbm11.Column
