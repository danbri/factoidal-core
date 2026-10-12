/-
L4Factoidal.Codec.Zstd — Zstandard decoding (RFC 8878).

Spec: RFC 8878 "Zstandard Compression and the 'application/zstd' Media
Type". A zstd stream is one or more frames (section 3.1). A Zstandard frame
is a header, one or more blocks, and an optional 32-bit content checksum (the
low 32 bits of XXH64 of the content, seed 0). Skippable frames (section
3.1.2) are skipped. A frame that names a dictionary is refused: this decoder
has no dictionaries.

A block (section 3.1.1.2) is Raw, RLE or Compressed. A Compressed block is a
literals section (3.1.1.3.1: Raw, RLE, Huffman-compressed or treeless, with 1
or 4 Huffman streams) and a sequences section (3.1.1.3.2: literal-length,
offset and match-length codes, each table predefined, RLE, FSE-compressed or
repeated from the previous block). Sequence execution (3.1.1.4) copies
literals and matches into the output with three repeat offsets (3.1.1.5).

## Loops

Every loop over input bytes, bits, literals, sequences or output bytes is a
tail-recursive function whose first argument is a fuel `Nat` that is the
count still to do (so it compiles to a jump, never one stack frame per
item), or a `for` loop in `Id` or `Except` over a range. Running out of fuel
before the work is done is an error with a message, never a truncation.
Buffers are `ByteArray` and `Array`, never `List`.

## Bit streams

FSE table descriptions are read forward, least-significant bit first. The
Huffman literal streams, the Huffman weight stream and the sequences stream
are read backward from their last byte, whose highest set bit is a padding
marker (section 4.1). `bitsAt` reads up to 56 bits at any bit offset of the
input and returns them as a number; a backward stream position is a bit
offset that decreases. Bits below the start of a backward stream read as 0,
as the RFC's reference decoder does when it peeks past the start.

## Errors

The result is `Except String`. Every refusal names the field or the section
that is wrong. No input makes the decoder panic: array reads use `getD` or a
bounds test, and every length read from the input is checked against the
bytes that remain before it is used.
-/

namespace L4Factoidal.Codec.Zstd

/-! ## Byte and bit access -/

/-- Byte `i` of `d`, or 0 past the end. -/
@[inline] def byteAt (d : ByteArray) (i : Nat) : UInt64 :=
  if h : i < d.size then (d[i]'h).toUInt64 else 0

/-- `word64` near the end of `d`: each byte tested (bytes past the end read 0). -/
def word64Slow (d : ByteArray) (i : Nat) : UInt64 :=
  byteAt d i ||| (byteAt d (i+1) <<< 8) ||| (byteAt d (i+2) <<< 16) |||
  (byteAt d (i+3) <<< 24) ||| (byteAt d (i+4) <<< 32) ||| (byteAt d (i+5) <<< 40) |||
  (byteAt d (i+6) <<< 48) ||| (byteAt d (i+7) <<< 56)

/-- The little-endian 64-bit word at byte `i` (bytes past the end read 0).
    One bounds test for the eight bytes when they are all inside `d`; the
    value is `word64Slow d i` (`word64_eq_slow`). -/
@[inline] def word64 (d : ByteArray) (i : Nat) : UInt64 :=
  if h : i + 8 ≤ d.size then
    (d[i]'(by omega)).toUInt64 ||| ((d[i+1]'(by omega)).toUInt64 <<< 8) |||
    ((d[i+2]'(by omega)).toUInt64 <<< 16) ||| ((d[i+3]'(by omega)).toUInt64 <<< 24) |||
    ((d[i+4]'(by omega)).toUInt64 <<< 32) ||| ((d[i+5]'(by omega)).toUInt64 <<< 40) |||
    ((d[i+6]'(by omega)).toUInt64 <<< 48) ||| ((d[i+7]'(by omega)).toUInt64 <<< 56)
  else word64Slow d i

theorem word64_eq_slow (d : ByteArray) (i : Nat) : word64 d i = word64Slow d i := by
  unfold word64 word64Slow byteAt
  split
  · rename_i h
    simp only [show i < d.size by omega, show i + 1 < d.size by omega, show i + 2 < d.size by omega,
      show i + 3 < d.size by omega, show i + 4 < d.size by omega, show i + 5 < d.size by omega,
      show i + 6 < d.size by omega, show i + 7 < d.size by omega, dite_true]
  · rfl

/-! ### `word64U`: the same word with a `UInt64` byte position

`word64` takes a `Nat` position: its generated C does eight `Nat` additions
(each a test for a big number), eight boxed-index byte reads and eight
reference-count tests per word. `word64U` takes the position as `UInt64`
and reads with `ByteArray.uget` at `USize` indices after one test in
`UInt64`; clang -O3 compiles its fast path to two compares and one 8-byte
load (docs/designissues/2026-10-12-lean-to-c-performance.md, "Audit").
`word64U_eq` proves it equal to `word64` at every position. -/

/-- On the fast path of `word64U`, the `USize` index `q + k` is exact and the
    eight bytes are inside `d`. -/
theorem word64U_toNat {d : ByteArray} {q : UInt64}
    (h : 8 ≤ d.usize.toUInt64 ∧ q ≤ d.usize.toUInt64 - 8) (k : Nat) (hk : k < 8) :
    (q.toUSize + k.toUSize).toNat = q.toNat + k ∧ q.toNat + 8 ≤ d.size := by
  obtain ⟨h1, h2⟩ := h
  have a1 := UInt64.le_iff_toNat_le.mp h1
  have a2 := UInt64.le_iff_toNat_le.mp h2
  have hb : (2 : Nat) ^ System.Platform.numBits ≤ 2 ^ 64 := by
    rcases System.Platform.numBits_eq with e | e <;> rw [e] <;> decide
  have h8 : 8 ≤ 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with e | e <;> rw [e] <;> decide
  have hu : d.usize.toUInt64.toNat = d.size % 2 ^ System.Platform.numBits := by
    simp [ByteArray.usize, USize.toUInt64, Nat.toUSize]
  have hm := Nat.mod_lt d.size (by omega : 0 < 2 ^ System.Platform.numBits)
  have hml := Nat.mod_le d.size (2 ^ System.Platform.numBits)
  rw [UInt64.toNat_sub_of_le _ _ h1] at a2
  have e8 : (8 : UInt64).toNat = 8 := by decide
  simp only [hu, e8] at a1 a2
  refine ⟨?_, by omega⟩
  simp only [USize.toNat_add, UInt64.toNat_toUSize, Nat.toUSize, USize.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by omega : q.toNat < _), Nat.mod_eq_of_lt (by omega : k < _),
    Nat.mod_eq_of_lt (by omega : q.toNat + k < _)]

theorem word64U_lt {d : ByteArray} {q : UInt64}
    (h : 8 ≤ d.usize.toUInt64 ∧ q ≤ d.usize.toUInt64 - 8) (k : Nat) (hk : k < 8) :
    (q.toUSize + k.toUSize).toNat < d.size := by
  have := word64U_toNat h k hk; omega

theorem uget_at (d : ByteArray) (u : USize) (h : u.toNat < d.size) (n : Nat) (e : u.toNat = n) :
    d.uget u h = d[n]'(e ▸ h) := by subst e; rfl

/-- `word64 d q.toNat`, read with one `UInt64` test and eight `uget`
    (`word64U_eq`). -/
@[inline] def word64U (d : ByteArray) (q : UInt64) : UInt64 :=
  if h : 8 ≤ d.usize.toUInt64 ∧ q ≤ d.usize.toUInt64 - 8 then
    (d.uget (q.toUSize + (0 : Nat).toUSize) (word64U_lt h 0 (by decide))).toUInt64 |||
    ((d.uget (q.toUSize + (1 : Nat).toUSize) (word64U_lt h 1 (by decide))).toUInt64 <<< 8) |||
    ((d.uget (q.toUSize + (2 : Nat).toUSize) (word64U_lt h 2 (by decide))).toUInt64 <<< 16) |||
    ((d.uget (q.toUSize + (3 : Nat).toUSize) (word64U_lt h 3 (by decide))).toUInt64 <<< 24) |||
    ((d.uget (q.toUSize + (4 : Nat).toUSize) (word64U_lt h 4 (by decide))).toUInt64 <<< 32) |||
    ((d.uget (q.toUSize + (5 : Nat).toUSize) (word64U_lt h 5 (by decide))).toUInt64 <<< 40) |||
    ((d.uget (q.toUSize + (6 : Nat).toUSize) (word64U_lt h 6 (by decide))).toUInt64 <<< 48) |||
    ((d.uget (q.toUSize + (7 : Nat).toUSize) (word64U_lt h 7 (by decide))).toUInt64 <<< 56)
  else word64Slow d q.toNat

theorem word64U_eq (d : ByteArray) (q : UInt64) : word64U d q = word64 d q.toNat := by
  unfold word64U
  split
  · rename_i h
    have hb := (word64U_toNat h 0 (by decide)).2
    unfold word64
    rw [dif_pos hb]
    rw [uget_at _ _ _ _ (word64U_toNat h 0 (by decide)).1, uget_at _ _ _ _ (word64U_toNat h 1 (by decide)).1,
      uget_at _ _ _ _ (word64U_toNat h 2 (by decide)).1, uget_at _ _ _ _ (word64U_toNat h 3 (by decide)).1,
      uget_at _ _ _ _ (word64U_toNat h 4 (by decide)).1, uget_at _ _ _ _ (word64U_toNat h 5 (by decide)).1,
      uget_at _ _ _ _ (word64U_toNat h 6 (by decide)).1, uget_at _ _ _ _ (word64U_toNat h 7 (by decide)).1]
    rfl
  · rw [word64_eq_slow]

/-- `n` bits (`n ≤ 56`) of `d` at bit offset `p`, least significant first. -/
@[inline] def bitsAt (d : ByteArray) (p n : Nat) : Nat :=
  if n == 0 then 0 else
  ((word64 d (p / 8) >>> (p % 8).toUInt64) &&& ((1 <<< n.toUInt64) - 1)).toNat

/-- The little-endian number in bytes `[i, i+n)` (`n ≤ 8`). -/
def leAt (d : ByteArray) (i n : Nat) : Nat :=
  if n ≥ 8 then (word64 d i).toNat else bitsAt d (i * 8) (n * 8)

/-- Peek `n` bits that END at bit offset `pos` of a backward stream that
    starts at bit `lo`; bits below `lo` read as 0. -/
@[inline] def peekBack (d : ByteArray) (lo pos n : Nat) : Nat :=
  if pos ≥ lo + n then bitsAt d (pos - n) n
  else bitsAt d lo (pos - lo) <<< (n - (pos - lo))

/-- The start position of a backward stream that occupies bytes `[a, b)`:
    the bit just below the padding marker in byte `b - 1`. -/
def backStart (d : ByteArray) (a b : Nat) (what : String) : Except String Nat :=
  if b ≤ a || b > d.size then .error s!"{what}: empty or out-of-range bit stream"
  else
    let last := byteAt d (b - 1)
    if last == 0 then .error s!"{what}: the last byte of the bit stream has no padding marker"
    else .ok ((b - 1) * 8 + Nat.log2 last.toNat)

/-! ## XXH64 (the content checksum) -/

def xP1 : UInt64 := 11400714785074694791
def xP2 : UInt64 := 14029467366897019727
def xP3 : UInt64 := 1609587929392839161
def xP4 : UInt64 := 9650029242287828579
def xP5 : UInt64 := 2870177450012600261

@[inline] def rotl64 (x : UInt64) (r : UInt64) : UInt64 := (x <<< r) ||| (x >>> (64 - r))
@[inline] def xRound (acc input : UInt64) : UInt64 := rotl64 (acc + input * xP2) 31 * xP1
@[inline] def xMerge (acc v : UInt64) : UInt64 := (acc ^^^ xRound 0 v) * xP1 + xP4

/-- The 32-byte stripes: `k` stripes left, starting at byte `i`. -/
def xxStripes (d : ByteArray) : Nat → Nat → UInt64 → UInt64 → UInt64 → UInt64 →
    (UInt64 × UInt64 × UInt64 × UInt64)
  | 0, _, v1, v2, v3, v4 => (v1, v2, v3, v4)
  | k+1, i, v1, v2, v3, v4 =>
    xxStripes d k (i + 32) (xRound v1 (word64 d i)) (xRound v2 (word64 d (i+8)))
      (xRound v3 (word64 d (i+16))) (xRound v4 (word64 d (i+24)))

/-- The 8-byte lanes of the tail: `k` lanes left at byte `i`. -/
def xxLanes (d : ByteArray) : Nat → Nat → UInt64 → UInt64
  | 0, _, h => h
  | k+1, i, h => xxLanes d k (i + 8) (rotl64 (h ^^^ xRound 0 (word64 d i)) 27 * xP1 + xP4)

/-- The single bytes of the tail: `k` bytes left at byte `i`. -/
def xxBytes (d : ByteArray) : Nat → Nat → UInt64 → UInt64
  | 0, _, h => h
  | k+1, i, h => xxBytes d k (i + 1) (rotl64 (h ^^^ byteAt d i * xP5) 11 * xP1)

/-- XXH64 of bytes `[start, start + len)` of `d`, seed `seed`. -/
def xxh64 (d : ByteArray) (start len : Nat) (seed : UInt64 := 0) : UInt64 :=
  let stripes := len / 32
  let h :=
    if stripes > 0 then
      let (v1, v2, v3, v4) := xxStripes d stripes start (seed + xP1 + xP2) (seed + xP2) seed (seed - xP1)
      let h := rotl64 v1 1 + rotl64 v2 7 + rotl64 v3 12 + rotl64 v4 18
      xMerge (xMerge (xMerge (xMerge h v1) v2) v3) v4
    else seed + xP5
  let h := h + len.toUInt64
  let i := start + stripes * 32
  let rest := len - stripes * 32
  let h := xxLanes d (rest / 8) i h
  let i := i + rest / 8 * 8
  let rest := rest % 8
  let (h, i, rest) :=
    if rest ≥ 4 then
      let w := byteAt d i ||| (byteAt d (i+1) <<< 8) ||| (byteAt d (i+2) <<< 16) ||| (byteAt d (i+3) <<< 24)
      (rotl64 (h ^^^ w * xP1) 23 * xP2 + xP3, i + 4, rest - 4)
    else (h, i, rest)
  let h := xxBytes d rest i h
  let h := h ^^^ (h >>> 33)
  let h := h * xP2
  let h := h ^^^ (h >>> 29)
  let h := h * xP3
  h ^^^ (h >>> 32)

/-! ## FSE tables (section 4.1) -/

/-- An FSE decoding table: for each state, the symbol, the number of bits
    to read and the baseline of the next state. -/
structure Fse where
  log  : Nat
  sym  : Array Nat
  nb   : Array Nat
  base : Array Nat
deriving Inhabited

/-- Build the decoding table of accuracy log `log` from the normalised
    counts (`-1` for "less than 1", section 4.1.1). The caller has checked
    that the counts fill `2^log` exactly. -/
def fseBuild (probs : Array Int) (log : Nat) : Except String Fse := do
  let size := 1 <<< log
  let mut sym := Array.replicate size 0
  let mut high := size
  let mut desc : Array Nat := Array.replicate probs.size 0
  for s in [0:probs.size] do
    if probs.getD s 0 == -1 then
      if high == 0 then throw "FSE table: too many \"less than 1\" symbols"
      high := high - 1
      sym := sym.set! high s
      desc := desc.set! s 1
  let step := (size >>> 1) + (size >>> 3) + 3
  let mask := size - 1
  let mut pos := 0
  let mut placed := 0
  for s in [0:probs.size] do
    let p := probs.getD s 0
    if p > 0 then
      desc := desc.set! s p.toNat
      for _ in [0:p.toNat] do
        if placed ≥ high then throw "FSE table: the counts exceed the table"
        sym := sym.set! pos s
        placed := placed + 1
        pos := (pos + step) &&& mask
        for _ in [0:size] do
          if pos < high then break
          pos := (pos + step) &&& mask
  if pos != 0 || placed != high then throw "FSE table: the counts do not fill the table"
  let mut nb := Array.replicate size 0
  let mut base := Array.replicate size 0
  for i in [0:size] do
    let s := sym.getD i 0
    let nsd := desc.getD s 1
    desc := desc.set! s (nsd + 1)
    let b := log - Nat.log2 nsd
    nb := nb.set! i b
    base := base.set! i ((nsd <<< b) - size)
  pure { log, sym, nb, base }

/-- The table of one symbol (RLE mode): accuracy log 0. -/
def fseRle (s : Nat) : Fse := { log := 0, sym := #[s], nb := #[0], base := #[0] }

/-- Read an FSE table description (section 4.1.1) forward from byte
    `start`; it must end at or before byte `limit`. Symbols above `maxSym`
    and accuracy logs above `maxLog` are refused. Returns the table and the
    first byte after the description. -/
def readFseTable (d : ByteArray) (start limit maxSym maxLog : Nat) (what : String) :
    Except String (Fse × Nat) := do
  if start ≥ limit then throw s!"{what}: the FSE table description is missing"
  let mut p := start * 8
  let log := bitsAt d p 4 + 5
  p := p + 4
  if log > maxLog then throw s!"{what}: FSE accuracy log {log} exceeds {maxLog}"
  let mut remaining : Nat := 1 <<< log
  let mut probs : Array Int := #[]
  for _ in [0:maxSym + 2] do
    if remaining == 0 then break
    if probs.size > maxSym then throw s!"{what}: FSE table has a symbol above {maxSym}"
    let bits := Nat.log2 (remaining + 1) + 1
    let raw := bitsAt d p bits
    let lowerMask := (1 <<< (bits - 1)) - 1
    let threshold := (1 <<< bits) - 1 - (remaining + 1)
    let low := raw &&& lowerMask
    let small := low < threshold
    let v := if small then low else if raw > lowerMask then raw - threshold else raw
    p := p + (if small then bits - 1 else bits)
    if v == 0 then
      probs := probs.push (-1)
      remaining := remaining - 1
    else
      let pr := v - 1
      if pr > remaining then throw s!"{what}: FSE count exceeds the remaining total"
      remaining := remaining - pr
      probs := probs.push (Int.ofNat pr)
      if pr == 0 then
        for _ in [0:maxSym + 2] do
          let r := bitsAt d p 2
          p := p + 2
          if probs.size + r > maxSym + 1 then throw s!"{what}: FSE zero run passes symbol {maxSym}"
          for _ in [0:r] do
            probs := probs.push 0
          if r != 3 then break
  if remaining != 0 then throw s!"{what}: FSE counts do not sum to 2^{log}"
  let endByte := (p + 7) / 8
  if endByte > limit then throw s!"{what}: the FSE table description runs past its section"
  let t ← fseBuild probs log
  pure (t, endByte)

/-! ## Predefined distributions and code tables (section 3.1.1.3.2.2) -/

def llDefault : Array Int := #[4, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 1, 1, 1, 1, 1, -1, -1, -1, -1]
def mlDefault : Array Int := #[1, 4, 3, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1]
def ofDefault : Array Int := #[1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1]

def predefLL : Fse := (fseBuild llDefault 6).toOption.getD default
def predefML : Fse := (fseBuild mlDefault 6).toOption.getD default
def predefOF : Fse := (fseBuild ofDefault 5).toOption.getD default

def llBase : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  16, 18, 20, 22, 24, 28, 32, 40, 48, 64, 128, 256, 512, 1024, 2048, 4096,
  8192, 16384, 32768, 65536]
def llBits : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  1, 1, 1, 1, 2, 2, 3, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
def mlBase : Array Nat := #[3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
  19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34,
  35, 37, 39, 41, 43, 47, 51, 59, 67, 83, 99, 131, 259, 515, 1027, 2051,
  4099, 8195, 16387, 32771, 65539]
def mlBits : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  1, 1, 1, 1, 2, 2, 3, 3, 4, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]

/-! ## Huffman literals (section 4.2) -/

/-- A Huffman decoding table indexed by the next `maxBits` bits of the
    stream: the symbol and the length of its code. -/
structure Huf where
  maxBits : Nat
  sym : ByteArray
  nb  : ByteArray
deriving Inhabited

/-- Fill `a[i]` with `v` for `k` positions from `i`. -/
def fillBytes (v : UInt8) : Nat → Nat → ByteArray → ByteArray
  | 0, _, a => a
  | k+1, i, a => fillBytes v k (i + 1) (a.set! i v)

/-- The Huffman table from the transmitted weights; the last weight is
    implied (section 4.2.1). -/
def hufBuild (w0 : Array Nat) : Except String Huf := do
  let mut sum := 0
  for x in w0 do
    if x > 11 then throw "Huffman weights: a weight above 11"
    if x > 0 then sum := sum + (1 <<< (x - 1))
  if sum == 0 then throw "Huffman weights: all weights are zero"
  let maxBits := Nat.log2 sum + 1
  if maxBits > 11 then throw s!"Huffman weights: code length {maxBits} exceeds 11"
  let left := (1 <<< maxBits) - sum
  if left &&& (left - 1) != 0 then throw "Huffman weights: the implied last weight is not a power of 2"
  let w := w0.push (Nat.log2 left + 1)
  if w.size > 256 then throw "Huffman weights: more than 256 symbols"
  let size := 1 <<< maxBits
  let bits := w.map fun x => if x > 0 then maxBits + 1 - x else 0
  let mut rankCount := Array.replicate (maxBits + 1) 0
  for b in bits do
    rankCount := rankCount.modify b (· + 1)
  let mut rankIdx := Array.replicate (maxBits + 1) 0
  let mut nb := ByteArray.mk (Array.replicate size 0)
  for j in [0:maxBits] do
    let i := maxBits - j
    let start := rankIdx.getD i 0
    let stop := start + rankCount.getD i 0 * (1 <<< (maxBits - i))
    if stop > size then throw "Huffman weights: the codes overflow the table"
    rankIdx := rankIdx.set! (i - 1) stop
    nb := fillBytes i.toUInt8 (stop - start) start nb
  if rankIdx.getD 0 0 != size then throw "Huffman weights: the codes do not fill the table"
  let mut sym := ByteArray.mk (Array.replicate size 0)
  for s in [0:w.size] do
    let b := bits.getD s 0
    if b != 0 then
      let code := rankIdx.getD b 0
      let len := 1 <<< (maxBits - b)
      sym := fillBytes s.toUInt8 len code sym
      rankIdx := rankIdx.set! b (code + len)
  pure { maxBits, sym, nb }

/-- Decode the FSE-compressed Huffman weights: two interleaved states on one
    backward stream, until the stream is exhausted (section 4.2.1.2). -/
def hufWeightsLoop (d : ByteArray) (lo : Nat) (t : Fse) :
    Nat → Nat → Nat → Nat → Array Nat → Except String (Array Nat)
  | 0, _, _, _, _ => .error "Huffman weights: more than 255 weights"
  | k+1, pos, s1, s2, acc =>
    let acc := acc.push (t.sym.getD s1 0)
    let n := t.nb.getD s1 0
    if n > pos - lo then .ok (acc.push (t.sym.getD s2 0))
    else
      let s1' := t.base.getD s1 0 + bitsAt d (pos - n) n
      hufWeightsLoop d lo t k (pos - n) s2 s1' acc

/-- The Huffman tree description at byte `p` (section 4.2.1); it must end at
    or before byte `limit`. Returns the table and the next byte. -/
def readHufTree (d : ByteArray) (p limit : Nat) : Except String (Huf × Nat) := do
  if p ≥ limit then throw "Huffman tree description: missing"
  let hb := (byteAt d p).toNat
  if hb ≥ 128 then
    let n := hb - 127
    let nbytes := (n + 1) / 2
    if p + 1 + nbytes > limit then throw "Huffman tree description: direct weights run past the literals section"
    let mut w := Array.emptyWithCapacity n
    for i in [0:n] do
      let b := (byteAt d (p + 1 + i / 2)).toNat
      w := w.push (if i % 2 == 0 then b >>> 4 else b &&& 15)
    pure (← hufBuild w, p + 1 + nbytes)
  else
    let stop := p + 1 + hb
    if stop > limit then throw "Huffman tree description: compressed weights run past the literals section"
    let (t, q) ← readFseTable d (p + 1) stop 255 6 "Huffman weights"
    let pos ← backStart d q stop "Huffman weights"
    let lo := q * 8
    if 2 * t.log > pos - lo then throw "Huffman weights: the stream is shorter than the two initial states"
    let s1 := bitsAt d (pos - t.log) t.log
    let pos := pos - t.log
    let s2 := bitsAt d (pos - t.log) t.log
    let pos := pos - t.log
    let w ← hufWeightsLoop d lo t 255 pos s1 s2 #[]
    pure (← hufBuild w, stop)

/-- Decode `k` literals from one backward Huffman stream starting at bit
    `pos`, whose first bit is `lo`; the stream must end exactly at `lo`. -/
def hufStreamLoop (d : ByteArray) (lo : Nat) (t : Huf) :
    Nat → Nat → ByteArray → Except String ByteArray
  | 0, pos, out =>
    if pos == lo then .ok out else .error "Huffman literal stream: bits left over at the end"
  | k+1, pos, out =>
    let idx := peekBack d lo pos t.maxBits
    let n := (byteAt t.nb idx).toNat
    if n > pos - lo then .error "Huffman literal stream: reads past the start of the stream"
    else hufStreamLoop d lo t k (pos - n) (out.push (byteAt t.sym idx).toUInt8)

def hufStream (d : ByteArray) (t : Huf) (a b n : Nat) (out : ByteArray) : Except String ByteArray := do
  let pos ← backStart d a b "Huffman literal stream"
  hufStreamLoop d (a * 8) t n pos out

/-! ## Decoder state carried between blocks of a frame -/

structure FrameState where
  huf : Option Huf := none
  ll  : Option Fse := none
  of  : Option Fse := none
  ml  : Option Fse := none
  r0  : Nat := 1
  r1  : Nat := 4
  r2  : Nat := 8

/-- Counts for the differential tests: blocks by type, literal sections by
    type. -/
structure Stats where
  frames : Nat := 0
  rawBlocks : Nat := 0
  rleBlocks : Nat := 0
  compressedBlocks : Nat := 0
  rawLits : Nat := 0
  rleLits : Nat := 0
  hufLits : Nat := 0
  treelessLits : Nat := 0
  sequences : Nat := 0
deriving Repr

/-- The largest block content (section 3.1.1.2.4). -/
def blockMax : Nat := 128 * 1024

/-! ## Literals section (section 3.1.1.3.1) -/

/-- Decode the literals section at byte `p` of a block that ends at `stop`.
    Returns the literals, the next byte, the Huffman table to keep, and the
    literal section type. -/
def readLiterals (d : ByteArray) (p stop : Nat) (prev : Option Huf) :
    Except String (ByteArray × Nat × Option Huf × Nat) := do
  if p ≥ stop then throw "literals section: missing"
  let b0 := (byteAt d p).toNat
  let typ := b0 &&& 3
  let sf := (b0 >>> 2) &&& 3
  if typ ≤ 1 then
    let (size, hlen) :=
      if sf &&& 1 == 0 then (b0 >>> 3, 1)
      else if sf == 1 then ((leAt d p 2) >>> 4, 2)
      else ((leAt d p 3) >>> 4, 3)
    if size > blockMax then throw "literals section: Regenerated_Size exceeds 128 KiB"
    let q := p + hlen
    if typ == 0 then
      if q + size > stop then throw "literals section: raw literals run past the block"
      pure (d.extract q (q + size), q + size, prev, 0)
    else
      if q + 1 > stop then throw "literals section: RLE byte missing"
      pure (ByteArray.mk (Array.replicate size (byteAt d q).toUInt8), q + 1, prev, 1)
  else
    let (hlen, fb) := match sf with
      | 0 => (3, 10) | 1 => (3, 10) | 2 => (4, 14) | _ => (5, 18)
    if p + hlen > stop then throw "literals section: header runs past the block"
    let h := leAt d p hlen
    let mask := (1 <<< fb) - 1
    let regen := (h >>> 4) &&& mask
    let comp := (h >>> (4 + fb)) &&& mask
    if regen > blockMax then throw "literals section: Regenerated_Size exceeds 128 KiB"
    let q := p + hlen
    let send := q + comp
    if send > stop then throw "literals section: Compressed_Size runs past the block"
    let (t, q) ←
      if typ == 2 then readHufTree d q send
      else match prev with
        | some t => pure (t, q)
        | none => throw "literals section: treeless literals with no previous Huffman table"
    let lits ←
      if sf == 0 then hufStream d t q send regen (ByteArray.emptyWithCapacity regen)
      else do
        if q + 6 > send then throw "literals section: jump table runs past the section"
        let s1 := leAt d q 2
        let s2 := leAt d (q + 2) 2
        let s3 := leAt d (q + 4) 2
        let a1 := q + 6
        let a2 := a1 + s1
        let a3 := a2 + s2
        let a4 := a3 + s3
        if a4 > send then throw "literals section: stream sizes exceed Compressed_Size"
        let per := (regen + 3) / 4
        if 3 * per > regen then throw "literals section: too few literals for four streams"
        let out := ByteArray.emptyWithCapacity regen
        let out ← hufStream d t a1 a2 per out
        let out ← hufStream d t a2 a3 per out
        let out ← hufStream d t a3 a4 per out
        hufStream d t a4 send (regen - 3 * per) out
    pure (lits, send, some t, typ)

/-! ## Sequences (sections 3.1.1.3.2 and 3.1.1.4) -/

/-- Append bytes `[s, s + len)` of `out` to `out`, where the source may
    overlap the bytes being written (`s < out.size`). Each step copies the
    whole run already available from `s`, so the period is kept and the
    number of steps grows with the logarithm of `len`. -/
def copyMatch (s : Nat) : Nat → Nat → ByteArray → ByteArray
  | 0, _, out => out
  | k+1, rem, out =>
    if rem == 0 then out
    else
      let m := min rem (out.size - s)
      if m == 0 then out
      else
        let chunk := out.extract s (s + m)
        copyMatch s k (rem - m) (out ++ chunk)

/-- Append `out[s + i]` for `i` from `i0`, `k` bytes, one byte at a time (the
    source may overlap the bytes being written). No allocation: `out` is
    unique, `get!` borrows it and `push` grows it in place. -/
def pushCopy (s : Nat) : Nat → Nat → ByteArray → ByteArray
  | 0, _, out => out
  | k+1, i, out => pushCopy s k (i + 1) (out.push (out.get! (s + i)))

theorem get!_eq_dite (a : ByteArray) (n : Nat) : a.get! n = if h : n < a.size then a[n] else 0 := by
  rcases a with ⟨bs⟩
  simp only [ByteArray.get!, ByteArray.size]
  split
  · rename_i h; simp [getElem!_pos, h]; rfl
  · rename_i h; simp [getElem!_neg, h]; rfl

theorem usize_lt_size {a : ByteArray} {i : USize} (h : i < a.usize) : i.toNat < a.size := by
  have h1 := USize.lt_iff_toNat_lt.mp h
  simp only [ByteArray.usize, USize.toNat_ofNat', Nat.toUSize] at h1
  have := Nat.mod_le a.size (2 ^ System.Platform.numBits)
  omega

theorem usize_pred_toNat {k : USize} (h : k ≠ 0) : (k - 1).toNat = k.toNat - 1 := by
  have h0 : k.toNat ≠ 0 := fun e => h (USize.toNat_inj.mp (by simpa using e))
  have h1 : (1 : USize) ≤ k := by
    apply USize.le_iff_toNat_le.mpr
    simp only [USize.toNat_one]
    omega
  rw [USize.toNat_sub_of_le _ _ h1, USize.toNat_one]

/-- `pushCopy` with `USize` counters and an unboxed read (`uget`). The
    generated C of `pushCopy` does, per byte, four `Nat` operations, three
    reference-count tests and a boxed-index read; this one none
    (docs/designissues/2026-10-12-lean-to-c-performance.md).
    `pushCopyU_eq`: equal to `pushCopy` when the counts fit in `USize`. -/
def pushCopyU (s : USize) (k i : USize) (out : ByteArray) : ByteArray :=
  if h : k = 0 then out
  else
    let j := s + i
    let b := if hj : j < out.usize then out.uget j (usize_lt_size hj) else 0
    pushCopyU s (k - 1) (i + 1) (out.push b)
termination_by k.toNat
decreasing_by
  have := usize_pred_toNat h
  have : k.toNat ≠ 0 := fun e => h (USize.toNat_inj.mp (by simpa using e))
  omega

theorem pushCopyU_eq (s i : USize) (out : ByteArray) : ∀ (k : USize),
    s.toNat + i.toNat + k.toNat < USize.size → out.size + k.toNat < USize.size →
    pushCopyU s k i out = pushCopy s.toNat k.toNat i.toNat out := by
  intro k
  induction hk : k.toNat generalizing k i out with
  | zero =>
    intro _ _
    have : k = 0 := USize.toNat_inj.mp (by simpa using hk)
    subst this
    unfold pushCopyU; simp [pushCopy]
  | succ n ih =>
    intro h1 h2
    have hk0 : k ≠ 0 := by intro e; subst e; simp at hk
    rw [pushCopyU, dif_neg hk0]
    simp only [pushCopy]
    have hs : USize.size = 2 ^ System.Platform.numBits := rfl
    have hi : (i + 1).toNat = i.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; apply Nat.mod_eq_of_lt; omega
    have hj : (s + i).toNat = s.toNat + i.toNat := by
      rw [USize.toNat_add]; apply Nat.mod_eq_of_lt; omega
    have hb : (if hj : s + i < out.usize then out.uget (s + i) (usize_lt_size hj) else 0)
        = out.get! (s.toNat + i.toNat) := by
      rw [get!_eq_dite]
      have hu : out.usize.toNat = out.size := by
        simp only [ByteArray.usize, USize.toNat_ofNat', Nat.toUSize]
        apply Nat.mod_eq_of_lt; omega
      by_cases c : s + i < out.usize
      · have c' : s.toNat + i.toNat < out.size := by
          have := USize.lt_iff_toNat_lt.mp c; omega
        rw [dif_pos c, dif_pos c']
        rcases out with ⟨bs⟩
        simp only [ByteArray.uget, ← hj]
        rfl
      · have c' : ¬ s.toNat + i.toNat < out.size := by
          intro c'; apply c; apply USize.lt_iff_toNat_lt.mpr; omega
        rw [dif_neg c, dif_neg c']
    rw [hb]
    have hk' : (k - 1).toNat = n := by rw [usize_pred_toNat hk0]; omega
    rw [ih (i + 1) (out.push _) (k - 1) hk' (by omega) (by simp [ByteArray.size_push]; omega), hi]

/-- A bound below `USize.size` on every platform that is also a small (unboxed)
    `Nat` on every platform: a test against `USize.size` itself compiles to
    a big-number comparison on 64-bit hosts (2^64 is not a small `Nat`), which
    put `lean_nat_big_lt` and GMP in the decoder's profile on 2026-10-12. -/
def copyBound : Nat := 1073741824

theorem copyBound_le : copyBound ≤ USize.size := by
  rcases USize.size_eq with e | e <;> rw [e] <;> decide

/-- Append `out[s + i]` for `i < k`, as `pushCopy s k 0 out`
    (`copyShort_eq`): by `pushCopyU` when the counts are below `copyBound`
    (one test per match), else by `pushCopy`. -/
@[inline] def copyShort (s k : Nat) (out : ByteArray) : ByteArray :=
  if s + k < copyBound ∧ out.size + k < copyBound then
    pushCopyU s.toUSize k.toUSize 0 out
  else pushCopy s k 0 out

theorem copyShort_eq (s k : Nat) (out : ByteArray) : copyShort s k out = pushCopy s k 0 out := by
  unfold copyShort
  have hb := copyBound_le
  split
  · rename_i h
    have hs : s.toUSize.toNat = s := by
      simp only [Nat.toUSize, USize.toNat_ofNat']; exact Nat.mod_eq_of_lt (by have := h.1; simp only [USize.size] at hb; omega)
    have hk : k.toUSize.toNat = k := by
      simp only [Nat.toUSize, USize.toNat_ofNat']; exact Nat.mod_eq_of_lt (by have := h.1; simp only [USize.size] at hb; omega)
    rw [pushCopyU_eq _ _ _ _ (by rw [hs, hk]; simp; omega) (by rw [hk]; omega), hs, hk]
    rfl
  · rfl

/-- Matches of at most this many bytes are copied byte by byte (`pushCopy`);
    longer ones by `copyMatch`, which allocates one chunk per step. -/
def shortMatch : Nat := 32

structure SeqOut where
  out : ByteArray
  litPos : Nat
  r0 : Nat
  r1 : Nat
  r2 : Nat

/-- `n` bits (`n ≤ 56`) of `d` at bit offset `p`, as `bitsAt`, in `UInt64`
    arithmetic. The word is read by `word64U` (since 2026-10-12; before, by
    `word64` at a `Nat` position, the same value: `bitsAtU_eq`). -/
@[inline] def bitsAtU (d : ByteArray) (p n : UInt64) : UInt64 :=
  if n == 0 then 0 else
  (word64U d (p >>> 3) >>> (p &&& 7)) &&& (((1 : UInt64) <<< n) - 1)

theorem bitsAtU_eq (d : ByteArray) (p n : UInt64) : bitsAtU d p n =
    if n == 0 then (0 : UInt64) else
    (word64 d (p >>> 3).toNat >>> (p &&& 7)) &&& (((1 : UInt64) <<< n) - 1) := by
  simp only [bitsAtU, word64U_eq]

/-- Decode and execute `k` sequences from the backward stream at bit `pos`
    (first bit `lo`). The states, repeat offsets, literal position and
    output are the accumulators. The bit position, the three states and the
    repeat offsets are `UInt64` (every value fits: positions are bit offsets
    of the input, states are below 2^9, offsets below 2^32); the literal
    position is a `Nat` (it indexes `lits`). Until 2026-10-11 all of them
    were `Nat`, with the same steps: `l4qlvr zstd-diff` over the 1,860
    column frames of the QLever instance gave 218 MB/s of output then and
    268-280 MB/s with `UInt64` (docs/designissues/2026-10-11-qlvr-performance.md). -/
def seqLoop (d : ByteArray) (lo : UInt64) (llT ofT mlT : Fse) (lits : ByteArray)
    (frameStart maxOut : Nat) :
    Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → Nat → ByteArray →
      Except String SeqOut
  | 0, pos, _, _, _, r0, r1, r2, litPos, out =>
    if pos != lo then .error "sequences section: bits left over at the end of the stream"
    else .ok ⟨out, litPos, r0.toNat, r1.toNat, r2.toNat⟩
  | k+1, pos, sLL, sOF, sML, r0, r1, r2, litPos, out =>
    let ofc := (ofT.sym.getD sOF.toNat 0).toUInt64
    let llc := llT.sym.getD sLL.toNat 0
    let mlc := mlT.sym.getD sML.toNat 0
    let llb := (llBits.getD llc 0).toUInt64
    let mlb := (mlBits.getD mlc 0).toUInt64
    if ofc > 31 then .error s!"sequences section: offset code {ofc} above 31"
    else if ofc + mlb + llb > pos - lo then .error "sequences section: the stream ends inside a sequence"
    else
    let pos := pos - ofc
    let ofv := ((1 : UInt64) <<< ofc) + bitsAtU d pos ofc
    let pos := pos - mlb
    let ml := (mlBase.getD mlc 0).toUInt64 + bitsAtU d pos mlb
    let pos := pos - llb
    let ll := (llBase.getD llc 0).toUInt64 + bitsAtU d pos llb
    -- repeat offsets (section 3.1.1.5)
    let i := ofv - 1 + (if ll == 0 then 1 else 0)
    let off :=
      if ofv > 3 then ofv - 3
      else if i == 0 then r0 else if i == 1 then r1 else if i == 2 then r2
      else if r0 == 0 then 0 else r0 - 1
    let n1 := if ofv ≤ 3 && i == 0 then r1 else r0
    let n2 := if ofv > 3 then r1 else if i ≤ 1 then r2 else r1
    -- state update, except after the last sequence: LL, ML, OF
    let nLL := (llT.nb.getD sLL.toNat 0).toUInt64
    let nML := (mlT.nb.getD sML.toNat 0).toUInt64
    let nOF := (ofT.nb.getD sOF.toNat 0).toUInt64
    if k != 0 && nLL + nML + nOF > pos - lo then .error "sequences section: the stream ends inside a state update"
    else
    let pos1 := if k != 0 then pos - nLL else pos
    let sLL' := if k != 0 then (llT.base.getD sLL.toNat 0).toUInt64 + bitsAtU d pos1 nLL else sLL
    let pos2 := if k != 0 then pos1 - nML else pos1
    let sML' := if k != 0 then (mlT.base.getD sML.toNat 0).toUInt64 + bitsAtU d pos2 nML else sML
    let pos3 := if k != 0 then pos2 - nOF else pos2
    let sOF' := if k != 0 then (ofT.base.getD sOF.toNat 0).toUInt64 + bitsAtU d pos3 nOF else sOF
    -- execution (section 3.1.1.4)
    let llN := ll.toNat
    let mlN := ml.toNat
    if litPos + llN > lits.size then .error "sequences section: Literals_Length exceeds the literals"
    else if out.size + llN + mlN > maxOut then .error "frame: output exceeds the limit"
    else
    let out := lits.copySlice litPos out out.size llN false
    if off == 0 then .error "sequences section: offset 0"
    else if off.toNat > out.size - frameStart then .error "sequences section: offset reaches before the start of the frame"
    else
    let s := out.size - off.toNat
    let out := if mlN ≤ shortMatch then copyShort s mlN out
      else copyMatch s (mlN + 1) mlN out
    seqLoop d lo llT ofT mlT lits frameStart maxOut k pos3 sLL' sOF' sML' off n1 n2 (litPos + llN) out

/-- Select one of the three sequence tables (section 3.1.1.3.2.1). -/
def readSeqTable (mode : Nat) (d : ByteArray) (p stop : Nat) (prev : Option Fse)
    (predef : Fse) (maxSym maxLog : Nat) (what : String) : Except String (Fse × Nat) :=
  match mode with
  | 0 => .ok (predef, p)
  | 1 =>
    if p ≥ stop then .error s!"{what}: RLE symbol missing"
    else
      let s := (byteAt d p).toNat
      if s > maxSym then .error s!"{what}: RLE symbol {s} above {maxSym}"
      else .ok (fseRle s, p + 1)
  | 2 => readFseTable d p stop maxSym maxLog what
  | _ => match prev with
    | some t => .ok (t, p)
    | none => .error s!"{what}: repeat mode with no previous table"

/-- Decode one Compressed block in bytes `[p, stop)` into `out`. -/
def compressedBlock (d : ByteArray) (p stop : Nat) (st : FrameState) (stats : Stats)
    (out : ByteArray) (frameStart maxOut : Nat) :
    Except String (ByteArray × FrameState × Stats) := do
  let startSize := out.size
  let (lits, q, huf, ltyp) ← readLiterals d p stop st.huf
  let stats := match ltyp with
    | 0 => { stats with rawLits := stats.rawLits + 1 }
    | 1 => { stats with rleLits := stats.rleLits + 1 }
    | 2 => { stats with hufLits := stats.hufLits + 1 }
    | _ => { stats with treelessLits := stats.treelessLits + 1 }
  let st := { st with huf := huf }
  if q ≥ stop then throw "sequences section: Number_of_Sequences missing"
  let b0 := (byteAt d q).toNat
  let (nseq, q) ←
    if b0 == 0 then pure (0, q + 1)
    else if b0 < 128 then pure (b0, q + 1)
    else if b0 < 255 then
      if q + 2 > stop then throw "sequences section: Number_of_Sequences runs past the block"
      else pure (((b0 - 128) <<< 8) + (byteAt d (q + 1)).toNat, q + 2)
    else
      if q + 3 > stop then throw "sequences section: Number_of_Sequences runs past the block"
      else pure ((byteAt d (q + 1)).toNat + ((byteAt d (q + 2)).toNat <<< 8) + 0x7F00, q + 3)
  if nseq == 0 then
    if q != stop then throw "sequences section: bytes after a section with no sequences"
    if out.size + lits.size > maxOut then throw "frame: output exceeds the limit"
    return (out ++ lits, st, stats)
  if q ≥ stop then throw "sequences section: Symbol_Compression_Modes missing"
  let modes := (byteAt d q).toNat
  if modes &&& 3 != 0 then throw "sequences section: reserved bits of Symbol_Compression_Modes set"
  let (llT, q) ← readSeqTable (modes >>> 6) d (q + 1) stop st.ll predefLL 35 9 "literal-length table"
  let (ofT, q) ← readSeqTable ((modes >>> 4) &&& 3) d q stop st.of predefOF 31 8 "offset table"
  let (mlT, q) ← readSeqTable ((modes >>> 2) &&& 3) d q stop st.ml predefML 52 9 "match-length table"
  let pos ← backStart d q stop "sequences section"
  let lo := q * 8
  if llT.log + ofT.log + mlT.log > pos - lo then throw "sequences section: the stream is shorter than the initial states"
  let sLL := bitsAt d (pos - llT.log) llT.log
  let pos := pos - llT.log
  let sOF := bitsAt d (pos - ofT.log) ofT.log
  let pos := pos - ofT.log
  let sML := bitsAt d (pos - mlT.log) mlT.log
  let pos := pos - mlT.log
  let r ← seqLoop d lo.toUInt64 llT ofT mlT lits frameStart maxOut nseq pos.toUInt64 sLL.toUInt64
    sOF.toUInt64 sML.toUInt64 st.r0.toUInt64 st.r1.toUInt64 st.r2.toUInt64 0 out
  let rest := lits.size - r.litPos
  if r.out.size + rest > maxOut then throw "frame: output exceeds the limit"
  let out := lits.copySlice r.litPos r.out r.out.size rest false
  if out.size - startSize > blockMax then throw "block: decompressed size exceeds 128 KiB"
  pure (out, { st with ll := some llT, of := some ofT, ml := some mlT, r0 := r.r0, r1 := r.r1, r2 := r.r2 },
    { stats with sequences := stats.sequences + nseq })

/-! ## Frames (section 3.1.1) -/

def zstdMagic : Nat := 0xFD2FB528

/-- Decode the frame at byte `p` and append its content to `out`. Returns
    the output, the byte after the frame and the updated counts. -/
def decodeFrame (d : ByteArray) (p : Nat) (out : ByteArray) (stats : Stats) (maxOut : Nat) :
    Except String (ByteArray × Nat × Stats) := do
  if p + 4 > d.size then throw "frame: truncated magic number"
  let magic := leAt d p 4
  if magic &&& 0xFFFFFFF0 == 0x184D2A50 then
    if p + 8 > d.size then throw "skippable frame: truncated Frame_Size"
    let n := leAt d (p + 4) 4
    if p + 8 + n > d.size then throw "skippable frame: data runs past the input"
    return (out, p + 8 + n, stats)
  if magic != zstdMagic then throw s!"frame: magic number {magic} is not 0xFD2FB528"
  if p + 5 > d.size then throw "frame: Frame_Header_Descriptor missing"
  let fhd := (byteAt d (p + 4)).toNat
  let fcsFlag := fhd >>> 6
  let single := (fhd >>> 5) &&& 1 == 1
  if (fhd >>> 3) &&& 1 == 1 then throw "frame: reserved bit of Frame_Header_Descriptor set"
  let checksum := (fhd >>> 2) &&& 1 == 1
  let dictBytes := match fhd &&& 3 with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 4
  let q := p + 5
  let q := if single then q else q + 1
  let fcsBytes := match fcsFlag with
    | 0 => if single then 1 else 0 | 1 => 2 | 2 => 4 | _ => 8
  if q + dictBytes + fcsBytes > d.size then throw "frame: header runs past the input"
  let dictId := leAt d q dictBytes
  if dictId != 0 then throw s!"frame: Dictionary_ID {dictId} is present; dictionaries are not supported"
  let q := q + dictBytes
  let fcs : Option Nat :=
    if fcsBytes == 0 then none
    else
      let v := leAt d q fcsBytes
      some (if fcsBytes == 2 then v + 256 else v)
  let q := q + fcsBytes
  let frameStart := out.size
  let mut out := out
  let mut q := q
  let mut st : FrameState := {}
  let mut stats := { stats with frames := stats.frames + 1 }
  let mut last := false
  for _ in [0:d.size] do
    if q + 3 > d.size then throw "block: truncated Block_Header"
    let bh := leAt d q 3
    last := bh &&& 1 == 1
    let btype := (bh >>> 1) &&& 3
    let bsize := bh >>> 3
    q := q + 3
    match btype with
    | 0 =>
      if q + bsize > d.size then throw "block: raw block runs past the input"
      if bsize > blockMax then throw "block: Block_Size exceeds 128 KiB"
      if out.size + bsize > maxOut then throw "frame: output exceeds the limit"
      out := d.copySlice q out out.size bsize false
      q := q + bsize
      stats := { stats with rawBlocks := stats.rawBlocks + 1 }
    | 1 =>
      if q + 1 > d.size then throw "block: RLE byte missing"
      if bsize > blockMax then throw "block: Block_Size exceeds 128 KiB"
      if out.size + bsize > maxOut then throw "frame: output exceeds the limit"
      out := out ++ ByteArray.mk (Array.replicate bsize (byteAt d q).toUInt8)
      q := q + 1
      stats := { stats with rleBlocks := stats.rleBlocks + 1 }
    | 2 =>
      if q + bsize > d.size then throw "block: compressed block runs past the input"
      if bsize > blockMax then throw "block: Block_Size exceeds 128 KiB"
      let (o, s, t) ← compressedBlock d q (q + bsize) st stats out frameStart maxOut
      out := o; st := s
      stats := { t with compressedBlocks := t.compressedBlocks + 1 }
      q := q + bsize
    | _ => throw "block: reserved Block_Type 3"
    if last then break
  if !last then throw "frame: no last block"
  let produced := out.size - frameStart
  match fcs with
  | some n => if n != produced then throw s!"frame: Frame_Content_Size {n} but {produced} bytes decoded"
  | none => pure ()
  if checksum then
    if q + 4 > d.size then throw "frame: Content_Checksum missing"
    let want := leAt d q 4
    let got := (xxh64 out frameStart produced).toNat &&& 0xFFFFFFFF
    if want != got then throw s!"frame: Content_Checksum {want} does not match XXH64 low bits {got}"
    q := q + 4
  pure (out, q, stats)

/-- The most output one call may produce unless the caller says otherwise
    (1 GiB). -/
def maxOutputDefault : Nat := 1024 * 1024 * 1024

/-- Decompress every frame of `d`, with the counts of what was decoded. -/
def decompressStats (d : ByteArray) (maxOut : Nat := maxOutputDefault) (sizeHint : Nat := 0) :
    Except String (ByteArray × Stats) := do
  if d.size == 0 then throw "input: empty, no frame"
  -- `sizeHint`: the expected output size, when the caller knows it; the
  -- output then never grows by reallocation. It does not change the result.
  let mut out := ByteArray.emptyWithCapacity (min sizeHint maxOut)
  let mut p := 0
  let mut stats : Stats := {}
  for _ in [0:d.size] do
    if p ≥ d.size then break
    let (o, q, s) ← decodeFrame d p out stats maxOut
    out := o; p := q; stats := s
  if p < d.size then throw "input: frames left after the frame limit"
  pure (out, stats)

/-- Decompress every frame of `d` (RFC 8878). -/
def decompress (d : ByteArray) (maxOut : Nat := maxOutputDefault) (sizeHint : Nat := 0) :
    Except String ByteArray :=
  (decompressStats d maxOut sizeHint).map (·.1)

end L4Factoidal.Codec.Zstd
