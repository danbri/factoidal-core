/-
L4Factoidal.Storage.Sbm11.VarintWord — a varint read without a data-dependent
branch per byte, and the zigzag step without a branch on the sign
(https://github.com/danbri/factoidal/issues/930).

The delta frames of `Sip` hold one varint per row: seven value bits per byte,
most significant group first, the continuation bit (bit 7) set on every byte
but the last. A byte loop tests that bit once per byte, and the length of the
varint of a random column is not predictable (a mispredicted branch costs
more than the loop body; `valgrind --tool=cachegrind --branch-sim=yes` on
DBpedia query d14: 455,383 mispredicted conditional branches in the gather
loop, record section 11.16).

`lenMask` and `vVal` read a varint of up to eight bytes from the 64-bit
window `w` at its start with word operations only:

* `y = w ||| C7` has bit 7 of byte `k` equal to the continuation bit of byte
  `k` and every other bit set. When no byte of the window ends a varint,
  `y` is all ones.
* `lenMask y = y ^^^ (y + 1)` is the mask of the bytes from byte 0 to the
  first byte whose continuation bit is clear: the carry of `y + 1` runs
  through the bytes that are `0xFF` and stops at the first byte `0x7F`.
* `vLen m` is the number of those bytes, `vVal w m` the value they hold.
  `vCompress` packs the seven-bit groups of the eight bytes, byte 0 into the
  highest position (three shift-or steps), and the variable shift drops the
  positions of the bytes after the last one.

`VarintWordTheorems.fastRead_spec`: for a window whose bytes `0 .. n-1` have
the continuation bit set and whose byte `n` has it clear (`n < 8`), the
length is `n + 1` and the value is the value the byte loop computes.

`zzV` and `zzOk` are the zigzag step of the delta frames without a branch on
the sign: `VarintWordTheorems.zz_spec`.
-/
namespace L4Factoidal.Storage.Sbm11.VarintWord

/-- Bits 0 to 6 of every byte. -/
@[inline] def C7 : UInt64 := 0x7f7f7f7f7f7f7f7f

/-- All ones: the `y` of a window in which no byte ends a varint. -/
@[inline] def allOnes : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- The mask of the bytes from byte 0 to the first byte of `y` that is not
    `0xFF` (the carry of `y + 1` stops there). -/
@[inline] def lenMask (y : UInt64) : UInt64 := y ^^^ (y + 1)

/-- Packs the seven-bit groups of the eight bytes of `x` (bit 7 of every byte
    clear): the group of byte `k` goes to bits `7 * (7 - k)` to
    `7 * (7 - k) + 6`. -/
@[inline] def vCompress (x : UInt64) : UInt64 :=
  let a : UInt64 := ((x &&& 0x00FF00FF00FF00FF) <<< (7 : UInt64)) ||| ((x >>> (8 : UInt64)) &&& 0x00FF00FF00FF00FF)
  let y : UInt64 := ((a &&& 0x0000FFFF0000FFFF) <<< (14 : UInt64)) ||| ((a >>> (16 : UInt64)) &&& 0x0000FFFF0000FFFF)
  ((y &&& 0x00000000FFFFFFFF) <<< (28 : UInt64)) ||| (y >>> (32 : UInt64))

/-- The number of bytes of the mask `m = lenMask y`: the sum of its bytes'
    low bits, collected in the top byte by one multiplication. -/
@[inline] def vLen (m : UInt64) : UInt64 :=
  ((m &&& 0x0101010101010101) * 0x0101010101010101) >>> (56 : UInt64)

/-- The value of the varint at the start of the window `w`, whose mask is
    `m`. -/
@[inline] def vVal (w m : UInt64) : UInt64 :=
  vCompress (w &&& m &&& C7) >>> (56 - 7 * vLen m)

/-- The value after the zigzag step of a delta frame, with the sign
    taken from the low bit of `z` and no branch: `prev + z / 2` for even
    `z`, `prev - (z / 2 + 1)` for odd `z` (word arithmetic). -/
@[inline] def zzV (prev z : UInt64) : UInt64 := prev + ((z >>> 1) ^^^ (0 - (z &&& 1)))

/-- The step stays inside `0 .. 2 ^ 64 - 1`: no carry out for an even `z`
    (`prev ≤ v`), no borrow for an odd one (`v < prev`). -/
@[inline] def zzOk (prev z v : UInt64) : Bool := decide (v < prev) == ((z &&& 1) == 1)

end L4Factoidal.Storage.Sbm11.VarintWord
