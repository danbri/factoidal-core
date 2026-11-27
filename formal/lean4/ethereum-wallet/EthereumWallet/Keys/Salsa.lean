/-
Salsa20/8 core and scryptBlockMix (RFC 7914 sections 3 and 4).

Words are unboxed `UInt32`; blocks are `ByteArray`s read and written as
little-endian words. `blockMix` can read its input as the XOR of a block and a
slice of a second array, so scryptROMix never builds the XORed block.
Imports nothing outside `Init`. Every loop is structural on a count and a tail
call. Checked against the RFC 7914 vectors (sections 8 and 9) in
`KeystoreTests`; not proved equal to an independent model.
-/

namespace EthereumWallet.Keys

/-- Sixteen 32-bit words: one Salsa20 block. -/
structure S16 where
  x0 : UInt32
  x1 : UInt32
  x2 : UInt32
  x3 : UInt32
  x4 : UInt32
  x5 : UInt32
  x6 : UInt32
  x7 : UInt32
  x8 : UInt32
  x9 : UInt32
  x10 : UInt32
  x11 : UInt32
  x12 : UInt32
  x13 : UInt32
  x14 : UInt32
  x15 : UInt32

/-- RFC 7914 section 3, `R(a,b)`: rotate left, for `0 < b < 32`. -/
@[inline] def rotl32 (a b : UInt32) : UInt32 := (a <<< b) ||| (a >>> (32 - b))

/-- One iteration of the RFC 7914 section 3 loop body (two Salsa20 rounds),
    line for line. -/
@[inline] def salsaDoubleRound (s : S16) : S16 :=
  let ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩ := s
  let x4 := x4 ^^^ rotl32 (x0 + x12) 7
  let x8 := x8 ^^^ rotl32 (x4 + x0) 9
  let x12 := x12 ^^^ rotl32 (x8 + x4) 13
  let x0 := x0 ^^^ rotl32 (x12 + x8) 18
  let x9 := x9 ^^^ rotl32 (x5 + x1) 7
  let x13 := x13 ^^^ rotl32 (x9 + x5) 9
  let x1 := x1 ^^^ rotl32 (x13 + x9) 13
  let x5 := x5 ^^^ rotl32 (x1 + x13) 18
  let x14 := x14 ^^^ rotl32 (x10 + x6) 7
  let x2 := x2 ^^^ rotl32 (x14 + x10) 9
  let x6 := x6 ^^^ rotl32 (x2 + x14) 13
  let x10 := x10 ^^^ rotl32 (x6 + x2) 18
  let x3 := x3 ^^^ rotl32 (x15 + x11) 7
  let x7 := x7 ^^^ rotl32 (x3 + x15) 9
  let x11 := x11 ^^^ rotl32 (x7 + x3) 13
  let x15 := x15 ^^^ rotl32 (x11 + x7) 18
  let x1 := x1 ^^^ rotl32 (x0 + x3) 7
  let x2 := x2 ^^^ rotl32 (x1 + x0) 9
  let x3 := x3 ^^^ rotl32 (x2 + x1) 13
  let x0 := x0 ^^^ rotl32 (x3 + x2) 18
  let x6 := x6 ^^^ rotl32 (x5 + x4) 7
  let x7 := x7 ^^^ rotl32 (x6 + x5) 9
  let x4 := x4 ^^^ rotl32 (x7 + x6) 13
  let x5 := x5 ^^^ rotl32 (x4 + x7) 18
  let x11 := x11 ^^^ rotl32 (x10 + x9) 7
  let x8 := x8 ^^^ rotl32 (x11 + x10) 9
  let x9 := x9 ^^^ rotl32 (x8 + x11) 13
  let x10 := x10 ^^^ rotl32 (x9 + x8) 18
  let x12 := x12 ^^^ rotl32 (x15 + x14) 7
  let x13 := x13 ^^^ rotl32 (x12 + x15) 9
  let x14 := x14 ^^^ rotl32 (x13 + x12) 13
  let x15 := x15 ^^^ rotl32 (x14 + x13) 18
  ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩

/-- Salsa20/8 core on words (RFC 7914 section 3): four double rounds, then the
    word-wise sum with the input. -/
def salsa208 (s : S16) : S16 :=
  let t := salsaDoubleRound (salsaDoubleRound (salsaDoubleRound (salsaDoubleRound s)))
  ⟨t.x0 + s.x0, t.x1 + s.x1, t.x2 + s.x2, t.x3 + s.x3,
   t.x4 + s.x4, t.x5 + s.x5, t.x6 + s.x6, t.x7 + s.x7,
   t.x8 + s.x8, t.x9 + s.x9, t.x10 + s.x10, t.x11 + s.x11,
   t.x12 + s.x12, t.x13 + s.x13, t.x14 + s.x14, t.x15 + s.x15⟩

/-- The little-endian 32-bit word at byte offset `i` (zero bytes past the end). -/
@[inline] def le32 (b : ByteArray) (i : Nat) : UInt32 :=
  (b.get! i).toUInt32 ||| ((b.get! (i + 1)).toUInt32 <<< 8) |||
    ((b.get! (i + 2)).toUInt32 <<< 16) ||| ((b.get! (i + 3)).toUInt32 <<< 24)

/-- Append a word, little-endian. -/
@[inline] def pushLe32 (acc : ByteArray) (w : UInt32) : ByteArray :=
  (((acc.push w.toUInt8).push (w >>> 8).toUInt8).push (w >>> 16).toUInt8).push (w >>> 24).toUInt8

/-- Append a block of sixteen words, little-endian: 64 bytes. -/
def pushS16 (acc : ByteArray) (s : S16) : ByteArray :=
  let acc := pushLe32 (pushLe32 (pushLe32 (pushLe32 acc s.x0) s.x1) s.x2) s.x3
  let acc := pushLe32 (pushLe32 (pushLe32 (pushLe32 acc s.x4) s.x5) s.x6) s.x7
  let acc := pushLe32 (pushLe32 (pushLe32 (pushLe32 acc s.x8) s.x9) s.x10) s.x11
  pushLe32 (pushLe32 (pushLe32 (pushLe32 acc s.x12) s.x13) s.x14) s.x15

/-- The word at byte offset `off` of the input block: `b`, XORed with `v` from
    `voff` on when `xorV` is set. -/
@[inline] def mixWord (b v : ByteArray) (voff : Nat) (xorV : Bool) (off : Nat) : UInt32 :=
  if xorV then le32 b off ^^^ le32 v (voff + off) else le32 b off

/-- `x` XORed with the 64-byte input block at byte offset `off`. -/
@[inline] def xorInput (x : S16) (b v : ByteArray) (voff : Nat) (xorV : Bool) (off : Nat) : S16 :=
  ⟨x.x0 ^^^ mixWord b v voff xorV off, x.x1 ^^^ mixWord b v voff xorV (off + 4),
   x.x2 ^^^ mixWord b v voff xorV (off + 8), x.x3 ^^^ mixWord b v voff xorV (off + 12),
   x.x4 ^^^ mixWord b v voff xorV (off + 16), x.x5 ^^^ mixWord b v voff xorV (off + 20),
   x.x6 ^^^ mixWord b v voff xorV (off + 24), x.x7 ^^^ mixWord b v voff xorV (off + 28),
   x.x8 ^^^ mixWord b v voff xorV (off + 32), x.x9 ^^^ mixWord b v voff xorV (off + 36),
   x.x10 ^^^ mixWord b v voff xorV (off + 40), x.x11 ^^^ mixWord b v voff xorV (off + 44),
   x.x12 ^^^ mixWord b v voff xorV (off + 48), x.x13 ^^^ mixWord b v voff xorV (off + 52),
   x.x14 ^^^ mixWord b v voff xorV (off + 56), x.x15 ^^^ mixWord b v voff xorV (off + 60)⟩

/-- Salsa20/8 core on a 64-byte string (RFC 7914 section 8's form). -/
def salsa208Bytes (b : ByteArray) : ByteArray :=
  pushS16 (ByteArray.emptyWithCapacity 64)
    (salsa208 (xorInput ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ b b 0 false 0))

/-- The scryptBlockMix loop (RFC 7914 section 4, step 2): `count` blocks from
    block `i` on. Even-numbered outputs go to `ye`, odd ones to `yo`; step 3's
    output order is `ye ++ yo`. Structural on `count`, a tail call. -/
def blockMixLoop (b v : ByteArray) (voff : Nat) (xorV : Bool) :
    Nat → Nat → S16 → ByteArray → ByteArray → ByteArray
  | 0, _, _, ye, yo => ye ++ yo
  | count + 1, i, x, ye, yo =>
    let t := salsa208 (xorInput x b v voff xorV (64 * i))
    if i % 2 == 0 then blockMixLoop b v voff xorV count (i + 1) t (pushS16 ye t) yo
    else blockMixLoop b v voff xorV count (i + 1) t ye (pushS16 yo t)

/-- scryptBlockMix (RFC 7914 section 4) with block size parameter `r`, on the
    `128 * r` byte input `b` (`xorV = false`) or on `b XOR v[voff ..]`
    (`xorV = true`). -/
def blockMix (r : Nat) (b v : ByteArray) (voff : Nat) (xorV : Bool) : ByteArray :=
  let x0 := xorInput ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ b v voff xorV (64 * (2 * r - 1))
  blockMixLoop b v voff xorV (2 * r) 0 x0
    (ByteArray.emptyWithCapacity (128 * r)) (ByteArray.emptyWithCapacity (64 * r))

end EthereumWallet.Keys
