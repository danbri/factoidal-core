import EthereumWallet.Keys.Bytes

/-!
# RIPEMD-160

Written from the algorithm's published description (Dobbertin, Bosselaers, Preneel,
"RIPEMD-160: a strengthened version of RIPEMD", 1996). BIP-32 needs it for the
4-byte parent fingerprint in extended-key serialisation, which is public data: no
secret passes through this hash in the wallet.

Tested against the eight vectors of the paper and, through the fingerprints, the BIP-32
vectors. Not proved equal to any other model. Structural, tail recursive loops.
-/

namespace EthereumWallet.Keys.Ripemd160

/-- Message word order, left line. -/
def rl : ByteArray := ByteArray.mk #[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
  3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
  1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
  4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]

/-- Message word order, right line. -/
def rr : ByteArray := ByteArray.mk #[
  5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
  6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
  15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
  8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
  12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]

/-- Rotation amounts, left line. -/
def sl : ByteArray := ByteArray.mk #[
  11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
  7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
  11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
  11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
  9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]

/-- Rotation amounts, right line. -/
def sr : ByteArray := ByteArray.mk #[
  8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
  9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
  9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
  15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
  8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]

def f (j : Nat) (x y z : UInt32) : UInt32 :=
  if j < 16 then x ^^^ y ^^^ z
  else if j < 32 then (x &&& y) ||| (~~~x &&& z)
  else if j < 48 then (x ||| ~~~y) ^^^ z
  else if j < 64 then (x &&& z) ||| (y &&& ~~~z)
  else x ^^^ (y ||| ~~~z)

def kl (j : Nat) : UInt32 :=
  if j < 16 then 0 else if j < 32 then 0x5A827999 else if j < 48 then 0x6ED9EBA1
  else if j < 64 then 0x8F1BBCDC else 0xA953FD4E

def kr (j : Nat) : UInt32 :=
  if j < 16 then 0x50A28BE6 else if j < 32 then 0x5C4DD124 else if j < 48 then 0x6D703EF3
  else if j < 64 then 0x7A6D76E9 else 0

/-- Rotate left by `s`, for `0 < s < 32`. -/
def rol (x s : UInt32) : UInt32 := (x <<< s) ||| (x >>> (32 - s))

structure State where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32

def step (x : Array UInt32) (r s : ByteArray) (k : UInt32) (fj j : Nat) (st : State) : State :=
  let t := rol (st.a + f fj st.b st.c st.d + x[(r.get! j).toNat]! + k) (s.get! j).toUInt32 + st.e
  ⟨st.e, t, st.b, rol st.c 10, st.d⟩

/-- The 80 steps of both lines; `count` steps are left, `j` is the step number. -/
def rounds (x : Array UInt32) : Nat → Nat → State → State → State × State
  | 0, _, l, r => (l, r)
  | count + 1, j, l, r =>
    rounds x count (j + 1) (step x rl sl (kl j) j j l) (step x rr sr (kr j) (79 - j) j r)

def wordLE (b : ByteArray) (off : Nat) : UInt32 :=
  (b.get! off).toUInt32 ||| ((b.get! (off + 1)).toUInt32 <<< 8)
    ||| ((b.get! (off + 2)).toUInt32 <<< 16) ||| ((b.get! (off + 3)).toUInt32 <<< 24)

def compress (h : State) (data : ByteArray) (off : Nat) : State :=
  let x : Array UInt32 := (Array.range 16).map fun i => wordLE data (off + 4 * i)
  let (l, r) := rounds x 80 0 h h
  ⟨h.b + l.c + r.d, h.c + l.d + r.e, h.d + l.e + r.a, h.e + l.a + r.b, h.a + l.b + r.c⟩

def blocks (data : ByteArray) : Nat → Nat → State → State
  | 0, _, h => h
  | count + 1, off, h => blocks data count (off + 64) (compress h data off)

def pushLE32 (acc : ByteArray) (w : UInt32) : ByteArray :=
  (((acc.push w.toUInt8).push (w >>> 8).toUInt8).push (w >>> 16).toUInt8).push (w >>> 24).toUInt8

/-- Merkle-Damgård padding: 0x80, zeros, then the bit length as 8 little-endian bytes. -/
def pad (m : ByteArray) : ByteArray :=
  let zeros := (119 - m.size % 64) % 64
  let bits := m.size * 8
  let withZeros := (m.push 0x80) ++ zeroBytes zeros
  (List.range 8).foldl (fun acc i => acc.push (UInt8.ofNat (bits >>> (8 * i)))) withZeros

/-- RIPEMD-160 of a byte string: 20 bytes. -/
def hash (m : ByteArray) : ByteArray :=
  let padded := pad m
  let h := blocks padded (padded.size / 64) 0
    ⟨0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0⟩
  pushLE32 (pushLE32 (pushLE32 (pushLE32 (pushLE32 ByteArray.empty h.a) h.b) h.c) h.d) h.e

end EthereumWallet.Keys.Ripemd160
