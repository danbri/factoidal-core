import EVMCleanroom.Precompiles.Basic

/-!
# RIPEMD-160 (precompile 0x03)

Written from the published algorithm description (Dobbertin, Bosselaers,
Preneel, "RIPEMD-160: a strengthened version of RIPEMD", 1996): two parallel
lines of 80 steps over 16 little-endian 32-bit message words, Merkle–Damgård
padding with a 64-bit little-endian bit length.

The digest values are checked against the vectors of the original paper and,
in CI, against an independent oracle on generated inputs. No cryptographic
property is proved.

Gas (Yellow Paper appendix E, EELS `ripemd160`): 600 + 120 per 32-byte word.
The 20-byte digest is returned left-padded to 32 bytes.
-/

namespace EVMCleanroom.Precompiles.Ripemd160

private def rl : Array Nat := #[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
  3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
  1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
  4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]

private def rr : Array Nat := #[
  5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
  6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
  15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
  8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
  12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]

private def sl : Array UInt32 := #[
  11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
  7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
  11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
  11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
  9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]

private def sr : Array UInt32 := #[
  8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
  9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
  9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
  15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
  8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]

private def kl : Array UInt32 := #[0x00000000, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e]
private def kr : Array UInt32 := #[0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0x00000000]

@[inline] private def rol (x s : UInt32) : UInt32 := (x <<< s) ||| (x >>> (32 - s))

/-- The five round functions, selected by the group `j / 16`. -/
@[inline] private def f (group : Nat) (x y z : UInt32) : UInt32 :=
  match group with
  | 0 => x ^^^ y ^^^ z
  | 1 => (x &&& y) ||| (~~~x &&& z)
  | 2 => (x ||| ~~~y) ^^^ z
  | 3 => (x &&& z) ||| (y &&& ~~~z)
  | _ => x ^^^ (y ||| ~~~z)

structure Line where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32

structure Digest where
  h0 : UInt32 := 0x67452301
  h1 : UInt32 := 0xefcdab89
  h2 : UInt32 := 0x98badcfe
  h3 : UInt32 := 0x10325476
  h4 : UInt32 := 0xc3d2e1f0

@[inline] private def word (block : ByteArray) (base i : Nat) : UInt32 :=
  let o := base + 4 * i
  (byteAt block o).toUInt32 ||| ((byteAt block (o+1)).toUInt32 <<< 8) |||
    ((byteAt block (o+2)).toUInt32 <<< 16) ||| ((byteAt block (o+3)).toUInt32 <<< 24)

@[inline] private def step (v : Line) (fv x k s : UInt32) : Line :=
  let t := rol (v.a + fv + x + k) s + v.e
  ⟨v.e, t, v.b, rol v.c 10, v.d⟩

/-- The 80 steps of both lines; `n` counts the remaining steps. -/
private def steps (data : ByteArray) (base : Nat) : Nat → Line → Line → Line × Line
  | 0, l, r => (l, r)
  | n+1, l, r =>
    let j := 79 - n
    let g := j / 16
    let l' := step l (f g l.b l.c l.d) (word data base rl[j]!) kl[g]! sl[j]!
    let r' := step r (f (4 - g) r.b r.c r.d) (word data base rr[j]!) kr[g]! sr[j]!
    steps data base n l' r'

private def compress (h : Digest) (data : ByteArray) (base : Nat) : Digest :=
  let start : Line := ⟨h.h0, h.h1, h.h2, h.h3, h.h4⟩
  let (l, r) := steps data base 80 start start
  { h0 := h.h1 + l.c + r.d
    h1 := h.h2 + l.d + r.e
    h2 := h.h3 + l.e + r.a
    h3 := h.h4 + l.a + r.b
    h4 := h.h0 + l.b + r.c }

private def blocks (data : ByteArray) : Nat → Nat → Digest → Digest
  | 0, _, h => h
  | n+1, base, h => blocks data n (base + 64) (compress h data base)

/-- Number of zero bytes between the 0x80 marker and the 8 length bytes. -/
def zeroPad (size : Nat) : Nat := (119 - size % 64) % 64

/-- Kind: padding.
    Says: message, marker, zero padding and length field fill whole 64-byte blocks.
    Does not say: the digest has a particular value. -/
theorem padded_blocks (size : Nat) : (size + 1 + zeroPad size + 8) % 64 = 0 := by
  simp only [zeroPad]
  omega

private def pad (m : ByteArray) : ByteArray :=
  let withMarker := m.push 0x80
  let zeros := readPadded ByteArray.empty 0 (zeroPad m.size)
  withMarker ++ zeros ++ natToLE 8 (8 * m.size)

private def putWord (acc : ByteArray) (w : UInt32) : ByteArray :=
  (((acc.push w.toUInt8).push (w >>> 8).toUInt8).push (w >>> 16).toUInt8).push (w >>> 24).toUInt8

/-- The 20-byte RIPEMD-160 digest. -/
def digest (m : ByteArray) : ByteArray :=
  let padded := pad m
  let h := blocks padded (padded.size / 64) 0 {}
  putWord (putWord (putWord (putWord (putWord ByteArray.empty h.h0) h.h1) h.h2) h.h3) h.h4

private theorem putWord_size (acc : ByteArray) (w : UInt32) : (putWord acc w).size = acc.size + 4 := by
  simp [putWord, ByteArray.size_push]

/-- Kind: length.
    Says: the digest is 20 bytes for every input.
    Does not say: the digest has a particular value. -/
theorem digest_size (m : ByteArray) : (digest m).size = 20 := by
  simp [digest, putWord_size]

def gasCost (size : Nat) : Nat := 600 + 120 * words32 size

/-- Precompile 0x03: twelve zero bytes followed by the digest. -/
def run (gas : Nat) (input : ByteArray) : Result :=
  charge gas (gasCost input.size) fun _ =>
    .output (readPadded ByteArray.empty 0 12 ++ digest input)

/-- Kind: output contract.
    Says: every successful call returns exactly 32 bytes and the exact unspent gas.
    Does not say: the digest is the RIPEMD-160 of the input (tested, not proved). -/
theorem run_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : run gas input = .success out left) :
    out.size = 32 ∧ left + gasCost input.size = gas := by
  have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
  cases hBody
  exact ⟨by simp [ByteArray.size_append, readPadded_size, digest_size], hGas⟩

/-- Kind: gas admission.
    Says: the call fails exactly when the forwarded gas is below 600 + 120 per word;
    otherwise it succeeds. There is no invalid input.
    Does not say: anything about the digest. -/
theorem run_total (gas : Nat) (input : ByteArray) :
    (gas < gasCost input.size → run gas input = .failure) ∧
    (gasCost input.size ≤ gas → ∃ out, run gas input = .success out (gas - gasCost input.size)) := by
  constructor
  · intro h; exact charge_underfunded _ _ _ h
  · intro h; exact ⟨_, charge_funded _ _ _ _ h rfl⟩

private def hexOf (s : String) : String := toHex (digest s.toUTF8)

#guard hexOf "" == "9c1185a5c5e9fc54612808977ee8f548b2258d31"
#guard hexOf "a" == "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe"
#guard hexOf "abc" == "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"
#guard hexOf "message digest" == "5d0689ef49d2fae572b881b123a85ffa21595f36"
#guard hexOf "abcdefghijklmnopqrstuvwxyz" == "f71c27109c692c1b56bbdceb5b9d2865b3708dbc"
#guard hexOf "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" ==
  "12a053384a9c0c88e405a06c27dcf49ada62eb2b"
#guard hexOf "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789" ==
  "b0e20b6e3116640286ed3a87a5713079b21f5189"
#guard hexOf "12345678901234567890123456789012345678901234567890123456789012345678901234567890" ==
  "9b752e45573d4b39f4dbd3323cab82bf63326bfb"
#guard gasCost 0 == 600 && gasCost 1 == 720 && gasCost 32 == 720 && gasCost 33 == 840
#guard (match run 600 ByteArray.empty with
  | .success out 0 => toHex out == "0000000000000000000000009c1185a5c5e9fc54612808977ee8f548b2258d31"
  | _ => false)
#guard (match run 599 ByteArray.empty with | .failure => true | _ => false)

#print axioms padded_blocks
#print axioms digest_size
#print axioms run_success
#print axioms run_total

end EVMCleanroom.Precompiles.Ripemd160
