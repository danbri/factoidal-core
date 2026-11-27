import EthereumWallet.Keys.Bytes

/-
AES-128 block encryption (FIPS 197) and AES-128-CTR (NIST SP 800-38A section
6.5, with the whole 16-byte IV as a big-endian counter that wraps at 2^128, as
the Web3 Secret Storage keystore uses it). Encryption direction only: CTR needs
no block decryption.

The S-box is computed from its definition (the inverse in GF(2^8), then the
affine map, FIPS 197 section 5.1.1) once, when the module is initialised.

Theorems (stated here, proved below):
* `aes128Ctr_refuses_key`, `aes128Ctr_refuses_iv`: wrong key or IV length is refused.
* `aes128Ctr_size`: the output is as long as the input.
* `aes128Ctr_involutive`: applying CTR twice with the same key and IV gives the
  input back (decryption is encryption).
Tested only (FIPS 197 Appendix B and C.1, SP 800-38A F.5.1, in `KeystoreTests`):
that the block function is AES-128 and the counter runs as specified.

Not constant-time: S-box lookups index a table by secret bytes (cache timing),
and the GF(2^8) helpers branch on data. The key schedule and blocks are
ordinary Lean heap objects, not zeroised.
-/

namespace EthereumWallet.Keys

/-- Multiplication by `x` in GF(2^8) modulo `x^8 + x^4 + x^3 + x + 1` (FIPS 197 section 4.2.1). -/
@[inline] def xtime (a : UInt8) : UInt8 :=
  if a &&& 0x80 == 0 then a <<< 1 else (a <<< 1) ^^^ 0x1b

/-- GF(2^8) product, shift-and-add over the eight bits of `b`. Structural on the count. -/
def gmulLoop : Nat → UInt8 → UInt8 → UInt8 → UInt8
  | 0, _, _, acc => acc
  | k + 1, a, b, acc =>
    gmulLoop k (xtime a) (b >>> 1) (if b &&& 1 == 1 then acc ^^^ a else acc)

def gmul (a b : UInt8) : UInt8 := gmulLoop 8 a b 0

/-- `acc * a^k` in GF(2^8). Structural on `k`. -/
def gpowLoop : Nat → UInt8 → UInt8 → UInt8
  | 0, _, acc => acc
  | k + 1, a, acc => gpowLoop k a (gmul acc a)

/-- The multiplicative inverse in GF(2^8) (`a^254`), with 0 sent to 0. -/
def ginv (a : UInt8) : UInt8 := gpowLoop 254 a 1

@[inline] def rotl8 (a : UInt8) (k : UInt8) : UInt8 := (a <<< k) ||| (a >>> (8 - k))

/-- One S-box entry from the definition (FIPS 197 section 5.1.1). -/
def sboxEntry (a : UInt8) : UInt8 :=
  let b := ginv a
  b ^^^ rotl8 b 1 ^^^ rotl8 b 2 ^^^ rotl8 b 3 ^^^ rotl8 b 4 ^^^ 0x63

/-- The AES S-box as a 256-byte table. -/
def sbox : ByteArray :=
  ByteArray.mk ((Array.range 256).map fun i => sboxEntry (UInt8.ofNat i))

@[inline] def subByte (a : UInt8) : UInt8 := sbox.get! a.toNat

/-- Key expansion for AES-128 (FIPS 197 section 5.2): words `i`, `i+1`, ... of
    the schedule, `count` of them, appended to `w`. `rc` is the round constant
    for the next multiple of four. Structural on `count`, a tail call. -/
def expandLoop : Nat → Nat → UInt8 → ByteArray → ByteArray
  | 0, _, _, w => w
  | count + 1, i, rc, w =>
    let t0 := w.get! (4 * i - 4)
    let t1 := w.get! (4 * i - 3)
    let t2 := w.get! (4 * i - 2)
    let t3 := w.get! (4 * i - 1)
    let p0 := w.get! (4 * i - 16)
    let p1 := w.get! (4 * i - 15)
    let p2 := w.get! (4 * i - 14)
    let p3 := w.get! (4 * i - 13)
    if i % 4 == 0 then
      expandLoop count (i + 1) (xtime rc)
        ((((w.push (p0 ^^^ subByte t1 ^^^ rc)).push (p1 ^^^ subByte t2)).push
          (p2 ^^^ subByte t3)).push (p3 ^^^ subByte t0))
    else
      expandLoop count (i + 1) rc
        ((((w.push (p0 ^^^ t0)).push (p1 ^^^ t1)).push (p2 ^^^ t2)).push (p3 ^^^ t3))

/-- The 176-byte AES-128 key schedule of a 16-byte key. -/
def expandKey (key : ByteArray) : ByteArray := expandLoop 40 4 1 key

/-- One column of one round: SubBytes and ShiftRows on column `c` of `st`, then
    MixColumns unless `last`, then AddRoundKey with round `round` of `rk`. -/
@[inline] def roundColumn (rk st : ByteArray) (round c : Nat) (last : Bool) (acc : ByteArray) :
    ByteArray :=
  let a0 := subByte (st.get! (4 * c))
  let a1 := subByte (st.get! (1 + 4 * ((c + 1) % 4)))
  let a2 := subByte (st.get! (2 + 4 * ((c + 2) % 4)))
  let a3 := subByte (st.get! (3 + 4 * ((c + 3) % 4)))
  let k := 16 * round + 4 * c
  if last then
    (((acc.push (a0 ^^^ rk.get! k)).push (a1 ^^^ rk.get! (k + 1))).push
      (a2 ^^^ rk.get! (k + 2))).push (a3 ^^^ rk.get! (k + 3))
  else
    let b0 := xtime a0 ^^^ (xtime a1 ^^^ a1) ^^^ a2 ^^^ a3
    let b1 := a0 ^^^ xtime a1 ^^^ (xtime a2 ^^^ a2) ^^^ a3
    let b2 := a0 ^^^ a1 ^^^ xtime a2 ^^^ (xtime a3 ^^^ a3)
    let b3 := (xtime a0 ^^^ a0) ^^^ a1 ^^^ a2 ^^^ xtime a3
    (((acc.push (b0 ^^^ rk.get! k)).push (b1 ^^^ rk.get! (k + 1))).push
      (b2 ^^^ rk.get! (k + 2))).push (b3 ^^^ rk.get! (k + 3))

/-- One whole round on the 16-byte state. -/
def aesRound (rk st : ByteArray) (round : Nat) (last : Bool) : ByteArray :=
  roundColumn rk st round 3 last (roundColumn rk st round 2 last
    (roundColumn rk st round 1 last (roundColumn rk st round 0 last
      (ByteArray.emptyWithCapacity 16))))

/-- Rounds `round`, `round + 1`, ... up to round 10. Structural on `count`, a tail call. -/
def aesRounds (rk : ByteArray) : Nat → Nat → ByteArray → ByteArray
  | 0, _, st => st
  | count + 1, round, st => aesRounds rk count (round + 1) (aesRound rk st round (count == 0))

/-- XOR of the first 16 bytes of `a` and `b`. -/
def xor16 (a b : ByteArray) : ByteArray :=
  ByteArray.mk ((Array.range 16).map fun i => a.get! i ^^^ b.get! i)

/-- AES-128 encryption of one 16-byte block under the schedule `rk` (FIPS 197 section 5.1). -/
def aesEncryptBlock (rk block : ByteArray) : ByteArray :=
  aesRounds rk 10 1 (xor16 block rk)

/-- The CTR keystream: `blocks` encrypted counter blocks starting at counter
    `ctr` (mod 2^128). The counter is public, so it is held as a number.
    Structural on `blocks`, a tail call. -/
def ctrStreamLoop (rk : ByteArray) : Nat → Nat → ByteArray → ByteArray
  | 0, _, acc => acc
  | blocks + 1, ctr, acc =>
    ctrStreamLoop rk blocks (ctr + 1) (acc ++ aesEncryptBlock rk (natToBytesBE ctr 16))

/-- The keystream for `len` bytes of data: whole blocks, at least `len` bytes. -/
def ctrStream (key iv : ByteArray) (len : Nat) : ByteArray :=
  let blocks := (len + 15) / 16
  ctrStreamLoop (expandKey key) blocks (bytesToNatBE iv) (ByteArray.emptyWithCapacity (16 * blocks))

/-- `m` XORed byte by byte with the keystream function `ks`. -/
def xorKs (m : ByteArray) (ks : Nat → UInt8) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := m.data.size) fun i => m.data[i] ^^^ ks i.val)

inductive AesError where
  | badKeyLength
  | badIvLength
  deriving Repr, BEq, DecidableEq

/-- AES-128-CTR: encryption and decryption are the same function. The key and
    the IV (the initial counter block) must each be 16 bytes. -/
def aes128Ctr (key iv data : ByteArray) : Except AesError ByteArray :=
  if key.size ≠ 16 then .error .badKeyLength
  else if iv.size ≠ 16 then .error .badIvLength
  else
    let stream := ctrStream key iv data.size
    .ok (xorKs data fun i => stream.get! i)

/-! ## Theorems -/

theorem xorKs_size (m : ByteArray) (ks : Nat → UInt8) : (xorKs m ks).size = m.size := by
  cases m with
  | mk d => exact Array.size_ofFn

theorem uint8_xor_cancel (a k : UInt8) : a ^^^ k ^^^ k = a := by
  rw [UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]

/-- Kind: algebra.
    Says: XORing with the same keystream twice gives the input back.
    Does not say: anything about a keystream that depends on the data. -/
theorem xorKs_xorKs (m : ByteArray) (ks : Nat → UInt8) : xorKs (xorKs m ks) ks = m := by
  cases m with
  | mk d =>
    simp only [xorKs]
    congr 1
    apply Array.ext
    · simp
    · intro i h1 h2
      simp [uint8_xor_cancel]

/-- Kind: refusal.
    Says: a key that is not 16 bytes is refused, whatever the IV and data.
    Does not say: anything about 16-byte keys. -/
theorem aes128Ctr_refuses_key (key iv data : ByteArray) (h : key.size ≠ 16) :
    aes128Ctr key iv data = .error .badKeyLength := by
  simp [aes128Ctr, h]

/-- Kind: refusal.
    Says: with a 16-byte key, an IV that is not 16 bytes is refused.
    Does not say: that the IV is fresh or unique; the caller must see to that. -/
theorem aes128Ctr_refuses_iv (key iv data : ByteArray) (hk : key.size = 16) (h : iv.size ≠ 16) :
    aes128Ctr key iv data = .error .badIvLength := by
  simp [aes128Ctr, hk, h]

/-- Kind: size.
    Says: the output of AES-128-CTR is exactly as long as the input.
    Does not say: anything about its bytes. -/
theorem aes128Ctr_size (key iv data out : ByteArray) (h : aes128Ctr key iv data = .ok out) :
    out.size = data.size := by
  unfold aes128Ctr at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      exact xorKs_size _ _

/-- Kind: round trip.
    Says: if CTR turns `data` into `out` under a key and IV, it turns `out` back
    into `data` under the same key and IV: decryption is the same function.
    Does not say: that the block function is AES (tested by published vectors),
    nor anything about secrecy. -/
theorem aes128Ctr_involutive (key iv data out : ByteArray)
    (h : aes128Ctr key iv data = .ok out) : aes128Ctr key iv out = .ok data := by
  have hs := aes128Ctr_size key iv data out h
  unfold aes128Ctr at h ⊢
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hk hi
      cases h
      simp only [if_neg hk, if_neg hi]
      rw [xorKs_size]
      rw [xorKs_xorKs]

end EthereumWallet.Keys
