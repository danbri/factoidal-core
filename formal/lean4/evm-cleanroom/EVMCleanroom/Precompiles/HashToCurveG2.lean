import EVMCleanroom.Precompiles.Sha256
import EVMCleanroom.Precompiles.BLS12381Map

/-!
# Hashing to the BLS12-381 group `G2` (RFC 9380, suite `BLS12381G2_XMD:SHA-256_SSWU_RO_`)

`hashToG2 dst msg` is `hash_to_curve` of RFC 9380, section 3, for the suite of
section 8.8.2, the one BLS signatures in the minimal-public-key-size variant use:

1. `expandMessageXmd` (section 5.3.1) with SHA-256 stretches the message and the
   domain separation tag to 256 uniform bytes;
2. `hashToFieldFp2` (section 5.2, `count = 2`, `m = 2`, `L = 64`) reads four
   64-byte big-endian integers and reduces them modulo `p`: two elements of `Fp2`;
3. each element is mapped to the curve isogenous to the twist by the simplified
   SWU map and carried to the twist by the 3-isogeny (`mapToCurveG2`);
4. the two points are added and the cofactor is cleared once.

Steps 3 and 4 are the limb functions of `BLS12381Map.lean` (`swu2`,
`isogenyFraction`, `clearCofactor2`); step 4 differs from the precompile 0x11,
which clears the cofactor of a single mapped point.

This module imports only `Sha256` and `BLS12381Map` (with their imports, all under
`EVMCleanroom/Precompiles`): no Keccak, no EVM, no `Lean.*`.

Proved: the output length of `expandMessageXmd` and its refusals, the number of
SHA-256 blocks produced, that no padding enters the result, and that `hashToG2`
answers for every tag of at most 255 bytes. Not proved: that the bytes are those
of RFC 9380, or that the point is in `G2`. Those are tested: the vectors of RFC
9380 appendices K.1 and J.10.1 and a differential run against the `Nat` definitions
(`EVMCleanroom/BLSSig`).

The data hashed here is public (messages to be verified). Nothing is constant-time.
-/

namespace EVMCleanroom.Precompiles.HashToCurve

open BLS12381 (p)

/-! ### `expand_message_xmd` with SHA-256 -/

/-- SHA-256 output size `b_in_bytes`, and its input block size `s_in_bytes`. -/
def hashBytes : Nat := 32
def blockBytes : Nat := 64

def xorLoop (a b : ByteArray) : Nat → Nat → ByteArray → ByteArray
  | 0, _, acc => acc
  | n+1, i, acc => xorLoop a b n (i + 1) (acc.push (byteAt a i ^^^ byteAt b i))

/-- Bytewise exclusive or of the first 32 bytes of two arrays. -/
def xor32 (a b : ByteArray) : ByteArray := xorLoop a b 32 0 ByteArray.empty

/-- `DST_prime = DST ‖ I2OSP(len(DST), 1)`. -/
def dstPrime (dst : ByteArray) : ByteArray := dst.push (UInt8.ofNat dst.size)

/-- `b_0 = H(Z_pad ‖ msg ‖ I2OSP(len, 2) ‖ I2OSP(0, 1) ‖ DST_prime)`. -/
def firstBlock (dst msg : ByteArray) (len : Nat) : ByteArray :=
  Sha256.digest
    (((((readPadded ByteArray.empty 0 blockBytes ++ msg).push (UInt8.ofNat (len / 256))).push
      (UInt8.ofNat len)).push 0) ++ dstPrime dst)

/-- `b_i = H((b_0 xor b_(i−1)) ‖ I2OSP(i, 1) ‖ DST_prime)`; with `previous` all zero this is `b_1`. -/
def nextBlock (b0 dstP previous : ByteArray) (i : Nat) : ByteArray :=
  Sha256.digest ((xor32 b0 previous).push (UInt8.ofNat i) ++ dstP)

/-- `count` blocks from index `i` on, appended to `acc`. -/
def xmdLoop (b0 dstP : ByteArray) : Nat → Nat → ByteArray → ByteArray → ByteArray
  | 0, _, _, acc => acc
  | n+1, i, previous, acc =>
    let block := nextBlock b0 dstP previous i
    xmdLoop b0 dstP n (i + 1) block (acc ++ block)

/-- `ell = ceil(len / 32)`. -/
def blockCount (len : Nat) : Nat := (len + 31) / 32

/-- `b_1 ‖ … ‖ b_ell`. -/
def uniformBlocks (dst msg : ByteArray) (len : Nat) : ByteArray :=
  xmdLoop (firstBlock dst msg len) (dstPrime dst) (blockCount len) 1 (readPadded ByteArray.empty 0 32)
    ByteArray.empty

/-- `expand_message_xmd(msg, DST, len_in_bytes)` of RFC 9380, section 5.3.1, with SHA-256.
    `none` is the RFC's ABORT: `ell > 255`, `len_in_bytes > 65535` or a tag above 255 bytes. -/
def expandMessageXmd (dst msg : ByteArray) (len : Nat) : Option ByteArray :=
  if 255 < dst.size ∨ 65535 < len ∨ 255 < blockCount len then none
  else some (readPadded (uniformBlocks dst msg len) 0 len)

theorem xorLoop_size (a b : ByteArray) (n i : Nat) (acc : ByteArray) :
    (xorLoop a b n i acc).size = acc.size + n := by
  induction n generalizing i acc with
  | zero => simp [xorLoop]
  | succ n ih => simp only [xorLoop, ih, ByteArray.size_push] <;> omega

/-- Kind: length.
    Says: the exclusive or of two blocks has exactly 32 bytes, whatever the inputs.
    Does not say: which bytes. -/
theorem xor32_size (a b : ByteArray) : (xor32 a b).size = 32 := by
  simp [xor32, xorLoop_size]

/-- Kind: length.
    Says: every block of the expansion is exactly 32 bytes.
    Does not say: which bytes. -/
theorem nextBlock_size (b0 dstP previous : ByteArray) (i : Nat) : (nextBlock b0 dstP previous i).size = 32 :=
  Sha256.digest_size _

/-- Kind: loop count and length.
    Says: `n` steps of the block loop append exactly `32·n` bytes: one SHA-256 digest per step.
    Does not say: which bytes. -/
theorem xmdLoop_size (b0 dstP : ByteArray) (n i : Nat) (previous acc : ByteArray) :
    (xmdLoop b0 dstP n i previous acc).size = acc.size + 32 * n := by
  induction n generalizing i previous acc with
  | zero => simp [xmdLoop]
  | succ n ih => simp only [xmdLoop, ih, ByteArray.size_append, nextBlock_size] <;> omega

/-- Kind: length.
    Says: the blocks produced are exactly `32·ceil(len/32)` bytes: `ceil(len/32)` digests
    after the first block `b_0`.
    Does not say: which bytes. -/
theorem uniformBlocks_size (dst msg : ByteArray) (len : Nat) :
    (uniformBlocks dst msg len).size = 32 * blockCount len := by
  simp [uniformBlocks, xmdLoop_size]

/-- Kind: bound.
    Says: the blocks cover the requested length, so the final read of `expandMessageXmd`
    takes digest bytes only and never the zero padding of `readPadded`.
    Does not say: which bytes. -/
theorem uniformBlocks_covers (dst msg : ByteArray) (len : Nat) : len ≤ (uniformBlocks dst msg len).size := by
  rw [uniformBlocks_size]
  unfold blockCount
  omega

/-- Kind: length.
    Says: when the expansion answers, the answer has exactly the requested length.
    Does not say: the bytes are those of RFC 9380 (tested: appendix K.1). -/
theorem expandMessageXmd_size (dst msg out : ByteArray) (len : Nat)
    (h : expandMessageXmd dst msg len = some out) : out.size = len := by
  unfold expandMessageXmd at h
  split at h
  · cases h
  · have h' := Option.some.inj h
    rw [← h']
    exact readPadded_size _ _ _

/-- Kind: refusal.
    Says: a tag above 255 bytes, a length above 65535, or a length needing more than 255
    blocks is refused, as RFC 9380 section 5.3.1 requires.
    Does not say: anything about accepted input. -/
theorem expandMessageXmd_refuses (dst msg : ByteArray) (len : Nat)
    (h : 255 < dst.size ∨ 65535 < len ∨ 255 < blockCount len) : expandMessageXmd dst msg len = none := by
  unfold expandMessageXmd
  exact if_pos h

/-- Kind: refusal.
    Says: with SHA-256 the block limit is the binding one: any length above `255·32 = 8160`
    bytes is refused, in particular every length above 65535.
    Does not say: anything about accepted input. -/
theorem expandMessageXmd_refuses_long (dst msg : ByteArray) (len : Nat) (h : 8160 < len) :
    expandMessageXmd dst msg len = none := by
  apply expandMessageXmd_refuses
  refine Or.inr (Or.inr ?_)
  unfold blockCount
  omega

/-- Kind: totality on accepted input.
    Says: a tag of at most 255 bytes and a length of at most 8160 bytes always give an answer.
    Does not say: which bytes. -/
theorem expandMessageXmd_isSome (dst msg : ByteArray) (len : Nat) (hDst : dst.size ≤ 255) (hLen : len ≤ 8160) :
    (expandMessageXmd dst msg len).isSome = true := by
  have hc : ¬ (255 < dst.size ∨ 65535 < len ∨ 255 < blockCount len) := by
    unfold blockCount
    omega
  unfold expandMessageXmd
  rw [if_neg hc] <;> rfl

/-! ### `hash_to_field` for `Fp2`, two elements -/

/-- Bytes requested for two elements of `Fp2`: `count · m · L = 2 · 2 · 64`. -/
def fieldBytes : Nat := 256

/-- `OS2IP` of the 64 bytes of element `index`, reduced modulo `p`. -/
def fieldElement (uniform : ByteArray) (index : Nat) : Nat := beNat uniform (64 * index) 64 % p

/-- `hash_to_field(msg, 2)` for `Fp2` (RFC 9380, section 5.2), as canonical residues. -/
def hashToFieldFp2 (dst msg : ByteArray) : Option (Fp2 × Fp2) :=
  (expandMessageXmd dst msg fieldBytes).map fun uniform =>
    (⟨fieldElement uniform 0, fieldElement uniform 1⟩, ⟨fieldElement uniform 2, fieldElement uniform 3⟩)

/-! ### Map and hash to `G2` -/

/-- `map_to_curve` for `G2`: simplified SWU and the 3-isogeny, without clearing the cofactor.
    The result is on the twist, in general outside the order-`r` subgroup. -/
def mapToCurveG2 (u : Q2 U384) : JPoint (Q2 U384) :=
  let s := BLS12381.Fast.swu2 u
  BLS12381.Fast.isogenyFraction BLS12381.Fast.fp2 BLS12381.Fast.iso2XNum BLS12381.Fast.iso2XDen
    BLS12381.Fast.iso2YNum BLS12381.Fast.iso2YDen s.1 s.2.1 s.2.2

/-- The point for two field elements: map both, add, clear the cofactor once. -/
def pointOfFields (u : Fp2 × Fp2) : JPoint (Q2 U384) :=
  BLS12381.Fast.clearCofactor2
    (Curve.add BLS12381.Fast.fp2 (mapToCurveG2 (BLS12381.Fast.toLimbs2 u.1))
      (mapToCurveG2 (BLS12381.Fast.toLimbs2 u.2)))

/-- `hash_to_curve(msg)` with tag `dst`: a point of `G2` in Jacobian coordinates over the
    Montgomery limb field. `none` only for a tag above 255 bytes. -/
def hashToG2 (dst msg : ByteArray) : Option (JPoint (Q2 U384)) :=
  (hashToFieldFp2 dst msg).map pointOfFields

/-- Kind: totality.
    Says: for a tag of at most 255 bytes hashing to `G2` answers for every message.
    Does not say: the point is the one of RFC 9380 or lies in `G2` (tested: appendix J.10.1
    and the differential run). -/
theorem hashToG2_isSome (dst msg : ByteArray) (h : dst.size ≤ 255) : (hashToG2 dst msg).isSome = true := by
  have hx := expandMessageXmd_isSome dst msg fieldBytes h (by unfold fieldBytes; omega)
  unfold hashToG2 hashToFieldFp2
  cases hE : expandMessageXmd dst msg fieldBytes with
  | none => rw [hE] at hx; simp at hx
  | some uniform => rfl

/-- Kind: refusal.
    Says: a tag above 255 bytes is refused before any hashing.
    Does not say: anything about accepted tags. -/
theorem hashToG2_refuses (dst msg : ByteArray) (h : 255 < dst.size) : hashToG2 dst msg = none := by
  unfold hashToG2 hashToFieldFp2
  rw [expandMessageXmd_refuses dst msg fieldBytes (Or.inl h)] <;> rfl

#guard blockCount 0 == 0 && blockCount 1 == 1 && blockCount 32 == 1 && blockCount 33 == 2 && blockCount 256 == 8
#guard (expandMessageXmd ByteArray.empty ByteArray.empty 8161).isNone &&
  (expandMessageXmd ByteArray.empty ByteArray.empty 8160).isSome &&
  (expandMessageXmd (readPadded ByteArray.empty 0 256) ByteArray.empty 32).isNone &&
  (expandMessageXmd (readPadded ByteArray.empty 0 255) ByteArray.empty 32).isSome
-- RFC 9380, appendix K.1, first vector: the empty message, 32 bytes.
#guard ((expandMessageXmd "QUUX-V01-CS02-with-expander-SHA256-128".toUTF8 ByteArray.empty 32).map toHex) ==
  some "68a985b87eb6b46952128911f2a4412bbc302a9d759667f87f7a21d803f07235"

#print axioms xorLoop_size
#print axioms xor32_size
#print axioms nextBlock_size
#print axioms xmdLoop_size
#print axioms uniformBlocks_size
#print axioms uniformBlocks_covers
#print axioms expandMessageXmd_size
#print axioms expandMessageXmd_refuses
#print axioms expandMessageXmd_refuses_long
#print axioms expandMessageXmd_isSome
#print axioms hashToG2_isSome
#print axioms hashToG2_refuses

end EVMCleanroom.Precompiles.HashToCurve
