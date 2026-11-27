import EVMCleanroom.Precompiles.HashToCurveG2
import EVMCleanroom.Precompiles.BLS12381Pairing

/-!
# BLS signature verification on BLS12-381, minimal-public-key-size variant

Verification only, for the scheme Ethereum consensus uses: public keys in `G1`
(48 bytes compressed), signatures in `G2` (96 bytes compressed), ciphersuite
`BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`.

Sources: draft-irtf-cfrg-bls-signature-05 (`KeyValidate`, `CoreVerify`,
`CoreAggregateVerify`, `FastAggregateVerify`), RFC 9380 (hash to curve, in
`HashToCurveG2.lean`), the point serialisation of that draft's appendix A (the
"ZCash" format: big-endian `x`, three flag bits in the first byte), and the `bls`
wrappers of the Ethereum consensus specifications (`eth_fast_aggregate_verify`,
`eth_aggregate_pubkeys`). No other implementation is imported, copied or translated.

## What is here

* `decodePublicKey`: 48 bytes to a `PublicKey` (affine, Montgomery limbs). It is
  `KeyValidate`: a valid encoding, on the curve, in the order-`r` subgroup, and not
  the point at infinity.
* `decodeSignature`: 96 bytes to a `Signature`. The point at infinity is a valid
  encoding of a signature; it then verifies false against every valid key (apart from
  a message that hashes to the point at infinity, which nobody can exhibit).
* `verify pk msg sig`: `e(pk, H(msg)) · e(−g₁, sig) = 1`, one product of two pairings
  with a shared Miller loop and one final exponentiation.
* `aggregateVerify`, `fastAggregateVerify`, `ethFastAggregateVerify`,
  `aggregatePublicKeys`.
* The lower layer for callers that keep decoded keys: `verifyDecoded`,
  `fastAggregateVerifyDecoded`, `aggregateVerifyDecoded`, `aggregateDecoded`,
  `verifyPoints` (for a message already hashed).

The domain separation tag is a parameter, with `consensusDst` as the default.

There is no signing function here and there must not be one: a secret-key operation
goes through HACL\*. Everything this module handles is public, and nothing in it is
constant-time.

## Built on

`BLS12381Fast` and `BLS12381Map` (limb field, square roots, endomorphism subgroup
checks, map to curve, cofactor clearing) and `BLS12381Pairing` (the product check on
the limb tower). Imports stay inside `EVMCleanroom/Precompiles`: no Keccak, no EVM,
no `Lean.*`.

## Proved, and only tested

Proved: wrong-length input is rejected by the decoders and gives `false` from every
verification function; an empty key list gives `false` (and `true` only for
`ethFastAggregateVerify` with the infinity signature); a list of keys decodes to as
many keys; `aggregateVerify` refuses lists of different lengths; a compressed key has
48 bytes. Not proved: every verdict. Pairing correctness, the subgroup criteria, the
square roots and the hash to the curve are tested, not proved: the RFC 9380 vectors,
the consensus-specification BLS vectors, and a differential run against the `Nat`
definitions (`EVMCleanroom/BLSSig`, exe `evm-blssig`).
-/

namespace EVMCleanroom.Precompiles.BLSSignature

open BLS12381 (p)
open BLS12381.Fast (M fp fp2 fmul fsqr fadd fneg toMont fromMont four inSubgroup1 inSubgroup2 sqrt1? sqrt2?)
open HashToCurve (hashToG2)

/-- A validated public key: an affine point of `G1` other than the point at infinity, in
    the order-`r` subgroup, coordinates in Montgomery limbs. Only `decodePublicKey` and
    `aggregateDecoded` are meant to build one. -/
structure PublicKey where
  x : U384
  y : U384

/-- A decoded signature: a point of `G2` in the order-`r` subgroup, `none` for the point
    at infinity. Only `decodeSignature` is meant to build one. -/
structure Signature where
  point : Option (Q2 U384 × Q2 U384)

/-- The tag of the Ethereum consensus ciphersuite (proof-of-possession scheme). -/
def consensusDst : ByteArray := "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_".toUTF8

/-! ### Point decompression -/

/-- `(p − 1)/2` as plain limbs: a canonical value above it is the larger of `a` and `−a`. -/
def halfP : U384 := U384.ofNat ((p - 1) / 2)

/-- The low 381 bits of the first 48 bytes: the value without the three flag bits. -/
def unflagged (raw : U384) : U384 := { raw with l5 := raw.l5 &&& 0x1fffffffffffffff }

/-- Decompress a 48-byte `G1` point. Outer `none`: wrong length, invalid flags, a value not
    below `p`, no point with this `x`, or a point outside the order-`r` subgroup. Inner
    `none`: the point at infinity (flag byte `0xc0`, all other bits zero). -/
def decompressG1 (data : ByteArray) : Option (Option (U384 × U384)) :=
  if data.size ≠ 48 then none
  else
    let first := byteAt data 0
    let larger := (first &&& 0x20) != 0
    let x := unflagged (U384.ofBE data 0)
    if (first &&& 0x80) == 0 then none
    else if (first &&& 0x40) != 0 then (if x.isZero && !larger then some none else none)
    else if !U384.lt x M.n then none
    else
      let xm := toMont x
      match sqrt1? (fadd (fmul (fsqr xm) xm) four) with
      | none => none
      | some root =>
        let y := if U384.lt halfP (fromMont root) == larger then root else fneg root
        if inSubgroup1 xm y then some (some (xm, y)) else none

/-- Is `y` the larger of `y` and `−y` in the order of the serialisation (imaginary part
    first, the real part when the imaginary part is zero)? -/
def larger2 (y : Q2 U384) : Bool :=
  let c1 := fromMont y.c1
  if c1.isZero then U384.lt halfP (fromMont y.c0) else U384.lt halfP c1

/-- Decompress a 96-byte `G2` point (`x.c1 ‖ x.c0`, flags in the first byte). Outer `none`:
    wrong length, invalid flags, a coordinate not below `p`, no point with this `x`, or a
    point outside the order-`r` subgroup. Inner `none`: the point at infinity. -/
def decompressG2 (data : ByteArray) : Option (Option (Q2 U384 × Q2 U384)) :=
  if data.size ≠ 96 then none
  else
    let first := byteAt data 0
    let larger := (first &&& 0x20) != 0
    let c1 := unflagged (U384.ofBE data 0)
    let c0 := U384.ofBE data 48
    if (first &&& 0x80) == 0 then none
    else if (first &&& 0x40) != 0 then (if c1.isZero && c0.isZero && !larger then some none else none)
    else if !U384.lt c1 M.n || !U384.lt c0 M.n then none
    else
      let x : Q2 U384 := ⟨toMont c0, toMont c1⟩
      match sqrt2? (Q2.add fp (Q2.mul fp (Q2.sqr fp x) x) BLS12381.Fast.twistB) with
      | none => none
      | some root =>
        let y := if larger2 root == larger then root else Q2.neg fp root
        if inSubgroup2 x y then some (some (x, y)) else none

/-- `KeyValidate` on 48 bytes: a public key is a point of `G1` other than infinity. -/
def decodePublicKey (bytes : ByteArray) : Option PublicKey :=
  match decompressG1 bytes with
  | some (some point) => some ⟨point.1, point.2⟩
  | _ => none

/-- A signature is a point of `G2`; the point at infinity is accepted here. -/
def decodeSignature (bytes : ByteArray) : Option Signature :=
  (decompressG2 bytes).map Signature.mk

/-- The 96 bytes of the point at infinity of `G2`: `0xc0` and 95 zero bytes. -/
def infinitySignature : ByteArray := ByteArray.empty.push 0xc0 ++ readPadded ByteArray.empty 0 95

/-- Compress a `G1` point to 48 bytes. -/
def compressG1 (point : Option (U384 × U384)) : ByteArray :=
  match point with
  | none => ByteArray.empty.push 0xc0 ++ readPadded ByteArray.empty 0 47
  | some point =>
    U384.pushBE ByteArray.empty
      { fromMont point.1 with
        l5 := (fromMont point.1).l5 |||
          (if U384.lt halfP (fromMont point.2) then (0xa000000000000000 : UInt64) else 0x8000000000000000) }

/-- The 48 bytes of a validated key. -/
def PublicKey.toBytes (key : PublicKey) : ByteArray := compressG1 (some (key.x, key.y))

/-! ### The pairing product -/

/-- An `Fp2` element of the group code as an element of the pairing tower: the same two
    Montgomery residues in one flat object. -/
def toQuad (a : Q2 U384) : Quad384 := Quad384.mk2 a.c0 a.c1

/-- The state of the pair `(P, Q)` for the shared Miller loop; both points finite, affine. -/
def pairState (x y : U384) (qx qy : Q2 U384) : PairState Quad384 :=
  { nx := Quad384.neg BLS12381.baseField (Quad384.ofReal x)
    y := Quad384.ofReal y
    qx := toQuad qx
    qy := toQuad qy
    nqy := Quad384.neg BLS12381.baseField (toQuad qy)
    t := ⟨toQuad qx, toQuad qy, Quad384.one BLS12381.baseField⟩ }

/-- `−g₁`: the generator of `G1` with its `y` negated. -/
def negG1X : U384 := M.ofNat BLS12381.g1Generator.1
def negG1Y : U384 := fneg (M.ofNat BLS12381.g1Generator.2)

/-- The pair `(−g₁, signature)`, or nothing for the signature at infinity (its pairing is one). -/
def signaturePairs (sig : Signature) : List (PairState Quad384) :=
  match sig.point with
  | some point => [pairState negG1X negG1Y point.1 point.2]
  | none => []

/-- The pair `(key, hashed)` in front of `rest`; a hashed point at infinity contributes one
    and is dropped. One field inversion to bring the hashed point to affine form. -/
def pushPair (key : PublicKey) (hashed : JPoint (Q2 U384)) (rest : List (PairState Quad384)) :
    List (PairState Quad384) :=
  match Curve.toAffineFast fp2 hashed with
  | some point => pairState key.x key.y point.1 point.2 :: rest
  | none => rest

/-- `e(key, hashed) · e(−g₁, sig) = 1` for a message already hashed to `G2`. -/
def verifyPoints (key : PublicKey) (hashed : JPoint (Q2 U384)) (sig : Signature) : Bool :=
  BLS12381Pairing.productIsOne (pushPair key hashed (signaturePairs sig))

/-! ### Verification -/

/-- `CoreVerify` on a decoded key and signature. `false` for a tag above 255 bytes. -/
def verifyDecoded (key : PublicKey) (msg : ByteArray) (sig : Signature) (dst : ByteArray := consensusDst) : Bool :=
  match hashToG2 dst msg with
  | some hashed => verifyPoints key hashed sig
  | none => false

/-- `Verify(PK, message, signature)`: `false` for an invalid key (wrong length, invalid
    encoding, off the curve, outside the subgroup, infinity), an invalid signature
    encoding, or a pairing product other than one. -/
def verify (pk msg sig : ByteArray) (dst : ByteArray := consensusDst) : Bool :=
  if pk.size ≠ 48 ∨ sig.size ≠ 96 then false
  else
    match decodePublicKey pk with
    | none => false
    | some key =>
      match decodeSignature sig with
      | none => false
      | some s => verifyDecoded key msg s dst

/-! ### Aggregates -/

def decodeKeysLoop (keys : Array ByteArray) : Nat → Nat → Array PublicKey → Option (Array PublicKey)
  | 0, _, acc => some acc
  | n+1, i, acc =>
    match decodePublicKey (keys.getD i ByteArray.empty) with
    | none => none
    | some key => decodeKeysLoop keys n (i + 1) (acc.push key)

/-- Decode every key of the list; `none` if any is invalid. -/
def decodePublicKeys (keys : Array ByteArray) : Option (Array PublicKey) :=
  decodeKeysLoop keys keys.size 0 #[]

def sumKeysLoop (keys : Array PublicKey) : Nat → Nat → JPoint U384 → JPoint U384
  | 0, _, acc => acc
  | n+1, i, acc =>
    match keys[i]? with
    | some key => sumKeysLoop keys n (i + 1) (Curve.addMixed fp acc key.x key.y)
    | none => acc

/-- The sum of the keys in `G1`, Jacobian: one mixed addition per key. -/
def sumKeys (keys : Array PublicKey) : JPoint U384 :=
  sumKeysLoop keys keys.size 0 (Curve.infinity fp)

/-- The aggregate of validated keys as a key: `none` for an empty list, and for a sum that
    is the point at infinity (not a valid key). One field inversion. -/
def aggregateDecoded (keys : Array PublicKey) : Option PublicKey :=
  if keys.size = 0 then none
  else
    match Curve.toAffineFast fp (sumKeys keys) with
    | some point => some ⟨point.1, point.2⟩
    | none => none

/-- `FastAggregateVerify` on decoded keys: all keys signed the same message. -/
def fastAggregateVerifyDecoded (keys : Array PublicKey) (msg : ByteArray) (sig : Signature)
    (dst : ByteArray := consensusDst) : Bool :=
  match aggregateDecoded keys with
  | some key => verifyDecoded key msg sig dst
  | none => false

/-- `FastAggregateVerify(PK_1, …, PK_n, message, signature)`: `false` for an empty list,
    an invalid key, an invalid signature encoding, or a failed check. -/
def fastAggregateVerify (pks : Array ByteArray) (msg sig : ByteArray) (dst : ByteArray := consensusDst) : Bool :=
  if pks.size = 0 ∨ sig.size ≠ 96 then false
  else
    match decodeSignature sig with
    | none => false
    | some s =>
      match decodePublicKeys pks with
      | none => false
      | some keys => fastAggregateVerifyDecoded keys msg s dst

/-- `eth_fast_aggregate_verify` of the consensus specifications: as `fastAggregateVerify`,
    except that no keys together with the infinity signature is `true`. -/
def ethFastAggregateVerify (pks : Array ByteArray) (msg sig : ByteArray) (dst : ByteArray := consensusDst) : Bool :=
  if pks.size = 0 ∧ sig.data = infinitySignature.data then true
  else fastAggregateVerify pks msg sig dst

/-- One pair `(keyᵢ, H(msgᵢ))` per key, in front of `acc`. `none` for a tag above 255 bytes
    or a missing message. -/
def messagePairsLoop (keys : Array PublicKey) (msgs : Array ByteArray) (dst : ByteArray) :
    Nat → Nat → List (PairState Quad384) → Option (List (PairState Quad384))
  | 0, _, acc => some acc
  | n+1, i, acc =>
    match keys[i]?, msgs[i]? with
    | some key, some msg =>
      match hashToG2 dst msg with
      | some hashed => messagePairsLoop keys msgs dst n (i + 1) (pushPair key hashed acc)
      | none => none
    | _, _ => none

/-- `CoreAggregateVerify` on decoded keys: `∏ e(keyᵢ, H(msgᵢ)) · e(−g₁, sig) = 1`, all
    pairs in one shared Miller loop. `false` for no keys or lists of different lengths. -/
def aggregateVerifyDecoded (keys : Array PublicKey) (msgs : Array ByteArray) (sig : Signature)
    (dst : ByteArray := consensusDst) : Bool :=
  if keys.size = 0 ∨ keys.size ≠ msgs.size then false
  else
    match messagePairsLoop keys msgs dst keys.size 0 (signaturePairs sig) with
    | some pairs => BLS12381Pairing.productIsOne pairs
    | none => false

/-- `AggregateVerify((PK_1, …, PK_n), (message_1, …, message_n), signature)` of the
    proof-of-possession scheme (messages need not be distinct). -/
def aggregateVerify (pks : Array ByteArray) (msgs : Array ByteArray) (sig : ByteArray)
    (dst : ByteArray := consensusDst) : Bool :=
  if pks.size = 0 ∨ pks.size ≠ msgs.size ∨ sig.size ≠ 96 then false
  else
    match decodeSignature sig with
    | none => false
    | some s =>
      match decodePublicKeys pks with
      | none => false
      | some keys => aggregateVerifyDecoded keys msgs s dst

/-- `eth_aggregate_pubkeys` of the consensus specifications: the compressed sum of valid
    keys; `none` for an empty list or an invalid key. A sum at infinity is returned as the
    encoding of the point at infinity, as the specification's `AggregatePKs` does. -/
def aggregatePublicKeys (pks : Array ByteArray) : Option ByteArray :=
  if pks.size = 0 then none
  else (decodePublicKeys pks).map fun keys =>
    compressG1 ((Curve.toAffineFast fp (sumKeys keys)).map fun point => (point.1, point.2))

/-! ### Theorems -/

/-- Kind: input-length rule.
    Says: bytes that are not exactly 48 long never decompress to a `G1` point.
    Does not say: anything about 48-byte input. -/
theorem decompressG1_wrong_size (data : ByteArray) (h : data.size ≠ 48) : decompressG1 data = none := by
  unfold decompressG1
  exact if_pos h

/-- Kind: input-length rule.
    Says: bytes that are not exactly 96 long never decompress to a `G2` point.
    Does not say: anything about 96-byte input. -/
theorem decompressG2_wrong_size (data : ByteArray) (h : data.size ≠ 96) : decompressG2 data = none := by
  unfold decompressG2
  exact if_pos h

/-- Kind: input-length rule.
    Says: a public key that is not exactly 48 bytes is rejected.
    Does not say: which 48-byte strings are keys (tested). -/
theorem decodePublicKey_wrong_size (bytes : ByteArray) (h : bytes.size ≠ 48) : decodePublicKey bytes = none := by
  simp [decodePublicKey, decompressG1_wrong_size bytes h]

/-- Kind: input-length rule.
    Says: a signature that is not exactly 96 bytes is rejected.
    Does not say: which 96-byte strings are signatures (tested). -/
theorem decodeSignature_wrong_size (bytes : ByteArray) (h : bytes.size ≠ 96) : decodeSignature bytes = none := by
  simp [decodeSignature, decompressG2_wrong_size bytes h]

/-- Kind: input-length rule.
    Says: `verify` is `false` whenever the key is not 48 bytes or the signature is not 96
    bytes, for every message and tag, before any field arithmetic.
    Does not say: anything about the verdict on well-sized input (tested, not proved). -/
theorem verify_wrong_size (pk msg sig dst : ByteArray) (h : pk.size ≠ 48 ∨ sig.size ≠ 96) :
    verify pk msg sig dst = false := by
  unfold verify
  exact if_pos h

/-- Kind: edge rule.
    Says: `fastAggregateVerify` is `false` for an empty key list or a signature that is not
    96 bytes.
    Does not say: anything about the verdict otherwise. -/
theorem fastAggregateVerify_refuses (pks : Array ByteArray) (msg sig dst : ByteArray)
    (h : pks.size = 0 ∨ sig.size ≠ 96) : fastAggregateVerify pks msg sig dst = false := by
  unfold fastAggregateVerify
  exact if_pos h

/-- Kind: edge rule.
    Says: the consensus wrapper accepts the empty key list together with the infinity
    signature, for every message and tag.
    Does not say: anything about other input. -/
theorem ethFastAggregateVerify_empty_infinity (pks : Array ByteArray) (msg dst : ByteArray) (h : pks.size = 0) :
    ethFastAggregateVerify pks msg infinitySignature dst = true := by
  unfold ethFastAggregateVerify
  exact if_pos ⟨h, rfl⟩

/-- Kind: edge rule.
    Says: with an empty key list and any other signature bytes the consensus wrapper is `false`.
    Does not say: anything about a non-empty list. -/
theorem ethFastAggregateVerify_empty_other (pks : Array ByteArray) (msg sig dst : ByteArray) (h : pks.size = 0)
    (hSig : sig.data ≠ infinitySignature.data) : ethFastAggregateVerify pks msg sig dst = false := by
  have hc : ¬ (pks.size = 0 ∧ sig.data = infinitySignature.data) := fun both => hSig both.2
  unfold ethFastAggregateVerify
  rw [if_neg hc]
  exact fastAggregateVerify_refuses pks msg sig dst (Or.inl h)

/-- Kind: edge rule.
    Says: `aggregateVerify` is `false` for an empty key list, for key and message lists of
    different lengths, and for a signature that is not 96 bytes.
    Does not say: anything about the verdict otherwise. -/
theorem aggregateVerify_refuses (pks msgs : Array ByteArray) (sig dst : ByteArray)
    (h : pks.size = 0 ∨ pks.size ≠ msgs.size ∨ sig.size ≠ 96) : aggregateVerify pks msgs sig dst = false := by
  unfold aggregateVerify
  exact if_pos h

/-- Kind: edge rule.
    Says: on decoded keys too, no keys or lists of different lengths give `false`.
    Does not say: anything about the verdict otherwise. -/
theorem aggregateVerifyDecoded_refuses (keys : Array PublicKey) (msgs : Array ByteArray) (sig : Signature)
    (dst : ByteArray) (h : keys.size = 0 ∨ keys.size ≠ msgs.size) :
    aggregateVerifyDecoded keys msgs sig dst = false := by
  unfold aggregateVerifyDecoded
  exact if_pos h

/-- Kind: edge rule.
    Says: an empty list of decoded keys has no aggregate, so `fastAggregateVerifyDecoded`
    is `false` for it.
    Does not say: anything about a non-empty list. -/
theorem aggregateDecoded_empty (keys : Array PublicKey) (h : keys.size = 0) : aggregateDecoded keys = none := by
  unfold aggregateDecoded
  exact if_pos h

theorem fastAggregateVerifyDecoded_empty (keys : Array PublicKey) (msg : ByteArray) (sig : Signature)
    (dst : ByteArray) (h : keys.size = 0) : fastAggregateVerifyDecoded keys msg sig dst = false := by
  simp [fastAggregateVerifyDecoded, aggregateDecoded_empty keys h]

/-- Kind: edge rule.
    Says: `aggregatePublicKeys` refuses an empty list.
    Does not say: anything about a non-empty list. -/
theorem aggregatePublicKeys_empty (pks : Array ByteArray) (h : pks.size = 0) : aggregatePublicKeys pks = none := by
  unfold aggregatePublicKeys
  exact if_pos h

theorem decodeKeysLoop_size (keys : Array ByteArray) (n i : Nat) (acc out : Array PublicKey)
    (h : decodeKeysLoop keys n i acc = some out) : out.size = acc.size + n := by
  induction n generalizing i acc with
  | zero =>
    simp only [decodeKeysLoop, Option.some.injEq] at h
    subst h
    rfl
  | succ n ih =>
    simp only [decodeKeysLoop] at h
    split at h
    · cases h
    · have hSize := ih _ _ h
      rw [Array.size_push] at hSize
      omega

/-- Kind: loop count.
    Says: when a list of keys decodes, the result has exactly one key per input: the loop
    ran once per key and stopped at the first invalid one otherwise.
    Does not say: the keys are valid points (tested). -/
theorem decodePublicKeys_size (keys : Array ByteArray) (out : Array PublicKey)
    (h : decodePublicKeys keys = some out) : out.size = keys.size := by
  have hSize := decodeKeysLoop_size keys keys.size 0 #[] out h
  rw [show (#[] : Array PublicKey).size = 0 from rfl] at hSize
  omega

/-- Kind: length.
    Says: a compressed `G1` point, and so every serialised key, has exactly 48 bytes.
    Does not say: which bytes. -/
theorem compressG1_size (point : Option (U384 × U384)) : (compressG1 point).size = 48 := by
  unfold compressG1
  split
  · simp [ByteArray.size_append, ByteArray.size_push, readPadded_size]
  · simp [U384.pushBE_size]

/-- Kind: length.
    Says: the infinity signature constant has exactly 96 bytes.
    Does not say: that it decodes (guard below). -/
theorem infinitySignature_size : infinitySignature.size = 96 := by
  simp [infinitySignature, ByteArray.size_append, ByteArray.size_push, readPadded_size]

/-- Kind: length.
    Says: when `aggregatePublicKeys` answers, the answer has exactly 48 bytes.
    Does not say: which bytes (tested: `eth_aggregate_pubkeys` vectors). -/
theorem aggregatePublicKeys_size (pks : Array ByteArray) (out : ByteArray)
    (h : aggregatePublicKeys pks = some out) : out.size = 48 := by
  unfold aggregatePublicKeys at h
  split at h
  · cases h
  · cases hKeys : decodePublicKeys pks with
    | none => rw [hKeys] at h; simp at h
    | some keys =>
      rw [hKeys] at h
      have h' := Option.some.inj h
      rw [← h']
      exact compressG1_size _

/-! ### Guards -/

-- The tag is the 43 bytes of the ciphersuite name.
#guard consensusDst.size == 43
-- Compressed generator of `G1` (consensus specifications): decodes, and compresses back.
private def generatorBytes : ByteArray :=
  hex "97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb"
#guard (decodePublicKey generatorBytes).map (fun key => (M.toNat key.x, M.toNat key.y)) == some BLS12381.g1Generator
#guard ((decodePublicKey generatorBytes).map fun key => toHex key.toBytes) == some (toHex generatorBytes)
-- The point at infinity: a valid `G1` encoding, not a valid key; a valid signature encoding.
#guard (match decompressG1 (compressG1 none) with | some none => true | _ => false) &&
  (decodePublicKey (compressG1 none)).isNone
#guard (match decodeSignature infinitySignature with | some ⟨none⟩ => true | _ => false)
-- Flag rules: uncompressed flag, infinity with the sign flag or other bits, wrong lengths.
#guard (decompressG1 (hex ("40" ++ String.ofList (List.replicate 94 '0')))).isNone &&
  (decompressG1 (hex ("e0" ++ String.ofList (List.replicate 94 '0')))).isNone &&
  (decompressG1 (hex ("c0" ++ String.ofList (List.replicate 93 '0') ++ "1"))).isNone &&
  (decompressG1 (generatorBytes.extract 0 47)).isNone && (decompressG1 (generatorBytes.push 0)).isNone
#guard (decompressG2 (hex ("e0" ++ String.ofList (List.replicate 190 '0')))).isNone &&
  (decompressG2 (hex ("80" ++ String.ofList (List.replicate 190 '0')))).isNone &&
  (decompressG2 (hex ("c0" ++ String.ofList (List.replicate 189 '0') ++ "1"))).isNone &&
  (decompressG2 (infinitySignature.extract 0 95)).isNone && (decompressG2 (infinitySignature.push 0)).isNone
-- The pair state is the one `BLS12381Pairing.pairOf` builds from the same points.
private def sameQuad (a b : Quad384) : Bool := Quad384.eq a b
#guard
  let g1 := BLS12381.g1Generator
  let g2 := BLS12381.g2Generator
  let mine := pairState (M.ofNat g1.1) (M.ofNat g1.2) (BLS12381.Fast.toLimbs2 g2.1) (BLS12381.Fast.toLimbs2 g2.2)
  let theirs := BLS12381Pairing.pairOf g1 g2
  sameQuad mine.nx theirs.nx && sameQuad mine.y theirs.y && sameQuad mine.qx theirs.qx &&
    sameQuad mine.qy theirs.qy && sameQuad mine.nqy theirs.nqy && sameQuad mine.t.x theirs.t.x &&
    sameQuad mine.t.y theirs.t.y && sameQuad mine.t.z theirs.t.z
-- Consensus-specification case `verify_valid_case_195246ee3bd3b6ec`, a tampered copy of its
-- signature, the wrong message, and the infinity signature against the valid key.
private def caseKey : ByteArray :=
  hex "b53d21a4cfd562c469cc81514d4ce5a6b577d8403d32a394dc265dd190b47fa9f829fdd7963afdf972e5e77854051f6f"
private def caseMessage : ByteArray := hex "abababababababababababababababababababababababababababababababab"
private def caseSignature : ByteArray :=
  hex ("ae82747ddeefe4fd64cf9cedb9b04ae3e8a43420cd255e3c7cd06a8d88b7c7f8638543719981c5d16fa3527c468c25f0" ++
    "026704a6951bde891360c7e8d12ddee0559004ccdbe6046b55bae1b257ee97f7cdb955773d7cf29adf3ccbb9975e4eb9")
#guard verify caseKey caseMessage caseSignature
#guard !verify caseKey (hex "5656565656565656565656565656565656565656565656565656565656565656") caseSignature
#guard !verify generatorBytes caseMessage caseSignature
#guard !verify caseKey caseMessage infinitySignature
#guard fastAggregateVerify #[caseKey] caseMessage caseSignature && ethFastAggregateVerify #[caseKey] caseMessage caseSignature
#guard aggregateVerify #[caseKey] #[caseMessage] caseSignature
#guard ethFastAggregateVerify #[] caseMessage infinitySignature && !fastAggregateVerify #[] caseMessage infinitySignature
#guard (aggregatePublicKeys #[caseKey]).map toHex == some (toHex caseKey)

#print axioms decompressG1_wrong_size
#print axioms decompressG2_wrong_size
#print axioms decodePublicKey_wrong_size
#print axioms decodeSignature_wrong_size
#print axioms verify_wrong_size
#print axioms fastAggregateVerify_refuses
#print axioms ethFastAggregateVerify_empty_infinity
#print axioms ethFastAggregateVerify_empty_other
#print axioms aggregateVerify_refuses
#print axioms aggregateVerifyDecoded_refuses
#print axioms aggregateDecoded_empty
#print axioms fastAggregateVerifyDecoded_empty
#print axioms aggregatePublicKeys_empty
#print axioms decodeKeysLoop_size
#print axioms decodePublicKeys_size
#print axioms compressG1_size
#print axioms infinitySignature_size
#print axioms aggregatePublicKeys_size

end EVMCleanroom.Precompiles.BLSSignature
