import EVMCleanroom.Precompiles.BLSSignature
import EVMCleanroom.Precompiles.KZG

/-!
# BLS signature verification by the `Nat` definitions: the differential oracle

A plain statement of the same checks as `Precompiles/BLSSignature.lean`, built only from
the definitional modules: `KZG.decompressG1` and `KZG.decompressG2` (with the infinity
case and the definitional subgroup check `[r]Q = O` added for `G2`), the map to the
curve from the parts of `BLS12381.mapToG2` (`swu`, `isogeny`, multiplication by the
effective cofactor), and `Pairing.productIsOne BLS12381.curve`.

It shares one piece with the fast path: `HashToCurve.hashToFieldFp2` (the SHA-256
expansion and the reduction modulo `p`, plain byte and `Nat` code with no fast variant,
tested by RFC 9380 appendix K.1 and the `u` values of J.10.1).

Test code: slow (about a tenth of a second per verification), nothing proved, and not in
the import closure of the library module. `testOnlyScalarMulG2` produces signatures for
generated test cases from small public test scalars; it is not a signing function and
must never be given a secret.
-/

namespace EVMCleanroom.BLSSig.Reference

open EVMCleanroom.Precompiles
open BLS12381 (p r field field2 curve)

def mapToCurve (u : Fp2) : JPoint Fp2 :=
  BLS12381.isogeny field2 BLS12381.iso2XNum BLS12381.iso2XDen BLS12381.iso2YNum BLS12381.iso2YDen
    (BLS12381.swu field2 BLS12381.sqrt2? BLS12381.sgn02 ⟨0, 240⟩ ⟨1012, 1012⟩ (Fp2.neg p ⟨2, 1⟩) u)

/-- `hash_to_curve` for `G2` on the `Nat` field: map both elements, add, multiply by `h_eff`. -/
def hashToG2 (dst msg : ByteArray) : Option (JPoint Fp2) :=
  (HashToCurve.hashToFieldFp2 dst msg).map fun u =>
    Curve.mul field2 BLS12381.cofactor2 (Curve.add field2 (mapToCurve u.1) (mapToCurve u.2))

def affine1 (point : JPoint Nat) : Option (Nat × Nat) := Curve.toAffine field point
def affine2 (point : JPoint Fp2) : Option (Fp2 × Fp2) := Curve.toAffine field2 point

def decodeG1 (bytes : ByteArray) : Option (Option (Nat × Nat)) :=
  if bytes.size ≠ 48 then none else KZG.decompressG1 bytes 0

def decodeG2 (bytes : ByteArray) : Option (Option (Fp2 × Fp2)) :=
  if bytes.size ≠ 96 then none
  else
    let first := (byteAt bytes 0).toNat
    if first / 128 % 2 ≠ 1 then none
    else if first / 64 % 2 = 1 then
      (if beNat bytes 0 96 % 2 ^ 766 == 0 then some none else none)
    else
      match KZG.decompressG2 bytes with
      | none => none
      | some point => if BLS12381.inSubgroup2 point.1 point.2 then some (some point) else none

def negG1 : Nat × Nat := (BLS12381.g1Generator.1, Fp.neg p BLS12381.g1Generator.2)

def keyPairs (key : Nat × Nat) (hashed : JPoint Fp2) : List (Pairing.G1 × Pairing.G2) :=
  match affine2 hashed with
  | some h => [(key, h)]
  | none => []

def signaturePairs (sig : Option (Fp2 × Fp2)) : List (Pairing.G1 × Pairing.G2) :=
  match sig with
  | some s => [(negG1, s)]
  | none => []

def verify (pk msg sig dst : ByteArray) : Bool :=
  match decodeG1 pk with
  | some (some key) =>
    match decodeG2 sig with
    | some s =>
      match hashToG2 dst msg with
      | some hashed => Pairing.productIsOne curve (keyPairs key hashed ++ signaturePairs s)
      | none => false
    | none => false
  | _ => false

def decodeKeys (pks : Array ByteArray) : Option (Array (Nat × Nat)) :=
  pks.foldl (fun acc pk =>
    match acc, decodeG1 pk with
    | some keys, some (some key) => some (keys.push key)
    | _, _ => none) (some #[])

def sumKeys (keys : Array (Nat × Nat)) : JPoint Nat :=
  keys.foldl (fun acc key => Curve.add field acc (Curve.ofAffine field key.1 key.2)) (Curve.infinity field)

def fastAggregateVerify (pks : Array ByteArray) (msg sig dst : ByteArray) : Bool :=
  if pks.size = 0 then false
  else
    match decodeKeys pks, decodeG2 sig with
    | some keys, some s =>
      match affine1 (sumKeys keys), hashToG2 dst msg with
      | some key, some hashed => Pairing.productIsOne curve (keyPairs key hashed ++ signaturePairs s)
      | _, _ => false
    | _, _ => false

def ethFastAggregateVerify (pks : Array ByteArray) (msg sig dst : ByteArray) : Bool :=
  if pks.size = 0 ∧ sig.data = (natToBE 96 (3 * 2 ^ 766)).data then true
  else fastAggregateVerify pks msg sig dst

def aggregateVerify (pks msgs : Array ByteArray) (sig dst : ByteArray) : Bool :=
  if pks.size = 0 ∨ pks.size ≠ msgs.size then false
  else
    match decodeKeys pks, decodeG2 sig with
    | some keys, some s =>
      let pairs := (keys.zip msgs).foldl (fun acc item =>
        match acc, hashToG2 dst item.2 with
        | some list, some hashed => some (keyPairs item.1 hashed ++ list)
        | _, _ => none) (some (signaturePairs s))
      match pairs with
      | some list => Pairing.productIsOne curve list
      | none => false
    | _, _ => false

/-- Compressed encodings from `Nat` coordinates (`none`: the point at infinity). -/
def compress1 (point : Option (Nat × Nat)) : ByteArray :=
  match point with
  | none => natToBE 48 (3 * 2 ^ 382)
  | some (x, y) => natToBE 48 (x + 2 ^ 383 + (if y > (p - 1) / 2 then 2 ^ 381 else 0))

def compress2 (point : Option (Fp2 × Fp2)) : ByteArray :=
  match point with
  | none => natToBE 96 (3 * 2 ^ 766)
  | some (x, y) =>
    natToBE 48 (x.c1 + 2 ^ 383 + (if KZG.larger2 y then 2 ^ 381 else 0)) ++ natToBE 48 x.c0

def aggregatePublicKeys (pks : Array ByteArray) : Option ByteArray :=
  if pks.size = 0 then none
  else (decodeKeys pks).map fun keys => compress1 (affine1 (sumKeys keys))

/-- TEST ONLY: `[k]Q` on the `Nat` field, to make signatures of generated cases from public
    test scalars. Variable-time; never a signing function. -/
def testOnlyScalarMulG2 (k : Nat) (point : JPoint Fp2) : JPoint Fp2 := Curve.mul field2 k point

/-- TEST ONLY: `[k]G₁` on the `Nat` field, the key of the public test scalar `k`. -/
def testOnlyKeyPoint (k : Nat) : Option (Nat × Nat) :=
  affine1 (Curve.mul field k (Curve.ofAffine field BLS12381.g1Generator.1 BLS12381.g1Generator.2))

-- The compressed generator of the consensus specifications, and the infinity encodings.
#guard toHex (compress1 (some BLS12381.g1Generator)) ==
  "97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb"
#guard (compress2 none).data == BLSSignature.infinitySignature.data &&
  (compress1 none).data == (BLSSignature.compressG1 none).data
#guard (match decodeG2 (compress2 none) with | some none => true | _ => false) &&
  decodeG2 (compress2 (some BLS12381.g2Generator)) == some (some BLS12381.g2Generator) &&
  decodeG1 (compress1 (some BLS12381.g1Generator)) == some (some BLS12381.g1Generator)

end EVMCleanroom.BLSSig.Reference
