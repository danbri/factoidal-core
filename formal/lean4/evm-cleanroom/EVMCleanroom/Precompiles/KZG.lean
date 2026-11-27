import EVMCleanroom.Precompiles.BLS12381
import EVMCleanroom.Precompiles.Sha256

/-!
# KZG point evaluation (precompile 0x0a, EIP-4844)

Input, exactly 192 bytes: `versioned_hash (32) ‖ z (32) ‖ y (32) ‖ commitment
(48) ‖ proof (48)`. The call costs 50000 gas and succeeds only if

* the versioned hash is `0x01 ‖ sha256(commitment)[1..]`;
* `z` and `y` are canonical scalars (below the group order `r`);
* commitment and proof are valid compressed `G1` points (the point at infinity
  is allowed; any other point must be on the curve and in the order-`r`
  subgroup);
* `e(C − [y]G₁, −G₂) · e(proof, [τ]G₂ − [z]G₂) = 1`.

The output is then `FIELD_ELEMENTS_PER_BLOB` (4096) and the scalar modulus,
each as 32 big-endian bytes. Every other case is an exceptional halt.

Compressed points follow the encoding used by the consensus specifications:
48 bytes, big-endian `x`, with the three top bits of the first byte holding
the flags *compressed* (must be set), *infinity*, and *y is the larger of the
two roots*.

Trusted setup. Verification needs one published value of the Ethereum KZG
ceremony, `[τ]G₂`: the second entry of `g2_monomial` in the mainnet
`trusted_setup_4096.json` of the consensus specifications (SHA-256 of that
file: `f8e44a31ebf0a6d0734dcb301b0716e2c77f3ae18ed0cab0870fbcc2ca55616f`).
It is data, not an implementation. It is stored here in affine form, and a
build-time guard checks that decompressing the published 96 bytes gives
exactly these coordinates and that the point is in the order-`r` subgroup.

Proved: the input-length rule, gas accounting, the constant output.
Not proved: the pairing equation (published vectors).
-/

namespace EVMCleanroom.Precompiles.KZG

open BLS12381 (p r field field2 curve)

def gasCost : Nat := 50000
def fieldElementsPerBlob : Nat := 4096

/-- `[τ]G₂` of the Ethereum KZG ceremony, affine. -/
def setupG2 : Fp2 × Fp2 :=
  (⟨0x185cbfee53492714734429b7b38608e23926c911cceceac9a36851477ba4c60b087041de621000edc98edada20c1def2,
    0x15bfd7dd8cdeb128843bc287230af38926187075cbfbefa81009a2ce615ac53d2914e5870cb452d2afaaab24f3499f72⟩,
   ⟨0x014353bdb96b626dd7d5ee8599d1fca2131569490e28de18e82451a496a9c9794ce26d105941f383ee689bfbbb832a99,
    0x1666c54b0a32529503432fcae0181b4bef79de09fc63671fda5ed1ba9bfa07899495346f3d7ac9cd23048ef30d0a154f⟩)

/-- The published compressed form of `[τ]G₂` (`g2_monomial[1]`). -/
def setupG2Compressed : String :=
  "b5bfd7dd8cdeb128843bc287230af38926187075cbfbefa81009a2ce615ac53d2914e5870cb452d2afaaab24f3499f72" ++
  "185cbfee53492714734429b7b38608e23926c911cceceac9a36851477ba4c60b087041de621000edc98edada20c1def2"

/-- Decompress a 48-byte `G1` point at `off`. Outer `none`: invalid encoding, off the
    curve, or outside the subgroup. Inner `none`: the point at infinity. -/
def decompressG1 (data : ByteArray) (off : Nat) : Option (Option (Nat × Nat)) :=
  let first := (byteAt data off).toNat
  let compressed := first / 128 % 2 == 1
  let infinity := first / 64 % 2 == 1
  let larger := first / 32 % 2 == 1
  let x := beNat data off 48 % 2 ^ 381
  if !compressed then none
  else if infinity then (if x == 0 && !larger then some none else none)
  else if x ≥ p then none
  else
    match Fp.sqrt? p ((x * x % p * x + 4) % p) with
    | none => none
    | some root =>
      let y := if decide (root > (p - 1) / 2) == larger then root else Fp.neg p root
      if BLS12381.inSubgroup1 x y then some (some (x, y)) else none

/-- Is `a` the larger of `a` and `−a` in the order used for compressed `G2` points
    (imaginary part first)? -/
def larger2 (a : Fp2) : Bool :=
  if a.c1 = 0 then a.c0 > (p - 1) / 2 else a.c1 > (p - 1) / 2

/-- Decompress a 96-byte `G2` point (`x.c1 ‖ x.c0`, flags in the first byte). Used
    at build time to check the stored setup point. -/
def decompressG2 (data : ByteArray) : Option (Fp2 × Fp2) :=
  let first := (byteAt data 0).toNat
  let x : Fp2 := ⟨beNat data 48 48, beNat data 0 48 % 2 ^ 381⟩
  if first / 128 % 2 ≠ 1 ∨ first / 64 % 2 = 1 ∨ x.c0 ≥ p ∨ x.c1 ≥ p then none
  else
    match BLS12381.sqrt2? (Fp2.add p (Fp2.mul p (Fp2.sqr p x) x) BLS12381.twistB) with
    | none => none
    | some root =>
      some (x, if larger2 root == (first / 32 % 2 == 1) then root else Fp2.neg p root)

def versionedHash (commitment : ByteArray) : ByteArray :=
  (ByteArray.empty.push 0x01) ++ (Sha256.digest commitment).extract 1 32

def bytesEqual (a b : ByteArray) : Bool := a.data == b.data

def toPair {α : Type} (O : FieldOps α) (point : JPoint α) : Option (α × α) := Curve.toAffine O point

/-- The pairing equation of `verify_kzg_proof`. Pairs with a point at infinity
    contribute one and are dropped. -/
def verify (commitment proof : Option (Nat × Nat)) (z y : Nat) : Bool :=
  let g1 := Curve.ofAffine field BLS12381.g1Generator.1 BLS12381.g1Generator.2
  let g2 := Curve.ofAffine field2 BLS12381.g2Generator.1 BLS12381.g2Generator.2
  let pMinusY := Curve.add field (BLS12381.jacobian1 commitment) (Curve.mul field ((r - y) % r) g1)
  let xMinusZ := Curve.add field2 (Curve.ofAffine field2 setupG2.1 setupG2.2) (Curve.mul field2 ((r - z) % r) g2)
  let negG2 : Fp2 × Fp2 := (BLS12381.g2Generator.1, Fp2.neg p BLS12381.g2Generator.2)
  let first := (toPair field pMinusY).map fun a => (a, negG2)
  let second :=
    match proof, toPair field2 xMinusZ with
    | some a, some b => some (a, b)
    | _, _ => none
  Pairing.productIsOne curve (first.toList ++ second.toList)

def successOutput : ByteArray := natToBE 32 fieldElementsPerBlob ++ natToBE 32 r

def body (input : ByteArray) : Body :=
  let z := beNat input 32 32
  let y := beNat input 64 32
  if !bytesEqual (versionedHash (input.extract 96 144)) (input.extract 0 32) then .invalid
  else if z ≥ r ∨ y ≥ r then .invalid
  else
    match decompressG1 input 96, decompressG1 input 144 with
    | some commitment, some proof =>
      if verify commitment proof z y then .output successOutput else .invalid
    | _, _ => .invalid

/-- Precompile 0x0a. -/
def run (gas : Nat) (input : ByteArray) : Result :=
  if input.size ≠ 192 then .failure else charge gas gasCost fun _ => body input

/-- Kind: input-length rule.
    Says: any input that is not exactly 192 bytes fails, whatever the gas.
    Does not say: anything about well-sized input. -/
theorem run_wrong_length (gas : Nat) (input : ByteArray) (h : input.size ≠ 192) :
    run gas input = .failure := by
  simp [run, h]

/-- Kind: output contract and accounting.
    Says: a successful call had exactly 192 input bytes, cost exactly 50000 gas, and
    returned the one constant output (64 bytes: 4096 and the scalar modulus).
    Does not say: the proof was valid (the pairing equation is tested, not proved). -/
theorem run_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : run gas input = .success out left) :
    input.size = 192 ∧ out = successOutput ∧ left + 50000 = gas := by
  unfold run at h
  split at h
  · cases h
  · rename_i hSize
    have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
    refine ⟨by omega, ?_, hGas⟩
    unfold body at hBody
    simp only at hBody
    split at hBody
    · exact Body.noConfusion hBody
    · split at hBody
      · exact Body.noConfusion hBody
      · split at hBody
        · split at hBody
          · exact (Body.output.inj hBody).symm
          · exact Body.noConfusion hBody
        · exact Body.noConfusion hBody

theorem successOutput_size : successOutput.size = 64 := by
  simp [successOutput, ByteArray.size_append, natToBE_size]

-- The stored setup point is the published one, is on the twist and has order r.
#guard decompressG2 (hex setupG2Compressed) == some setupG2
#guard Curve.onCurve field2 BLS12381.twistB setupG2.1 setupG2.2 && BLS12381.inSubgroup2 setupG2.1 setupG2.2
-- Compressed generator of G1 (consensus specifications) and the point at infinity.
#guard decompressG1 (hex ("97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac58" ++
  "6c55e83ff97a1aeffb3af00adb22c6bb")) 0 == some (some BLS12381.g1Generator)
#guard decompressG1 (hex ("c0" ++ String.ofList (List.replicate 94 '0'))) 0 == some none
#guard decompressG1 (hex ("40" ++ String.ofList (List.replicate 94 '0'))) 0 == none
#guard decompressG1 (hex ("e0" ++ String.ofList (List.replicate 94 '0'))) 0 == none
-- The zero polynomial: commitment and proof at infinity, y = 0, any z.
#guard verify none none 5 0
#guard !verify none none 5 1
#guard toHex successOutput ==
  "0000000000000000000000000000000000000000000000000000000000001000" ++
  "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"

#print axioms run_wrong_length
#print axioms run_success
#print axioms successOutput_size

end EVMCleanroom.Precompiles.KZG
