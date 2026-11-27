import EVMCleanroom.Precompiles.KZG
import EVMCleanroom.Precompiles.BLS12381Pairing

/-!
# KZG point evaluation (0x0a) with the pairing product on the limb tower

The same contract as `KZG.run` (EIP-4844). Everything except the final product check is
the code of `KZG.lean`: the versioned hash, the canonical scalars, the two decompressions
with their subgroup checks, and the two fixed-base scalar multiplications `[y]G₁` and
`[z]G₂` on the `Nat` path. The product `e(C − [y]G₁, −G₂) · e(proof, [τ]G₂ − [z]G₂) = 1`
is decided by `BLS12381Pairing.productIsOne`.

Proved: the input-length rule, gas accounting, the constant output. Not proved: the
verdict (the 122 consensus-specification cases through the router, and the differential
check `evm-pairingperf` against `KZG.verify`).
-/

namespace EVMCleanroom.Precompiles.KZGPairing

open BLS12381 (p r field field2)

/-- The pairing equation of `verify_kzg_proof`, as `KZG.verify` with the fast product check.
    Pairs with a point at infinity contribute one and are dropped. -/
def verify (commitment proof : Option (Nat × Nat)) (z y : Nat) : Bool :=
  let g1 := Curve.ofAffine field BLS12381.g1Generator.1 BLS12381.g1Generator.2
  let g2 := Curve.ofAffine field2 BLS12381.g2Generator.1 BLS12381.g2Generator.2
  let pMinusY := Curve.add field (BLS12381.jacobian1 commitment) (Curve.mul field ((r - y) % r) g1)
  let xMinusZ := Curve.add field2 (Curve.ofAffine field2 KZG.setupG2.1 KZG.setupG2.2)
    (Curve.mul field2 ((r - z) % r) g2)
  let negG2 : Fp2 × Fp2 := (BLS12381.g2Generator.1, Fp2.neg p BLS12381.g2Generator.2)
  let first := (KZG.toPair field pMinusY).map fun a => BLS12381Pairing.pairOf a negG2
  let second :=
    match proof, KZG.toPair field2 xMinusZ with
    | some a, some b => some (BLS12381Pairing.pairOf a b)
    | _, _ => none
  BLS12381Pairing.productIsOne (first.toList ++ second.toList)

def body (input : ByteArray) : Body :=
  let z := beNat input 32 32
  let y := beNat input 64 32
  if !KZG.bytesEqual (KZG.versionedHash (input.extract 96 144)) (input.extract 0 32) then .invalid
  else if z ≥ r ∨ y ≥ r then .invalid
  else
    match KZG.decompressG1 input 96, KZG.decompressG1 input 144 with
    | some commitment, some proof =>
      if verify commitment proof z y then .output KZG.successOutput else .invalid
    | _, _ => .invalid

/-- Precompile 0x0a. -/
def run (gas : Nat) (input : ByteArray) : Result :=
  if input.size ≠ 192 then .failure else charge gas KZG.gasCost fun _ => body input

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
    input.size = 192 ∧ out = KZG.successOutput ∧ left + 50000 = gas := by
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

-- The zero polynomial: commitment and proof at infinity, y = 0, any z; and a constant
-- polynomial c: commitment [c]G₁, proof at infinity, y = c.
#guard verify none none 5 0
#guard !verify none none 5 1
#guard verify (some BLS12381.g1Generator) none 7 1 && !verify (some BLS12381.g1Generator) none 7 2
#guard verify (some BLS12381.g1Generator) none 7 1 == KZG.verify (some BLS12381.g1Generator) none 7 1
#guard verify (some BLS12381.g1Generator) (some BLS12381.g1Generator) 7 2 ==
  KZG.verify (some BLS12381.g1Generator) (some BLS12381.g1Generator) 7 2

#print axioms run_wrong_length
#print axioms run_success

end EVMCleanroom.Precompiles.KZGPairing
