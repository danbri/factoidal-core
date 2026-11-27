import EVMCleanroom.Precompiles.MontgomeryProofs
import EVMCleanroom.Precompiles.Secp256k1Field
import EVMCleanroom.Precompiles.BN254Field
import EVMCleanroom.Precompiles.BLS12381Field
import EVMCleanroom.Precompiles.Secp256k1
import EVMCleanroom.Precompiles.BN254
import EVMCleanroom.Precompiles.BLS12381

/-!
# The three Montgomery parameter sets are valid, and their fields refine the `Nat` fields

For `Secp256k1.scalarField`, `BN254.baseField` and `BLS12381.baseField`:
the parameter literals satisfy `Valid` (checked by the kernel on closed
terms, `decide`), the modulus is the modulus of the `Nat` module
(`Secp256k1.n`, `BN254.p`, `BLS12381.p`), an inverse of the radix is stated as
a literal, and the limb dictionary `ops` refines `Fp.ops` of that modulus on
canonical stored values.

Not proved: that these moduli are prime.
-/

set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

namespace EVMCleanroom.Precompiles


/-- Kind: parameter check (closed terms, by the kernel).
    Says: the literals of the secp256k1 scalar field (integers modulo the group order) are a valid Montgomery parameter set.
    Does not say: that the modulus is prime. -/
theorem Secp256k1.scalarField_valid : Secp256k1.scalarField.Valid :=
  ⟨by first | decide | decide +kernel, by first | decide | decide +kernel,
   by first | decide | decide +kernel, by first | decide | decide +kernel,
   by first | decide | decide +kernel⟩

/-- Kind: parameter check (closed terms, by the kernel).
    Says: the modulus of the limb parameter set is the modulus of the `Nat` module.
    Does not say: anything else. -/
theorem Secp256k1.scalarField_modulus : Secp256k1.scalarField.n.toNat = Secp256k1.n := by first | decide | decide +kernel

/-- Kind: parameter check (closed terms, by the kernel).
    Says: the stated literal is an inverse of the radix `2^256` modulo the modulus.
    Does not say: anything else. -/
theorem Secp256k1.scalarField_Rinv :
    2 ^ 256 * 0xd9e8890d6494ef93897f30c127cfab5d3bbbd4567fa50c3c80fd22938097c016 % Secp256k1.scalarField.n.toNat = 1 := by
  first | decide | decide +kernel

/-- Kind: refinement (leaving Montgomery form, with the literal inverse).
    Says: `toNat a` is `a · Rinv mod N` for the stated literal `Rinv`.
    Does not say: anything about timing. -/
theorem Secp256k1.scalarField_toNat (a : U256) :
    Secp256k1.scalarField.toNat a = a.toNat * 0xd9e8890d6494ef93897f30c127cfab5d3bbbd4567fa50c3c80fd22938097c016 % Secp256k1.n := by
  have h := (Mont256.toNat_eq_value Secp256k1.scalarField_valid Secp256k1.scalarField_Rinv a).2
  rw [Secp256k1.scalarField_modulus] at h
  exact h

/-- Kind: refinement (the whole dictionary).
    Says: the limb operations of the secp256k1 scalar field (integers modulo the group order) refine `Fp.ops Secp256k1.n` on stored values below the
    modulus, read through `toNat`.
    Does not say: that the modulus is prime, that `Fp.inv` inverts, or anything about timing. -/
theorem Secp256k1.scalarField_refines :
    FieldRefines Secp256k1.scalarField.ops Secp256k1.n (fun a => a.toNat < Secp256k1.n) Secp256k1.scalarField.toNat := by
  have h := Mont256.ops_refines Secp256k1.scalarField_valid
  rw [Secp256k1.scalarField_modulus] at h
  exact h

/-- Kind: parameter check (closed terms, by the kernel).
    Says: the literals of the alt_bn128 base field are a valid Montgomery parameter set.
    Does not say: that the modulus is prime. -/
theorem BN254.baseField_valid : BN254.baseField.Valid :=
  ⟨by first | decide | decide +kernel, by first | decide | decide +kernel,
   by first | decide | decide +kernel, by first | decide | decide +kernel,
   by first | decide | decide +kernel⟩

/-- Kind: parameter check (closed terms, by the kernel).
    Says: the modulus of the limb parameter set is the modulus of the `Nat` module.
    Does not say: anything else. -/
theorem BN254.baseField_modulus : BN254.baseField.n.toNat = BN254.p := by first | decide | decide +kernel

/-- Kind: parameter check (closed terms, by the kernel).
    Says: the stated literal is an inverse of the radix `2^256` modulo the modulus.
    Does not say: anything else. -/
theorem BN254.baseField_Rinv :
    2 ^ 256 * 0x2e67157159e5c639cf63e9cfb74492d9eb2022850278edf8ed84884a014afa37 % BN254.baseField.n.toNat = 1 := by
  first | decide | decide +kernel

/-- Kind: refinement (leaving Montgomery form, with the literal inverse).
    Says: `toNat a` is `a · Rinv mod N` for the stated literal `Rinv`.
    Does not say: anything about timing. -/
theorem BN254.baseField_toNat (a : U256) :
    BN254.baseField.toNat a = a.toNat * 0x2e67157159e5c639cf63e9cfb74492d9eb2022850278edf8ed84884a014afa37 % BN254.p := by
  have h := (Mont256.toNat_eq_value BN254.baseField_valid BN254.baseField_Rinv a).2
  rw [BN254.baseField_modulus] at h
  exact h

/-- Kind: refinement (the whole dictionary).
    Says: the limb operations of the alt_bn128 base field refine `Fp.ops BN254.p` on stored values below the
    modulus, read through `toNat`.
    Does not say: that the modulus is prime, that `Fp.inv` inverts, or anything about timing. -/
theorem BN254.baseField_refines :
    FieldRefines BN254.baseField.ops BN254.p (fun a => a.toNat < BN254.p) BN254.baseField.toNat := by
  have h := Mont256.ops_refines BN254.baseField_valid
  rw [BN254.baseField_modulus] at h
  exact h

/-- Kind: parameter check (closed terms, by the kernel).
    Says: the literals of the BLS12-381 base field are a valid Montgomery parameter set.
    Does not say: that the modulus is prime. -/
theorem BLS12381.baseField_valid : BLS12381.baseField.Valid :=
  ⟨by first | decide | decide +kernel, by first | decide | decide +kernel,
   by first | decide | decide +kernel, by first | decide | decide +kernel,
   by first | decide | decide +kernel⟩

/-- Kind: parameter check (closed terms, by the kernel).
    Says: the modulus of the limb parameter set is the modulus of the `Nat` module.
    Does not say: anything else. -/
theorem BLS12381.baseField_modulus : BLS12381.baseField.n.toNat = BLS12381.p := by first | decide | decide +kernel

/-- Kind: parameter check (closed terms, by the kernel).
    Says: the stated literal is an inverse of the radix `2^384` modulo the modulus.
    Does not say: anything else. -/
theorem BLS12381.baseField_Rinv :
    2 ^ 384 * 0x14fec701e8fb0ce9ed5e64273c4f538b1797ab1458a88de9343ea97914956dc87fe11274d898fafbf4d38259380b4820 % BLS12381.baseField.n.toNat = 1 := by
  first | decide | decide +kernel

/-- Kind: refinement (leaving Montgomery form, with the literal inverse).
    Says: `toNat a` is `a · Rinv mod N` for the stated literal `Rinv`.
    Does not say: anything about timing. -/
theorem BLS12381.baseField_toNat (a : U384) :
    BLS12381.baseField.toNat a = a.toNat * 0x14fec701e8fb0ce9ed5e64273c4f538b1797ab1458a88de9343ea97914956dc87fe11274d898fafbf4d38259380b4820 % BLS12381.p := by
  have h := (Mont384.toNat_eq_value BLS12381.baseField_valid BLS12381.baseField_Rinv a).2
  rw [BLS12381.baseField_modulus] at h
  exact h

/-- Kind: refinement (the whole dictionary).
    Says: the limb operations of the BLS12-381 base field refine `Fp.ops BLS12381.p` on stored values below the
    modulus, read through `toNat`.
    Does not say: that the modulus is prime, that `Fp.inv` inverts, or anything about timing. -/
theorem BLS12381.baseField_refines :
    FieldRefines BLS12381.baseField.ops BLS12381.p (fun a => a.toNat < BLS12381.p) BLS12381.baseField.toNat := by
  have h := Mont384.ops_refines BLS12381.baseField_valid
  rw [BLS12381.baseField_modulus] at h
  exact h

#print axioms Secp256k1.scalarField_valid
#print axioms Secp256k1.scalarField_modulus
#print axioms Secp256k1.scalarField_Rinv
#print axioms Secp256k1.scalarField_toNat
#print axioms Secp256k1.scalarField_refines
#print axioms BN254.baseField_valid
#print axioms BN254.baseField_modulus
#print axioms BN254.baseField_Rinv
#print axioms BN254.baseField_toNat
#print axioms BN254.baseField_refines
#print axioms BLS12381.baseField_valid
#print axioms BLS12381.baseField_modulus
#print axioms BLS12381.baseField_Rinv
#print axioms BLS12381.baseField_toNat
#print axioms BLS12381.baseField_refines

end EVMCleanroom.Precompiles
