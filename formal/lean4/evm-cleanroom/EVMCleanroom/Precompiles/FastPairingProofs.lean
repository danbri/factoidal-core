import EVMCleanroom.Precompiles.BN254Pairing
import EVMCleanroom.Precompiles.BLS12381Pairing

/-!
# Integer facts behind the fast pairing checks

The algebra of the fast pairing (`FastPairing`, `BN254Pairing`, `BLS12381Pairing`) is
tested, not proved. What can be proved cheaply is the integer arithmetic the published
algorithms rest on, for the two concrete curves. Each theorem below is a closed statement
about natural numbers or integers, checked by the kernel's evaluation (`decide +kernel`:
no compiled code is trusted, and no axiom beyond the three standard ones is used).

* The signed recodings stand for the scalars they claim: the Miller loop scalar, the curve
  parameter in the hard part, and `6x²` of the subgroup test.
* The exponent of the hard-part chain: the BN chain raises to
  `λ₀ + λ₁p + λ₂p² + λ₃p³ = 2x(6x²+3x+1)·(p⁴−p²+1)/r`; the BLS12 chain to
  `(x−1)²(x+p)(x²+p²−1) + 3 = 3·(p⁴−p²+1)/r` for the negative parameter. Both multipliers
  are coprime to `r`.
* The arithmetic step of the subgroup criterion on alt_bn128: with `t = 6x² + 1`,
  `(t−1)² + p = t(t−1) + r`, so `ψ(Q) = [t−1]Q` and `ψ² − [t]ψ + [p] = 0` give `[r]Q = O`;
  and `gcd(r, 2p − r) = 1`.
* The number of pairs entering the Miller loop is at most the number of 192-byte or
  384-byte items of the input.

None of this says that the chains, the recoded loops or the endomorphism compute what the
integer identities describe: that is the tested part.
-/

namespace EVMCleanroom.Precompiles.FastPairingProofs

/-- Kind: recoding identity.
    Says: the digit lists of alt_bn128, read after their leading one, are `6x + 2`, `x` and `6x²`.
    Does not say: the loops over these digits compute the corresponding multiples or powers. -/
theorem bn_digits :
    digitsValue BN254Pairing.loopDigits 1 = Int.ofNat (6 * BN254.parameter + 2) ∧
    digitsValue BN254Pairing.xDigits 1 = Int.ofNat BN254.parameter ∧
    digitsValue BN254Pairing.psiDigits 1 = Int.ofNat (6 * BN254.parameter ^ 2) := by
  decide +kernel

/-- Kind: recoding identity.
    Says: the digit list of BLS12-381, read after its leading one, is `|x|`.
    Does not say: the loops over these digits compute the corresponding multiples or powers. -/
theorem bls_digits : digitsValue BLS12381Pairing.xDigits 1 = Int.ofNat BLS12381.parameter := by
  decide +kernel

/-- Kind: loop bound.
    Says: the Miller loop of alt_bn128 runs 64 shared squarings, its hard-part powers 62
    cyclotomic squarings each, its subgroup test 127 doublings; BLS12-381 runs 63 and 63.
    Does not say: how long a step takes. -/
theorem digit_counts :
    BN254Pairing.loopDigits.length = 64 ∧ BN254Pairing.xDigits.length = 62 ∧
    BN254Pairing.psiDigits.length = 127 ∧ BLS12381Pairing.xDigits.length = 63 := by
  decide +kernel

/-- Kind: decomposition identity.
    Says: for the alt_bn128 parameter, the exponent of the BN hard-part chain,
    `λ₀ + λ₁p + λ₂p² + λ₃p³`, equals `hardPower · (p⁴ − p² + 1)/r`, the division is exact,
    and `hardPower = 2x(6x²+3x+1)` is coprime to `r`.
    Does not say: the chain computes that power (guards and the differential check). -/
theorem bn_hard_exponent :
    (12 * BN254.parameter ^ 3 + 12 * BN254.parameter ^ 2 + 6 * BN254.parameter + 1) +
        (12 * BN254.parameter ^ 3 + 6 * BN254.parameter ^ 2 + 4 * BN254.parameter) * BN254.p +
        (12 * BN254.parameter ^ 3 + 6 * BN254.parameter ^ 2 + 6 * BN254.parameter) * BN254.p ^ 2 +
        (12 * BN254.parameter ^ 3 + 6 * BN254.parameter ^ 2 + 4 * BN254.parameter - 1) * BN254.p ^ 3 =
      BN254Pairing.hardPower * ((BN254.p ^ 4 - BN254.p ^ 2 + 1) / BN254.r) ∧
    (BN254.p ^ 4 - BN254.p ^ 2 + 1) % BN254.r = 0 ∧ Nat.gcd BN254Pairing.hardPower BN254.r = 1 := by
  decide +kernel

/-- Kind: decomposition identity.
    Says: for the BLS12-381 parameter `x = −|x|`, `(x−1)²(x+p)(x²+p²−1) + 3 = 3·(p⁴−p²+1)/r`
    (written with `|x|`: `(|x|+1)²(p−|x|)(|x|²+p²−1) + 3`), the division is exact, and 3 is
    coprime to `r`.
    Does not say: the chain computes that power (guards and the differential check). -/
theorem bls_hard_exponent :
    (BLS12381.parameter + 1) ^ 2 * (BLS12381.p - BLS12381.parameter) *
        (BLS12381.parameter ^ 2 + BLS12381.p ^ 2 - 1) + 3 =
      3 * ((BLS12381.p ^ 4 - BLS12381.p ^ 2 + 1) / BLS12381.r) ∧
    (BLS12381.p ^ 4 - BLS12381.p ^ 2 + 1) % BLS12381.r = 0 ∧
    Nat.gcd BLS12381Pairing.hardPower BLS12381.r = 1 := by
  decide +kernel

/-- Kind: arithmetic step of the subgroup criterion.
    Says: for alt_bn128, with `t − 1 = 6x²` (`psiScalar`): `p + 1 = r + t`,
    `(t−1)² + p = t·(t−1) + r`, and `gcd(r, 2p − r) = 1`.
    Does not say: that `ψ` satisfies `ψ² − [t]ψ + [p] = 0` or acts on the subgroup as
    `[t − 1]` (published, tested here, not proved). -/
theorem bn_subgroup_arithmetic :
    BN254Pairing.psiScalar = 6 * BN254.parameter ^ 2 ∧ BN254.p + 1 = BN254.r + (BN254Pairing.psiScalar + 1) ∧
    BN254Pairing.psiScalar ^ 2 + BN254.p = (BN254Pairing.psiScalar + 1) * BN254Pairing.psiScalar + BN254.r ∧
    Nat.gcd BN254.r (2 * BN254.p - BN254.r) = 1 := by
  decide +kernel

/-- Kind: loop bound.
    Says: decoding returns at most one pair per 192-byte item on top of the pairs already
    held, so the shared Miller loop of 0x08 runs over at most `input.size / 192` pairs.
    Does not say: how long the loop takes. -/
theorem bn_decodePairs_length (data : ByteArray) (count off : Nat) (acc pairs : List (PairState U256))
    (h : BN254Pairing.decodePairs data count off acc = some pairs) : pairs.length ≤ acc.length + count := by
  induction count generalizing off acc with
  | zero =>
    simp only [BN254Pairing.decodePairs, Option.some.injEq] at h
    subst h
    omega
  | succ n ih =>
    simp only [BN254Pairing.decodePairs] at h
    split at h
    · split at h
      · have hl := ih _ _ h
        simp only [List.length_cons] at hl
        omega
      · have hl := ih _ _ h
        omega
    · cases h

/-- Kind: loop bound.
    Says: the same for 0x0f: at most `input.size / 384` pairs enter the Miller loop.
    Does not say: how long the loop takes. -/
theorem bls_decodePairs_length (data : ByteArray) (count off : Nat) (acc pairs : List (PairState U384))
    (h : BLS12381Pairing.decodePairs data count off acc = some pairs) : pairs.length ≤ acc.length + count := by
  induction count generalizing off acc with
  | zero =>
    simp only [BLS12381Pairing.decodePairs, Option.some.injEq] at h
    subst h
    omega
  | succ n ih =>
    simp only [BLS12381Pairing.decodePairs] at h
    split at h
    · split at h
      · have hl := ih _ _ h
        simp only [List.length_cons] at hl
        omega
      · have hl := ih _ _ h
        omega
    · cases h

#print axioms bn_digits
#print axioms bls_digits
#print axioms digit_counts
#print axioms bn_hard_exponent
#print axioms bls_hard_exponent
#print axioms bn_subgroup_arithmetic
#print axioms bn_decodePairs_length
#print axioms bls_decodePairs_length

end EVMCleanroom.Precompiles.FastPairingProofs
