import EVMCleanroom.Precompiles.ModExp

/-!
# MODEXP computes the modular power

Functional correctness of the exponent loop of precompile 0x05 against the
mathematical definition `base ^ exponent % modulus` on natural numbers, for
every input: the loop over exponent bytes, most significant bit first, returns
exactly that residue, where the exponent is the big-endian number formed by
the bytes it consumed.

This is a statement about the Lean function. It does not cover the byte
decoding of the three operands, the price, or the correctness of the Lean
runtime's big-integer arithmetic.
-/

namespace EVMCleanroom.Precompiles.ModExp

private theorem mod_mul_left (m x y : Nat) : (x % m) * y % m = x * y % m := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

private theorem pow_congr (m x y k : Nat) (h : x % m = y % m) : x ^ k % m = y ^ k % m := by
  rw [Nat.pow_mod, h, ← Nat.pow_mod]

private theorem mul_congr (m a b c d : Nat) (h1 : a % m = c % m) (h2 : b % m = d % m) :
    a * b % m = c * d % m := by
  rw [Nat.mul_mod, h1, h2, ← Nat.mul_mod]

/-- Kind: functional correctness (one exponent byte).
    Says: `k` steps on a byte raise the accumulator to the `2^k`-th power and multiply by the
    base to the power of the byte's low `k` bits, modulo the modulus.
    Does not say: anything about bytes beyond the low `k` bits. -/
theorem powByte_spec (modulus base : Nat) (byte : UInt8) (k acc : Nat) :
    powByte modulus base byte k acc % modulus =
      acc ^ (2 ^ k) * base ^ (byte.toNat % 2 ^ k) % modulus := by
  induction k generalizing acc with
  | zero => simp [powByte, Nat.mod_one]
  | succ k ih =>
    simp only [powByte]
    rw [ih, Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    by_cases hBit : byte.toNat / 2 ^ k % 2 = 1
    · simp only [hBit, decide_true, ↓reduceIte, Nat.mul_one]
      have hAcc : (acc * acc % modulus * base % modulus) % modulus = (acc * acc * base) % modulus := by
        rw [Nat.mod_mod, mod_mul_left]
      have hPow := pow_congr modulus _ _ (2 ^ k) hAcc
      rw [mul_congr modulus _ _ _ _ hPow rfl]
      have hAlg : (acc * acc * base) ^ 2 ^ k * base ^ (byte.toNat % 2 ^ k) =
          acc ^ 2 ^ (k + 1) * base ^ (byte.toNat % 2 ^ k + 2 ^ k) := by
        rw [Nat.mul_pow, ← Nat.pow_two, ← Nat.pow_mul, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2,
          Nat.pow_add, Nat.mul_assoc, Nat.mul_comm (base ^ 2 ^ k)]
      rw [hAlg]
    · have hZero : byte.toNat / 2 ^ k % 2 = 0 := by omega
      simp only [hZero, Nat.zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.mul_zero,
        Nat.add_zero]
      have hAcc : (acc * acc % modulus) % modulus = (acc * acc) % modulus := Nat.mod_mod _ _
      have hPow := pow_congr modulus _ _ (2 ^ k) hAcc
      rw [mul_congr modulus _ _ _ _ hPow rfl]
      have hAlg : (acc * acc) ^ 2 ^ k = acc ^ 2 ^ (k + 1) := by
        rw [← Nat.pow_two, ← Nat.pow_mul, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2]
      rw [hAlg]

private theorem beLoop_acc (b : ByteArray) (n off acc : Nat) :
    beLoop b n off acc = acc * 256 ^ n + beLoop b n off 0 := by
  induction n generalizing off acc with
  | zero => simp [beLoop]
  | succ n ih =>
    simp only [beLoop]
    rw [ih, ih (off + 1) (0 * 256 + (byteAt b off).toNat), Nat.pow_succ]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
    rw [Nat.mul_comm 256 (256 ^ n)]

/-- Kind: functional correctness (the exponent loop).
    Says: consuming `n` exponent bytes raises the accumulator to the `256^n`-th power and
    multiplies by the base to the power of the big-endian number those bytes spell, modulo
    the modulus.
    Does not say: where the bytes come from. -/
theorem powBytes_spec (modulus base : Nat) (input : ByteArray) (n off acc : Nat) :
    powBytes modulus base input n off acc % modulus =
      acc ^ (256 ^ n) * base ^ (beLoop input n off 0) % modulus := by
  induction n generalizing off acc with
  | zero => simp [powBytes, beLoop]
  | succ n ih =>
    simp only [powBytes, beLoop]
    have hE : beLoop input n (off + 1) (0 * 256 + (byteAt input off).toNat) =
        (byteAt input off).toNat * 256 ^ n + beLoop input n (off + 1) 0 := by
      rw [beLoop_acc, Nat.zero_mul, Nat.zero_add]
    rw [ih, hE]
    have hByte := powByte_spec modulus base (byteAt input off) 8 acc
    have hLow : (byteAt input off).toNat % 2 ^ 8 = (byteAt input off).toNat :=
      Nat.mod_eq_of_lt (UInt8.toNat_lt _)
    rw [hLow] at hByte
    have hPow := pow_congr modulus _ _ (256 ^ n) hByte
    rw [mul_congr modulus _ _ _ _ hPow rfl]
    have h256 : (2 : Nat) ^ 8 * 256 ^ n = 256 ^ (n + 1) := by
      have : (2 : Nat) ^ 8 = 256 := by decide
      rw [this, Nat.pow_succ, Nat.mul_comm]
    have hAlg : (acc ^ 2 ^ 8 * base ^ (byteAt input off).toNat) ^ 256 ^ n * base ^ beLoop input n (off + 1) 0 =
        acc ^ 256 ^ (n + 1) * base ^ ((byteAt input off).toNat * 256 ^ n + beLoop input n (off + 1) 0) := by
      rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, h256, Nat.mul_assoc, ← Nat.pow_add]
    rw [hAlg]

/-- Kind: functional correctness.
    Says: for a non-zero modulus, the loop started as the precompile starts it returns
    exactly `base ^ exponent % modulus`, with the exponent read big-endian from the
    `expLen` bytes at `off` (zero-padded beyond the input).
    Does not say: that operand decoding and pricing match the EIP (vectors). -/
theorem powBytes_eq_pow_mod (modulus base : Nat) (input : ByteArray) (expLen off : Nat)
    (hMod : 0 < modulus) :
    powBytes modulus base input expLen off (1 % modulus) =
      base ^ (beNat input off expLen) % modulus := by
  have hLt := powBytes_lt modulus base input expLen off (1 % modulus) hMod (Nat.mod_lt _ hMod)
  have hSpec := powBytes_spec modulus base input expLen off (1 % modulus)
  rw [Nat.mod_eq_of_lt hLt] at hSpec
  rw [hSpec, beNat]
  have hOne : (1 % modulus) ^ 256 ^ expLen % modulus = 1 ^ 256 ^ expLen % modulus :=
    pow_congr modulus _ _ _ (Nat.mod_mod _ _)
  rw [mul_congr modulus _ _ _ _ hOne rfl, Nat.one_pow, Nat.one_mul]

/-- Kind: functional correctness of the precompile body.
    Says: when the declared lengths are within the local bounds and the modulus is not
    zero, the output is the `modLen`-byte big-endian encoding of
    `base ^ exponent % modulus` for the three operands read from the input.
    Does not say: anything about the price or about refused inputs. -/
theorem body_eq_pow_mod (input : ByteArray)
    (hLen : (header input).modLen ≠ 0)
    (hBound : ¬ ((header input).expLen > maxExponentBytes ∨ (header input).baseLen > maxOperandBytes ∨
      (header input).modLen > maxOperandBytes))
    (hMod : beNat input (96 + (header input).baseLen + (header input).expLen) (header input).modLen ≠ 0) :
    ∃ out, body input = .output out ∧
      out = natToBE (header input).modLen
        (beNat input 96 (header input).baseLen ^ beNat input (96 + (header input).baseLen) (header input).expLen %
          beNat input (96 + (header input).baseLen + (header input).expLen) (header input).modLen) := by
  refine ⟨_, ?_, rfl⟩
  unfold body
  simp only [hLen, ↓reduceIte, hBound, hMod]
  rw [powBytes_eq_pow_mod _ _ _ _ _ (Nat.pos_of_ne_zero hMod), ← Nat.pow_mod]

#print axioms mod_mul_left
#print axioms pow_congr
#print axioms mul_congr
#print axioms powByte_spec
#print axioms beLoop_acc
#print axioms powBytes_spec
#print axioms powBytes_eq_pow_mod
#print axioms body_eq_pow_mod

end EVMCleanroom.Precompiles.ModExp
