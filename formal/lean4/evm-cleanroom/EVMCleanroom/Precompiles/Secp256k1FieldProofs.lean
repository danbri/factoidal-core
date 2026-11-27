import EVMCleanroom.Precompiles.LimbU256Proofs
import EVMCleanroom.Precompiles.Secp256k1Field
import EVMCleanroom.Precompiles.Secp256k1

/-!
# The secp256k1 base field on limbs computes the `Nat` field

`Secp256k1.Fe` keeps plain residues in four limbs and reduces a 512-bit
product by folding with `2^256 ≡ 2^32 + 977 (mod p)`. Proved here, against
`Fp.add`, `Fp.sub`, `Fp.mul` and `Fp.neg` of `Field.lean` at the modulus
`Secp256k1.p`:

* `reduce_spec`: the folding reduction returns the residue modulo `p` of any
  eight-limb value;
* `mul_spec`, `sqr_spec`: the limb product is `Fp.mul`, for all inputs (no
  canonical hypothesis), and the result is canonical;
* `add_spec`, `sub_spec`, `neg_spec`: on canonical values the limb operations
  are `Fp.add`, `Fp.sub`, `Fp.neg`, with canonical results;
* `toNat_ofNat`, `pNat_eq_p`, and `ops_refines`, which states the above for the
  dictionary `Fe.ops` against `Fp.ops Secp256k1.p`, with the zero and equality
  tests.

* `inv_spec`, `sqrtCandidate_spec`: the two fixed power chains return the
  residues of `a ^ (p − 2)` and `a ^ ((p + 1) / 4)`.

Not proved here: that `p` is prime, any field law, and so neither that
`a ^ (p − 2)` is an inverse nor that `a ^ ((p + 1) / 4)` is a square root
(`evm-fieldperf` compares `Fe.inv` with `Fp.inv` at run time, and `Fe.sqrt?`
checks the square).
Nothing is said about timing.
-/

namespace EVMCleanroom.Precompiles.Secp256k1.Fe

open Limb

private theorem zero_toNat : (0 : UInt64).toNat = 0 := rfl

private theorem C_toNat : C.toNat = 4294968273 := rfl

/-- Kind: constant.
    Says: the modulus of this module is the number `2^256 − 2^32 − 977`, written out.
    Does not say: that it is prime. -/
theorem pNat_eq :
    pNat = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  first | rfl | decide

/-- Kind: constant.
    Says: the limbs `P` are the modulus.
    Does not say: that it is prime. -/
theorem P_toNat : P.toNat = pNat := by
  first | rfl | decide

/-- Kind: constant.
    Says: the modulus of the limb field is the modulus `Secp256k1.p` of the `Nat` curve code.
    Does not say: that it is prime. -/
theorem pNat_eq_p : pNat = Secp256k1.p := rfl

/-- Kind: constant.
    Says: the modulus is not zero.
    Does not say: that it is prime. -/
theorem pNat_pos : 0 < pNat := by
  rw [pNat_eq]
  decide

/-- Kind: constant.
    Says: the modulus is below `2^256`, so a residue fits in four limbs.
    Does not say: that it is prime. -/
theorem pNat_lt : pNat < 2 ^ 256 := by
  have h := U256.toNat_lt P
  rw [P_toNat] at h
  exact h

/-- The high limb of `x · c + y + carry` is at most `c` when the carry is. -/
private theorem carry_le (hi lo x y c : Nat)
    (h : hi * 2 ^ 64 + lo = x * 4294968273 + y + c)
    (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (hc : c ≤ 4294968273) : hi ≤ 4294968273 := by
  limb_omega

/-- The second and third folds of `reduce` on natural numbers: the value `m + k · c` with
    `m < 2^256` and `k ≤ c` is folded to four limbs `b` and the carry `a31` of the second
    fold, and the third fold does not carry. -/
private theorem fold_tail
    {m0 m1 m2 m3 k n1 n0 a11 a12 a21 a22 a31 a32 b01 b02 b11 b12 b21 b22 b31 b32 : Nat}
    (hm0 : m0 < 2 ^ 64) (hm1 : m1 < 2 ^ 64) (hm2 : m2 < 2 ^ 64) (hm3 : m3 < 2 ^ 64)
    (hk : k ≤ 4294968273)
    (sn : n1 * 2 ^ 64 + n0 = k * 4294968273 + m0 + 0)
    (sa1 : a11 * 2 ^ 64 + a12 = m1 + n1 + 0)
    (sa2 : a21 * 2 ^ 64 + a22 = m2 + 0 + a11)
    (sa3 : a31 * 2 ^ 64 + a32 = m3 + 0 + a21)
    (sb0 : b01 * 2 ^ 64 + b02 = n0 + a31 * 4294968273 + 0)
    (sb1 : b11 * 2 ^ 64 + b12 = a12 + 0 + b01)
    (sb2 : b21 * 2 ^ 64 + b22 = a22 + 0 + b11)
    (sb3 : b31 * 2 ^ 64 + b32 = a32 + 0 + b21)
    (hn0 : n0 < 2 ^ 64) (ha12 : a12 < 2 ^ 64) (ha22 : a22 < 2 ^ 64) (ha32 : a32 < 2 ^ 64)
    (hb02 : b02 < 2 ^ 64) (hb12 : b12 < 2 ^ 64) (hb22 : b22 < 2 ^ 64) (hb32 : b32 < 2 ^ 64)
    (ka1 : a11 ≤ 1) (ka2 : a21 ≤ 1) (ka3 : a31 ≤ 1)
    (kb0 : b01 ≤ 1) (kb1 : b11 ≤ 1) (kb2 : b21 ≤ 1) (kb3 : b31 ≤ 1) :
    b02 + b12 * 2 ^ 64 + b22 * 2 ^ 128 + b32 * 2 ^ 192 + a31 * 2 ^ 256 =
      m0 + m1 * 2 ^ 64 + m2 * 2 ^ 128 + m3 * 2 ^ 192 + k * 4294968273 + a31 * 4294968273 := by
  have hn : n1 ≤ 4294968273 := by limb_omega
  have f1 : a11 = 0 ∨ a12 < 4294968273 := by limb_omega
  have f2 : a21 = 0 ∨ (a11 = 1 ∧ a22 = 0) := by limb_omega
  have f3 : a31 = 0 ∨ (a21 = 1 ∧ a32 = 0) := by limb_omega
  have g0 : a31 = 1 ∨ b01 = 0 := by limb_omega
  have g1 : b11 = 0 := by limb_omega
  have g2 : b21 = 0 := by limb_omega
  have g3 : b31 = 0 := by limb_omega
  limb_omega

/-- Kind: functional correctness (special reduction).
    Says: for every eight-limb value `t`, `reduce t` is the residue of `t` modulo `p`; in
    particular the three folds lose nothing and the last one does not carry.
    Does not say: that `p` is prime; anything about running time. -/
theorem reduce_spec (t : U512) : (reduce t).toNat = t.toNat % pNat := by
  have z := zero_toNat
  have hC := C_toNat
  simp only [reduce]
  have sm0 := mac_spec t.l4 C t.l0 0
  generalize mac t.l4 C t.l0 0 = m0 at sm0 ⊢
  have sm1 := mac_spec t.l5 C t.l1 m0.1
  generalize mac t.l5 C t.l1 m0.1 = m1 at sm1 ⊢
  have sm2 := mac_spec t.l6 C t.l2 m1.1
  generalize mac t.l6 C t.l2 m1.1 = m2 at sm2 ⊢
  have sm3 := mac_spec t.l7 C t.l3 m2.1
  generalize mac t.l7 C t.l3 m2.1 = m3 at sm3 ⊢
  have sn0 := mac_spec m3.1 C m0.2 0
  generalize mac m3.1 C m0.2 0 = n0 at sn0 ⊢
  have sa1 := adc_spec m1.2 n0.1 0
  have ka1 := adc_carry_le m1.2 n0.1 0 (by limb_omega)
  generalize adc m1.2 n0.1 0 = a1 at sa1 ka1 ⊢
  have sa2 := adc_spec m2.2 0 a1.1
  have ka2 := adc_carry_le m2.2 0 a1.1 ka1
  generalize adc m2.2 0 a1.1 = a2 at sa2 ka2 ⊢
  have sa3 := adc_spec m3.2 0 a2.1
  have ka3 := adc_carry_le m3.2 0 a2.1 ka2
  generalize adc m3.2 0 a2.1 = a3 at sa3 ka3 ⊢
  have hm : (a3.1 * C).toNat = a3.1.toNat * 4294968273 := by
    rw [UInt64.toNat_mul, hC]
    limb_omega
  have sb0 := adc_spec n0.2 (a3.1 * C) 0
  have kb0 := adc_carry_le n0.2 (a3.1 * C) 0 (by limb_omega)
  generalize adc n0.2 (a3.1 * C) 0 = b0 at sb0 kb0 ⊢
  have sb1 := adc_spec a1.2 0 b0.1
  have kb1 := adc_carry_le a1.2 0 b0.1 kb0
  generalize adc a1.2 0 b0.1 = b1 at sb1 kb1 ⊢
  have sb2 := adc_spec a2.2 0 b1.1
  have kb2 := adc_carry_le a2.2 0 b1.1 kb1
  generalize adc a2.2 0 b1.1 = b2 at sb2 kb2 ⊢
  have sb3 := adc_spec a3.2 0 b2.1
  have kb3 := adc_carry_le a3.2 0 b2.1 kb2
  generalize adc a3.2 0 b2.1 = b3 at sb3 kb3 ⊢
  simp only [hC, z, hm] at sm0 sm1 sm2 sm3 sn0 sa1 sa2 sa3 sb0 sb1 sb2 sb3
  have hk0 := carry_le _ _ _ _ _ sm0 (UInt64.toNat_lt _) (UInt64.toNat_lt _) (Nat.zero_le _)
  have hk1 := carry_le _ _ _ _ _ sm1 (UInt64.toNat_lt _) (UInt64.toNat_lt _) hk0
  have hk2 := carry_le _ _ _ _ _ sm2 (UInt64.toNat_lt _) (UInt64.toNat_lt _) hk1
  have hk3 := carry_le _ _ _ _ _ sm3 (UInt64.toNat_lt _) (UInt64.toNat_lt _) hk2
  have tail := fold_tail (UInt64.toNat_lt m0.2) (UInt64.toNat_lt m1.2) (UInt64.toNat_lt m2.2)
    (UInt64.toNat_lt m3.2) hk3 sn0 sa1 sa2 sa3 sb0 sb1 sb2 sb3
    (UInt64.toNat_lt n0.2) (UInt64.toNat_lt a1.2) (UInt64.toNat_lt a2.2) (UInt64.toNat_lt a3.2)
    (UInt64.toNat_lt b0.2) (UInt64.toNat_lt b1.2) (UInt64.toNat_lt b2.2) (UInt64.toNat_lt b3.2)
    ka1 ka2 ka3 kb0 kb1 kb2 kb3
  have hp := pNat_eq
  have key : t.toNat = U256.toNat ⟨b0.2, b1.2, b2.2, b3.2⟩ +
      (t.l4.toNat + t.l5.toNat * 2 ^ 64 + t.l6.toNat * 2 ^ 128 + t.l7.toNat * 2 ^ 192 +
        m3.1.toNat + a3.1.toNat) * pNat := by
    clear sn0 sa1 sa2 sa3 sb0 sb1 sb2 sb3 hk0 hk1 hk2 hk3 ka1 ka2 ka3 kb0 kb1 kb2 kb3 hm
    rw [hp]
    simp only [U512.toNat, U256.toNat]
    limb_omega
  have hlt := U256.toNat_lt ⟨b0.2, b1.2, b2.2, b3.2⟩
  have hcs := (U256.condSub_spec P 0 ⟨b0.2, b1.2, b2.2, b3.2⟩ (by
    rw [z, P_toNat, hp]
    clear sm0 sm1 sm2 sm3 sn0 sa1 sa2 sa3 sb0 sb1 sb2 sb3 tail key
    limb_omega)).1
  rw [z, Nat.zero_mul, Nat.zero_add, P_toNat] at hcs
  rw [hcs, key, Nat.add_mul_mod_self_right]

/-- Kind: refinement (field multiplication).
    Says: for all four-limb inputs, canonical or not, `Fe.mul` is `Fp.mul` at the modulus `p`
    on the numbers of its arguments.
    Does not say: that `p` is prime; anything about running time. -/
theorem mul_spec (a b : U256) : (mul a b).toNat = Fp.mul pNat a.toNat b.toNat := by
  show (reduce (U256.mulWide a b)).toNat = a.toNat * b.toNat % pNat
  rw [reduce_spec, U256.mulWide_spec]

/-- Kind: canonical representation.
    Says: a limb product is below the modulus, for all inputs.
    Does not say: anything about the inputs. -/
theorem mul_lt (a b : U256) : (mul a b).toNat < pNat := by
  rw [mul_spec]
  exact Fp.mul_lt _ _ _ pNat_pos

/-- Kind: refinement (field squaring).
    Says: for every four-limb input `Fe.sqr a` is `Fp.mul` of the number with itself.
    Does not say: that `p` is prime. -/
theorem sqr_spec (a : U256) : (sqr a).toNat = Fp.mul pNat a.toNat a.toNat := by
  show (reduce (U256.mulWide a a)).toNat = a.toNat * a.toNat % pNat
  rw [reduce_spec, U256.mulWide_spec]

/-- Kind: canonical representation.
    Says: a limb square is below the modulus, for all inputs.
    Does not say: anything about the input. -/
theorem sqr_lt (a : U256) : (sqr a).toNat < pNat := by
  rw [sqr_spec]
  exact Fp.mul_lt _ _ _ pNat_pos

/-- Kind: refinement (field addition).
    Says: on values below `p`, `Fe.add` is `Fp.add`, and the result is below `p`.
    Does not say: anything for a non-canonical argument. -/
theorem add_spec (a b : U256) (ha : a.toNat < pNat) (hb : b.toNat < pNat) :
    (add a b).toNat = Fp.add pNat a.toNat b.toNat ∧ (add a b).toNat < pNat := by
  have h := U256.addMod_spec P a b (by rw [P_toNat]; exact ha) (by rw [P_toNat]; exact hb)
  rw [P_toNat] at h
  have h' : (add a b).toNat = Fp.add pNat a.toNat b.toNat := h
  refine ⟨h', ?_⟩
  rw [h']
  exact Fp.add_lt _ _ _ ha hb

/-- Kind: refinement (field subtraction).
    Says: on values below `p`, `Fe.sub` is `Fp.sub`, and the result is below `p`.
    Does not say: anything for a non-canonical argument. -/
theorem sub_spec (a b : U256) (ha : a.toNat < pNat) (hb : b.toNat < pNat) :
    (sub a b).toNat = Fp.sub pNat a.toNat b.toNat ∧ (sub a b).toNat < pNat := by
  have h := U256.subMod_spec P a b (by rw [P_toNat]; exact ha) (by rw [P_toNat]; exact hb)
  rw [P_toNat] at h
  have h' : (sub a b).toNat = Fp.sub pNat a.toNat b.toNat := h
  refine ⟨h', ?_⟩
  rw [h']
  exact Fp.sub_lt _ _ _ ha hb

/-- Kind: refinement (field negation).
    Says: on a value below `p`, `Fe.neg` is `Fp.neg`, and the result is below `p`.
    Does not say: anything for a non-canonical argument. -/
theorem neg_spec (a : U256) (ha : a.toNat < pNat) :
    (neg a).toNat = Fp.neg pNat a.toNat ∧ (neg a).toNat < pNat := by
  have h := U256.negMod_spec P a (by rw [P_toNat]; exact ha)
  rw [P_toNat] at h
  have h' : (neg a).toNat = Fp.neg pNat a.toNat := h
  refine ⟨h', ?_⟩
  rw [h']
  exact Fp.neg_lt _ _ ha

/-- Kind: functional correctness (conversion).
    Says: the limbs made from a natural number are its residue modulo `p`.
    Does not say: anything about `U256.ofNat`, which does not reduce. -/
theorem toNat_ofNat (x : Nat) : (ofNat x).toNat = x % pNat := by
  show (U256.ofNat (x % pNat)).toNat = x % pNat
  rw [U256.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ pNat_pos) pNat_lt)

/-- Kind: constant.
    Says: the zero limbs are the number zero.
    Does not say: anything else. -/
theorem zero_spec : U256.zero.toNat = 0 := by
  first | rfl | decide

/-- Kind: constant.
    Says: the limbs `one` are the number one, which is `1 % p`.
    Does not say: anything else. -/
theorem one_spec : one.toNat = 1 % pNat := by
  first | rfl | decide

private theorem bool_eq_of_iff {x y : Bool} (h : x = true ↔ y = true) : x = y := by
  cases x with
  | true => exact (h.1 rfl).symm
  | false =>
    cases y with
    | false => rfl
    | true => exact h.2 rfl

/-- Kind: refinement (the whole dictionary except the inverse).
    Says: on values below `Secp256k1.p`, each of `add`, `sub`, `mul`, `sqr`, `neg`, `isZero`,
    `eq`, `zero` and `one` of the limb dictionary `Fe.ops` gives, read through `toNat`, what the
    same operation of the `Nat` dictionary `Fp.ops Secp256k1.p` gives on the numbers; and the
    results of the five arithmetic operations are again below `Secp256k1.p`.
    Does not say: anything about `inv` (a fixed power chain, compared with `Fp.inv` only by the
    run-time differential check); that `Secp256k1.p` is prime; any field law. -/
theorem ops_refines (a b : U256) (ha : a.toNat < Secp256k1.p) (hb : b.toNat < Secp256k1.p) :
    ((@FieldOps.add U256 ops a b).toNat = @FieldOps.add Nat (Fp.ops Secp256k1.p) a.toNat b.toNat ∧
      (@FieldOps.add U256 ops a b).toNat < Secp256k1.p) ∧
    ((@FieldOps.sub U256 ops a b).toNat = @FieldOps.sub Nat (Fp.ops Secp256k1.p) a.toNat b.toNat ∧
      (@FieldOps.sub U256 ops a b).toNat < Secp256k1.p) ∧
    ((@FieldOps.mul U256 ops a b).toNat = @FieldOps.mul Nat (Fp.ops Secp256k1.p) a.toNat b.toNat ∧
      (@FieldOps.mul U256 ops a b).toNat < Secp256k1.p) ∧
    ((@FieldOps.sqr U256 ops a).toNat = @FieldOps.sqr Nat (Fp.ops Secp256k1.p) a.toNat ∧
      (@FieldOps.sqr U256 ops a).toNat < Secp256k1.p) ∧
    ((@FieldOps.neg U256 ops a).toNat = @FieldOps.neg Nat (Fp.ops Secp256k1.p) a.toNat ∧
      (@FieldOps.neg U256 ops a).toNat < Secp256k1.p) ∧
    @FieldOps.isZero U256 ops a = @FieldOps.isZero Nat (Fp.ops Secp256k1.p) a.toNat ∧
    @FieldOps.eq U256 ops a b = @FieldOps.eq Nat (Fp.ops Secp256k1.p) a.toNat b.toNat ∧
    (@FieldOps.zero U256 ops).toNat = @FieldOps.zero Nat (Fp.ops Secp256k1.p) ∧
    (@FieldOps.one U256 ops).toNat = @FieldOps.one Nat (Fp.ops Secp256k1.p) :=
  ⟨add_spec a b ha hb, sub_spec a b ha hb, ⟨mul_spec a b, mul_lt a b⟩, ⟨sqr_spec a, sqr_lt a⟩,
    neg_spec a ha,
    bool_eq_of_iff ((U256.isZero_iff a).trans (beq_iff_eq (a := a.toNat) (b := 0)).symm),
    bool_eq_of_iff ((U256.beq_iff a b).trans (beq_iff_eq (a := a.toNat) (b := b.toNat)).symm),
    zero_spec, one_spec⟩

/-! ### The fixed power chains

`Fe.inv` and `Fe.sqrtCandidate` are addition chains built from `mul`, `sqr` and `sqrN`. Each
step multiplies residues, so the exponents add; the theorems below follow the chain and
compare the final exponent with `p − 2` and `(p + 1) / 4` by evaluation. -/

/-- `x` is the `e`-th power of `A` modulo `p` (the limbs need not be canonical). -/
private def Pow (A : Nat) (x : U256) (e : Nat) : Prop := x.toNat % pNat = A ^ e % pNat

private theorem pow_cast {A : Nat} {x : U256} {e f : Nat} (h : Pow A x e) (he : e = f) :
    Pow A x f := he ▸ h

private theorem pow_self (a : U256) : Pow a.toNat a 1 := by
  unfold Pow
  rw [Nat.pow_one]

private theorem pow_mul_val {A : Nat} {x y : U256} {e f : Nat} (hx : Pow A x e) (hy : Pow A y f) :
    (mul x y).toNat = A ^ (e + f) % pNat := by
  unfold Pow at hx hy
  rw [mul_spec]
  show x.toNat * y.toNat % pNat = A ^ (e + f) % pNat
  rw [Nat.mul_mod, hx, hy, ← Nat.mul_mod, ← Nat.pow_add]

private theorem pow_mul {A : Nat} {x y : U256} {e f : Nat} (hx : Pow A x e) (hy : Pow A y f) :
    Pow A (mul x y) (e + f) := by
  unfold Pow
  rw [pow_mul_val hx hy, Nat.mod_mod]

private theorem pow_sqr {A : Nat} {x : U256} {e : Nat} (hx : Pow A x e) :
    Pow A (sqr x) (e + e) := pow_mul hx hx

private theorem double_exp (e k : Nat) : (e + e) * 2 ^ k = e * 2 ^ (k + 1) :=
  calc (e + e) * 2 ^ k = e * 2 ^ k + e * 2 ^ k := Nat.add_mul e e (2 ^ k)
    _ = e * 2 ^ k * 2 := (Nat.mul_two _).symm
    _ = e * (2 ^ k * 2) := Nat.mul_assoc e (2 ^ k) 2
    _ = e * 2 ^ (k + 1) := by rw [Nat.pow_succ]

private theorem sqrN_zero (x : U256) : sqrN x 0 = x := rfl

-- With `sqr` opaque the two sides are compared by unfolding `sqrN` only; otherwise the
-- comparison first tries `x` against `sqr x` and unfolds the whole reduction.
attribute [local irreducible] sqr in
private theorem sqrN_succ (x : U256) (k : Nat) : sqrN x (k + 1) = sqrN (sqr x) k := rfl

/-- At least one squaring leaves a canonical value. -/
private theorem sqrN_lt (k : Nat) : ∀ (x : U256), (sqrN x (k + 1)).toNat < pNat := by
  induction k with
  | zero =>
    intro x
    rw [sqrN_succ, sqrN_zero]
    exact sqr_lt x
  | succ k ih =>
    intro x
    rw [sqrN_succ]
    exact ih (sqr x)

private theorem pow_sqrN {A : Nat} (k : Nat) :
    ∀ (x : U256) (e : Nat), Pow A x e → Pow A (sqrN x k) (e * 2 ^ k) := by
  induction k with
  | zero =>
    intro x e h
    rw [Nat.pow_zero, Nat.mul_one, sqrN_zero]
    exact h
  | succ k ih =>
    intro x e h
    have h2 := ih (sqr x) (e + e) (pow_sqr h)
    rw [double_exp] at h2
    rw [sqrN_succ]
    exact h2

private theorem chain_pow (a : U256) :
    Pow a.toNat (chain a).1 (2 ^ 223 - 1) ∧ Pow a.toNat (chain a).2.1 (2 ^ 22 - 1) ∧
      Pow a.toNat (chain a).2.2 3 := by
  have h1 := pow_self a
  simp only [chain]
  have hx2 : Pow a.toNat (mul (sqr a) a) 3 :=
    pow_cast (pow_mul (pow_sqr h1) h1) (by first | rfl | decide)
  generalize mul (sqr a) a = x2 at hx2 ⊢
  have hx3 : Pow a.toNat (mul (sqr x2) a) 7 :=
    pow_cast (pow_mul (pow_sqr hx2) h1) (by first | rfl | decide)
  generalize mul (sqr x2) a = x3 at hx3 ⊢
  have hx6 : Pow a.toNat (mul (sqrN x3 3) x3) (2 ^ 6 - 1) :=
    pow_cast (pow_mul (pow_sqrN 3 _ _ hx3) hx3) (by first | rfl | decide)
  generalize mul (sqrN x3 3) x3 = x6 at hx6 ⊢
  have hx9 : Pow a.toNat (mul (sqrN x6 3) x3) (2 ^ 9 - 1) :=
    pow_cast (pow_mul (pow_sqrN 3 _ _ hx6) hx3) (by first | rfl | decide)
  generalize mul (sqrN x6 3) x3 = x9 at hx9 ⊢
  have hx11 : Pow a.toNat (mul (sqrN x9 2) x2) (2 ^ 11 - 1) :=
    pow_cast (pow_mul (pow_sqrN 2 _ _ hx9) hx2) (by first | rfl | decide)
  generalize mul (sqrN x9 2) x2 = x11 at hx11 ⊢
  have hx22 : Pow a.toNat (mul (sqrN x11 11) x11) (2 ^ 22 - 1) :=
    pow_cast (pow_mul (pow_sqrN 11 _ _ hx11) hx11) (by first | rfl | decide)
  generalize mul (sqrN x11 11) x11 = x22 at hx22 ⊢
  have hx44 : Pow a.toNat (mul (sqrN x22 22) x22) (2 ^ 44 - 1) :=
    pow_cast (pow_mul (pow_sqrN 22 _ _ hx22) hx22) (by first | rfl | decide)
  generalize mul (sqrN x22 22) x22 = x44 at hx44 ⊢
  have hx88 : Pow a.toNat (mul (sqrN x44 44) x44) (2 ^ 88 - 1) :=
    pow_cast (pow_mul (pow_sqrN 44 _ _ hx44) hx44) (by first | rfl | decide)
  generalize mul (sqrN x44 44) x44 = x88 at hx88 ⊢
  have hx176 : Pow a.toNat (mul (sqrN x88 88) x88) (2 ^ 176 - 1) :=
    pow_cast (pow_mul (pow_sqrN 88 _ _ hx88) hx88) (by first | rfl | decide)
  generalize mul (sqrN x88 88) x88 = x176 at hx176 ⊢
  have hx220 : Pow a.toNat (mul (sqrN x176 44) x44) (2 ^ 220 - 1) :=
    pow_cast (pow_mul (pow_sqrN 44 _ _ hx176) hx44) (by first | rfl | decide)
  generalize mul (sqrN x176 44) x44 = x220 at hx220 ⊢
  have hx223 : Pow a.toNat (mul (sqrN x220 3) x3) (2 ^ 223 - 1) :=
    pow_cast (pow_mul (pow_sqrN 3 _ _ hx220) hx3) (by first | rfl | decide)
  generalize mul (sqrN x220 3) x3 = x223 at hx223 ⊢
  exact ⟨hx223, hx22, hx2⟩

/-- Kind: functional correctness (inverse as a power).
    Says: for every four-limb input, canonical or not, `Fe.inv a` is the residue of
    `a ^ (p − 2)` modulo `p`.
    Does not say: that this is an inverse (that needs `p` prime and Fermat's little theorem,
    neither of which is proved in this package); anything about running time. -/
theorem inv_spec (a : U256) : (inv a).toNat = a.toNat ^ (pNat - 2) % pNat := by
  obtain ⟨h223, h22, h2⟩ := chain_pow a
  have h1 := pow_self a
  unfold inv
  generalize chain a = c at h223 h22 h2 ⊢
  obtain ⟨x223, x22, x2⟩ := c
  have h223' : Pow a.toNat x223 (2 ^ 223 - 1) := h223
  have h22' : Pow a.toNat x22 (2 ^ 22 - 1) := h22
  have h2' : Pow a.toNat x2 3 := h2
  show (mul (sqrN (mul (sqrN (mul (sqrN (mul (sqrN x223 23) x22) 5) a) 3) x2) 2) a).toNat = _
  have t1 := pow_mul (pow_sqrN 23 _ _ h223') h22'
  have t2 := pow_mul (pow_sqrN 5 _ _ t1) h1
  have t3 := pow_mul (pow_sqrN 3 _ _ t2) h2'
  rw [pow_mul_val (pow_sqrN 2 _ _ t3) h1]
  have he : ((((2 ^ 223 - 1) * 2 ^ 23 + (2 ^ 22 - 1)) * 2 ^ 5 + 1) * 2 ^ 3 + 3) * 2 ^ 2 + 1 =
      pNat - 2 := by first | rfl | decide
  rw [he]

/-- Kind: functional correctness (square-root candidate as a power).
    Says: for every four-limb input, canonical or not, `Fe.sqrtCandidate a` is the residue of
    `a ^ ((p + 1) / 4)` modulo `p`.
    Does not say: that this is a square root (`Fe.sqrt?` checks the square at run time);
    that `p` is prime. -/
theorem sqrtCandidate_spec (a : U256) :
    (sqrtCandidate a).toNat = a.toNat ^ ((pNat + 1) / 4) % pNat := by
  obtain ⟨h223, h22, h2⟩ := chain_pow a
  unfold sqrtCandidate
  generalize chain a = c at h223 h22 h2 ⊢
  obtain ⟨x223, x22, x2⟩ := c
  have h223' : Pow a.toNat x223 (2 ^ 223 - 1) := h223
  have h22' : Pow a.toNat x22 (2 ^ 22 - 1) := h22
  have h2' : Pow a.toNat x2 3 := h2
  show (sqrN (mul (sqrN (mul (sqrN x223 23) x22) 6) x2) 2).toNat = _
  have t1 := pow_mul (pow_sqrN 23 _ _ h223') h22'
  have t2 := pow_mul (pow_sqrN 6 _ _ t1) h2'
  have t3 := pow_sqrN 2 _ _ t2
  have hlt : (sqrN (mul (sqrN (mul (sqrN x223 23) x22) 6) x2) 2).toNat < pNat := sqrN_lt 1 _
  unfold Pow at t3
  rw [Nat.mod_eq_of_lt hlt] at t3
  rw [t3]
  have he : (((2 ^ 223 - 1) * 2 ^ 23 + (2 ^ 22 - 1)) * 2 ^ 6 + 3) * 2 ^ 2 = (pNat + 1) / 4 := by
    first | rfl | decide
  rw [he]

#print axioms pNat_eq
#print axioms P_toNat
#print axioms pNat_eq_p
#print axioms pNat_pos
#print axioms pNat_lt
#print axioms reduce_spec
#print axioms mul_spec
#print axioms mul_lt
#print axioms sqr_spec
#print axioms sqr_lt
#print axioms add_spec
#print axioms sub_spec
#print axioms neg_spec
#print axioms toNat_ofNat
#print axioms zero_spec
#print axioms one_spec
#print axioms ops_refines
#print axioms inv_spec
#print axioms sqrtCandidate_spec

end EVMCleanroom.Precompiles.Secp256k1.Fe
