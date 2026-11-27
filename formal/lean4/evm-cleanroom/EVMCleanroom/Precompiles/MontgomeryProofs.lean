import EVMCleanroom.Precompiles.MontgomeryRedcProofs
import EVMCleanroom.Precompiles.Montgomery

/-!
# Montgomery arithmetic on four and six limbs refines the `Nat` field operations

For a parameter set `M` (`Mont256` or `Mont384`) that is `Valid` (odd modulus
above 1, the `n0inv` property, `one = R mod N`, `r2 = R² mod N`), every field
operation on stored limbs is proved against the `Nat` definitions of
`Field.lean`, read through `M.toNat` (which leaves Montgomery form):

* `mul`, `sqr` against `Fp.mul`; `add`, `sub`, `neg` against `Fp.add`, `Fp.sub`, `Fp.neg`;
* `ofNat x` has value `x mod N`; the stored one has value `1 mod N`; zero has value 0;
* `inv` has value `Fp.inv` of the value (it is defined through `Fp.inv`);
* results are canonical (limbs below the modulus); `toNat` is always below the modulus;
* `isZero` and `beq` on canonical limbs decide zero and equality of values.

`FieldRefines` packages these as one statement about the dictionary `M.ops`
against `Fp.ops N`.

Proved for all inputs satisfying the stated hypotheses. Not proved (here or
anywhere in the package): that a modulus is prime, that `Fp.inv` is an inverse,
field laws beyond what the refinement transports. `pow` is not covered. Nothing
is said about timing; these routines branch on data.
-/

set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

namespace EVMCleanroom.Precompiles

private theorem zero_toNat'' : (0 : UInt64).toNat = 0 := rfl

/-- A dictionary `O` on a representation `F` refines the `Nat` field operations modulo `p` on the
    elements satisfying `C`, read through `v`: each operation keeps `C` and commutes with `v`;
    the zero and equality tests agree with `v`. (`Fp.ops p` tests are `· == 0` and `· == ·`.) -/
structure FieldRefines {F : Type} (O : FieldOps F) (p : Nat) (C : F → Prop) (v : F → Nat) : Prop where
  zero : C O.zero ∧ v O.zero = (Fp.ops p).zero
  one : C O.one ∧ v O.one = (Fp.ops p).one
  add : ∀ a b, C a → C b → C (O.add a b) ∧ v (O.add a b) = (Fp.ops p).add (v a) (v b)
  sub : ∀ a b, C a → C b → C (O.sub a b) ∧ v (O.sub a b) = (Fp.ops p).sub (v a) (v b)
  mul : ∀ a b, C a → C b → C (O.mul a b) ∧ v (O.mul a b) = (Fp.ops p).mul (v a) (v b)
  sqr : ∀ a, C a → C (O.sqr a) ∧ v (O.sqr a) = (Fp.ops p).sqr (v a)
  neg : ∀ a, C a → C (O.neg a) ∧ v (O.neg a) = (Fp.ops p).neg (v a)
  inv : ∀ a, C a → C (O.inv a) ∧ v (O.inv a) = (Fp.ops p).inv (v a)
  isZero : ∀ a, C a → (O.isZero a = true ↔ v a = 0)
  eq : ∀ a b, C a → C b → (O.eq a b = true ↔ v a = v b)
  lt : ∀ a, v a < p

variable [LimbB.MacOK]

/-! ### 4 limbs -/

private theorem zsum4 (z : Nat) (hz : z = 0) : z + z * 2 ^ 64 + z * 2 ^ 128 + z * 2 ^ 192 = 0 := by omega

private theorem wsum4 (s z : Nat) (hz : z = 0) : s + z * 2 ^ 256 + z * 2 ^ 320 + z * 2 ^ 384 + z * 2 ^ 448 = s := by omega

/-- Kind: representation.
    Says: widening a 4-limb value to 8 limbs keeps the number.
    Does not say: anything about a modulus. -/
theorem U256.widen_toNat (a : U256) : a.widen.toNat = a.toNat := by
  show a.l0.toNat + a.l1.toNat * 2 ^ 64 + a.l2.toNat * 2 ^ 128 + a.l3.toNat * 2 ^ 192 + (0 : UInt64).toNat * 2 ^ 256 + (0 : UInt64).toNat * 2 ^ 320 + (0 : UInt64).toNat * 2 ^ 384 + (0 : UInt64).toNat * 2 ^ 448 = a.l0.toNat + a.l1.toNat * 2 ^ 64 + a.l2.toNat * 2 ^ 128 + a.l3.toNat * 2 ^ 192
  exact wsum4 _ _ zero_toNat''

/-- Kind: representation.
    Says: the 4-limb zero is the number zero.
    Does not say: anything about a modulus. -/
theorem U256.toNat_zero : U256.zero.toNat = 0 := by
  show (0 : UInt64).toNat + (0 : UInt64).toNat * 2 ^ 64 + (0 : UInt64).toNat * 2 ^ 128 + (0 : UInt64).toNat * 2 ^ 192 = 0
  exact zsum4 _ zero_toNat''

namespace Mont256

/-- What the Montgomery routines need of a parameter set: an odd modulus above 1, the `n0inv`
    property `n0inv · N ≡ −1 (mod 2^64)`, `one = R mod N` and `r2 = R² mod N`, with `R = 2^256`.
    All five are closed statements for a literal parameter set, checked by `decide`. -/
structure Valid (M : Mont256) : Prop where
  odd : M.n.toNat % 2 = 1
  one_lt : 1 < M.n.toNat
  n0inv_spec : (M.n0inv.toNat * (M.n.toNat % 2 ^ 64) + 1) % 2 ^ 64 = 0
  one_spec : M.one.toNat = 2 ^ 256 % M.n.toNat
  r2_spec : M.r2.toNat = 2 ^ 256 * 2 ^ 256 % M.n.toNat

variable {M : Mont256}

/-- Kind: existence.
    Says: for a valid parameter set the radix `2^256` has an inverse modulo the modulus.
    Does not say: what it is (the curve modules give it as a literal), or that the modulus is prime. -/
theorem exists_Rinv (hV : M.Valid) : ∃ Rinv, 2 ^ 256 * Rinv % M.n.toNat = 1 :=
  MontMath.exists_Rinv256 M.n0inv.toNat M.n.toNat hV.one_lt hV.n0inv_spec

/-- Kind: bound.
    Says: the modulus of a valid parameter set is positive.
    Does not say: anything else. -/
theorem pos (hV : M.Valid) : 0 < M.n.toNat := Nat.lt_trans Nat.zero_lt_one hV.one_lt

/-- Kind: refinement (leaving Montgomery form).
    Says: for a valid parameter set and any inverse `Rinv` of the radix, `toNat a` is below the
    modulus and is the value `a · Rinv mod N` of the stored limbs, for every `a` (canonical or not).
    Does not say: that the modulus is prime, or anything about timing. -/
theorem toNat_eq_value (hV : M.Valid) {Rinv : Nat} (hR : 2 ^ 256 * Rinv % M.n.toNat = 1) (a : U256) :
    M.toNat a < M.n.toNat ∧ M.toNat a = MontMath.value M.n.toNat Rinv a.toNat := by
  have hN := pos hV
  have ht : a.widen.toNat < M.n.toNat * 2 ^ 256 := by
    rw [U256.widen_toNat]
    exact MontMath.lt_mul_radix (U256.toNat_lt a) hN
  obtain ⟨h1, h2⟩ := U256.redc_spec M.n M.n0inv a.widen hV.n0inv_spec ht
  rw [U256.widen_toNat] at h2
  exact ⟨h1, MontMath.eq_value_of_mul_R hN hR h1 h2⟩

/-- Kind: canonical representation.
    Says: `toNat` of any limbs is below the modulus.
    Does not say: anything else. -/
theorem toNat_lt (hV : M.Valid) (a : U256) : M.toNat a < M.n.toNat := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  exact (toNat_eq_value hV hR a).1

/-- Kind: refinement (multiplication).
    Says: for a valid parameter set and a canonical first factor, the Montgomery product is
    canonical and its value is `Fp.mul` of the values.
    Does not say: anything when the first factor is not below the modulus; nothing about timing. -/
theorem mul_spec (hV : M.Valid) (a b : U256) (ha : a.toNat < M.n.toNat) :
    (M.mul a b).toNat < M.n.toNat ∧
      M.toNat (M.mul a b) = Fp.mul M.n.toNat (M.toNat a) (M.toNat b) := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  have hN := pos hV
  have ht : (U256.mulWide a b).toNat < M.n.toNat * 2 ^ 256 := by
    rw [U256.mulWide_spec]
    exact MontMath.mul_lt_mul_radix ha (U256.toNat_lt b)
  obtain ⟨h1, h2⟩ := U256.redc_spec M.n M.n0inv (U256.mulWide a b) hV.n0inv_spec ht
  rw [U256.mulWide_spec] at h2
  have hv := MontMath.value_mul hN hR h2
  refine ⟨h1, ?_⟩
  rw [(toNat_eq_value hV hR (M.mul a b)).2, (toNat_eq_value hV hR a).2, (toNat_eq_value hV hR b).2]
  exact hv

/-- Kind: refinement (squaring).
    Says: the Montgomery square of a canonical value is canonical and its value is `Fp.mul` of the value with itself.
    Does not say: anything for a non-canonical argument. -/
theorem sqr_spec (hV : M.Valid) (a : U256) (ha : a.toNat < M.n.toNat) :
    (M.sqr a).toNat < M.n.toNat ∧
      M.toNat (M.sqr a) = Fp.mul M.n.toNat (M.toNat a) (M.toNat a) :=
  mul_spec hV a a ha

/-- Kind: refinement (addition).
    Says: the sum of two canonical stored values is canonical and its value is `Fp.add` of the values.
    Does not say: anything for non-canonical arguments. -/
theorem add_spec (hV : M.Valid) (a b : U256) (ha : a.toNat < M.n.toNat) (hb : b.toNat < M.n.toNat) :
    (M.add a b).toNat < M.n.toNat ∧
      M.toNat (M.add a b) = Fp.add M.n.toNat (M.toNat a) (M.toNat b) := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  have hN := pos hV
  have e : (M.add a b).toNat = Fp.add M.n.toNat a.toNat b.toNat := U256.addMod_spec M.n a b ha hb
  refine ⟨by rw [e]; exact Fp.add_lt _ _ _ ha hb, ?_⟩
  rw [(toNat_eq_value hV hR (M.add a b)).2, (toNat_eq_value hV hR a).2, (toNat_eq_value hV hR b).2, e]
  exact MontMath.value_add hN Rinv ha hb

/-- Kind: refinement (subtraction).
    Says: the difference of two canonical stored values is canonical and its value is `Fp.sub` of the values.
    Does not say: anything for non-canonical arguments. -/
theorem sub_spec (hV : M.Valid) (a b : U256) (ha : a.toNat < M.n.toNat) (hb : b.toNat < M.n.toNat) :
    (M.sub a b).toNat < M.n.toNat ∧
      M.toNat (M.sub a b) = Fp.sub M.n.toNat (M.toNat a) (M.toNat b) := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  have hN := pos hV
  have e : (M.sub a b).toNat = Fp.sub M.n.toNat a.toNat b.toNat := U256.subMod_spec M.n a b ha hb
  refine ⟨by rw [e]; exact Fp.sub_lt _ _ _ ha hb, ?_⟩
  rw [(toNat_eq_value hV hR (M.sub a b)).2, (toNat_eq_value hV hR a).2, (toNat_eq_value hV hR b).2, e]
  exact MontMath.value_sub hN Rinv ha hb

/-- Kind: refinement (negation).
    Says: the negation of a canonical stored value is canonical and its value is `Fp.neg` of the value.
    Does not say: anything for a non-canonical argument. -/
theorem neg_spec (hV : M.Valid) (a : U256) (ha : a.toNat < M.n.toNat) :
    (M.neg a).toNat < M.n.toNat ∧ M.toNat (M.neg a) = Fp.neg M.n.toNat (M.toNat a) := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  have hN := pos hV
  have e : (M.neg a).toNat = Fp.neg M.n.toNat a.toNat := U256.negMod_spec M.n a ha
  refine ⟨by rw [e]; exact Fp.neg_lt _ _ ha, ?_⟩
  rw [(toNat_eq_value hV hR (M.neg a)).2, (toNat_eq_value hV hR a).2, e]
  exact MontMath.value_neg hN hR ha

/-- Kind: refinement (entering Montgomery form).
    Says: `ofNat x` is canonical and its value is `x mod N`, for every natural number `x`.
    Does not say: anything about timing. -/
theorem ofNat_spec (hV : M.Valid) (x : Nat) :
    (M.ofNat x).toNat < M.n.toNat ∧ M.toNat (M.ofNat x) = x % M.n.toNat := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  have hN := pos hV
  have hx : x % M.n.toNat < M.n.toNat := Nat.mod_lt _ hN
  have hu : (U256.ofNat (x % M.n.toNat)).toNat = x % M.n.toNat := by
    rw [U256.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans hx (U256.toNat_lt M.n))
  have ht : (U256.mulWide (U256.ofNat (x % M.n.toNat)) M.r2).toNat < M.n.toNat * 2 ^ 256 := by
    rw [U256.mulWide_spec, hu]
    exact MontMath.mul_lt_mul_radix hx (U256.toNat_lt M.r2)
  obtain ⟨h1, h2⟩ := U256.redc_spec M.n M.n0inv (U256.mulWide (U256.ofNat (x % M.n.toNat)) M.r2)
    hV.n0inv_spec ht
  rw [U256.mulWide_spec, hu, hV.r2_spec] at h2
  have h3 : x % M.n.toNat * (2 ^ 256 * 2 ^ 256 % M.n.toNat) % M.n.toNat =
      x % M.n.toNat * 2 ^ 256 * 2 ^ 256 % M.n.toNat := by
    rw [Nat.mul_assoc (x % M.n.toNat) (2 ^ 256) (2 ^ 256)]
    exact MontMath.mul_congr rfl (Nat.mod_mod _ _)
  have h4 := MontMath.cancel_R hN hR (h2.trans h3)
  rw [Nat.mod_eq_of_lt h1] at h4
  refine ⟨h1, ?_⟩
  show M.toNat (U256.redc M.n M.n0inv (U256.mulWide (U256.ofNat (x % M.n.toNat)) M.r2)) = x % M.n.toNat
  rw [(toNat_eq_value hV hR _).2, h4, MontMath.value_toMont hN hR, Nat.mod_mod]

/-- Kind: refinement (one).
    Says: the stored one is canonical and its value is `1 mod N` (which is 1, the modulus being above 1).
    Does not say: anything else. -/
theorem one_spec (hV : M.Valid) : M.one.toNat < M.n.toNat ∧ M.toNat M.one = 1 % M.n.toNat := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  have hN := pos hV
  have h := MontMath.value_toMont hN hR 1
  rw [Nat.one_mul] at h
  refine ⟨by rw [hV.one_spec]; exact Nat.mod_lt _ hN, ?_⟩
  rw [(toNat_eq_value hV hR M.one).2, hV.one_spec]
  exact h

/-- Kind: refinement (zero).
    Says: the stored zero is canonical and its value is zero.
    Does not say: anything else. -/
theorem zero_spec (hV : M.Valid) : U256.zero.toNat < M.n.toNat ∧ M.toNat U256.zero = 0 := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  have hN := pos hV
  refine ⟨by rw [U256.toNat_zero]; exact hN, ?_⟩
  rw [(toNat_eq_value hV hR U256.zero).2, U256.toNat_zero]
  exact MontMath.value_zero _ _

/-- Kind: refinement (inverse routine).
    Says: `inv a` is canonical and its value is `Fp.inv` of the value of `a`.
    Does not say: that `Fp.inv` is an inverse (not proved anywhere; callers and guards check `a · inv a = 1`). -/
theorem inv_spec (hV : M.Valid) (a : U256) :
    (M.inv a).toNat < M.n.toNat ∧ M.toNat (M.inv a) = Fp.inv M.n.toNat (M.toNat a) := by
  obtain ⟨h1, h2⟩ := ofNat_spec hV (Fp.inv M.n.toNat (M.toNat a))
  rw [Nat.mod_eq_of_lt (Fp.inv_lt M.n.toNat (M.toNat a) (pos hV))] at h2
  exact ⟨h1, h2⟩

/-- Kind: refinement (zero test).
    Says: on a canonical stored value the limb zero test holds exactly when the value is zero.
    Does not say: anything for a non-canonical argument. -/
theorem isZero_spec (hV : M.Valid) (a : U256) (ha : a.toNat < M.n.toNat) :
    a.isZero = true ↔ M.toNat a = 0 := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  rw [(toNat_eq_value hV hR a).2, MontMath.value_eq_zero_iff (pos hV) hR ha]
  exact U256.isZero_iff a

/-- Kind: refinement (equality test).
    Says: on canonical stored values the limb equality test holds exactly when the values are equal.
    Does not say: anything for non-canonical arguments. -/
theorem beq_spec (hV : M.Valid) (a b : U256) (ha : a.toNat < M.n.toNat) (hb : b.toNat < M.n.toNat) :
    U256.beq a b = true ↔ M.toNat a = M.toNat b := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  rw [U256.beq_iff, (toNat_eq_value hV hR a).2, (toNat_eq_value hV hR b).2]
  exact ⟨fun h => by rw [h], fun h => MontMath.value_inj (pos hV) hR ha hb h⟩

/-- Kind: refinement (the whole dictionary).
    Says: for a valid parameter set, `M.ops` refines `Fp.ops N` on canonical stored values
    (limbs below the modulus), read through `M.toNat`: every operation keeps values canonical
    and commutes with `toNat`, and the two tests agree with equality of values.
    Does not say: that the modulus is prime, that `Fp.inv` inverts, or anything about timing. -/
theorem ops_refines (hV : M.Valid) :
    FieldRefines M.ops M.n.toNat (fun a => a.toNat < M.n.toNat) M.toNat where
  zero := zero_spec hV
  one := one_spec hV
  add := fun a b ha hb => add_spec hV a b ha hb
  sub := fun a b ha hb => sub_spec hV a b ha hb
  mul := fun a b ha _ => mul_spec hV a b ha
  sqr := fun a ha => sqr_spec hV a ha
  neg := fun a ha => neg_spec hV a ha
  inv := fun a _ => inv_spec hV a
  isZero := fun a ha => isZero_spec hV a ha
  eq := fun a b ha hb => beq_spec hV a b ha hb
  lt := fun a => toNat_lt hV a

end Mont256

/-! ### 6 limbs -/

private theorem zsum6 (z : Nat) (hz : z = 0) : z + z * 2 ^ 64 + z * 2 ^ 128 + z * 2 ^ 192 + z * 2 ^ 256 + z * 2 ^ 320 = 0 := by omega

private theorem wsum6 (s z : Nat) (hz : z = 0) : s + z * 2 ^ 384 + z * 2 ^ 448 + z * 2 ^ 512 + z * 2 ^ 576 + z * 2 ^ 640 + z * 2 ^ 704 = s := by omega

/-- Kind: representation.
    Says: widening a 6-limb value to 12 limbs keeps the number.
    Does not say: anything about a modulus. -/
theorem U384.widen_toNat (a : U384) : a.widen.toNat = a.toNat := by
  show a.l0.toNat + a.l1.toNat * 2 ^ 64 + a.l2.toNat * 2 ^ 128 + a.l3.toNat * 2 ^ 192 + a.l4.toNat * 2 ^ 256 + a.l5.toNat * 2 ^ 320 + (0 : UInt64).toNat * 2 ^ 384 + (0 : UInt64).toNat * 2 ^ 448 + (0 : UInt64).toNat * 2 ^ 512 + (0 : UInt64).toNat * 2 ^ 576 + (0 : UInt64).toNat * 2 ^ 640 + (0 : UInt64).toNat * 2 ^ 704 = a.l0.toNat + a.l1.toNat * 2 ^ 64 + a.l2.toNat * 2 ^ 128 + a.l3.toNat * 2 ^ 192 + a.l4.toNat * 2 ^ 256 + a.l5.toNat * 2 ^ 320
  exact wsum6 _ _ zero_toNat''

/-- Kind: representation.
    Says: the 6-limb zero is the number zero.
    Does not say: anything about a modulus. -/
theorem U384.toNat_zero : U384.zero.toNat = 0 := by
  show (0 : UInt64).toNat + (0 : UInt64).toNat * 2 ^ 64 + (0 : UInt64).toNat * 2 ^ 128 + (0 : UInt64).toNat * 2 ^ 192 + (0 : UInt64).toNat * 2 ^ 256 + (0 : UInt64).toNat * 2 ^ 320 = 0
  exact zsum6 _ zero_toNat''

namespace Mont384

/-- What the Montgomery routines need of a parameter set: an odd modulus above 1, the `n0inv`
    property `n0inv · N ≡ −1 (mod 2^64)`, `one = R mod N` and `r2 = R² mod N`, with `R = 2^384`.
    All five are closed statements for a literal parameter set, checked by `decide`. -/
structure Valid (M : Mont384) : Prop where
  odd : M.n.toNat % 2 = 1
  one_lt : 1 < M.n.toNat
  n0inv_spec : (M.n0inv.toNat * (M.n.toNat % 2 ^ 64) + 1) % 2 ^ 64 = 0
  one_spec : M.one.toNat = 2 ^ 384 % M.n.toNat
  r2_spec : M.r2.toNat = 2 ^ 384 * 2 ^ 384 % M.n.toNat

variable {M : Mont384}

/-- Kind: existence.
    Says: for a valid parameter set the radix `2^384` has an inverse modulo the modulus.
    Does not say: what it is (the curve modules give it as a literal), or that the modulus is prime. -/
theorem exists_Rinv (hV : M.Valid) : ∃ Rinv, 2 ^ 384 * Rinv % M.n.toNat = 1 :=
  MontMath.exists_Rinv384 M.n0inv.toNat M.n.toNat hV.one_lt hV.n0inv_spec

/-- Kind: bound.
    Says: the modulus of a valid parameter set is positive.
    Does not say: anything else. -/
theorem pos (hV : M.Valid) : 0 < M.n.toNat := Nat.lt_trans Nat.zero_lt_one hV.one_lt

/-- Kind: refinement (leaving Montgomery form).
    Says: for a valid parameter set and any inverse `Rinv` of the radix, `toNat a` is below the
    modulus and is the value `a · Rinv mod N` of the stored limbs, for every `a` (canonical or not).
    Does not say: that the modulus is prime, or anything about timing. -/
theorem toNat_eq_value (hV : M.Valid) {Rinv : Nat} (hR : 2 ^ 384 * Rinv % M.n.toNat = 1) (a : U384) :
    M.toNat a < M.n.toNat ∧ M.toNat a = MontMath.value M.n.toNat Rinv a.toNat := by
  have hN := pos hV
  have ht : a.widen.toNat < M.n.toNat * 2 ^ 384 := by
    rw [U384.widen_toNat]
    exact MontMath.lt_mul_radix (U384.toNat_lt a) hN
  obtain ⟨h1, h2⟩ := U384.redc_spec M.n M.n0inv a.widen hV.n0inv_spec ht
  rw [U384.widen_toNat] at h2
  exact ⟨h1, MontMath.eq_value_of_mul_R hN hR h1 h2⟩

/-- Kind: canonical representation.
    Says: `toNat` of any limbs is below the modulus.
    Does not say: anything else. -/
theorem toNat_lt (hV : M.Valid) (a : U384) : M.toNat a < M.n.toNat := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  exact (toNat_eq_value hV hR a).1

/-- Kind: refinement (multiplication).
    Says: for a valid parameter set and a canonical first factor, the Montgomery product is
    canonical and its value is `Fp.mul` of the values.
    Does not say: anything when the first factor is not below the modulus; nothing about timing. -/
theorem mul_spec (hV : M.Valid) (a b : U384) (ha : a.toNat < M.n.toNat) :
    (M.mul a b).toNat < M.n.toNat ∧
      M.toNat (M.mul a b) = Fp.mul M.n.toNat (M.toNat a) (M.toNat b) := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  have hN := pos hV
  have ht : (U384.mulWide a b).toNat < M.n.toNat * 2 ^ 384 := by
    rw [U384.mulWide_spec]
    exact MontMath.mul_lt_mul_radix ha (U384.toNat_lt b)
  obtain ⟨h1, h2⟩ := U384.redc_spec M.n M.n0inv (U384.mulWide a b) hV.n0inv_spec ht
  rw [U384.mulWide_spec] at h2
  have hv := MontMath.value_mul hN hR h2
  refine ⟨h1, ?_⟩
  rw [(toNat_eq_value hV hR (M.mul a b)).2, (toNat_eq_value hV hR a).2, (toNat_eq_value hV hR b).2]
  exact hv

/-- Kind: refinement (squaring).
    Says: the Montgomery square of a canonical value is canonical and its value is `Fp.mul` of the value with itself.
    Does not say: anything for a non-canonical argument. -/
theorem sqr_spec (hV : M.Valid) (a : U384) (ha : a.toNat < M.n.toNat) :
    (M.sqr a).toNat < M.n.toNat ∧
      M.toNat (M.sqr a) = Fp.mul M.n.toNat (M.toNat a) (M.toNat a) :=
  mul_spec hV a a ha

/-- Kind: refinement (addition).
    Says: the sum of two canonical stored values is canonical and its value is `Fp.add` of the values.
    Does not say: anything for non-canonical arguments. -/
theorem add_spec (hV : M.Valid) (a b : U384) (ha : a.toNat < M.n.toNat) (hb : b.toNat < M.n.toNat) :
    (M.add a b).toNat < M.n.toNat ∧
      M.toNat (M.add a b) = Fp.add M.n.toNat (M.toNat a) (M.toNat b) := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  have hN := pos hV
  have e : (M.add a b).toNat = Fp.add M.n.toNat a.toNat b.toNat := U384.addMod_spec M.n a b ha hb
  refine ⟨by rw [e]; exact Fp.add_lt _ _ _ ha hb, ?_⟩
  rw [(toNat_eq_value hV hR (M.add a b)).2, (toNat_eq_value hV hR a).2, (toNat_eq_value hV hR b).2, e]
  exact MontMath.value_add hN Rinv ha hb

/-- Kind: refinement (subtraction).
    Says: the difference of two canonical stored values is canonical and its value is `Fp.sub` of the values.
    Does not say: anything for non-canonical arguments. -/
theorem sub_spec (hV : M.Valid) (a b : U384) (ha : a.toNat < M.n.toNat) (hb : b.toNat < M.n.toNat) :
    (M.sub a b).toNat < M.n.toNat ∧
      M.toNat (M.sub a b) = Fp.sub M.n.toNat (M.toNat a) (M.toNat b) := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  have hN := pos hV
  have e : (M.sub a b).toNat = Fp.sub M.n.toNat a.toNat b.toNat := U384.subMod_spec M.n a b ha hb
  refine ⟨by rw [e]; exact Fp.sub_lt _ _ _ ha hb, ?_⟩
  rw [(toNat_eq_value hV hR (M.sub a b)).2, (toNat_eq_value hV hR a).2, (toNat_eq_value hV hR b).2, e]
  exact MontMath.value_sub hN Rinv ha hb

/-- Kind: refinement (negation).
    Says: the negation of a canonical stored value is canonical and its value is `Fp.neg` of the value.
    Does not say: anything for a non-canonical argument. -/
theorem neg_spec (hV : M.Valid) (a : U384) (ha : a.toNat < M.n.toNat) :
    (M.neg a).toNat < M.n.toNat ∧ M.toNat (M.neg a) = Fp.neg M.n.toNat (M.toNat a) := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  have hN := pos hV
  have e : (M.neg a).toNat = Fp.neg M.n.toNat a.toNat := U384.negMod_spec M.n a ha
  refine ⟨by rw [e]; exact Fp.neg_lt _ _ ha, ?_⟩
  rw [(toNat_eq_value hV hR (M.neg a)).2, (toNat_eq_value hV hR a).2, e]
  exact MontMath.value_neg hN hR ha

/-- Kind: refinement (entering Montgomery form).
    Says: `ofNat x` is canonical and its value is `x mod N`, for every natural number `x`.
    Does not say: anything about timing. -/
theorem ofNat_spec (hV : M.Valid) (x : Nat) :
    (M.ofNat x).toNat < M.n.toNat ∧ M.toNat (M.ofNat x) = x % M.n.toNat := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  have hN := pos hV
  have hx : x % M.n.toNat < M.n.toNat := Nat.mod_lt _ hN
  have hu : (U384.ofNat (x % M.n.toNat)).toNat = x % M.n.toNat := by
    rw [U384.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans hx (U384.toNat_lt M.n))
  have ht : (U384.mulWide (U384.ofNat (x % M.n.toNat)) M.r2).toNat < M.n.toNat * 2 ^ 384 := by
    rw [U384.mulWide_spec, hu]
    exact MontMath.mul_lt_mul_radix hx (U384.toNat_lt M.r2)
  obtain ⟨h1, h2⟩ := U384.redc_spec M.n M.n0inv (U384.mulWide (U384.ofNat (x % M.n.toNat)) M.r2)
    hV.n0inv_spec ht
  rw [U384.mulWide_spec, hu, hV.r2_spec] at h2
  have h3 : x % M.n.toNat * (2 ^ 384 * 2 ^ 384 % M.n.toNat) % M.n.toNat =
      x % M.n.toNat * 2 ^ 384 * 2 ^ 384 % M.n.toNat := by
    rw [Nat.mul_assoc (x % M.n.toNat) (2 ^ 384) (2 ^ 384)]
    exact MontMath.mul_congr rfl (Nat.mod_mod _ _)
  have h4 := MontMath.cancel_R hN hR (h2.trans h3)
  rw [Nat.mod_eq_of_lt h1] at h4
  refine ⟨h1, ?_⟩
  show M.toNat (U384.redc M.n M.n0inv (U384.mulWide (U384.ofNat (x % M.n.toNat)) M.r2)) = x % M.n.toNat
  rw [(toNat_eq_value hV hR _).2, h4, MontMath.value_toMont hN hR, Nat.mod_mod]

/-- Kind: refinement (one).
    Says: the stored one is canonical and its value is `1 mod N` (which is 1, the modulus being above 1).
    Does not say: anything else. -/
theorem one_spec (hV : M.Valid) : M.one.toNat < M.n.toNat ∧ M.toNat M.one = 1 % M.n.toNat := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  have hN := pos hV
  have h := MontMath.value_toMont hN hR 1
  rw [Nat.one_mul] at h
  refine ⟨by rw [hV.one_spec]; exact Nat.mod_lt _ hN, ?_⟩
  rw [(toNat_eq_value hV hR M.one).2, hV.one_spec]
  exact h

/-- Kind: refinement (zero).
    Says: the stored zero is canonical and its value is zero.
    Does not say: anything else. -/
theorem zero_spec (hV : M.Valid) : U384.zero.toNat < M.n.toNat ∧ M.toNat U384.zero = 0 := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  have hN := pos hV
  refine ⟨by rw [U384.toNat_zero]; exact hN, ?_⟩
  rw [(toNat_eq_value hV hR U384.zero).2, U384.toNat_zero]
  exact MontMath.value_zero _ _

/-- Kind: refinement (inverse routine).
    Says: `inv a` is canonical and its value is `Fp.inv` of the value of `a`.
    Does not say: that `Fp.inv` is an inverse (not proved anywhere; callers and guards check `a · inv a = 1`). -/
theorem inv_spec (hV : M.Valid) (a : U384) :
    (M.inv a).toNat < M.n.toNat ∧ M.toNat (M.inv a) = Fp.inv M.n.toNat (M.toNat a) := by
  obtain ⟨h1, h2⟩ := ofNat_spec hV (Fp.inv M.n.toNat (M.toNat a))
  rw [Nat.mod_eq_of_lt (Fp.inv_lt M.n.toNat (M.toNat a) (pos hV))] at h2
  exact ⟨h1, h2⟩

/-- Kind: refinement (zero test).
    Says: on a canonical stored value the limb zero test holds exactly when the value is zero.
    Does not say: anything for a non-canonical argument. -/
theorem isZero_spec (hV : M.Valid) (a : U384) (ha : a.toNat < M.n.toNat) :
    a.isZero = true ↔ M.toNat a = 0 := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  rw [(toNat_eq_value hV hR a).2, MontMath.value_eq_zero_iff (pos hV) hR ha]
  exact U384.isZero_iff a

/-- Kind: refinement (equality test).
    Says: on canonical stored values the limb equality test holds exactly when the values are equal.
    Does not say: anything for non-canonical arguments. -/
theorem beq_spec (hV : M.Valid) (a b : U384) (ha : a.toNat < M.n.toNat) (hb : b.toNat < M.n.toNat) :
    U384.beq a b = true ↔ M.toNat a = M.toNat b := by
  obtain ⟨Rinv, hR⟩ := exists_Rinv hV
  rw [U384.beq_iff, (toNat_eq_value hV hR a).2, (toNat_eq_value hV hR b).2]
  exact ⟨fun h => by rw [h], fun h => MontMath.value_inj (pos hV) hR ha hb h⟩

/-- Kind: refinement (the whole dictionary).
    Says: for a valid parameter set, `M.ops` refines `Fp.ops N` on canonical stored values
    (limbs below the modulus), read through `M.toNat`: every operation keeps values canonical
    and commutes with `toNat`, and the two tests agree with equality of values.
    Does not say: that the modulus is prime, that `Fp.inv` inverts, or anything about timing. -/
theorem ops_refines (hV : M.Valid) :
    FieldRefines M.ops M.n.toNat (fun a => a.toNat < M.n.toNat) M.toNat where
  zero := zero_spec hV
  one := one_spec hV
  add := fun a b ha hb => add_spec hV a b ha hb
  sub := fun a b ha hb => sub_spec hV a b ha hb
  mul := fun a b ha _ => mul_spec hV a b ha
  sqr := fun a ha => sqr_spec hV a ha
  neg := fun a ha => neg_spec hV a ha
  inv := fun a _ => inv_spec hV a
  isZero := fun a ha => isZero_spec hV a ha
  eq := fun a b ha hb => beq_spec hV a b ha hb
  lt := fun a => toNat_lt hV a

end Mont384

#print axioms U256.widen_toNat
#print axioms U256.toNat_zero
#print axioms Mont256.exists_Rinv
#print axioms Mont256.pos
#print axioms Mont256.toNat_eq_value
#print axioms Mont256.toNat_lt
#print axioms Mont256.mul_spec
#print axioms Mont256.sqr_spec
#print axioms Mont256.add_spec
#print axioms Mont256.sub_spec
#print axioms Mont256.neg_spec
#print axioms Mont256.ofNat_spec
#print axioms Mont256.one_spec
#print axioms Mont256.zero_spec
#print axioms Mont256.inv_spec
#print axioms Mont256.isZero_spec
#print axioms Mont256.beq_spec
#print axioms Mont256.ops_refines
#print axioms U384.widen_toNat
#print axioms U384.toNat_zero
#print axioms Mont384.exists_Rinv
#print axioms Mont384.pos
#print axioms Mont384.toNat_eq_value
#print axioms Mont384.toNat_lt
#print axioms Mont384.mul_spec
#print axioms Mont384.sqr_spec
#print axioms Mont384.add_spec
#print axioms Mont384.sub_spec
#print axioms Mont384.neg_spec
#print axioms Mont384.ofNat_spec
#print axioms Mont384.one_spec
#print axioms Mont384.zero_spec
#print axioms Mont384.inv_spec
#print axioms Mont384.isZero_spec
#print axioms Mont384.beq_spec
#print axioms Mont384.ops_refines

end EVMCleanroom.Precompiles
