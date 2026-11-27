import EVMCleanroom.Precompiles.Field

/-!
# Montgomery reduction and Montgomery form, on natural numbers

The facts about Montgomery arithmetic (Montgomery, "Modular multiplication
without trial division", Mathematics of Computation 44, 1985) that do not
depend on limbs, stated for a modulus `N`, a radix `R` and the limb base `2^64`:

* the reduction fact: if `t + m · N = q · R` with `t < N · R` and `m < R`, then
  `q < 2N`, and one conditional subtraction gives the canonical `q'` with
  `q' · R ≡ t (mod N)`;
* the per-row fact: with `n0inv · N₀ ≡ −1 (mod 2^64)` and
  `m = t₀ · n0inv mod 2^64`, the low limb of `t + m · N` is zero;
* the representation algebra: with `R · Rinv ≡ 1 (mod N)`, the value of a stored
  residue `x` is `x · Rinv mod N`; it turns Montgomery products into products,
  and commutes with the division-free sum, difference and negation of `Fp`;
* an inverse of `2^64` modulo `N` exists whenever the `n0inv` property holds;
* the rows of the limb routines as equations between natural numbers
  (`redc_row4`, `redc_chain4`, and the six-limb versions), so the limb proofs
  only supply the equations of `mac` and `adc`.

Everything here is proved for all natural numbers satisfying the stated
hypotheses. Nothing here says the modulus is prime, and nothing is said about
the limb routines themselves: that is `MontgomeryProofs.lean`.
-/

set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

namespace EVMCleanroom.Precompiles.MontMath

/-! ### Congruences written with `%` -/

/-- Kind: algebraic fact.
    Says: sums of congruent numbers are congruent.
    Does not say: anything about subtraction. -/
theorem add_congr {N a a' b b' : Nat} (ha : a % N = a' % N) (hb : b % N = b' % N) :
    (a + b) % N = (a' + b') % N := by
  rw [Nat.add_mod a b N, ha, hb, ← Nat.add_mod a' b' N]

/-- Kind: algebraic fact.
    Says: products of congruent numbers are congruent.
    Does not say: anything about division. -/
theorem mul_congr {N a a' b b' : Nat} (ha : a % N = a' % N) (hb : b % N = b' % N) :
    (a * b) % N = (a' * b') % N := by
  rw [Nat.mul_mod a b N, ha, hb, ← Nat.mul_mod a' b' N]

/-- Kind: algebraic fact.
    Says: two numbers that have congruent additive complements modulo `N` are congruent.
    Does not say: that complements exist (the callers exhibit them). -/
theorem mod_neg_unique {N x x' y y' : Nat} (h1 : (x + y) % N = 0) (h2 : (x' + y') % N = 0)
    (hy : y % N = y' % N) : x % N = x' % N := by
  have a1 : (x + (x' + y')) % N = x % N := by
    rw [Nat.add_mod x (x' + y') N, h2, Nat.add_zero, Nat.mod_mod]
  have a2 : (x' + (x + y)) % N = x' % N := by
    rw [Nat.add_mod x' (x + y) N, h1, Nat.add_zero, Nat.mod_mod]
  have a3 : (x + (x' + y')) % N = (x' + (x + y)) % N := by
    rw [Nat.add_left_comm x x' y']
    exact add_congr rfl (add_congr rfl hy.symm)
  exact a1.symm.trans (a3.trans a2)

/-- Kind: algebraic fact.
    Says: `(N − b) · c` is congruent to `N − (b · c mod N)` modulo `N`, for `b ≤ N`.
    Does not say: that the right-hand side is canonical (it is `N` when `b · c ≡ 0`). -/
theorem neg_mul_mod {N : Nat} (hN : 0 < N) (b c : Nat) (hb : b ≤ N) :
    (N - b) * c % N = (N - b * c % N) % N := by
  refine mod_neg_unique (y := b * c) (y' := b * c % N) ?_ ?_ (Nat.mod_mod _ _).symm
  · rw [← Nat.add_mul, Nat.sub_add_cancel hb, Nat.mul_mod_right]
  · rw [Nat.sub_add_cancel (Nat.le_of_lt (Nat.mod_lt _ hN)), Nat.mod_self]

/-- Kind: algebraic fact.
    Says: multiplying by a number congruent to one does not change the residue.
    Does not say: that such a number exists. -/
theorem mul_unit {N u : Nat} (x : Nat) (hu : u % N = 1 % N) : x * u % N = x % N := by
  have h : (x * u) % N = (x * 1) % N := mul_congr rfl hu
  rw [Nat.mul_one] at h
  exact h

/-! ### The reduction fact -/

/-- Kind: bound (Montgomery reduction).
    Says: if `t + m · N = q · R` with `t < N · R` and `m < R` then `q < 2N`.
    Does not say: that such `m` and `q` exist (the rows of the limb routine produce them). -/
theorem redc_lt_two (N R t m q : Nat) (h : t + m * N = q * R) (ht : t < N * R) (hm : m < R) :
    q < 2 * N := by
  have h1 : (m + 1) * N ≤ R * N := Nat.mul_le_mul_right N (Nat.succ_le_of_lt hm)
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm R N] at h1
  rcases Nat.lt_or_ge q (2 * N) with hq | hq
  · exact hq
  · have h2 : 2 * N * R ≤ q * R := Nat.mul_le_mul_right R hq
    rw [Nat.mul_assoc] at h2
    omega

/-- Kind: functional correctness (Montgomery reduction, the final conditional subtraction).
    Says: if `t + m · N = q · R` with `t < N · R` and `m < R`, then `q` less `N` when `q ≥ N` is
    below `N`, and times `R` it is congruent to `t` modulo `N`.
    Does not say: that `R` is invertible modulo `N` (see `eq_value_of_mul_R` for what follows when it is). -/
theorem redc_final (N R t m q : Nat) (h : t + m * N = q * R) (ht : t < N * R) (hm : m < R) :
    (if N ≤ q then q - N else q) < N ∧ (if N ≤ q then q - N else q) * R % N = t % N := by
  have hq := redc_lt_two N R t m q h ht hm
  have hmod : q * R % N = t % N := by rw [← h, Nat.add_mul_mod_self_right]
  by_cases hc : N ≤ q
  · rw [if_pos hc]
    refine ⟨by omega, ?_⟩
    have e : q - N + N = q := Nat.sub_add_cancel hc
    have e2 : (q - N) * R + N * R = q * R := by rw [← Nat.add_mul, e]
    rw [← hmod, ← e2, Nat.add_mul_mod_self_left]
  · rw [if_neg hc]
    exact ⟨by omega, hmod⟩

/-- Kind: functional correctness (Montgomery reduction, the final reduction written with `%`).
    Says: if `t + m · N = q · R` then `(q mod N) · R ≡ t (mod N)`.
    Does not say: that `q mod N` is what a single conditional subtraction returns; that needs `q < 2N` (`redc_lt_two`). -/
theorem redc_mod (N R t m q : Nat) (h : t + m * N = q * R) : q % N * R % N = t % N := by
  have e1 : q % N * R % N = q * R % N := mul_congr (Nat.mod_mod q N) rfl
  have e2 : q * R % N = t % N := by rw [← h, Nat.add_mul_mod_self_right]
  exact e1.trans e2

/-- Kind: algebraic fact.
    Says: for a number below `2n`, subtracting `n` once when it is not below `n` gives its residue.
    Does not say: anything for a number of `2n` or more. -/
theorem mod_of_lt_two (v n : Nat) (h : v < 2 * n) : (if v < n then v else v - n) = v % n := by
  by_cases hlt : v < n
  · rw [if_pos hlt, Nat.mod_eq_of_lt hlt]
  · rw [if_neg hlt]
    have h1 : v - n < n := by omega
    exact ((Nat.mod_eq_sub_mod (Nat.le_of_not_lt hlt)).trans (Nat.mod_eq_of_lt h1)).symm

/-- Kind: bound.
    Says: a number below the radix is below any positive multiple of the radix.
    Does not say: anything for a zero modulus. -/
theorem lt_mul_radix {x N R : Nat} (hx : x < R) (hN : 0 < N) : x < N * R := by
  have h : 1 * R ≤ N * R := Nat.mul_le_mul_right R hN
  rw [Nat.one_mul] at h
  exact Nat.lt_of_lt_of_le hx h

/-- Kind: bound.
    Says: the product of a canonical residue and a number below the radix is below `N · R`, the range Montgomery reduction accepts.
    Does not say: anything when the first factor is not below `N`. -/
theorem mul_lt_mul_radix {a b N R : Nat} (ha : a < N) (hb : b < R) : a * b < N * R := by
  have h1 : a * b ≤ a * R := Nat.mul_le_mul_left a (Nat.le_of_lt hb)
  have h2 : (a + 1) * R ≤ N * R := Nat.mul_le_mul_right R (Nat.succ_le_of_lt ha)
  rw [Nat.add_mul, Nat.one_mul] at h2
  omega

/-! ### The per-row fact -/

/-- Kind: algebraic fact (the low limb of a Montgomery row vanishes).
    Says: for a base `B`, if `n0inv · n0 + 1 ≡ 0 (mod B)` then `(a0 · n0inv mod B) · n0 + a0 ≡ 0 (mod B)`.
    Does not say: anything about the higher limbs. -/
theorem row_low_zero (B n0inv n0 a0 : Nat) (h : (n0inv * n0 + 1) % B = 0) :
    (a0 * n0inv % B * n0 + a0) % B = 0 := by
  have e1 : (a0 * n0inv % B * n0 + a0) % B = (a0 * n0inv * n0 + a0) % B :=
    add_congr (mul_congr (Nat.mod_mod _ _) rfl) rfl
  have e2 : a0 * n0inv * n0 + a0 = a0 * (n0inv * n0 + 1) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  rw [e1, e2, Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

/-- Kind: algebraic fact (the per-row fact for whole numbers).
    Says: with `n0inv · (N mod B) + 1 ≡ 0 (mod B)` and `m = (t mod B) · n0inv mod B`,
    `t + m · N ≡ 0 (mod B)`; for `B = 2^64` this is the statement that a row of the reduction clears the low limb.
    Does not say: anything about `(t + m · N) / B`. -/
theorem row_low_zero_gen (B n0inv N t : Nat) (h : (n0inv * (N % B) + 1) % B = 0) :
    (t + (t % B * n0inv % B) * N) % B = 0 := by
  have e : (t + (t % B * n0inv % B) * N) % B = ((t % B * n0inv % B) * (N % B) + t % B) % B := by
    rw [Nat.add_comm t _]
    exact add_congr (mul_congr rfl (Nat.mod_mod N B).symm) (Nat.mod_mod t B).symm
  rw [e]
  exact row_low_zero B n0inv (N % B) (t % B) h

/-! ### Montgomery form: the value of a stored residue -/

/-- The value of a stored residue `x`: `x · Rinv mod N`. -/
def value (N Rinv x : Nat) : Nat := x * Rinv % N

section Repr

variable {N R Rinv : Nat}

/-- Kind: bound.
    Says: an inverse of `R` modulo `N` can only exist for `N > 1`.
    Does not say: that one exists. -/
theorem one_lt_of_inv (hN : 0 < N) (hR : R * Rinv % N = 1) : 1 < N := by
  have h := Nat.mod_lt (R * Rinv) hN
  rw [hR] at h
  exact h

/-- Kind: algebraic fact.
    Says: `R · Rinv` is congruent to one, in the form the congruence lemmas take.
    Does not say: more than the hypothesis. -/
theorem unit_of_inv (hN : 0 < N) (hR : R * Rinv % N = 1) : R * Rinv % N = 1 % N := by
  rw [hR, Nat.mod_eq_of_lt (one_lt_of_inv hN hR)]

/-- Kind: canonical representation.
    Says: a value is below the modulus.
    Does not say: anything else. -/
theorem value_lt (hN : 0 < N) (Rinv x : Nat) : value N Rinv x < N := Nat.mod_lt _ hN

/-- Kind: algebraic fact.
    Says: the value of zero is zero.
    Does not say: anything else. -/
theorem value_zero (N Rinv : Nat) : value N Rinv 0 = 0 := by
  unfold value
  rw [Nat.zero_mul, Nat.zero_mod]

/-- Kind: algebraic fact (Montgomery product).
    Says: if `z · R ≡ x · y (mod N)`, as Montgomery reduction of `x · y` gives, then the value of
    `z` is the product modulo `N` of the values of `x` and `y`.
    Does not say: that `N` is prime, or anything about how `z` was computed. -/
theorem value_mul (hN : 0 < N) (hR : R * Rinv % N = 1) {x y z : Nat}
    (h : z * R % N = x * y % N) :
    value N Rinv z = value N Rinv x * value N Rinv y % N := by
  have hu := unit_of_inv hN hR
  have e1 : (x * Rinv % N) * (y * Rinv % N) % N = (x * Rinv) * (y * Rinv) % N :=
    (Nat.mul_mod _ _ _).symm
  have e2 : x * Rinv * (y * Rinv) = x * y * (Rinv * Rinv) := by
    first
      | exact Nat.mul_mul_mul_comm x Rinv y Rinv
      | simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      | grind
  have e3 : x * y * (Rinv * Rinv) % N = z * R * (Rinv * Rinv) % N := mul_congr h.symm rfl
  have e4 : z * R * (Rinv * Rinv) = z * Rinv * (R * Rinv) := by
    first
      | exact Nat.mul_mul_mul_comm z R Rinv Rinv
      | simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      | grind
  have e5 : z * Rinv * (R * Rinv) % N = z * Rinv % N := mul_unit _ hu
  show z * Rinv % N = (x * Rinv % N) * (y * Rinv % N) % N
  rw [e1, e2, e3, e4, e5]

/-- Kind: algebraic fact (entering Montgomery form).
    Says: the value of `x · R mod N` is `x mod N`.
    Does not say: anything about how `x · R mod N` is computed. -/
theorem value_toMont (hN : 0 < N) (hR : R * Rinv % N = 1) (x : Nat) :
    value N Rinv (x * R % N) = x % N := by
  have hu := unit_of_inv hN hR
  have e1 : x * R % N * Rinv % N = x * R * Rinv % N := mul_congr (Nat.mod_mod _ _) rfl
  have e2 : x * R * Rinv = x * (R * Rinv) := Nat.mul_assoc x R Rinv
  have e3 : x * (R * Rinv) % N = x % N := mul_unit _ hu
  show x * R % N * Rinv % N = x % N
  rw [e1, e2, e3]

/-- Kind: algebraic fact (leaving Montgomery form is inverse to entering it).
    Says: the value of `x` times `R` is congruent to `x`.
    Does not say: anything for a radix without inverse. -/
theorem value_mul_R (hN : 0 < N) (hR : R * Rinv % N = 1) (x : Nat) :
    value N Rinv x * R % N = x % N := by
  have hu := unit_of_inv hN hR
  have e1 : x * Rinv % N * R % N = x * Rinv * R % N := mul_congr (Nat.mod_mod _ _) rfl
  have e2 : x * Rinv * R = x * (R * Rinv) := by rw [Nat.mul_assoc, Nat.mul_comm Rinv R]
  have e3 : x * (R * Rinv) % N = x % N := mul_unit _ hu
  show x * Rinv % N * R % N = x % N
  rw [e1, e2, e3]

/-- Kind: algebraic fact (what Montgomery reduction of a stored residue returns).
    Says: a canonical `f` with `f · R ≡ a (mod N)` is the value of `a`.
    Does not say: how `f` was computed. -/
theorem eq_value_of_mul_R (hN : 0 < N) (hR : R * Rinv % N = 1) {f a : Nat} (hf : f < N)
    (h : f * R % N = a % N) : f = value N Rinv a := by
  have hu := unit_of_inv hN hR
  have e1 : f * R * Rinv % N = a * Rinv % N := mul_congr h rfl
  have e2 : f * R * Rinv = f * (R * Rinv) := Nat.mul_assoc f R Rinv
  have e3 : f * (R * Rinv) % N = f % N := mul_unit _ hu
  rw [e2, e3, Nat.mod_eq_of_lt hf] at e1
  exact e1

/-- Kind: algebraic fact (the radix cancels).
    Says: `u · R ≡ v · R (mod N)` gives `u ≡ v (mod N)`.
    Does not say: anything for a radix without inverse. -/
theorem cancel_R (hN : 0 < N) (hR : R * Rinv % N = 1) {u v : Nat}
    (h : u * R % N = v * R % N) : u % N = v % N := by
  have hu := unit_of_inv hN hR
  have e1 : u * R * Rinv % N = v * R * Rinv % N := mul_congr h rfl
  have e2 : u * R * Rinv = u * (R * Rinv) := Nat.mul_assoc u R Rinv
  have e3 : v * R * Rinv = v * (R * Rinv) := Nat.mul_assoc v R Rinv
  have e4 : u * (R * Rinv) % N = u % N := mul_unit _ hu
  have e5 : v * (R * Rinv) % N = v % N := mul_unit _ hu
  rw [e2, e3, e4, e5] at e1
  exact e1

/-- Kind: algebraic fact (the value map is injective on canonical residues).
    Says: two residues below `N` with the same value are equal.
    Does not say: anything for non-canonical arguments. -/
theorem value_inj (hN : 0 < N) (hR : R * Rinv % N = 1) {x y : Nat} (hx : x < N) (hy : y < N)
    (h : value N Rinv x = value N Rinv y) : x = y := by
  have ex := value_mul_R hN hR x
  have ey := value_mul_R hN hR y
  rw [h, ey, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at ex
  exact ex.symm

/-- Kind: algebraic fact.
    Says: a canonical residue has value zero exactly when it is zero.
    Does not say: anything for non-canonical arguments. -/
theorem value_eq_zero_iff (hN : 0 < N) (hR : R * Rinv % N = 1) {x : Nat} (hx : x < N) :
    value N Rinv x = 0 ↔ x = 0 := by
  constructor
  · intro h
    exact value_inj hN hR hx hN (h.trans (value_zero N Rinv).symm)
  · intro h
    rw [h]
    exact value_zero N Rinv

/-- Kind: algebraic fact (sums).
    Says: the value of the division-free sum of two canonical residues is the division-free sum of their values.
    Does not say: anything for non-canonical arguments; it does not need an inverse of the radix. -/
theorem value_add (hN : 0 < N) (Rinv : Nat) {a b : Nat} (ha : a < N) (hb : b < N) :
    value N Rinv (Fp.add N a b) = Fp.add N (value N Rinv a) (value N Rinv b) := by
  rw [Fp.add_eq_mod N a b ha hb,
    Fp.add_eq_mod N (value N Rinv a) (value N Rinv b) (value_lt hN Rinv a) (value_lt hN Rinv b)]
  have e1 : (a + b) % N * Rinv % N = (a + b) * Rinv % N := mul_congr (Nat.mod_mod _ _) rfl
  have e2 : (a * Rinv % N + b * Rinv % N) % N = (a * Rinv + b * Rinv) % N :=
    (Nat.add_mod _ _ _).symm
  show (a + b) % N * Rinv % N = (a * Rinv % N + b * Rinv % N) % N
  rw [e1, e2, Nat.add_mul]

/-- Kind: algebraic fact (differences).
    Says: the value of the division-free difference of two canonical residues is the division-free difference of their values.
    Does not say: anything for non-canonical arguments; it does not need an inverse of the radix. -/
theorem value_sub (hN : 0 < N) (Rinv : Nat) {a b : Nat} (ha : a < N) (hb : b < N) :
    value N Rinv (Fp.sub N a b) = Fp.sub N (value N Rinv a) (value N Rinv b) := by
  rw [Fp.sub_eq_mod N a b ha hb,
    Fp.sub_eq_mod N (value N Rinv a) (value N Rinv b) (value_lt hN Rinv a) (value_lt hN Rinv b)]
  have e1 : (a + (N - b)) % N * Rinv % N = (a + (N - b)) * Rinv % N :=
    mul_congr (Nat.mod_mod _ _) rfl
  have e2 : (a + (N - b)) * Rinv = a * Rinv + (N - b) * Rinv := Nat.add_mul _ _ _
  have e3 : (a * Rinv + (N - b) * Rinv) % N = (a * Rinv % N + (N - b * Rinv % N)) % N :=
    add_congr (Nat.mod_mod _ _).symm (neg_mul_mod hN b Rinv (Nat.le_of_lt hb))
  show (a + (N - b)) % N * Rinv % N = (a * Rinv % N + (N - b * Rinv % N)) % N
  rw [e1, e2, e3]

/-- Kind: algebraic fact (negation).
    Says: the value of the negation of a canonical residue is the negation of its value.
    Does not say: anything for non-canonical arguments. -/
theorem value_neg (hN : 0 < N) (hR : R * Rinv % N = 1) {a : Nat} (ha : a < N) :
    value N Rinv (Fp.neg N a) = Fp.neg N (value N Rinv a) := by
  by_cases h0 : a = 0
  · have hv : value N Rinv a = 0 := by rw [h0]; exact value_zero N Rinv
    have e1 : Fp.neg N a = 0 := by unfold Fp.neg; rw [if_pos h0]
    have e2 : Fp.neg N (value N Rinv a) = 0 := by unfold Fp.neg; rw [if_pos hv]
    rw [e1, e2]
    exact value_zero N Rinv
  · have hv : value N Rinv a ≠ 0 := fun h => h0 ((value_eq_zero_iff hN hR ha).1 h)
    have e1 : Fp.neg N a = N - a := by unfold Fp.neg; rw [if_neg h0]
    have e2 : Fp.neg N (value N Rinv a) = N - value N Rinv a := by unfold Fp.neg; rw [if_neg hv]
    rw [e1, e2]
    have hlt : N - value N Rinv a < N := by omega
    have e3 : (N - a) * Rinv % N = (N - a * Rinv % N) % N := neg_mul_mod hN a Rinv (Nat.le_of_lt ha)
    show (N - a) * Rinv % N = N - a * Rinv % N
    rw [e3]
    exact Nat.mod_eq_of_lt hlt

end Repr

/-! ### An inverse of the radix exists -/

/-- Kind: existence (the limb base is invertible).
    Says: for `N > 1` and a base `B`, the `n0inv` property `n0inv · (N mod B) + 1 ≡ 0 (mod B)` gives a `Binv`
    with `B · Binv ≡ 1 (mod N)`, namely `(n0inv · N + 1) / B`.
    Does not say: that `N` is odd or prime; the property itself forces `N` coprime to `B`. -/
theorem exists_base_inv (B n0inv N : Nat) (hN : 1 < N) (h : (n0inv * (N % B) + 1) % B = 0) :
    ∃ Binv, B * Binv % N = 1 := by
  have h' : (n0inv * N + 1) % B = 0 := by
    have e : (n0inv * N + 1) % B = (n0inv * (N % B) + 1) % B :=
      add_congr (mul_congr rfl (Nat.mod_mod N B).symm) rfl
    rw [e]; exact h
  have hd := Nat.div_add_mod (n0inv * N + 1) B
  rw [h', Nat.add_zero] at hd
  refine ⟨(n0inv * N + 1) / B, ?_⟩
  rw [hd, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hN]

/-- Kind: algebraic fact.
    Says: inverses modulo `N` multiply.
    Does not say: that inverses exist. -/
theorem inv_mul {N a a' b b' : Nat} (hN : 1 < N) (h1 : a * a' % N = 1) (h2 : b * b' % N = 1) :
    (a * b) * (a' * b') % N = 1 := by
  have e : a * b * (a' * b') = a * a' * (b * b') := by
    first
      | exact Nat.mul_mul_mul_comm a b a' b'
      | simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      | grind
  rw [e, Nat.mul_mod, h1, h2, Nat.mul_one, Nat.mod_eq_of_lt hN]

/-- Kind: existence (the four-limb radix is invertible).
    Says: under the `n0inv` property for the base `2^64`, `2^256` has an inverse modulo `N`.
    Does not say: what the inverse is (the curve modules state it as a literal). -/
theorem exists_Rinv256 (n0inv N : Nat) (hN : 1 < N) (h : (n0inv * (N % 2 ^ 64) + 1) % 2 ^ 64 = 0) :
    ∃ Rinv, 2 ^ 256 * Rinv % N = 1 := by
  obtain ⟨k, hk⟩ := exists_base_inv (2 ^ 64) n0inv N hN h
  have h2 := inv_mul hN hk hk
  have h4 := inv_mul hN h2 h2
  have e : (2 : Nat) ^ 256 = 2 ^ 64 * 2 ^ 64 * (2 ^ 64 * 2 ^ 64) := by first | decide | rfl
  exact ⟨k * k * (k * k), by rw [e]; exact h4⟩

/-- Kind: existence (the six-limb radix is invertible).
    Says: under the `n0inv` property for the base `2^64`, `2^384` has an inverse modulo `N`.
    Does not say: what the inverse is (the curve modules state it as a literal). -/
theorem exists_Rinv384 (n0inv N : Nat) (hN : 1 < N) (h : (n0inv * (N % 2 ^ 64) + 1) % 2 ^ 64 = 0) :
    ∃ Rinv, 2 ^ 384 * Rinv % N = 1 := by
  obtain ⟨k, hk⟩ := exists_base_inv (2 ^ 64) n0inv N hN h
  have h2 := inv_mul hN hk hk
  have h4 := inv_mul hN h2 h2
  have h6 := inv_mul hN h4 h2
  have e : (2 : Nat) ^ 384 = 2 ^ 64 * 2 ^ 64 * (2 ^ 64 * 2 ^ 64) * (2 ^ 64 * 2 ^ 64) := by first | decide | rfl
  exact ⟨k * k * (k * k) * (k * k), by rw [e]; exact h6⟩

/-! ### The rows of the limb routines, as equations between natural numbers -/

/-- Kind: algebraic identity.
    Says: a number times a 4-limb sum is the sum of the limb products with the same weights.
    Does not say: anything about limb sizes. -/
theorem mul_sum4 (x n0 n1 n2 n3 : Nat) :
    x * (n0 + n1 * 2 ^ 64 + n2 * 2 ^ 128 + n3 * 2 ^ 192) = x * n0 + x * n1 * 2 ^ 64 + x * n2 * 2 ^ 128 + x * n3 * 2 ^ 192 := by
  first
    | simp only [Nat.mul_add, Nat.mul_assoc]
    | grind

/-- Kind: algebraic identity.
    Says: a 4-limb sum times a number is the sum of the limb products with the same weights.
    Does not say: anything about limb sizes. -/
theorem sum_mul4 (m0 m1 m2 m3 y : Nat) :
    (m0 + m1 * 2 ^ 64 + m2 * 2 ^ 128 + m3 * 2 ^ 192) * y = m0 * y + m1 * y * 2 ^ 64 + m2 * y * 2 ^ 128 + m3 * y * 2 ^ 192 := by
  first
    | rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.mul_right_comm m1 (2 ^ 64) y, Nat.mul_right_comm m2 (2 ^ 128) y, Nat.mul_right_comm m3 (2 ^ 192) y]
    | grind

/-- Kind: algebraic fact (one row of Montgomery reduction on 4 limbs, on natural numbers).
    Says: given the equations of the row's multiply-accumulate steps and its final add-with-carry,
    with `m` the low limb times `n0inv` modulo `2^64` and `n0inv * n0 ≡ -1`, the low limb of the
    row is zero, so the window plus `m` times the modulus equals the next window times `2^64`,
    and the carry passed up is at most 1 when the carry coming in is.
    Does not say: that the equations hold for the limb routines (that is `mac_spec`/`adc_spec`). -/
theorem redc_row4 (n0inv n0 n1 n2 n3 a0 a1 a2 a3 a4 e m c0 c1 c2 c3 lo b1 b2 b3 b4 e' : Nat)
    (hinv : (n0inv * n0 + 1) % 2 ^ 64 = 0)
    (hm : m = a0 * n0inv % 2 ^ 64)
    (h0 : c0 * 2 ^ 64 + lo = m * n0 + a0)
    (h1 : c1 * 2 ^ 64 + b1 = m * n1 + a1 + c0)
    (h2 : c2 * 2 ^ 64 + b2 = m * n2 + a2 + c1)
    (h3 : c3 * 2 ^ 64 + b3 = m * n3 + a3 + c2)
    (h4 : e' * 2 ^ 64 + b4 = a4 + c3 + e)
    (hlo : lo < 2 ^ 64) (hc : c3 < 2 ^ 64) (ha : a4 < 2 ^ 64) (he : e ≤ 1) :
    e' ≤ 1 ∧
    a0 + a1 * 2 ^ 64 + a2 * 2 ^ 128 + a3 * 2 ^ 192 + a4 * 2 ^ 256 + e * 2 ^ 256 + m * (n0 + n1 * 2 ^ 64 + n2 * 2 ^ 128 + n3 * 2 ^ 192) =
      (b1 + b2 * 2 ^ 64 + b3 * 2 ^ 128 + b4 * 2 ^ 192 + e' * 2 ^ 256) * 2 ^ 64 := by
  have hz : (m * n0 + a0) % 2 ^ 64 = 0 := by
    rw [hm]; exact row_low_zero (2 ^ 64) n0inv n0 a0 hinv
  rw [mul_sum4 m n0 n1 n2 n3]
  constructor
  · omega
  · omega

/-- Kind: algebraic fact (the 4 rows of Montgomery reduction chained, on natural numbers).
    Says: given the 4 row equations, the input `t` (as 8 limbs) plus a multiple `M · N` of
    the modulus with `M < 2^256` equals the top window `q` times `2^256`.
    Does not say: anything about the final conditional subtraction (see `redc_final`). -/
theorem redc_chain4 {t0 t1 t2 t3 t4 t5 t6 t7 N m0 m1 m2 m3 x0_1 x0_2 x0_3 x0_4 x1_1 x1_2 x1_3 x1_4 x2_1 x2_2 x2_3 x2_4 x3_1 x3_2 x3_3 x3_4 e0 e1 e2 e3 e4 : Nat}
    (E0 : t0 + t1 * 2 ^ 64 + t2 * 2 ^ 128 + t3 * 2 ^ 192 + t4 * 2 ^ 256 + e0 * 2 ^ 256 + m0 * N =
      (x0_1 + x0_2 * 2 ^ 64 + x0_3 * 2 ^ 128 + x0_4 * 2 ^ 192 + e1 * 2 ^ 256) * 2 ^ 64)
    (E1 : x0_1 + x0_2 * 2 ^ 64 + x0_3 * 2 ^ 128 + x0_4 * 2 ^ 192 + t5 * 2 ^ 256 + e1 * 2 ^ 256 + m1 * N =
      (x1_1 + x1_2 * 2 ^ 64 + x1_3 * 2 ^ 128 + x1_4 * 2 ^ 192 + e2 * 2 ^ 256) * 2 ^ 64)
    (E2 : x1_1 + x1_2 * 2 ^ 64 + x1_3 * 2 ^ 128 + x1_4 * 2 ^ 192 + t6 * 2 ^ 256 + e2 * 2 ^ 256 + m2 * N =
      (x2_1 + x2_2 * 2 ^ 64 + x2_3 * 2 ^ 128 + x2_4 * 2 ^ 192 + e3 * 2 ^ 256) * 2 ^ 64)
    (E3 : x2_1 + x2_2 * 2 ^ 64 + x2_3 * 2 ^ 128 + x2_4 * 2 ^ 192 + t7 * 2 ^ 256 + e3 * 2 ^ 256 + m3 * N =
      (x3_1 + x3_2 * 2 ^ 64 + x3_3 * 2 ^ 128 + x3_4 * 2 ^ 192 + e4 * 2 ^ 256) * 2 ^ 64)
    (he0 : e0 = 0) (hm0 : m0 < 2 ^ 64) (hm1 : m1 < 2 ^ 64) (hm2 : m2 < 2 ^ 64) (hm3 : m3 < 2 ^ 64) :
    (m0 + m1 * 2 ^ 64 + m2 * 2 ^ 128 + m3 * 2 ^ 192) < 2 ^ 256 ∧
    t0 + t1 * 2 ^ 64 + t2 * 2 ^ 128 + t3 * 2 ^ 192 + t4 * 2 ^ 256 + t5 * 2 ^ 320 + t6 * 2 ^ 384 + t7 * 2 ^ 448 + (m0 + m1 * 2 ^ 64 + m2 * 2 ^ 128 + m3 * 2 ^ 192) * N =
      (e4 * 2 ^ 256 + (x3_1 + x3_2 * 2 ^ 64 + x3_3 * 2 ^ 128 + x3_4 * 2 ^ 192)) * 2 ^ 256 := by
  rw [sum_mul4 m0 m1 m2 m3 N]
  constructor
  · omega
  · omega

/-- Kind: algebraic identity.
    Says: a number times a 6-limb sum is the sum of the limb products with the same weights.
    Does not say: anything about limb sizes. -/
theorem mul_sum6 (x n0 n1 n2 n3 n4 n5 : Nat) :
    x * (n0 + n1 * 2 ^ 64 + n2 * 2 ^ 128 + n3 * 2 ^ 192 + n4 * 2 ^ 256 + n5 * 2 ^ 320) = x * n0 + x * n1 * 2 ^ 64 + x * n2 * 2 ^ 128 + x * n3 * 2 ^ 192 + x * n4 * 2 ^ 256 + x * n5 * 2 ^ 320 := by
  first
    | simp only [Nat.mul_add, Nat.mul_assoc]
    | grind

/-- Kind: algebraic identity.
    Says: a 6-limb sum times a number is the sum of the limb products with the same weights.
    Does not say: anything about limb sizes. -/
theorem sum_mul6 (m0 m1 m2 m3 m4 m5 y : Nat) :
    (m0 + m1 * 2 ^ 64 + m2 * 2 ^ 128 + m3 * 2 ^ 192 + m4 * 2 ^ 256 + m5 * 2 ^ 320) * y = m0 * y + m1 * y * 2 ^ 64 + m2 * y * 2 ^ 128 + m3 * y * 2 ^ 192 + m4 * y * 2 ^ 256 + m5 * y * 2 ^ 320 := by
  first
    | rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.mul_right_comm m1 (2 ^ 64) y, Nat.mul_right_comm m2 (2 ^ 128) y, Nat.mul_right_comm m3 (2 ^ 192) y, Nat.mul_right_comm m4 (2 ^ 256) y, Nat.mul_right_comm m5 (2 ^ 320) y]
    | grind

/-- Kind: algebraic fact (one row of Montgomery reduction on 6 limbs, on natural numbers).
    Says: given the equations of the row's multiply-accumulate steps and its final add-with-carry,
    with `m` the low limb times `n0inv` modulo `2^64` and `n0inv * n0 ≡ -1`, the low limb of the
    row is zero, so the window plus `m` times the modulus equals the next window times `2^64`,
    and the carry passed up is at most 1 when the carry coming in is.
    Does not say: that the equations hold for the limb routines (that is `mac_spec`/`adc_spec`). -/
theorem redc_row6 (n0inv n0 n1 n2 n3 n4 n5 a0 a1 a2 a3 a4 a5 a6 e m c0 c1 c2 c3 c4 c5 lo b1 b2 b3 b4 b5 b6 e' : Nat)
    (hinv : (n0inv * n0 + 1) % 2 ^ 64 = 0)
    (hm : m = a0 * n0inv % 2 ^ 64)
    (h0 : c0 * 2 ^ 64 + lo = m * n0 + a0)
    (h1 : c1 * 2 ^ 64 + b1 = m * n1 + a1 + c0)
    (h2 : c2 * 2 ^ 64 + b2 = m * n2 + a2 + c1)
    (h3 : c3 * 2 ^ 64 + b3 = m * n3 + a3 + c2)
    (h4 : c4 * 2 ^ 64 + b4 = m * n4 + a4 + c3)
    (h5 : c5 * 2 ^ 64 + b5 = m * n5 + a5 + c4)
    (h6 : e' * 2 ^ 64 + b6 = a6 + c5 + e)
    (hlo : lo < 2 ^ 64) (hc : c5 < 2 ^ 64) (ha : a6 < 2 ^ 64) (he : e ≤ 1) :
    e' ≤ 1 ∧
    a0 + a1 * 2 ^ 64 + a2 * 2 ^ 128 + a3 * 2 ^ 192 + a4 * 2 ^ 256 + a5 * 2 ^ 320 + a6 * 2 ^ 384 + e * 2 ^ 384 + m * (n0 + n1 * 2 ^ 64 + n2 * 2 ^ 128 + n3 * 2 ^ 192 + n4 * 2 ^ 256 + n5 * 2 ^ 320) =
      (b1 + b2 * 2 ^ 64 + b3 * 2 ^ 128 + b4 * 2 ^ 192 + b5 * 2 ^ 256 + b6 * 2 ^ 320 + e' * 2 ^ 384) * 2 ^ 64 := by
  have hz : (m * n0 + a0) % 2 ^ 64 = 0 := by
    rw [hm]; exact row_low_zero (2 ^ 64) n0inv n0 a0 hinv
  rw [mul_sum6 m n0 n1 n2 n3 n4 n5]
  constructor
  · omega
  · omega

/-- Kind: algebraic fact (the 6 rows of Montgomery reduction chained, on natural numbers).
    Says: given the 6 row equations, the input `t` (as 12 limbs) plus a multiple `M · N` of
    the modulus with `M < 2^384` equals the top window `q` times `2^384`.
    Does not say: anything about the final conditional subtraction (see `redc_final`). -/
theorem redc_chain6 {t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 N m0 m1 m2 m3 m4 m5 x0_1 x0_2 x0_3 x0_4 x0_5 x0_6 x1_1 x1_2 x1_3 x1_4 x1_5 x1_6 x2_1 x2_2 x2_3 x2_4 x2_5 x2_6 x3_1 x3_2 x3_3 x3_4 x3_5 x3_6 x4_1 x4_2 x4_3 x4_4 x4_5 x4_6 x5_1 x5_2 x5_3 x5_4 x5_5 x5_6 e0 e1 e2 e3 e4 e5 e6 : Nat}
    (E0 : t0 + t1 * 2 ^ 64 + t2 * 2 ^ 128 + t3 * 2 ^ 192 + t4 * 2 ^ 256 + t5 * 2 ^ 320 + t6 * 2 ^ 384 + e0 * 2 ^ 384 + m0 * N =
      (x0_1 + x0_2 * 2 ^ 64 + x0_3 * 2 ^ 128 + x0_4 * 2 ^ 192 + x0_5 * 2 ^ 256 + x0_6 * 2 ^ 320 + e1 * 2 ^ 384) * 2 ^ 64)
    (E1 : x0_1 + x0_2 * 2 ^ 64 + x0_3 * 2 ^ 128 + x0_4 * 2 ^ 192 + x0_5 * 2 ^ 256 + x0_6 * 2 ^ 320 + t7 * 2 ^ 384 + e1 * 2 ^ 384 + m1 * N =
      (x1_1 + x1_2 * 2 ^ 64 + x1_3 * 2 ^ 128 + x1_4 * 2 ^ 192 + x1_5 * 2 ^ 256 + x1_6 * 2 ^ 320 + e2 * 2 ^ 384) * 2 ^ 64)
    (E2 : x1_1 + x1_2 * 2 ^ 64 + x1_3 * 2 ^ 128 + x1_4 * 2 ^ 192 + x1_5 * 2 ^ 256 + x1_6 * 2 ^ 320 + t8 * 2 ^ 384 + e2 * 2 ^ 384 + m2 * N =
      (x2_1 + x2_2 * 2 ^ 64 + x2_3 * 2 ^ 128 + x2_4 * 2 ^ 192 + x2_5 * 2 ^ 256 + x2_6 * 2 ^ 320 + e3 * 2 ^ 384) * 2 ^ 64)
    (E3 : x2_1 + x2_2 * 2 ^ 64 + x2_3 * 2 ^ 128 + x2_4 * 2 ^ 192 + x2_5 * 2 ^ 256 + x2_6 * 2 ^ 320 + t9 * 2 ^ 384 + e3 * 2 ^ 384 + m3 * N =
      (x3_1 + x3_2 * 2 ^ 64 + x3_3 * 2 ^ 128 + x3_4 * 2 ^ 192 + x3_5 * 2 ^ 256 + x3_6 * 2 ^ 320 + e4 * 2 ^ 384) * 2 ^ 64)
    (E4 : x3_1 + x3_2 * 2 ^ 64 + x3_3 * 2 ^ 128 + x3_4 * 2 ^ 192 + x3_5 * 2 ^ 256 + x3_6 * 2 ^ 320 + t10 * 2 ^ 384 + e4 * 2 ^ 384 + m4 * N =
      (x4_1 + x4_2 * 2 ^ 64 + x4_3 * 2 ^ 128 + x4_4 * 2 ^ 192 + x4_5 * 2 ^ 256 + x4_6 * 2 ^ 320 + e5 * 2 ^ 384) * 2 ^ 64)
    (E5 : x4_1 + x4_2 * 2 ^ 64 + x4_3 * 2 ^ 128 + x4_4 * 2 ^ 192 + x4_5 * 2 ^ 256 + x4_6 * 2 ^ 320 + t11 * 2 ^ 384 + e5 * 2 ^ 384 + m5 * N =
      (x5_1 + x5_2 * 2 ^ 64 + x5_3 * 2 ^ 128 + x5_4 * 2 ^ 192 + x5_5 * 2 ^ 256 + x5_6 * 2 ^ 320 + e6 * 2 ^ 384) * 2 ^ 64)
    (he0 : e0 = 0) (hm0 : m0 < 2 ^ 64) (hm1 : m1 < 2 ^ 64) (hm2 : m2 < 2 ^ 64) (hm3 : m3 < 2 ^ 64) (hm4 : m4 < 2 ^ 64) (hm5 : m5 < 2 ^ 64) :
    (m0 + m1 * 2 ^ 64 + m2 * 2 ^ 128 + m3 * 2 ^ 192 + m4 * 2 ^ 256 + m5 * 2 ^ 320) < 2 ^ 384 ∧
    t0 + t1 * 2 ^ 64 + t2 * 2 ^ 128 + t3 * 2 ^ 192 + t4 * 2 ^ 256 + t5 * 2 ^ 320 + t6 * 2 ^ 384 + t7 * 2 ^ 448 + t8 * 2 ^ 512 + t9 * 2 ^ 576 + t10 * 2 ^ 640 + t11 * 2 ^ 704 + (m0 + m1 * 2 ^ 64 + m2 * 2 ^ 128 + m3 * 2 ^ 192 + m4 * 2 ^ 256 + m5 * 2 ^ 320) * N =
      (e6 * 2 ^ 384 + (x5_1 + x5_2 * 2 ^ 64 + x5_3 * 2 ^ 128 + x5_4 * 2 ^ 192 + x5_5 * 2 ^ 256 + x5_6 * 2 ^ 320)) * 2 ^ 384 := by
  rw [sum_mul6 m0 m1 m2 m3 m4 m5 N]
  constructor
  · omega
  · omega

#print axioms add_congr
#print axioms mul_congr
#print axioms mod_neg_unique
#print axioms neg_mul_mod
#print axioms mul_unit
#print axioms redc_lt_two
#print axioms redc_final
#print axioms redc_mod
#print axioms mod_of_lt_two
#print axioms lt_mul_radix
#print axioms mul_lt_mul_radix
#print axioms row_low_zero
#print axioms row_low_zero_gen
#print axioms one_lt_of_inv
#print axioms unit_of_inv
#print axioms value_lt
#print axioms value_zero
#print axioms value_mul
#print axioms value_toMont
#print axioms value_mul_R
#print axioms eq_value_of_mul_R
#print axioms cancel_R
#print axioms value_inj
#print axioms value_eq_zero_iff
#print axioms value_add
#print axioms value_sub
#print axioms value_neg
#print axioms exists_base_inv
#print axioms inv_mul
#print axioms exists_Rinv256
#print axioms exists_Rinv384
#print axioms mul_sum4
#print axioms sum_mul4
#print axioms redc_row4
#print axioms redc_chain4
#print axioms mul_sum6
#print axioms sum_mul6
#print axioms redc_row6
#print axioms redc_chain6

end EVMCleanroom.Precompiles.MontMath
