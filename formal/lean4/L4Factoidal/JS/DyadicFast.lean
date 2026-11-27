import L4Factoidal.XPath4.Atomic

/-!
# Scale invariance of exact rational rounding, for a fast `dyadic`

`XSD.roundRational p emin emax num den` rounds the positive rational
`num/den`. Its result depends only on the value `num/den`: scaling both
by the same positive `c` does not change it (`roundRational_scale`).

`JS.dyadic` writes `m × 2^(-k)` as the decimal `(m × 5^k) × 10^(-k)` and
gives it to `XPath4.floatOfParsed`, which prints `m × 5^k` in decimal for
its range guard and then rounds `(m × 5^k) / 10^k`. When `1 ≤ m < 2^64`
and `1 ≤ k ≤ 1100` both guards are false (`floatOfParsed_dyadic`), and
since `10^k = 2^k × 5^k` the rounding is that of `m / 2^k`. `JS.Number`
uses this for `dyadicFast` and its `@[csimp]` theorem.

Says: these equalities of functions on `Nat`, for the stated bounds.
Does not say: anything about other inputs of `floatOfParsed`.
-/

namespace L4Factoidal.JS

open L4Factoidal.XSD

/-- `geqRatio` with a common shift: for any `M` with `M + k ≥ 0`. -/
theorem geqRatio_shift (a b M : Nat) (k : Int) (hM : 0 ≤ (M : Int) + k) :
    geqRatio a b k = decide (a * 2 ^ M ≥ b * 2 ^ ((M : Int) + k).toNat) := by
  unfold geqRatio
  by_cases hk : k ≥ 0
  · simp only [hk, if_true]
    have hx : ((M : Int) + k).toNat = k.toNat + M := by omega
    rw [hx, Nat.pow_add, ← Nat.mul_assoc]
    have hp : 0 < 2 ^ M := Nat.pow_pos (by omega)
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact (Nat.mul_le_mul_right_iff hp).symm
  · simp only [hk, if_false]
    have hx : 2 ^ M = 2 ^ (-k).toNat * 2 ^ ((M : Int) + k).toNat := by
      rw [← Nat.pow_add]; congr 1; omega
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    have hp : 0 < 2 ^ ((M : Int) + k).toNat := Nat.pow_pos (by omega)
    rw [hx, ← Nat.mul_assoc]
    exact (Nat.mul_le_mul_right_iff hp).symm

theorem geqRatio_antitone (a b : Nat) (j k : Int) (hjk : j ≤ k)
    (h : geqRatio a b k = true) : geqRatio a b j = true := by
  have hj := geqRatio_shift a b (j.natAbs + k.natAbs) j (by omega)
  have hk := geqRatio_shift a b (j.natAbs + k.natAbs) k (by omega)
  rw [hk] at h; rw [hj]
  simp only [decide_eq_true_eq] at h ⊢
  refine Nat.le_trans ?_ h
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right (by omega)
  omega

theorem geqRatio_scale (a b c : Nat) (hc : 0 < c) (k : Int) :
    geqRatio (a * c) (b * c) k = geqRatio a b k := by
  rw [geqRatio_shift (a * c) (b * c) k.natAbs k (by omega),
    geqRatio_shift a b k.natAbs k (by omega)]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [Nat.mul_right_comm a, Nat.mul_right_comm b]
  exact Nat.mul_le_mul_right_iff hc

/-- `k` is `⌊log₂(a/b)⌋` in the sense of `geqRatio`. -/
def IsFloorLog2 (a b : Nat) (k : Int) : Prop :=
  geqRatio a b k = true ∧ geqRatio a b (k + 1) = false

theorem isFloorLog2_unique (a b : Nat) (k1 k2 : Int)
    (h1 : IsFloorLog2 a b k1) (h2 : IsFloorLog2 a b k2) : k1 = k2 := by
  rcases Int.lt_trichotomy k1 k2 with hlt | heq | hgt
  · have := geqRatio_antitone a b (k1 + 1) k2 (by omega) h2.1
    rw [h1.2] at this; contradiction
  · exact heq
  · have := geqRatio_antitone a b (k2 + 1) k1 (by omega) h1.1
    rw [h2.2] at this; contradiction

theorem floorLog2Ratio_spec (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    IsFloorLog2 a b (floorLog2Ratio a b) := by
  have hla := Nat.log2_self_le (n := a) (by omega)
  have hua := Nat.lt_log2_self (n := a)
  have hlb := Nat.log2_self_le (n := b) (by omega)
  have hub := Nat.lt_log2_self (n := b)
  have hk0 : ((bitlen a : Int) - (bitlen b : Int)) =
      (a.log2 : Int) - (b.log2 : Int) := by
    simp only [bitlen]
    have : (a == 0) = false := by simp; omega
    have : (b == 0) = false := by simp; omega
    simp only [*, Bool.false_eq_true, if_false]
    omega
  -- geq at k0 - 1
  have hlo : geqRatio a b ((a.log2 : Int) - (b.log2 : Int) - 1) = true := by
    rw [geqRatio_shift a b (b.log2 + 1) _ (by omega)]
    have hx : (((b.log2 + 1 : Nat) : Int) + ((a.log2 : Int) - (b.log2 : Int) - 1)).toNat
        = a.log2 := by omega
    rw [hx]; simp only [decide_eq_true_eq]
    calc b * 2 ^ a.log2 ≤ 2 ^ (b.log2 + 1) * 2 ^ a.log2 :=
          Nat.mul_le_mul_right _ (Nat.le_of_lt hub)
      _ = 2 ^ a.log2 * 2 ^ (b.log2 + 1) := Nat.mul_comm _ _
      _ ≤ a * 2 ^ (b.log2 + 1) := Nat.mul_le_mul_right _ hla
  -- not geq at k0 + 1
  have hhi : geqRatio a b ((a.log2 : Int) - (b.log2 : Int) + 1) = false := by
    rw [geqRatio_shift a b b.log2 _ (by omega)]
    have hx : ((b.log2 : Int) + ((a.log2 : Int) - (b.log2 : Int) + 1)).toNat
        = a.log2 + 1 := by omega
    rw [hx]; simp only [decide_eq_false_iff_not, Nat.not_le]
    calc a * 2 ^ b.log2 < 2 ^ (a.log2 + 1) * 2 ^ b.log2 :=
          Nat.mul_lt_mul_of_pos_right hua (Nat.pow_pos (by omega))
      _ = 2 ^ b.log2 * 2 ^ (a.log2 + 1) := Nat.mul_comm _ _
      _ ≤ b * 2 ^ (a.log2 + 1) := Nat.mul_le_mul_right _ hlb
  unfold floorLog2Ratio
  simp only [hk0]
  split
  · rename_i h
    exact ⟨h, hhi⟩
  · rename_i h
    refine ⟨hlo, ?_⟩
    simp only [Int.sub_add_cancel]
    simpa using h

theorem floorLog2Ratio_scale (a b c : Nat) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    floorLog2Ratio (a * c) (b * c) = floorLog2Ratio a b := by
  apply isFloorLog2_unique a b
  · have h := floorLog2Ratio_spec (a * c) (b * c) (Nat.mul_pos ha hc) (Nat.mul_pos hb hc)
    unfold IsFloorLog2 at h ⊢
    rw [geqRatio_scale a b c hc, geqRatio_scale a b c hc] at h
    exact h
  · exact floorLog2Ratio_spec a b ha hb

theorem roundTiesEven_scale (n d c : Nat) (hc : 0 < c) :
    roundTiesEven (n * c) (d * c) = roundTiesEven n d := by
  unfold roundTiesEven
  rw [Nat.mul_div_mul_right n d hc, Nat.mul_mod_mul_right]
  have h1 : (2 * (n % d * c) < d * c) = (2 * (n % d) < d) := by
    rw [← Nat.mul_assoc]; exact propext (Nat.mul_lt_mul_right hc)
  have h2 : (2 * (n % d * c) > d * c) = (2 * (n % d) > d) := by
    rw [← Nat.mul_assoc]; exact propext (Nat.mul_lt_mul_right hc)
  simp only [h1, h2]

theorem roundRational_scale (p : Nat) (emin emax : Int) (a b c : Nat)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    roundRational p emin emax (a * c) (b * c) = roundRational p emin emax a b := by
  unfold roundRational
  rw [floorLog2Ratio_scale a b c ha hb hc]
  have hr : ∀ e : Int,
      roundTiesEven (if e ≥ 0 then a * c else a * c * 2 ^ (-e).toNat)
        (if e ≥ 0 then b * c * 2 ^ e.toNat else b * c) =
      roundTiesEven (if e ≥ 0 then a else a * 2 ^ (-e).toNat)
        (if e ≥ 0 then b * 2 ^ e.toNat else b) := by
    intro e
    split
    · rw [Nat.mul_right_comm b c]; exact roundTiesEven_scale _ _ c hc
    · rw [Nat.mul_right_comm a c]; exact roundTiesEven_scale _ _ c hc
  simp only [hr]

theorem two_pow_le_five_pow (j n : Nat) (h : j ≤ 2 * n) : 2 ^ j ≤ 5 ^ n :=
  Nat.le_trans (Nat.pow_le_pow_right (by omega) h) (by
    rw [Nat.pow_mul]
    exact Nat.pow_le_pow_left (by decide : 2 ^ 2 ≤ 5) n)

theorem ten_pow_sub_le (m k t : Nat) (hm0 : 0 < m) (ht : t ≤ k) (hj : k - t ≤ 2 * t) :
    10 ^ (k - t) ≤ m * 5 ^ k :=
  calc 10 ^ (k - t) = 2 ^ (k - t) * 5 ^ (k - t) := by rw [← Nat.mul_pow]
    _ ≤ 5 ^ t * 5 ^ (k - t) := Nat.mul_le_mul_right _ (two_pow_le_five_pow _ _ hj)
    _ = 5 ^ k := by rw [← Nat.pow_add, Nat.add_sub_of_le ht]
    _ ≤ m * 5 ^ k := Nat.le_mul_of_pos_left _ hm0

/-- The two range guards of `floatOfParsed` are false on `(m × 5^k) × 10^(-k)`
for `1 ≤ m < 2^64` and `1 ≤ k ≤ 1100`, and the rounding is that of `m / 2^k`.

Says: `floatOfParsed` on this decimal equals rounding `m / 2^k` directly.
Does not say: anything for `k > 1100` or `m ≥ 2^64` (the fast path is not
taken there). -/
theorem floatOfParsed_dyadic (m k : Nat) (hm0 : 0 < m) (hm : m < 2 ^ 64)
    (hk1 : 1 ≤ k) (hk : k ≤ 1100) :
    XPath4.floatOfParsed (.num false (m * 5 ^ k) (-(k : Int))) =
      XPath4.fvalToFloat ⟨false, roundRational 53 (-1022) 1023 m (2 ^ k)⟩ := by
  have h5 : 0 < 5 ^ k := Nat.pow_pos (by omega)
  have hn0 : m * 5 ^ k ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hm0 h5)
  -- upper bound on the decimal length
  have hup : (toString (m * 5 ^ k)).length ≤ 400 + k := by
    simp only [Nat.toString_eq_repr]
    rw [Nat.length_repr_le_iff (by omega)]
    have h64 : 2 ^ 64 ≤ 10 ^ 64 := Nat.pow_le_pow_left (by omega) 64
    have h5k : 5 ^ k ≤ 10 ^ k := Nat.pow_le_pow_left (by omega) k
    calc m * 5 ^ k < 10 ^ 64 * 10 ^ k :=
          Nat.mul_lt_mul_of_lt_of_le (Nat.lt_of_lt_of_le hm h64) h5k
            (Nat.pow_pos (by omega))
      _ = 10 ^ (64 + k) := (Nat.pow_add _ _ _).symm
      _ ≤ 10 ^ (400 + k) := Nat.pow_le_pow_right (by omega) (by omega)
  -- lower bound on the decimal length
  have hlo : k ≤ 400 + (toString (m * 5 ^ k)).length := by
    simp only [Nat.toString_eq_repr]
    have hpos := Nat.length_repr_pos (n := m * 5 ^ k)
    by_cases hsmall : k ≤ 401
    · omega
    · apply Classical.byContradiction
      intro hc
      have hlen : (m * 5 ^ k).repr.length ≤ k - 401 := by omega
      rw [Nat.length_repr_le_iff (by omega)] at hlen
      -- 10^(k-401) = 2^(k-401) * 5^(k-401) ≤ 5^401 * 5^(k-401) = 5^k ≤ m * 5^k
      have : 10 ^ (k - 401) ≤ m * 5 ^ k := ten_pow_sub_le m k 401 hm0 (by omega) (by omega)
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlen this)
  unfold XPath4.floatOfParsed
  have hg1 : ((m * 5 ^ k != 0) &&
      decide (-(k : Int) + ((toString (m * 5 ^ k)).length : Int) > 400)) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right; omega
  have hg2 : ((m * 5 ^ k == 0) ||
      decide (-(k : Int) + ((toString (m * 5 ^ k)).length : Int) < -400)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
    exact ⟨hn0, by omega⟩
  simp only [hg1, hg2, Bool.false_eq_true, if_false]
  congr 1
  unfold canonDouble canon
  have hne : (m * 5 ^ k == 0) = false := by simpa using hn0
  have he : ¬ (-(k : Int) ≥ 0) := by omega
  simp only [hne, Bool.false_eq_true, if_false, he]
  have hkn : (-(-(k : Int))).toNat = k := by omega
  rw [hkn, show (10 : Nat) ^ k = 2 ^ k * 5 ^ k by rw [← Nat.mul_pow],
    roundRational_scale 53 (-1022) 1023 m (2 ^ k) (5 ^ k) hm0 (Nat.pow_pos (by omega)) h5]

end L4Factoidal.JS
