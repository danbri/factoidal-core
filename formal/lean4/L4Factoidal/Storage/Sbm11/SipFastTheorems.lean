/-
L4Factoidal.Storage.Sbm11.SipFastTheorems — the delta loops of sideways
information passing on machine words equal their `Nat` loops
(https://github.com/danbri/factoidal/issues/930).

* `candAt_eq`, `probeFast_eq`: the guarded candidate test and the pointer
  with its frequent case first are `q < cands.size && cands[q]! == w` and
  `probeFrom`.
* `deltaFindGoW_eq`: `Sip.deltaFindGoW` (byte position `USize`, previous
  value and accumulator `UInt64`, no fuel) equals `Sip.deltaFindGo` from the
  same state, with the fuel `b.size - i + 3`, when the bytes are fewer than
  `Sip.smallBytes`.
* `deltaGatherGoW_eq`: the same for `Sip.deltaGatherGo`.
* `deltaFindStartNat_eq`, `deltaGatherStartNat_eq`: the starts that `findWords`
  and `gatherWords` call equal the `Nat` loops with the fuel those used
  before (`b.size - i + 2` from byte `i + 1`), so `SipTheorems.findWords_spec`
  and `gatherWords_spec` hold of the word loops.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.Sip

namespace L4Factoidal.Storage.Sbm11.Sip

open L4Factoidal (two64)
open L4Factoidal.Storage.Sbm11.FrameWords (put64)

/-! ## The candidate pointer -/

theorem candAt_eq (cands : Array UInt64) (q : Nat) (w : UInt64) :
    candAt cands q w = (q < cands.size && cands[q]! == w) := by
  unfold candAt
  split
  · rename_i h
    simp [h]
  · rename_i h
    simp [h]

theorem probeFast_eq (cands : Array UInt64) (w : UInt64) (p : Nat) :
    probeFast cands w p = probeFrom cands w p := by
  unfold probeFast
  split
  · rename_i h
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true,
        beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨hlt, hpre⟩ := hc
      unfold probeFrom startFor
      have hs : (p ≤ cands.size && (p == 0 || cands[p - 1]! < w)) = true := by
        rcases hpre with h0 | h1
        · simp [h0]
        · have : p - 1 < cands.size := by omega
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
          refine ⟨by omega, Or.inr ?_⟩
          rw [getElem!_pos cands (p - 1) this]
          exact h1
      rw [if_pos hs]
      obtain ⟨k, hk⟩ : ∃ k, cands.size - p = k + 1 := ⟨cands.size - p - 1, by omega⟩
      show p = advGo cands w (cands.size - p) p
      rw [hk, advGo.eq_2]
      have : ¬ ((p < cands.size && cands[p]! < w) = true) := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
        intro _
        rw [getElem!_pos cands p h]
        exact hlt
      rw [if_neg this]
    · rfl
  · rfl

/-! ## Word arithmetic -/

theorem accCap_toNat : accCap.toNat = 144115188075855872 := rfl

theorem z_toNat (acc : UInt64) (x : UInt8) (ha : acc < accCap) (hx : x.toNat < 128) :
    (acc * 128 + x.toUInt64).toNat = acc.toNat * 128 + x.toNat := by
  have h1 : acc.toNat < 144115188075855872 := by
    have := UInt64.lt_iff_toNat_lt.mp ha; rwa [accCap_toNat] at this
  have h2 : x.toNat < 256 := x.toNat_lt
  rw [UInt64.toNat_add, UInt64.toNat_mul, UInt8.toNat_toUInt64]
  have : (128 : UInt64).toNat = 128 := rfl
  rw [this]
  have e1 : acc.toNat * 128 % 2 ^ 64 = acc.toNat * 128 := Nat.mod_eq_of_lt (by omega)
  rw [e1, Nat.mod_eq_of_lt (by omega)]

theorem cont_toNat (acc : UInt64) (x : UInt8) (ha : acc < accCap) (hx : ¬ x < 128) :
    (acc * 128 + (x - 128).toUInt64).toNat = acc.toNat * 128 + (x.toNat - 128) := by
  have h1 : acc.toNat < 144115188075855872 := by
    have := UInt64.lt_iff_toNat_lt.mp ha; rwa [accCap_toNat] at this
  have h2 : x.toNat < 256 := x.toNat_lt
  have hx' : 128 ≤ x.toNat := by
    have : ¬ x.toNat < 128 := fun h => hx (UInt8.lt_iff_toNat_lt.mpr h)
    omega
  have h3 : (x - 128).toNat = x.toNat - 128 := by
    rw [UInt8.toNat_sub_of_le]
    · rfl
    · exact UInt8.le_iff_toNat_le.mpr (by simpa using hx')
  rw [UInt64.toNat_add, UInt64.toNat_mul, UInt8.toNat_toUInt64, h3]
  have : (128 : UInt64).toNat = 128 := rfl
  rw [this]
  have e1 : acc.toNat * 128 % 2 ^ 64 = acc.toNat * 128 := Nat.mod_eq_of_lt (by omega)
  rw [e1, Nat.mod_eq_of_lt (by omega)]

theorem x_lt_iff (x : UInt8) : x < 128 ↔ x.toNat < 128 := by
  rw [UInt8.lt_iff_toNat_lt]; rfl

theorem even_iff (z : UInt64) : (z % 2 == 0) = true ↔ z.toNat % 2 = 0 := by
  rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_mod]
  rfl

theorem div2_toNat (z : UInt64) : (z / 2).toNat = z.toNat / 2 := by
  rw [UInt64.toNat_div]; rfl

/-- The even case: `prev ≤ prev + z / 2` exactly when the `Nat` sum is below
    `2 ^ 64`, and then the word is the sum. -/
theorem add_ok (prev h : UInt64) :
    (prev ≤ prev + h ↔ prev.toNat + h.toNat < two64) ∧
      (prev.toNat + h.toNat < two64 → (prev + h).toNat = prev.toNat + h.toNat) := by
  have hp := prev.toNat_lt
  have hh := h.toNat_lt
  have e : two64 = 2 ^ 64 := rfl
  rw [e]
  refine ⟨?_, fun hlt => ?_⟩
  · rw [UInt64.le_iff_toNat_le, UInt64.toNat_add]
    by_cases hlt : prev.toNat + h.toNat < 2 ^ 64
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · have : (prev.toNat + h.toNat) % 2 ^ 64 = prev.toNat + h.toNat - 2 ^ 64 := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [this]; omega
  · rw [UInt64.toNat_add, Nat.mod_eq_of_lt hlt]

/-- The odd case: `z / 2 + 1` is `(z + 1) / 2`, and `prev - (z / 2 + 1)` is
    exact when it is at most `prev`. -/
theorem odd_toNat (z : UInt64) (hodd : z.toNat % 2 ≠ 0) :
    (z / 2 + 1).toNat = (z.toNat + 1) / 2 := by
  have hz := z.toNat_lt
  rw [UInt64.toNat_add, div2_toNat]
  have : (1 : UInt64).toNat = 1 := rfl
  rw [this, Nat.mod_eq_of_lt (by omega)]
  omega

theorem sub_ok (prev h : UInt64) :
    (h ≤ prev ↔ h.toNat ≤ prev.toNat) ∧ (h ≤ prev → (prev - h).toNat = prev.toNat - h.toNat) :=
  ⟨UInt64.le_iff_toNat_le, fun hle => UInt64.toNat_sub_of_le _ _ hle⟩

theorem toUInt64_toNat (v : UInt64) : v.toNat.toUInt64 = v := by
  simp [Nat.toUInt64]

/-! ## Positions -/

/-- `i < b.usize` is `i.toNat < b.size` when the bytes are fewer than
    `smallBytes`. -/
theorem usize_lt_iff (b : ByteArray) (i : USize) (hb : b.size < smallBytes) :
    i < b.usize ↔ i.toNat < b.size := by
  have hs : b.usize.toNat = b.size := by
    simp only [ByteArray.usize, USize.toNat_ofNat', Nat.toUSize]
    apply Nat.mod_eq_of_lt
    have : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
      rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
    have : smallBytes = 2147483648 := rfl
    omega
  rw [USize.lt_iff_toNat_lt, hs]

theorem uget_eq (b : ByteArray) (i : USize) (h : i.toNat < b.size) :
    (b.uget i h).toNat = (b.get! i.toNat).toNat := by
  simp [ByteArray.uget, ByteArray.get!, getElem!_pos, h]

/-! ## The find loop -/

theorem usize_succ (b : ByteArray) (i : USize) (hb : b.size < smallBytes) (h : i.toNat < b.size) :
    (i + 1).toNat = i.toNat + 1 :=
  L4Factoidal.Prim.Bytes.usize_succ_toNat ((usize_lt_iff b i hb).mpr h)

/-- **The find loop on words** equals the `Nat` find loop from the same
    state, with the fuel `b.size - i + 3`. -/
theorem deltaFindGoW_eq (b : ByteArray) (lo hi : Nat) (cands : Array UInt64) (hb : b.size < smallBytes) :
    ∀ n (i : USize) idx prev acc p pos out, b.size - i.toNat = n →
      deltaFindGoW b lo hi cands idx prev i acc p pos out =
        deltaFindGo b lo hi cands (b.size - i.toNat + 3) idx prev.toNat i.toNat acc.toNat p pos out := by
  intro n
  induction n with
  | zero =>
    intro i idx prev acc p pos out hn
    rw [deltaFindGoW, show b.size - i.toNat + 3 = (b.size - i.toNat + 2) + 1 by omega, deltaFindGo.eq_2]
    have h1 : ¬ i < b.usize := by rw [usize_lt_iff b i hb]; omega
    have h2 : ¬ i.toNat < b.size := by omega
    simp only [h1, h2, dite_false, if_false]
  | succ n ih =>
    intro i idx prev acc p pos out hn
    have hib : i.toNat < b.size := by omega
    have hiu : i < b.usize := (usize_lt_iff b i hb).mpr hib
    have hs := usize_succ b i hb hib
    have ih' : ∀ idx prev acc p pos out,
        deltaFindGoW b lo hi cands idx prev (i + 1) acc p pos out =
          deltaFindGo b lo hi cands (b.size - i.toNat + 2) idx prev.toNat (i.toNat + 1) acc.toNat p pos out := by
      intro idx prev acc p pos out
      rw [ih (i + 1) idx prev acc p pos out (by rw [hs]; omega), hs]
      congr 1
      omega
    rw [deltaFindGoW]
    by_cases hidx : idx ≥ hi
    · rw [if_pos hidx, show b.size - i.toNat + 3 = (b.size - i.toNat + 2) + 1 by omega, deltaFindGo.eq_2,
        if_pos hidx]
    rw [if_neg hidx, dif_pos hiu]
    by_cases hacc : acc < accCap
    case neg => rw [if_neg hacc]
    rw [if_pos hacc, show b.size - i.toNat + 3 = (b.size - i.toNat + 2) + 1 by omega, deltaFindGo.eq_2,
      if_neg hidx, if_pos hib]
    have hxe := uget_eq b i hib
    generalize b.uget i _ = x at hxe ⊢
    rw [← hxe]
    by_cases hx : x < 128
    case neg =>
      have hxn : ¬ x.toNat < 128 := fun h => hx ((x_lt_iff x).mpr h)
      rw [if_neg hx, if_neg hxn, ih', cont_toNat acc x hacc hx]
    have hxn : x.toNat < 128 := (x_lt_iff x).mp hx
    rw [if_pos hx, if_pos hxn]
    have hz := z_toNat acc x hacc hxn
    generalize acc * 128 + x.toUInt64 = z at hz ⊢
    rw [← hz]
    by_cases he : z.toNat % 2 = 0
    · have he' : (z % 2 == 0) = true := (even_iff z).mpr he
      rw [if_pos he']
      simp only [he, beq_self_eq_true, if_true]
      have ha := add_ok prev (z / 2)
      rw [div2_toNat] at ha
      by_cases hok : prev ≤ prev + z / 2
      · have hlt := ha.1.mp hok
        have hv := ha.2 hlt
        rw [if_pos hok, if_pos hlt]
        simp only
        rw [← hv, toUInt64_toNat, probeFast_eq, candAt_eq]
        split <;> (try split) <;> rw [ih'] <;> rfl
      · have hlt : ¬ prev.toNat + z.toNat / 2 < two64 := fun h => hok (ha.1.mpr h)
        rw [if_neg hok, if_neg hlt]
    · have he' : ¬ (z % 2 == 0) = true := fun h => he ((even_iff z).mp h)
      have he2 : (z.toNat % 2 == 0) = false := by simpa using he
      rw [if_neg he']
      simp only [he2, Bool.false_eq_true, if_false]
      have ho := odd_toNat z he
      have hsb := sub_ok prev (z / 2 + 1)
      rw [ho] at hsb
      by_cases hok : z / 2 + 1 ≤ prev
      · have hle := hsb.1.mp hok
        have hv := hsb.2 hok
        rw [if_pos hok, if_pos hle]
        simp only
        rw [← hv, toUInt64_toNat, probeFast_eq, candAt_eq]
        split <;> (try split) <;> rw [ih'] <;> rfl
      · have hle : ¬ (z.toNat + 1) / 2 ≤ prev.toNat := fun h => hok (hsb.1.mpr h)
        rw [if_neg hok, if_neg hle]

/-! ## The find loop with the candidate in the loop state -/

theorem candAt_cAt (cands : Array UInt64) (q : Nat) (w : UInt64) :
    candAt cands q w = (q < cands.size && cAt cands q == w) := by
  unfold candAt cAt
  by_cases h : q < cands.size <;> simp [h]

/-- With the invariants, `probeFast` is the pointer itself when `isFast`
    holds and `probeFrom` otherwise. -/
theorem probeFast_isFast (cands : Array UInt64) (w : UInt64) (p : Nat) (c lc : UInt64)
    (hc : c = cAt cands p) (hlc : lc = lAt cands p) :
    probeFast cands w p = if isFast cands w p c lc then p else probeFrom cands w p := by
  subst hc hlc
  unfold probeFast isFast cAt lAt
  by_cases h : p < cands.size
  · rw [dif_pos h]
    by_cases hp : p = 0
    · subst hp
      simp [h]
    · have h1 : p - 1 < cands.size := by omega
      simp [h, hp, h1]
  · rw [dif_neg h]
    simp [h]

theorem deltaFindGoC_eq (b : ByteArray) (lo hi : Nat) (cands : Array UInt64) :
    ∀ n (i : USize) idx prev acc p (c lc : UInt64) pos out, b.size - i.toNat ≤ n →
      c = cAt cands p → lc = lAt cands p →
      deltaFindGoC b lo hi cands idx prev i acc p c lc pos out =
        deltaFindGoW b lo hi cands idx prev i acc p pos out := by
  intro n
  induction n with
  | zero =>
    intro i idx prev acc p c lc pos out hn hc hlc
    rw [deltaFindGoC, deltaFindGoW]
    have h1 : ¬ i < b.usize := fun h => by
      have := L4Factoidal.Prim.Bytes.usize_lt_size h; omega
    simp only [h1, dite_false]
  | succ n ih =>
    intro i idx prev acc p c lc pos out hn hc hlc
    rw [deltaFindGoC, deltaFindGoW]
    by_cases hidx : idx ≥ hi
    · rw [if_pos hidx, if_pos hidx]
    rw [if_neg hidx, if_neg hidx]
    by_cases hiu : i < b.usize
    case neg => rw [dif_neg hiu, dif_neg hiu]
    rw [dif_pos hiu, dif_pos hiu]
    have hib := L4Factoidal.Prim.Bytes.usize_lt_size hiu
    have hs := L4Factoidal.Prim.Bytes.usize_succ_toNat hiu
    have hn' : b.size - (i + 1).toNat ≤ n := by omega
    by_cases hacc : acc < accCap
    case neg => rw [if_neg hacc, if_neg hacc]
    rw [if_pos hacc, if_pos hacc]
    generalize b.uget i _ = x
    by_cases hx : x < 128
    case neg =>
      rw [if_neg hx, if_neg hx]
      exact ih (i + 1) idx prev _ p c lc pos out hn' hc hlc
    rw [if_pos hx, if_pos hx]
    generalize acc * 128 + x.toUInt64 = z
    subst hc hlc
    cases he : (z % 2 == 0)
    · simp only [he, Bool.false_eq_true, if_false]
      by_cases hok : z / 2 + 1 ≤ prev
      · simp only [hok, if_true]
        by_cases hlo : idx ≥ lo
        · simp only [hlo, if_true]
          rw [probeFast_isFast cands _ p _ _ rfl rfl, candAt_cAt]
          by_cases hf : isFast cands (prev - (z / 2 + 1)) p (cAt cands p) (lAt cands p) = true
          · simp only [hf, if_true]
            by_cases hcond : (decide (p < cands.size) && cAt cands p == prev - (z / 2 + 1)) = true
            · simp only [hcond, if_true]
              exact ih _ _ _ _ _ _ _ _ _ hn' rfl rfl
            · simp only [hcond]
              exact ih _ _ _ _ _ _ _ _ _ hn' rfl rfl
          · simp only [hf, Bool.false_eq_true, if_false]
            generalize probeFrom cands (prev - (z / 2 + 1)) p = q
            by_cases hcond : (decide (q < cands.size) && cAt cands q == prev - (z / 2 + 1)) = true
            · simp only [hcond, if_true]
              exact ih _ _ _ _ _ _ _ _ _ hn' rfl rfl
            · simp only [hcond]
              exact ih _ _ _ _ _ _ _ _ _ hn' rfl rfl
        · simp only [hlo, if_false]
          exact ih _ _ _ _ _ _ _ _ _ hn' rfl rfl
      · simp [hok]
    · simp only [he, if_true]
      by_cases hok : prev ≤ prev + z / 2
      · simp only [hok, if_true]
        by_cases hlo : idx ≥ lo
        · simp only [hlo, if_true]
          rw [probeFast_isFast cands _ p _ _ rfl rfl, candAt_cAt]
          by_cases hf : isFast cands (prev + z / 2) p (cAt cands p) (lAt cands p) = true
          · simp only [hf, if_true]
            by_cases hcond : (decide (p < cands.size) && cAt cands p == prev + z / 2) = true
            · simp only [hcond, if_true]
              exact ih _ _ _ _ _ _ _ _ _ hn' rfl rfl
            · simp only [hcond]
              exact ih _ _ _ _ _ _ _ _ _ hn' rfl rfl
          · simp only [hf, Bool.false_eq_true, if_false]
            generalize probeFrom cands (prev + z / 2) p = q
            by_cases hcond : (decide (q < cands.size) && cAt cands q == prev + z / 2) = true
            · simp only [hcond, if_true]
              exact ih _ _ _ _ _ _ _ _ _ hn' rfl rfl
            · simp only [hcond]
              exact ih _ _ _ _ _ _ _ _ _ hn' rfl rfl
        · simp only [hlo, if_false]
          exact ih _ _ _ _ _ _ _ _ _ hn' rfl rfl
      · simp [hok]

/-! ## The gather loop -/

/-- **The gather loop on words** equals the `Nat` gather loop from the same
    state, with the fuel `b.size - i + 3`. -/
theorem deltaGatherGoW_eq (b : ByteArray) (pos : Array Nat) (hb : b.size < smallBytes) :
    ∀ n (i : USize) idx prev acc k out, b.size - i.toNat = n →
      deltaGatherGoW b pos idx prev i acc k out =
        deltaGatherGo b pos (b.size - i.toNat + 3) idx prev.toNat i.toNat acc.toNat k out := by
  intro n
  induction n with
  | zero =>
    intro i idx prev acc k out hn
    rw [deltaGatherGoW, show b.size - i.toNat + 3 = (b.size - i.toNat + 2) + 1 by omega, deltaGatherGo.eq_2]
    have h1 : ¬ i < b.usize := by rw [usize_lt_iff b i hb]; omega
    have h2 : ¬ i.toNat < b.size := by omega
    simp only [h1, h2, dite_false, if_false]
  | succ n ih =>
    intro i idx prev acc k out hn
    have hib : i.toNat < b.size := by omega
    have hiu : i < b.usize := (usize_lt_iff b i hb).mpr hib
    have hs := usize_succ b i hb hib
    have ih' : ∀ idx prev acc k out,
        deltaGatherGoW b pos idx prev (i + 1) acc k out =
          deltaGatherGo b pos (b.size - i.toNat + 2) idx prev.toNat (i.toNat + 1) acc.toNat k out := by
      intro idx prev acc k out
      rw [ih (i + 1) idx prev acc k out (by rw [hs]; omega), hs]
      congr 1
      omega
    rw [deltaGatherGoW]
    by_cases hk : k ≥ pos.size
    · rw [if_pos hk, show b.size - i.toNat + 3 = (b.size - i.toNat + 2) + 1 by omega, deltaGatherGo.eq_2,
        if_pos hk]
    rw [if_neg hk, dif_pos hiu]
    by_cases hacc : acc < accCap
    case neg => rw [if_neg hacc]
    rw [if_pos hacc, show b.size - i.toNat + 3 = (b.size - i.toNat + 2) + 1 by omega, deltaGatherGo.eq_2,
      if_neg hk, if_pos hib]
    have hxe := uget_eq b i hib
    generalize b.uget i _ = x at hxe ⊢
    rw [← hxe]
    by_cases hx : x < 128
    case neg =>
      have hxn : ¬ x.toNat < 128 := fun h => hx ((x_lt_iff x).mpr h)
      rw [if_neg hx, if_neg hxn, ih', cont_toNat acc x hacc hx]
    have hxn : x.toNat < 128 := (x_lt_iff x).mp hx
    rw [if_pos hx, if_pos hxn]
    have hz := z_toNat acc x hacc hxn
    generalize acc * 128 + x.toUInt64 = z at hz ⊢
    rw [← hz]
    by_cases he : z.toNat % 2 = 0
    · have he' : (z % 2 == 0) = true := (even_iff z).mpr he
      rw [if_pos he']
      simp only [he, beq_self_eq_true, if_true]
      have ha := add_ok prev (z / 2)
      rw [div2_toNat] at ha
      by_cases hok : prev ≤ prev + z / 2
      · have hlt := ha.1.mp hok
        have hv := ha.2 hlt
        rw [if_pos hok, if_pos hlt]
        simp only
        rw [← hv, toUInt64_toNat]
        split <;> rw [ih'] <;> rfl
      · have hlt : ¬ prev.toNat + z.toNat / 2 < two64 := fun h => hok (ha.1.mpr h)
        rw [if_neg hok, if_neg hlt]
    · have he' : ¬ (z % 2 == 0) = true := fun h => he ((even_iff z).mp h)
      have he2 : (z.toNat % 2 == 0) = false := by simpa using he
      rw [if_neg he']
      simp only [he2, Bool.false_eq_true, if_false]
      have ho := odd_toNat z he
      have hsb := sub_ok prev (z / 2 + 1)
      rw [ho] at hsb
      by_cases hok : z / 2 + 1 ≤ prev
      · have hle := hsb.1.mp hok
        have hv := hsb.2 hok
        rw [if_pos hok, if_pos hle]
        simp only
        rw [← hv, toUInt64_toNat]
        split <;> rw [ih'] <;> rfl
      · have hle : ¬ (z.toNat + 1) / 2 ≤ prev.toNat := fun h => hok (hsb.1.mpr h)
        rw [if_neg hok, if_neg hle]

/-! ## The gather loop with the next wanted row in the loop state -/

theorem posAt_eq (pos : Array Nat) (k : Nat) : posAt pos k = pos[k]! := by
  unfold posAt
  by_cases h : k < pos.size
  · simp [h]
  · rw [dif_neg h]
    simp [getElem!_neg pos k h]

theorem deltaGatherGoK_eq (b : ByteArray) (pos : Array Nat) :
    ∀ n (i : USize) idx prev acc k nk out, b.size - i.toNat ≤ n → nk = posAt pos k →
      deltaGatherGoK b pos idx prev i acc k nk out = deltaGatherGoW b pos idx prev i acc k out := by
  intro n
  induction n with
  | zero =>
    intro i idx prev acc k nk out hn hnk
    rw [deltaGatherGoK, deltaGatherGoW]
    have h1 : ¬ i < b.usize := fun h => by
      have := L4Factoidal.Prim.Bytes.usize_lt_size h; omega
    simp only [h1, dite_false]
  | succ n ih =>
    intro i idx prev acc k nk out hn hnk
    rw [deltaGatherGoK, deltaGatherGoW]
    by_cases hk : k ≥ pos.size
    · rw [if_pos hk, if_pos hk]
    rw [if_neg hk, if_neg hk]
    by_cases hiu : i < b.usize
    case neg => rw [dif_neg hiu, dif_neg hiu]
    rw [dif_pos hiu, dif_pos hiu]
    have hib := L4Factoidal.Prim.Bytes.usize_lt_size hiu
    have hs := L4Factoidal.Prim.Bytes.usize_succ_toNat hiu
    have hn' : b.size - (i + 1).toNat ≤ n := by omega
    by_cases hacc : acc < accCap
    case neg => rw [if_neg hacc, if_neg hacc]
    rw [if_pos hacc, if_pos hacc]
    generalize b.uget i _ = x
    by_cases hx : x < 128
    case neg =>
      rw [if_neg hx, if_neg hx]
      exact ih (i + 1) idx prev _ k nk out hn' hnk
    rw [if_pos hx, if_pos hx]
    generalize acc * 128 + x.toUInt64 = z
    have hnk' : nk = pos[k]! := by rw [hnk, posAt_eq]
    cases he : (z % 2 == 0)
    · simp only [he, Bool.false_eq_true, if_false]
      by_cases hok : z / 2 + 1 ≤ prev
      · simp only [hok, if_true]
        by_cases hidx : idx = nk
        · have hb : (idx == pos[k]!) = true := by rw [← hnk']; simpa using hidx
          have ha : (idx == nk) = true := by simpa using hidx
          simp only [ha, hb, if_true]
          exact ih _ _ _ _ _ _ _ hn' rfl
        · have hb : (idx == pos[k]!) = false := by rw [← hnk']; simpa using hidx
          have ha : (idx == nk) = false := by simpa using hidx
          simp only [ha, hb, Bool.false_eq_true, if_false]
          exact ih _ _ _ _ _ _ _ hn' hnk
      · simp [hok]
    · simp only [he, if_true]
      by_cases hok : prev ≤ prev + z / 2
      · simp only [hok, if_true]
        by_cases hidx : idx = nk
        · have hb : (idx == pos[k]!) = true := by rw [← hnk']; simpa using hidx
          have ha : (idx == nk) = true := by simpa using hidx
          simp only [ha, hb, if_true]
          exact ih _ _ _ _ _ _ _ hn' rfl
        · have hb : (idx == pos[k]!) = false := by rw [← hnk']; simpa using hidx
          have ha : (idx == nk) = false := by simpa using hidx
          simp only [ha, hb, Bool.false_eq_true, if_false]
          exact ih _ _ _ _ _ _ _ hn' hnk
      · simp [hok]

/-! ## The starts -/

theorem toUSize_succ (b : ByteArray) (i : Nat) (hb : b.size < smallBytes) (hi : i < b.size) :
    (i + 1).toUSize.toNat = i + 1 := by
  simp only [Nat.toUSize, USize.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
  have : smallBytes = 2147483648 := rfl
  omega

/-- The start that `findWords` calls equals the `Nat` find loop with the
    fuel it had before the word loop. -/
theorem deltaFindStartNat_eq (b : ByteArray) (lo hi : Nat) (cands : Array UInt64) (i p : Nat) (hi' : i < b.size) :
    deltaFindStartNat b lo hi cands i p = deltaFindGo b lo hi cands (b.size - i + 2) 0 0 (i + 1) 0 p #[] .empty := by
  unfold deltaFindStartNat
  split
  · rename_i hb
    rw [deltaFindGoC_eq b lo hi cands _ (i + 1).toUSize 0 0 0 p _ _ #[] .empty (Nat.le_refl _) rfl rfl,
      deltaFindGoW_eq b lo hi cands hb _ (i + 1).toUSize 0 0 0 p #[] .empty rfl, toUSize_succ b i hb hi']
    congr 1
    omega
  · rfl

/-- The start that `gatherWords` calls equals the `Nat` gather loop with
    the fuel it had before the word loop. -/
theorem deltaGatherStartNat_eq (b : ByteArray) (pos : Array Nat) (i : Nat) (hi' : i < b.size) :
    deltaGatherStartNat b pos i =
      deltaGatherGo b pos (b.size - i + 2) 0 0 (i + 1) 0 0 (ByteArray.emptyWithCapacity (8 * pos.size)) := by
  unfold deltaGatherStartNat
  split
  · rename_i hb
    rw [deltaGatherGoK_eq b pos _ (i + 1).toUSize 0 0 0 0 _ _ (Nat.le_refl _) rfl,
      deltaGatherGoW_eq b pos hb _ (i + 1).toUSize 0 0 0 0 _ rfl, toUSize_succ b i hb hi']
    congr 1
    omega
  · rfl

#print axioms candAt_eq
#print axioms probeFast_eq
#print axioms deltaFindGoW_eq
#print axioms candAt_cAt
#print axioms probeFast_isFast
#print axioms deltaFindGoC_eq
#print axioms deltaGatherGoW_eq
#print axioms posAt_eq
#print axioms deltaGatherGoK_eq
#print axioms deltaFindStartNat_eq
#print axioms deltaGatherStartNat_eq

end L4Factoidal.Storage.Sbm11.Sip
