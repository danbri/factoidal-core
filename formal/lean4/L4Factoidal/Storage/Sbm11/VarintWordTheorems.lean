/-
L4Factoidal.Storage.Sbm11.VarintWordTheorems — proofs about `VarintWord`
(https://github.com/danbri/factoidal/issues/930).

* `lenMask_eq`: for a window whose bytes `0 .. n-1` have the continuation bit
  set and whose byte `n` has it clear, `lenMask (w ||| C7)` is the mask of
  the bytes `0 .. n` (`2 ^ (8 * n + 8) - 1`). Proof: `y ^^^ (y + 1)` has bit
  `i` set exactly when the bits of `y` below `i` are all set
  (`xor_add_one_bit`, from `BitVec.carry_succ_one`).
* `vVal_eq`: the value is the Horner form `hf` of the groups of the bytes
  `0 .. n`, one bit-level proof per `n` (`val_0` .. `val_7`).
* `hz_eq_hf`: the Horner form of the byte loop (`hz`: `acc * 128 + group`)
  equals `hf`.
* `fastRead_spec`: the two together, for the window of any `n < 8`, and
  `exists_term`: a window with `w ||| C7 ≠ allOnes` has such an `n`.
* `zz_spec`: `zzV` and `zzOk` are the sign cases of the zigzag step.

No `sorry`, no `native_decide`, no `partial`, no user `axiom`.
-/
import L4Factoidal.Storage.Sbm11.VarintWord

namespace L4Factoidal.Storage.Sbm11.VarintWord

/-- Byte `k` of the window `w` (little-endian order of the load). -/
def bt (w : UInt64) (k : Nat) : UInt8 := (w >>> UInt64.ofNat (8 * k)).toUInt8

/-- The seven-bit group of a byte, as a word. -/
def gb (x : UInt8) : UInt64 := x.toUInt64 &&& 127

/-- Horner form of the groups of bytes `j .. j + m`, written with shifts and
    ors, the first byte the most significant. -/
def hf (f : Nat → UInt8) : Nat → Nat → UInt64
  | j, 0 => gb (f j)
  | j, m + 1 => (gb (f j) <<< UInt64.ofNat (7 * (m + 1))) ||| hf f (j + 1) m

/-- The accumulation of the byte loop: `m` continuation bytes from `j`, then
    the last byte. -/
def hz (f : Nat → UInt8) : UInt64 → Nat → Nat → UInt64
  | acc, j, 0 => acc * 128 + (f j).toUInt64
  | acc, j, m + 1 => hz f (acc * 128 + (f j - 128).toUInt64) (j + 1) m

theorem xor_add_one_bit {w : Nat} (x : BitVec w) (i : Nat) (hi : i < w) :
    (x ^^^ (x + 1#w)).getLsbD i = decide (∀ j, j < i → x.getLsbD j = true) := by
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_add hi]
  cases i with
  | zero =>
    have hw : 0 < w := hi
    simp [hw]
  | succ i' =>
    rw [BitVec.carry_succ_one i' x (by omega)]
    simp only [BitVec.getLsbD_one, Nat.add_one_ne_zero, decide_false]
    have : (∀ j, j ≤ i' → x.getLsbD j = true) ↔ (∀ j, j < i' + 1 → x.getLsbD j = true) :=
      ⟨fun h j hj => h j (by omega), fun h j hj => h j (by omega)⟩
    cases hx : x.getLsbD (i'+1) <;> simp [this]

theorem bt_bit (w : UInt64) (k t : Nat) (hk : k < 8) (ht : t < 8) :
    (bt w k).toBitVec.getLsbD t = w.toBitVec.getLsbD (8 * k + t) := by
  unfold bt
  simp only [UInt64.toBitVec_toUInt8, BitVec.getLsbD_setWidth, UInt64.toBitVec_shiftRight,
    BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight]
  have : ((UInt64.ofNat (8 * k)).toBitVec % 64).toNat = 8 * k := by
    simp [UInt64.toBitVec_ofNat, BitVec.toNat_ofNat, BitVec.toNat_umod]
    omega
  rw [this]
  simp [ht, Nat.add_comm]

theorem bt_elem (w : UInt64) (k t : Nat) (hk : k < 8) (ht : t < 8) :
    (bt w k).toBitVec[t]'(by omega) = w.toBitVec[8 * k + t]'(by omega) := by
  rw [← BitVec.getLsbD_eq_getElem (by omega), ← BitVec.getLsbD_eq_getElem (by omega)]
  exact bt_bit w k t hk ht

theorem C7_bit : ∀ j, j < 64 → C7.toBitVec.getLsbD j = decide (j % 8 ≠ 7) := by decide

theorem u8_bit7_of_lt (x : UInt8) (h : x < 128) : x.toBitVec.getLsbD 7 = false := by
  have h1 := UInt8.lt_iff_toNat_lt.mp h
  have h2 : x.toNat < 128 := by simpa using h1
  show Nat.testBit x.toNat 7 = false
  exact Nat.testBit_lt_two_pow (by omega)

theorem u8_bit7_of_ge (x : UInt8) (h : ¬ x < 128) : x.toBitVec.getLsbD 7 = true := by
  have h1 : ¬ x.toNat < 128 := fun h' => h (UInt8.lt_iff_toNat_lt.mpr (by simpa using h'))
  have h3 := x.toNat_lt
  show Nat.testBit x.toNat 7 = true
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_true_eq]
  omega

theorem lenMask_eq (w : UInt64) (n : Nat) (hn : n < 8)
    (hc : ∀ k, k < n → ¬ bt w k < 128) (ht : bt w n < 128) :
    lenMask (w ||| C7) = UInt64.ofNat (2 ^ (8 * n + 8) - 1) := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold lenMask
  rw [UInt64.toBitVec_xor, UInt64.toBitVec_add]
  have h1 : UInt64.toBitVec 1 = 1#64 := rfl
  rw [h1, xor_add_one_bit _ i hi]
  show _ = (BitVec.ofNat 64 (2 ^ (8 * n + 8) - 1)).getLsbD i
  simp only [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  simp only [UInt64.toBitVec_or, BitVec.getLsbD_or]
  have hb : 8 * n + 8 ≤ 64 := by omega
  by_cases hlt : i < 8 * n + 8
  · simp only [hlt, decide_true, Bool.and_true, hi]
    rw [decide_eq_true_iff]
    intro j hj
    rw [C7_bit j (by omega)]
    by_cases hj7 : j % 8 = 7
    · have hjk : j = 8 * (j / 8) + 7 := by omega
      have hk : j / 8 < n := by omega
      have := bt_bit w (j / 8) 7 (by omega) (by omega)
      rw [hjk, ← this, u8_bit7_of_ge _ (hc _ hk)]
      simp
    · simp [hj7]
  · have : decide (i < 8 * n + 8) = false := by simp [hlt]
    simp only [this, Bool.and_false, hi]
    rw [decide_eq_false_iff_not]
    intro hall
    have := hall (8 * n + 7) (by omega)
    rw [C7_bit _ (by omega)] at this
    have e := bt_bit w n 7 (by omega) (by omega)
    rw [u8_bit7_of_lt _ ht] at e
    simp [e.symm] at this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem val_0 (w : UInt64) : vCompress (w &&& 0xff &&& C7) >>> 49 = hf (bt w) 0 0 := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [hf, gb, vCompress, C7]
  simp
  have hi64 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases hi64 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp (disch := omega) [bt_elem]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem val_1 (w : UInt64) : vCompress (w &&& 0xffff &&& C7) >>> 42 = hf (bt w) 0 1 := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [hf, gb, vCompress, C7]
  simp
  have hi64 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases hi64 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp (disch := omega) [bt_elem]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem val_2 (w : UInt64) : vCompress (w &&& 0xffffff &&& C7) >>> 35 = hf (bt w) 0 2 := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [hf, gb, vCompress, C7]
  simp
  have hi64 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases hi64 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp (disch := omega) [bt_elem]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem val_3 (w : UInt64) : vCompress (w &&& 0xffffffff &&& C7) >>> 28 = hf (bt w) 0 3 := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [hf, gb, vCompress, C7]
  simp
  have hi64 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases hi64 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp (disch := omega) [bt_elem]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem val_4 (w : UInt64) : vCompress (w &&& 0xffffffffff &&& C7) >>> 21 = hf (bt w) 0 4 := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [hf, gb, vCompress, C7]
  simp
  have hi64 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases hi64 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp (disch := omega) [bt_elem]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem val_5 (w : UInt64) : vCompress (w &&& 0xffffffffffff &&& C7) >>> 14 = hf (bt w) 0 5 := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [hf, gb, vCompress, C7]
  simp
  have hi64 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases hi64 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp (disch := omega) [bt_elem]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem val_6 (w : UInt64) : vCompress (w &&& 0xffffffffffffff &&& C7) >>> 7 = hf (bt w) 0 6 := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [hf, gb, vCompress, C7]
  simp
  have hi64 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases hi64 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp (disch := omega) [bt_elem]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem val_7 (w : UInt64) : vCompress (w &&& 0xffffffffffffffff &&& C7) >>> 0 = hf (bt w) 0 7 := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [hf, gb, vCompress, C7]
  simp
  have hi64 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases hi64 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp (disch := omega) [bt_elem]



theorem vLen_eq (n : Nat) (hn : n < 8) :
    vLen (UInt64.ofNat (2 ^ (8 * n + 8) - 1)) = UInt64.ofNat (n + 1) := by
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
  rcases this with h | h | h | h | h | h | h | h <;> subst h <;> decide

theorem toBitVec_ofNat' (s : Nat) : (UInt64.ofNat s).toBitVec = BitVec.ofNat 64 s := rfl

theorem shift_mod (s : Nat) (h : s < 64) : (UInt64.ofNat s).toBitVec % 64 = BitVec.ofNat 64 s := by
  rw [toBitVec_ofNat']
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_umod, BitVec.toNat_ofNat]
  omega

theorem shl_shl (a : UInt64) (s1 s2 : Nat) (h : s1 + s2 < 64) :
    (a <<< UInt64.ofNat s1) <<< UInt64.ofNat s2 = a <<< UInt64.ofNat (s1 + s2) := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_shiftLeft]
  rw [shift_mod s1 (by omega), shift_mod s2 (by omega), shift_mod (s1 + s2) h]
  rw [BitVec.shiftLeft_eq', BitVec.shiftLeft_eq', BitVec.shiftLeft_eq']
  simp only [BitVec.toNat_ofNat]
  have e1 : s1 % 2 ^ 64 = s1 := Nat.mod_eq_of_lt (by omega)
  have e2 : s2 % 2 ^ 64 = s2 := Nat.mod_eq_of_lt (by omega)
  have e3 : (s1 + s2) % 2 ^ 64 = s1 + s2 := Nat.mod_eq_of_lt (by omega)
  rw [e1, e2, e3, BitVec.shiftLeft_add]

theorem shl_or (a b : UInt64) (s : UInt64) : (a ||| b) <<< s = (a <<< s) ||| (b <<< s) := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_shiftLeft, UInt64.toBitVec_or]
  exact BitVec.shiftLeft_or_distrib _ _ _

theorem mul128_eq_shl (a : UInt64) : a * (128 : UInt64) = a <<< (7 : UInt64) := by
  apply UInt64.eq_of_toBitVec_eq
  rw [UInt64.toBitVec_mul, UInt64.toBitVec_shiftLeft]
  have h7 : UInt64.toBitVec 7 % 64 = 7#64 := by decide
  have h128 : UInt64.toBitVec 128 = 128#64 := by decide
  rw [h7, h128, BitVec.shiftLeft_eq', BitVec.shiftLeft_eq_mul_twoPow]
  congr 1

theorem add_eq_or_shl (a c : UInt64) (hc : c < 128) :
    a * (128 : UInt64) + c = (a <<< (7 : UInt64)) ||| c := by
  rw [mul128_eq_shl]
  apply UInt64.eq_of_toBitVec_eq
  rw [UInt64.toBitVec_add, UInt64.toBitVec_or]
  apply BitVec.add_eq_or_of_and_eq_zero
  have hc' : c.toNat < 128 := by
    have := UInt64.lt_iff_toNat_lt.mp hc
    simpa using this
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, UInt64.toBitVec_shiftLeft]
  have h7 : UInt64.toBitVec 7 % 64 = 7#64 := by decide
  rw [h7, BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft]
  by_cases h : i < 7
  · simp [h]
  · have : c.toBitVec.getLsbD i = false := by
      show Nat.testBit c.toNat i = false
      exact Nat.testBit_lt_two_pow (by
        have : 2 ^ 7 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
        omega)
    simp [this]

theorem gb_toNat (x : UInt8) : (gb x).toNat = x.toNat % 128 := by
  unfold gb
  rw [UInt64.toNat_and]
  have : (127 : UInt64).toNat = 2 ^ 7 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  simp

theorem gb_lt (x : UInt8) : gb x < 128 := by
  apply UInt64.lt_iff_toNat_lt.mpr
  rw [gb_toNat]
  have : (128 : UInt64).toNat = 128 := by decide
  rw [this]; omega

theorem gb_of_lt (x : UInt8) (h : x < 128) : x.toUInt64 = gb x := by
  apply UInt64.toNat_inj.mp
  rw [gb_toNat]
  have := UInt8.lt_iff_toNat_lt.mp h
  simp at this ⊢
  omega

theorem gb_of_ge (x : UInt8) (h : ¬ x < 128) : (x - 128).toUInt64 = gb x := by
  apply UInt64.toNat_inj.mp
  rw [gb_toNat]
  have h1 : ¬ x.toNat < 128 := fun h' => h (UInt8.lt_iff_toNat_lt.mpr (by simpa using h'))
  have h3 := x.toNat_lt
  have : (x - 128).toNat = x.toNat - 128 := by
    rw [UInt8.toNat_sub_of_le]
    · rfl
    · exact UInt8.le_iff_toNat_le.mpr (by simp; omega)
  rw [UInt8.toNat_toUInt64, this]
  omega

theorem hz_eq_hf (f : Nat → UInt8) : ∀ (m : Nat) (acc : UInt64) (j : Nat), m ≤ 7 →
    (∀ t, t < m → ¬ f (j + t) < 128) → f (j + m) < 128 →
    hz f acc j m = (acc <<< UInt64.ofNat (7 * (m + 1))) ||| hf f j m := by
  intro m
  induction m with
  | zero =>
    intro acc j _ _ ht
    simp only [hz, hf, Nat.add_zero] at ht ⊢
    rw [gb_of_lt _ ht, add_eq_or_shl acc _ (gb_lt _)]
    rfl
  | succ m ih =>
    intro acc j hm hc ht
    have hj : ¬ f j < 128 := by simpa using hc 0 (by omega)
    simp only [hz, hf]
    have hc' : ∀ t, t < m → ¬ f (j + 1 + t) < 128 := fun t htm => by
      have := hc (t + 1) (by omega)
      rwa [show j + (t + 1) = j + 1 + t by omega] at this
    have ht' : f (j + 1 + m) < 128 := by
      rwa [show j + (m + 1) = j + 1 + m by omega] at ht
    rw [ih _ (j + 1) (by omega) hc' ht', gb_of_ge _ hj, add_eq_or_shl acc _ (gb_lt _), shl_or]
    have e1 : (7 : UInt64) = UInt64.ofNat 7 := rfl
    rw [e1, shl_shl _ 7 (7 * (m + 1)) (by omega), UInt64.or_assoc]
    congr 3
    omega

theorem vVal_eq (w : UInt64) (n : Nat) (hn : n < 8)
    (hc : ∀ k, k < n → ¬ bt w k < 128) (ht : bt w n < 128) :
    vVal w (lenMask (w ||| C7)) = hf (bt w) 0 n := by
  rw [lenMask_eq w n hn hc ht]
  unfold vVal
  rw [vLen_eq n hn]
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
  rcases this with h | h | h | h | h | h | h | h <;> subst h
  · exact val_0 w
  · exact val_1 w
  · exact val_2 w
  · exact val_3 w
  · exact val_4 w
  · exact val_5 w
  · exact val_6 w
  · exact val_7 w

theorem exists_term_aux (w : UInt64) (h : (w ||| C7) ≠ allOnes) : ∃ n, n < 8 ∧ bt w n < 128 := by
  by_cases hex : ∃ n, n < 8 ∧ bt w n < 128
  · exact hex
  exfalso
  have hne := hex
  apply h
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [UInt64.toBitVec_or, BitVec.getLsbD_or]
  show _ = (BitVec.allOnes 64).getLsbD j
  rw [C7_bit j hj, BitVec.getLsbD_allOnes]
  simp only [hj, decide_true]
  by_cases h7 : j % 8 = 7
  · have hjk : j = 8 * (j / 8) + 7 := by omega
    have hk : ¬ bt w (j / 8) < 128 := fun hh => hne ⟨j / 8, by omega, hh⟩
    have := bt_bit w (j / 8) 7 (by omega) (by omega)
    rw [hjk, ← this, u8_bit7_of_ge _ hk]
    simp
  · simp [h7]

theorem first_of_exists (P : Nat → Prop) : ∀ N, (∃ n, n < N ∧ P n) →
    ∃ n, n < N ∧ (∀ k, k < n → ¬ P k) ∧ P n := by
  intro N
  induction N with
  | zero => intro ⟨n, hn, _⟩; omega
  | succ N ih =>
    intro ⟨n, hn, hp⟩
    by_cases hex : ∃ m, m < N ∧ P m
    · obtain ⟨m, hm, hk, hpm⟩ := ih hex
      exact ⟨m, by omega, hk, hpm⟩
    · refine ⟨N, by omega, fun k hk hpk => hex ⟨k, hk, hpk⟩, ?_⟩
      have : n = N := by
        by_cases h : n < N
        · exact absurd ⟨n, h, hp⟩ hex
        · omega
      rwa [this] at hp

theorem exists_term (w : UInt64) (h : (w ||| C7) ≠ allOnes) :
    ∃ n, n < 8 ∧ (∀ k, k < n → ¬ bt w k < 128) ∧ bt w n < 128 :=
  first_of_exists (fun n => bt w n < 128) 8 (exists_term_aux w h)

theorem fastRead_spec (w : UInt64) (n : Nat) (hn : n < 8)
    (hc : ∀ k, k < n → ¬ bt w k < 128) (ht : bt w n < 128) :
    (w ||| C7) ≠ allOnes ∧ vLen (lenMask (w ||| C7)) = UInt64.ofNat (n + 1) ∧
      vVal w (lenMask (w ||| C7)) = hf (bt w) 0 n := by
  refine ⟨?_, ?_, vVal_eq w n hn hc ht⟩
  · intro hall
    have := congrArg (fun y => y.toBitVec.getLsbD (8 * n + 7)) hall
    simp only [UInt64.toBitVec_or, BitVec.getLsbD_or] at this
    rw [C7_bit _ (by omega)] at this
    have e := bt_bit w n 7 (by omega) (by omega)
    rw [u8_bit7_of_lt _ ht] at e
    revert this
    show _ → False
    intro this
    have h2 : (allOnes).toBitVec.getLsbD (8 * n + 7) = true := by
      show (BitVec.allOnes 64).getLsbD (8 * n + 7) = true
      rw [BitVec.getLsbD_allOnes]; simp; omega
    rw [h2] at this
    simp [e.symm] at this
  · rw [lenMask_eq w n hn hc ht]
    exact vLen_eq n hn

/-! ## The zigzag step without a branch on the sign -/

theorem and_one (z : UInt64) : z &&& 1 = z % 2 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_mod]
  simp [Nat.and_one_is_mod]

theorem shr_one (z : UInt64) : z >>> 1 = z / 2 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, UInt64.toNat_div]
  simp [Nat.shiftRight_eq_div_pow]

theorem xor_allOnes_sub (q : UInt64) : q ^^^ (0 - 1) = (0 - 1) - q := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_xor, UInt64.toBitVec_sub]
  have h0 : UInt64.toBitVec 0 = 0#64 := rfl
  have h1 : UInt64.toBitVec 1 = 1#64 := rfl
  simp only [h0, h1]
  have : (0#64 - 1#64) = BitVec.allOnes 64 := by decide
  rw [this, BitVec.xor_allOnes, BitVec.allOnes_sub_eq_not]

theorem zz_even (prev z : UInt64) (he : z % 2 = 0) :
    zzV prev z = prev + z / 2 ∧ zzOk prev z (zzV prev z) = decide (prev ≤ prev + z / 2) := by
  have h1 : z &&& 1 = 0 := by rw [and_one, he]
  have h2 : z >>> 1 = z / 2 := shr_one z
  have hv : zzV prev z = prev + z / 2 := by
    unfold zzV; rw [h1, h2]
    have : (0 : UInt64) - 0 = 0 := rfl
    rw [this]
    congr 1
    apply UInt64.toNat_inj.mp
    simp
  refine ⟨hv, ?_⟩
  unfold zzOk; rw [hv, h1]
  have : decide (prev + z / 2 < prev) = !decide (prev ≤ prev + z / 2) := by
    by_cases h : prev ≤ prev + z / 2
    · have : ¬ prev + z / 2 < prev := Nat.not_lt.mpr (UInt64.le_iff_toNat_le.mp h) |> fun x => by
        intro hh; exact absurd (UInt64.lt_iff_toNat_lt.mp hh) (by have := UInt64.le_iff_toNat_le.mp h; omega)
      simp [h, this]
    · have : prev + z / 2 < prev := by
        have := Nat.lt_of_not_le (fun hh => h (UInt64.le_iff_toNat_le.mpr hh))
        exact UInt64.lt_iff_toNat_lt.mpr this
      simp [h, this]
  rw [this]
  simp

theorem alg1 (prev q : UInt64) : prev + ((0 - 1) - q) = prev - (q + 1) := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_sub]
  have h0 : UInt64.toBitVec 0 = 0#64 := rfl
  have h1 : UInt64.toBitVec 1 = 1#64 := rfl
  simp only [h0, h1]
  bv_omega

theorem sub_lt_iff (prev c : UInt64) (hc : 0 < c.toNat) :
    decide (prev - c < prev) = decide (c ≤ prev) := by
  by_cases h : c ≤ prev
  · have h' := UInt64.le_iff_toNat_le.mp h
    have e := UInt64.toNat_sub_of_le prev c h
    have : prev - c < prev := UInt64.lt_iff_toNat_lt.mpr (by rw [e]; omega)
    simp [h, this]
  · have h' : prev.toNat < c.toNat := Nat.lt_of_not_le (fun hh => h (UInt64.le_iff_toNat_le.mpr hh))
    have e := UInt64.toNat_sub prev c
    have hp := prev.toNat_lt
    have hcc := c.toNat_lt
    have : ¬ prev - c < prev := by
      intro hh
      have := UInt64.lt_iff_toNat_lt.mp hh
      rw [e] at this
      omega
    simp [h, this]

theorem zz_odd (prev z : UInt64) (ho : z % 2 ≠ 0) :
    zzV prev z = prev - (z / 2 + 1) ∧ zzOk prev z (zzV prev z) = decide (z / 2 + 1 ≤ prev) := by
  have hz : z % 2 = 1 := by
    have h0 : z.toNat % 2 ≠ 0 := by
      intro h; apply ho; apply UInt64.toNat_inj.mp; simp [UInt64.toNat_mod, h]
    apply UInt64.toNat_inj.mp
    simp [UInt64.toNat_mod]; omega
  have h1 : z &&& 1 = 1 := by rw [and_one, hz]
  have h2 : z >>> 1 = z / 2 := shr_one z
  have hv : zzV prev z = prev - (z / 2 + 1) := by
    unfold zzV; rw [h1, h2, xor_allOnes_sub, alg1]
  refine ⟨hv, ?_⟩
  unfold zzOk; rw [hv, h1]
  have hlt := z.toNat_lt
  have hq : (z / 2).toNat = z.toNat / 2 := by rw [UInt64.toNat_div]; rfl
  have e1 : (z / 2 + 1).toNat = z.toNat / 2 + 1 := by
    rw [UInt64.toNat_add, hq]; simp
    have hlt' : z.toNat < 18446744073709551616 := hlt
    omega
  rw [sub_lt_iff _ _ (by omega)]
  simp

#print axioms lenMask_eq
#print axioms vVal_eq
#print axioms hz_eq_hf
#print axioms exists_term
#print axioms fastRead_spec
#print axioms zz_even
#print axioms zz_odd

end L4Factoidal.Storage.Sbm11.VarintWord
