/-
L4Factoidal.Prim.Bytes — fixed-width little-endian access to a `ByteArray`
at `USize` byte positions, and the `USize` loop lemmas that go with it.

Tracking: https://github.com/danbri/factoidal/issues/797. Record and
measurements: docs/designissues/2026-10-12-lean-to-c-performance.md, section
"The support library". Owner, 2026-10-12: "library yes".

## Contents

- `ldU64LE d p`: the little-endian `UInt64` at byte `p`. Pure Lean: one
  bounds test in `USize`, then eight `ByteArray.uget`; clang -O3 compiles the
  fast path to two compares and ONE 8-byte load. Bytes past the end read 0
  (`ldU64LE_eq`: equal to `ldU64LESpec d p.toNat` at every position).
- `stU64LE b p x`: write `x` little-endian at byte `p`. An
  `@[extern c inline]` primitive: ONE bounds and overflow test, ONE
  exclusivity test (copy when shared), eight byte stores that clang merges
  into one 8-byte store. Its Lean body is `stU64LERef` (eight
  `ByteArray.uset`, each tested): when the eight bytes are not all inside
  `b`, the result is `b` unchanged.
- Lemmas over the Lean definitions: size preserved, read after write, other
  bytes unchanged, out of bounds is the identity, and the `USize` loop
  lemmas (successor, predecessor, bounds).

## What is proved and what is trusted

Every theorem here is about the Lean definitions. The compiled code of
`ldU64LE` is the Lean compiler's code for its body. The compiled code of
`stU64LE` is NOT its body: it is the C expression in its `@[extern c inline]`
attribute, which the Lean compiler pastes into each call site of the
generated C. That C expression is trusted. It is checked by the differential
test `Harness/PrimBytesTest.lean` (run by `tests/prim/run.sh`), which
compares `stU64LE` with `stU64LERef` (a separate, non-extern definition) on
random and edge-case inputs, natively and in the wasm32 build. The trusted
facts about the C expression are:

1. Byte order. The C writes byte `k` as `(uint8_t)(x >> 8k)`: the order is
   explicit in the source and does not depend on the host. On a
   little-endian host clang merges the eight stores into one; on a
   big-endian host it emits a byte swap and one store, or eight stores.
2. Bounds and wrap-around. The C test is `p + 8 <= size && p < p + 8` in
   `size_t`. `size_t` and `USize` have the same width on every Lean target
   (64 bits native, 32 bits on wasm32), so `p + 8` wraps in C exactly where
   it wraps in Lean, and the second test refuses it in both.
3. `lean_sarray_size` is `ByteArray.usize`. Lean defines `usize` as
   `size % 2 ^ numBits`; the runtime returns the stored size, which is
   smaller than `2 ^ numBits` for every array that can be allocated.
4. Sharing. When the array is not exclusive, the C copies it
   (`lean_copy_byte_array`, which consumes its argument), exactly as
   `lean_byte_array_uset` does for each `uset` of the reference.

## Width of `USize`

No theorem here assumes a 64-bit `USize`: each one holds for
`System.Platform.numBits = 32` (wasm32) and 64, by case analysis on
`System.Platform.numBits_eq` where the width matters. No executable code
here tests against `USize.size`: on a 64-bit host it is 2^64, a big `Nat`,
and the test would call GMP.
-/

namespace L4Factoidal.Prim.Bytes

/-! ## `USize` arithmetic, for both widths -/

/-- `i + 1` does not wrap when `i < n`. -/
theorem usize_succ_toNat {i n : USize} (h : i < n) : (i + 1).toNat = i.toNat + 1 := by
  have h1 := USize.lt_iff_toNat_lt.mp h
  have h2 := n.toNat_lt_size
  rw [USize.toNat_add, USize.toNat_one]
  apply Nat.mod_eq_of_lt
  simp only [USize.size] at h2
  omega

/-- `k - 1` does not wrap when `0 < k`. -/
theorem usize_pred_toNat {k : USize} (h : 0 < k) : (k - 1).toNat = k.toNat - 1 := by
  have h1 : (1 : USize) ≤ k := by
    have := USize.lt_iff_toNat_lt.mp h
    apply USize.le_iff_toNat_le.mpr
    simp only [USize.toNat_one]
    simp only [USize.toNat_zero] at this
    omega
  rw [USize.toNat_sub_of_le _ _ h1, USize.toNat_one]

/-- A position below `a.usize` is a valid `Nat` index of `a`. -/
theorem usize_lt_size {a : ByteArray} {i : USize} (h : i < a.usize) : i.toNat < a.size := by
  have h1 := USize.lt_iff_toNat_lt.mp h
  simp only [ByteArray.usize, USize.toNat_ofNat', Nat.toUSize] at h1
  have := Nat.mod_le a.size (2 ^ System.Platform.numBits)
  omega

/-- `8 ≤ 2 ^ numBits` on every platform. -/
theorem eight_le_pow : 8 ≤ 2 ^ System.Platform.numBits := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide

/-- `(8 : USize).toNat = 8` on every platform. -/
theorem usize_eight_toNat : (8 : USize).toNat = 8 := by simp

/-- When `p + 8` does not wrap (`p < p + 8`), neither does `p + k` for
    `k ≤ 8`. -/
theorem usize_add_small {p : USize} (h2 : p < p + 8) (k : USize) (hk : k.toNat ≤ 8) :
    (p + k).toNat = p.toNat + k.toNat := by
  have a2 := USize.lt_iff_toNat_lt.mp h2
  have hs := p.toNat_lt_size
  simp only [USize.size] at hs
  simp only [USize.toNat_add, usize_eight_toNat] at a2 ⊢
  have h8 := eight_le_pow
  have hw : p.toNat + 8 < 2 ^ System.Platform.numBits := by
    rcases Nat.lt_or_ge (p.toNat + 8) (2 ^ System.Platform.numBits) with h | h
    · exact h
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)] at a2; omega
  exact Nat.mod_eq_of_lt (by omega)

/-- The eight-byte window test of `ldU64LE` and `stU64LERef`, in `Nat`. -/
theorem window_of_test {d : ByteArray} {p : USize} (h1 : p + 8 ≤ d.usize) (h2 : p < p + 8) :
    p.toNat + 8 ≤ d.size := by
  have a1 := USize.le_iff_toNat_le.mp h1
  rw [usize_add_small h2 8 (by rw [usize_eight_toNat]; omega), usize_eight_toNat] at a1
  simp only [ByteArray.usize, USize.toNat_ofNat', Nat.toUSize] at a1
  have := Nat.mod_le d.size (2 ^ System.Platform.numBits)
  omega

/-- Byte `p + k` (`k < 8`) of the window is a valid index. -/
theorem window_lt {d : ByteArray} {p : USize} (h1 : p + 8 ≤ d.usize) (h2 : p < p + 8)
    (k : USize) (hk : k.toNat < 8) : (p + k).toNat < d.size := by
  rw [usize_add_small h2 k (by omega)]
  have := window_of_test h1 h2
  omega

/-- The window test holds for every array smaller than `USize.size` and every
    position with `p.toNat + 8 ≤ size`. -/
theorem test_of_window {d : ByteArray} {p : USize} (hs : d.size < USize.size)
    (hp : p.toNat + 8 ≤ d.size) : p + 8 ≤ d.usize ∧ p < p + 8 := by
  simp only [USize.size] at hs
  have hu : d.usize.toNat = d.size := by
    simp only [ByteArray.usize, USize.toNat_ofNat', Nat.toUSize]
    exact Nat.mod_eq_of_lt hs
  have he : (p + 8).toNat = p.toNat + 8 := by
    rw [USize.toNat_add, usize_eight_toNat]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨USize.le_iff_toNat_le.mpr ?_, USize.lt_iff_toNat_lt.mpr ?_⟩ <;> omega

/-! ## Reading -/

/-- Byte `i` of `d`, or 0 past the end. -/
@[inline] def getOr0 (d : ByteArray) (i : Nat) : UInt8 :=
  if h : i < d.size then d[i]'h else 0

theorem uget_eq_getOr0 (d : ByteArray) (u : USize) (h : u.toNat < d.size) :
    d.uget u h = getOr0 d u.toNat := by
  unfold getOr0; rw [dif_pos h]; rfl

/-- The specification of `ldU64LE`: the little-endian `UInt64` of bytes
    `i` to `i + 7` of `d`; bytes past the end read 0. -/
def ldU64LESpec (d : ByteArray) (i : Nat) : UInt64 :=
  (getOr0 d i).toUInt64 ||| ((getOr0 d (i+1)).toUInt64 <<< 8) |||
  ((getOr0 d (i+2)).toUInt64 <<< 16) ||| ((getOr0 d (i+3)).toUInt64 <<< 24) |||
  ((getOr0 d (i+4)).toUInt64 <<< 32) ||| ((getOr0 d (i+5)).toUInt64 <<< 40) |||
  ((getOr0 d (i+6)).toUInt64 <<< 48) ||| ((getOr0 d (i+7)).toUInt64 <<< 56)

/-- The little-endian `UInt64` at byte `p` of `d` (bytes past the end read
    0): one `USize` test, then eight `uget`. Equal to `ldU64LESpec d p.toNat`
    (`ldU64LE_eq`). -/
@[inline] def ldU64LE (d : ByteArray) (p : USize) : UInt64 :=
  if h : p + 8 ≤ d.usize ∧ p < p + 8 then
    (d.uget p (by have := window_of_test h.1 h.2; omega)).toUInt64 |||
    ((d.uget (p+1) (window_lt h.1 h.2 1 (by simp))).toUInt64 <<< 8) |||
    ((d.uget (p+2) (window_lt h.1 h.2 2 (by simp))).toUInt64 <<< 16) |||
    ((d.uget (p+3) (window_lt h.1 h.2 3 (by simp))).toUInt64 <<< 24) |||
    ((d.uget (p+4) (window_lt h.1 h.2 4 (by simp))).toUInt64 <<< 32) |||
    ((d.uget (p+5) (window_lt h.1 h.2 5 (by simp))).toUInt64 <<< 40) |||
    ((d.uget (p+6) (window_lt h.1 h.2 6 (by simp))).toUInt64 <<< 48) |||
    ((d.uget (p+7) (window_lt h.1 h.2 7 (by simp))).toUInt64 <<< 56)
  else ldU64LESpec d p.toNat

/-- The `USize` index facts of the window, one per byte. -/
theorem window_idx {p : USize} (h2 : p < p + 8) :
    (p + 1).toNat = p.toNat + 1 ∧ (p + 2).toNat = p.toNat + 2 ∧ (p + 3).toNat = p.toNat + 3 ∧
    (p + 4).toNat = p.toNat + 4 ∧ (p + 5).toNat = p.toNat + 5 ∧ (p + 6).toNat = p.toNat + 6 ∧
    (p + 7).toNat = p.toNat + 7 := by
  have e : ∀ k : USize, k.toNat < 8 → (p + k).toNat = p.toNat + k.toNat :=
    fun k hk => usize_add_small h2 k (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := e 1 (by simp); simpa using this
  · have := e 2 (by simp); simpa using this
  · have := e 3 (by simp); simpa using this
  · have := e 4 (by simp); simpa using this
  · have := e 5 (by simp); simpa using this
  · have := e 6 (by simp); simpa using this
  · have := e 7 (by simp); simpa using this

theorem ldU64LE_eq (d : ByteArray) (p : USize) : ldU64LE d p = ldU64LESpec d p.toNat := by
  unfold ldU64LE
  split
  · rename_i h
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := window_idx h.2
    simp only [uget_eq_getOr0, i1, i2, i3, i4, i5, i6, i7]
    rfl
  · rfl

/-! ## Writing -/

/-- Byte `i` of `a` set to `v`; `a` unchanged when `i` is out of range. The
    test is on `USize` (`i < a.usize`); `i.toNat < a.size` would compile to
    `Nat` operations. -/
@[inline] def setU8 (a : ByteArray) (i : USize) (v : UInt8) : ByteArray :=
  if h : i < a.usize then a.uset i v (usize_lt_size h) else a

theorem size_setU8 (a : ByteArray) (i : USize) (v : UInt8) : (setU8 a i v).size = a.size := by
  unfold setU8; split
  · cases a; simp [ByteArray.uset, ByteArray.size, Array.uset]
  · rfl

theorem usize_setU8 (a : ByteArray) (i : USize) (v : UInt8) : (setU8 a i v).usize = a.usize := by
  simp only [ByteArray.usize, size_setU8]

theorem getOr0_setU8 (a : ByteArray) (i : USize) (v : UInt8) (j : Nat) :
    getOr0 (setU8 a i v) j = if i < a.usize ∧ j = i.toNat then v else getOr0 a j := by
  unfold setU8
  by_cases h : i < a.usize
  · rw [dif_pos h]
    have hl := usize_lt_size h
    have hd : (a.uset i v hl).data = a.data.set i.toNat v hl := by cases a; rfl
    have hsz : (a.uset i v hl).size = a.size := by
      simp only [ByteArray.size, hd, Array.size_set]
    unfold getOr0
    by_cases hj : j < a.size
    · rw [dif_pos (hsz ▸ hj), dif_pos hj]
      simp only [ByteArray.getElem_eq_getElem_data, hd, Array.getElem_set]
      by_cases e : j = i.toNat
      · subst e; rw [if_pos rfl, if_pos ⟨h, rfl⟩]
      · rw [if_neg (Ne.symm e), if_neg (fun hh => e hh.2)]
    · rw [dif_neg (by rw [hsz]; exact hj), dif_neg hj]
      have : ¬ j = i.toNat := by omega
      rw [if_neg (fun hh => this hh.2)]
  · rw [dif_neg h, if_neg (fun hh => h hh.1)]

/-- The pure reference of `stU64LE`: write `x` little-endian at byte `p` when
    the eight bytes are inside `b` (eight `uset`, in place when `b` is
    unique); otherwise `b` unchanged. Executable, and NOT an extern: the
    differential test calls it to compare with the C of `stU64LE`. -/
@[inline] def stU64LERef (b : ByteArray) (p : USize) (x : UInt64) : ByteArray :=
  if p + 8 ≤ b.usize ∧ p < p + 8 then
    setU8 b p x.toUInt8 |> (setU8 · (p+1) (x >>> 8).toUInt8) |> (setU8 · (p+2) (x >>> 16).toUInt8)
     |> (setU8 · (p+3) (x >>> 24).toUInt8) |> (setU8 · (p+4) (x >>> 32).toUInt8)
     |> (setU8 · (p+5) (x >>> 40).toUInt8) |> (setU8 · (p+6) (x >>> 48).toUInt8)
     |> (setU8 · (p+7) (x >>> 56).toUInt8)
  else b

/-- Write `x` little-endian at byte `p` of `b` when the eight bytes are
    inside `b`; otherwise `b` unchanged. Compiled to ONE inline C expression
    (one bounds and wrap test, one exclusivity test, eight byte stores that
    clang merges into one 8-byte store). Its Lean meaning is `stU64LERef`;
    the C is trusted and checked by `Harness/PrimBytesTest.lean` on each
    target (see the module comment). -/
@[extern c inline "({ lean_object* _l4a = #1; size_t _l4p = #2; uint64_t _l4x = #3; if (_l4p + 8 <= lean_sarray_size(_l4a) && _l4p < _l4p + 8) { if (!lean_is_exclusive(_l4a)) _l4a = lean_copy_byte_array(_l4a); uint8_t* _l4q = lean_sarray_cptr(_l4a) + _l4p; _l4q[0] = (uint8_t)_l4x; _l4q[1] = (uint8_t)(_l4x >> 8); _l4q[2] = (uint8_t)(_l4x >> 16); _l4q[3] = (uint8_t)(_l4x >> 24); _l4q[4] = (uint8_t)(_l4x >> 32); _l4q[5] = (uint8_t)(_l4x >> 40); _l4q[6] = (uint8_t)(_l4x >> 48); _l4q[7] = (uint8_t)(_l4x >> 56); } _l4a; })"]
def stU64LE (b : ByteArray) (p : USize) (x : UInt64) : ByteArray := stU64LERef b p x

theorem stU64LE_eq_ref (b : ByteArray) (p : USize) (x : UInt64) : stU64LE b p x = stU64LERef b p x := rfl

/-- Out of bounds (or `p + 8` wraps): the array is unchanged. -/
theorem stU64LE_oob {b : ByteArray} {p : USize} (x : UInt64) (h : ¬ (p + 8 ≤ b.usize ∧ p < p + 8)) :
    stU64LE b p x = b := by
  simp only [stU64LE, stU64LERef, if_neg h]

theorem size_stU64LE (b : ByteArray) (p : USize) (x : UInt64) : (stU64LE b p x).size = b.size := by
  simp only [stU64LE, stU64LERef]
  split
  · simp only [size_setU8]
  · rfl

/-- Every byte of `stU64LE b p x`, as a function of `b`, `p` and `x`. -/
theorem getOr0_stU64LE (b : ByteArray) (p : USize) (x : UInt64) (j : Nat) :
    getOr0 (stU64LE b p x) j =
      if (p + 8 ≤ b.usize ∧ p < p + 8) ∧ p.toNat ≤ j ∧ j < p.toNat + 8 then
        (x >>> (8 * (j - p.toNat)).toUInt64).toUInt8
      else getOr0 b j := by
  simp only [stU64LE, stU64LERef]
  by_cases h : p + 8 ≤ b.usize ∧ p < p + 8
  · rw [if_pos h]
    have hw := window_of_test h.1 h.2
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := window_idx h.2
    have l : ∀ k : USize, k.toNat < 8 → p + k < b.usize := by
      intro k hk
      have e := usize_add_small h.2 k (by omega)
      have a1 := USize.le_iff_toNat_le.mp h.1
      rw [usize_add_small h.2 8 (by rw [usize_eight_toNat]; omega), usize_eight_toNat] at a1
      exact USize.lt_iff_toNat_lt.mpr (by omega)
    have l0 : p < b.usize := by
      have := l 0 (by simp); simpa using this
    simp only [getOr0_setU8, usize_setU8, l0, l 1 (by simp), l 2 (by simp), l 3 (by simp),
      l 4 (by simp), l 5 (by simp), l 6 (by simp), l 7 (by simp), true_and, i1, i2, i3, i4, i5, i6, i7]
    by_cases hj : p.toNat ≤ j ∧ j < p.toNat + 8
    · simp only [h, hj, and_self, if_true]
      obtain ⟨hj1, hj2⟩ := hj
      rcases (by omega : j = p.toNat ∨ j = p.toNat + 1 ∨ j = p.toNat + 2 ∨ j = p.toNat + 3 ∨
          j = p.toNat + 4 ∨ j = p.toNat + 5 ∨ j = p.toNat + 6 ∨ j = p.toNat + 7)
        with e | e | e | e | e | e | e | e <;> subst e <;> simp (disch := omega) [Nat.add_sub_cancel_left]
      all_goals rfl
    · simp only [hj, and_false, if_false]
      have n0 : ¬ j = p.toNat := by omega
      have n1 : ¬ j = p.toNat + 1 := by omega
      have n2 : ¬ j = p.toNat + 2 := by omega
      have n3 : ¬ j = p.toNat + 3 := by omega
      have n4 : ¬ j = p.toNat + 4 := by omega
      have n5 : ¬ j = p.toNat + 5 := by omega
      have n6 : ¬ j = p.toNat + 6 := by omega
      have n7 : ¬ j = p.toNat + 7 := by omega
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, if_false]
  · rw [if_neg h, if_neg (fun hh => h hh.1)]

/-- Bytes outside the window are unchanged. -/
theorem getOr0_stU64LE_other (b : ByteArray) (p : USize) (x : UInt64) (j : Nat)
    (hj : j < p.toNat ∨ p.toNat + 8 ≤ j) : getOr0 (stU64LE b p x) j = getOr0 b j := by
  rw [getOr0_stU64LE]
  have : ¬ (p.toNat ≤ j ∧ j < p.toNat + 8) := by omega
  simp [this]

/-- The bytes outside the window, as array elements. -/
theorem getElem_stU64LE_other (b : ByteArray) (p : USize) (x : UInt64) (j : Nat)
    (hj : j < p.toNat ∨ p.toNat + 8 ≤ j) (h : j < (stU64LE b p x).size) :
    (stU64LE b p x)[j] = b[j]'(by rw [size_stU64LE] at h; exact h) := by
  have e := getOr0_stU64LE_other b p x j hj
  unfold getOr0 at e
  rw [dif_pos h, dif_pos (by rw [size_stU64LE] at h; exact h)] at e
  exact e

/-- Reassembling the eight little-endian bytes of `x` gives `x`. -/
theorem u64_of_bytes (x : UInt64) :
    (x.toUInt8.toUInt64 ||| ((x >>> 8).toUInt8.toUInt64 <<< 8) ||| ((x >>> 16).toUInt8.toUInt64 <<< 16) |||
     ((x >>> 24).toUInt8.toUInt64 <<< 24) ||| ((x >>> 32).toUInt8.toUInt64 <<< 32) |||
     ((x >>> 40).toUInt8.toUInt64 <<< 40) ||| ((x >>> 48).toUInt8.toUInt64 <<< 48) |||
     ((x >>> 56).toUInt8.toUInt64 <<< 56)) = x := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have e8 : (UInt64.toBitVec 8 % 64).toNat = 8 := by decide
  have e16 : (UInt64.toBitVec 16 % 64).toNat = 16 := by decide
  have e24 : (UInt64.toBitVec 24 % 64).toNat = 24 := by decide
  have e32 : (UInt64.toBitVec 32 % 64).toNat = 32 := by decide
  have e40 : (UInt64.toBitVec 40 % 64).toNat = 40 := by decide
  have e48 : (UInt64.toBitVec 48 % 64).toNat = 48 := by decide
  have e56 : (UInt64.toBitVec 56 % 64).toNat = 56 := by decide
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8, BitVec.getElem_or, BitVec.shiftLeft_eq',
    BitVec.ushiftRight_eq', BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, e8, e16, e24, e32, e40, e48, e56]
  rw [← BitVec.getLsbD_eq_getElem hi]
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨
      (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) ∨ (56 ≤ i ∧ i < 64))
    with h | h | h | h | h | h | h | h <;>
    simp (disch := omega) only [decide_eq_true, decide_eq_false, Nat.add_sub_cancel', Bool.true_and,
      Bool.false_and, Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or, Bool.and_false]

/-- Byte `k` (`k < 8`) of the window holds byte `k` of `x`. -/
theorem getOr0_stU64LE_at (b : ByteArray) (p : USize) (x : UInt64)
    (ht : p + 8 ≤ b.usize ∧ p < p + 8) (k : Nat) (hk : k < 8) :
    getOr0 (stU64LE b p x) (p.toNat + k) = (x >>> (8 * k).toUInt64).toUInt8 := by
  rw [getOr0_stU64LE, if_pos ⟨ht, by omega, by omega⟩, Nat.add_sub_cancel_left]

/-- Read after write: inside the array, `ldU64LE` reads back what
    `stU64LE` wrote. -/
theorem ldU64LE_stU64LE (b : ByteArray) (p : USize) (x : UInt64)
    (hs : b.size < USize.size) (hp : p.toNat + 8 ≤ b.size) :
    ldU64LE (stU64LE b p x) p = x := by
  have ht := test_of_window hs hp
  rw [ldU64LE_eq]
  unfold ldU64LESpec
  have a0 := getOr0_stU64LE_at b p x ht 0 (by decide)
  rw [Nat.add_zero] at a0
  rw [a0, getOr0_stU64LE_at b p x ht 1 (by decide), getOr0_stU64LE_at b p x ht 2 (by decide),
    getOr0_stU64LE_at b p x ht 3 (by decide), getOr0_stU64LE_at b p x ht 4 (by decide),
    getOr0_stU64LE_at b p x ht 5 (by decide), getOr0_stU64LE_at b p x ht 6 (by decide),
    getOr0_stU64LE_at b p x ht 7 (by decide)]
  have s0 : x >>> (8 * 0 : Nat).toUInt64 = x := by
    apply UInt64.eq_of_toBitVec_eq
    have e0 : (Nat.toUInt64 (8 * 0)).toBitVec % 64 = 0 := by decide
    rw [UInt64.toBitVec_shiftRight, e0]; simp
  have s1 : (8 * 1 : Nat).toUInt64 = 8 := by decide
  have s2 : (8 * 2 : Nat).toUInt64 = 16 := by decide
  have s3 : (8 * 3 : Nat).toUInt64 = 24 := by decide
  have s4 : (8 * 4 : Nat).toUInt64 = 32 := by decide
  have s5 : (8 * 5 : Nat).toUInt64 = 40 := by decide
  have s6 : (8 * 6 : Nat).toUInt64 = 48 := by decide
  have s7 : (8 * 7 : Nat).toUInt64 = 56 := by decide
  rw [s0, s1, s2, s3, s4, s5, s6, s7]
  exact u64_of_bytes x

end L4Factoidal.Prim.Bytes
