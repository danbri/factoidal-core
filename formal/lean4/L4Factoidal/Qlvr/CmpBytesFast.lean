/-
L4Factoidal.Qlvr.CmpBytesFast — `cmpBytes` eight bytes at a time.
https://github.com/danbri/factoidal/issues/804.

`cmpBytesFast a b` skips the equal 8-byte words at the start of `a` and `b`
(one `ldU64LE` load from each, compared as `UInt64`), then finishes with the
byte loop of `cmpBytes` at the first word that differs. `cmpBytesFast_eq`
proves it equal to `cmpBytes` at every input, and `@[csimp]` makes the
compiler use it wherever `cmpBytes` is called from a module that imports this
one. `cmpBytes` (`L4Factoidal/Qlvr/Sort.lean`) stays the specification.

Measured cause: the k-way merges of the SBM11 packer compare run heads that
share long prefixes (`http://...`); gdb samples put about one third of packer
phase 2 in `cmpBytesLoop` after the merge became a loser tree.

Loops: `cmpBytesWordGo` is a tail call with a fuel `Nat` first.
-/
import L4Factoidal.Qlvr.Sort
import L4Factoidal.Prim.Bytes

namespace L4Factoidal.Qlvr

open L4Factoidal.Prim.Bytes (ldU64LE ldU64LESpec getOr0 ldU64LE_eq)

/-- From byte `i`: while both arrays hold the eight bytes `i .. i+7` and the
    two little-endian words there are equal, move on by 8; then the byte loop
    of `cmpBytes` from `i`. `n` is `min a.size b.size`. -/
def cmpBytesWordGo (a b : ByteArray) (n : Nat) : Nat → Nat → Ordering
  | 0, i => cmpBytesLoop a b (n - i + 1) i
  | k + 1, i =>
    if i + 8 ≤ n then
      if ldU64LE a i.toUSize == ldU64LE b i.toUSize then cmpBytesWordGo a b n k (i + 8)
      else cmpBytesLoop a b (n - i + 1) i
    else cmpBytesLoop a b (n - i + 1) i

/-- `cmpBytes`, eight bytes at a time (`cmpBytesFast_eq`). Arrays of
    `USize.size` bytes or more (none exist at run time) take `cmpBytes`. -/
def cmpBytesFast (a b : ByteArray) : Ordering :=
  let n := min a.size b.size
  if n < USize.size then cmpBytesWordGo a b n (n / 8 + 1) 0 else cmpBytes a b

/-! ## Proof -/

/-- The byte loop does not depend on its fuel once the fuel exceeds the
    bytes left. -/
theorem cmpBytesLoop_fuel (a b : ByteArray) :
    ∀ k1 k2 i, min a.size b.size - i < k1 → min a.size b.size - i < k2 →
      cmpBytesLoop a b k1 i = cmpBytesLoop a b k2 i := by
  intro k1
  induction k1 with
  | zero => intro k2 i h1 _; omega
  | succ k ih =>
    intro k2 i h1 h2
    cases k2 with
    | zero => omega
    | succ k2 =>
      unfold cmpBytesLoop
      split
      · rename_i h
        have hm : i < min a.size b.size := by omega
        rw [ih k2 (i + 1) (by omega) (by omega)]
      · rfl

/-- Equal bytes `i .. i+r-1`: the byte loop moves past them. -/
theorem cmpBytesLoop_skip (a b : ByteArray) (K : Nat) :
    ∀ r i, i + r ≤ min a.size b.size → (∀ j, j < r → getOr0 a (i + j) = getOr0 b (i + j)) →
      cmpBytesLoop a b (K + r) i = cmpBytesLoop a b K (i + r) := by
  intro r
  induction r with
  | zero => intro i _ _; rfl
  | succ r ih =>
    intro i hle heq
    have ha : i < a.size := by omega
    have hb : i < b.size := by omega
    have h0 := heq 0 (by omega)
    simp only [getOr0, Nat.add_zero, dif_pos ha, dif_pos hb] at h0
    rw [show K + (r + 1) = (K + r) + 1 by omega]
    conv => lhs; unfold cmpBytesLoop
    rw [dif_pos ⟨ha, hb⟩, h0]
    simp only [UInt8.lt_irrefl, ↓reduceIte]
    rw [ih (i + 1) (by omega) (fun j hj => by
      have := heq (j + 1) (by omega)
      rwa [show i + (j + 1) = i + 1 + j by omega] at this)]
    rw [show i + 1 + r = i + (r + 1) by omega]

/-- Byte `k` of the little-endian word at `i` is byte `i + k`. -/
theorem ldU64LESpec_byte (d : ByteArray) (i k : Nat) (hk : k < 8) :
    ((ldU64LESpec d i) >>> (8 * k).toUInt64).toUInt8 = getOr0 d (i + k) := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getElem_eq
  intro t ht
  have e8 : (UInt64.toBitVec 8 % 64).toNat = 8 := by decide
  have e16 : (UInt64.toBitVec 16 % 64).toNat = 16 := by decide
  have e24 : (UInt64.toBitVec 24 % 64).toNat = 24 := by decide
  have e32 : (UInt64.toBitVec 32 % 64).toNat = 32 := by decide
  have e40 : (UInt64.toBitVec 40 % 64).toNat = 40 := by decide
  have e48 : (UInt64.toBitVec 48 % 64).toNat = 48 := by decide
  have e56 : (UInt64.toBitVec 56 % 64).toNat = 56 := by decide
  have f0 : ((8 * 0 : Nat).toUInt64.toBitVec % 64).toNat = 0 := by decide
  have f1 : ((8 * 1 : Nat).toUInt64.toBitVec % 64).toNat = 8 := by decide
  have f2 : ((8 * 2 : Nat).toUInt64.toBitVec % 64).toNat = 16 := by decide
  have f3 : ((8 * 3 : Nat).toUInt64.toBitVec % 64).toNat = 24 := by decide
  have f4 : ((8 * 4 : Nat).toUInt64.toBitVec % 64).toNat = 32 := by decide
  have f5 : ((8 * 5 : Nat).toUInt64.toBitVec % 64).toNat = 40 := by decide
  have f6 : ((8 * 6 : Nat).toUInt64.toBitVec % 64).toNat = 48 := by decide
  have f7 : ((8 * 7 : Nat).toUInt64.toBitVec % 64).toNat = 56 := by decide
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ldU64LESpec, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
      UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8, BitVec.getElem_setWidth, BitVec.ushiftRight_eq',
      BitVec.shiftLeft_eq', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, Nat.add_zero, e8, e16, e24, e32, e40, e48, e56,
      f0, f1, f2, f3, f4, f5, f6, f7]
    rw [← BitVec.getLsbD_eq_getElem ht]
    simp (disch := omega) only [decide_eq_true, decide_eq_false, Nat.add_sub_cancel_left, Nat.zero_add,
      Bool.true_and, Bool.false_and, Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or,
      Bool.and_false, Bool.and_true, BitVec.getLsbD_of_ge]

/-- Equal little-endian words at `i`: the eight bytes `i .. i+7` are equal. -/
theorem bytes_of_word_eq {a b : ByteArray} {i : Nat} (h : ldU64LESpec a i = ldU64LESpec b i) :
    ∀ j, j < 8 → getOr0 a (i + j) = getOr0 b (i + j) := by
  intro j hj
  rw [← ldU64LESpec_byte a i j hj, ← ldU64LESpec_byte b i j hj, h]

/-- The word loop is the byte loop, for every fuel and every start `i ≤ n`. -/
theorem cmpBytesWordGo_eq (a b : ByteArray) (hU : min a.size b.size < USize.size) :
    ∀ k i, i ≤ min a.size b.size →
      cmpBytesWordGo a b (min a.size b.size) k i = cmpBytesLoop a b (min a.size b.size - i + 1) i := by
  intro k
  induction k with
  | zero => intro i _; rfl
  | succ k ih =>
    intro i hi
    unfold cmpBytesWordGo
    split
    · rename_i h8
      split
      · rename_i hw
        have hw' := eq_of_beq hw
        have hti : i.toUSize.toNat = i := by
          show (USize.ofNat i).toNat = i
          exact USize.toNat_ofNat_of_lt' (by omega)
        rw [ldU64LE_eq, ldU64LE_eq, hti] at hw'
        rw [ih (i + 8) (by omega)]
        have hs := cmpBytesLoop_skip a b (min a.size b.size - (i + 8) + 1) 8 i h8 (bytes_of_word_eq hw')
        rw [show min a.size b.size - (i + 8) + 1 + 8 = min a.size b.size - i + 1 by omega] at hs
        exact hs.symm
      · rfl
    · rfl

/-- `cmpBytesFast` is `cmpBytes`. -/
theorem cmpBytesFast_eq (a b : ByteArray) : cmpBytesFast a b = cmpBytes a b := by
  unfold cmpBytesFast cmpBytes
  dsimp only
  split
  · rename_i hU
    rw [cmpBytesWordGo_eq a b hU _ 0 (Nat.zero_le _), Nat.sub_zero]
  · rfl

/-- Compiled code calls `cmpBytesFast` for `cmpBytes`. -/
@[csimp] theorem cmpBytes_eq_cmpBytesFast : @cmpBytes = @cmpBytesFast := by
  funext a b
  exact (cmpBytesFast_eq a b).symm

#guard cmpBytesFast "abcdefghij".toUTF8 "abcdefghik".toUTF8 == .lt
#guard cmpBytesFast "abcdefghijklmnopq".toUTF8 "abcdefghijklmnopq".toUTF8 == .eq
#guard cmpBytesFast "abcdefghijklmnop".toUTF8 "abcdefghijklmnopq".toUTF8 == .lt
#guard cmpBytesFast "abcdefgh\xffz".toUTF8 "abcdefgh\x01z".toUTF8 == .gt

end L4Factoidal.Qlvr
