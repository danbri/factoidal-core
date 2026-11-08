/-
L4Factoidal.WasmVM.Proofs.Slots: reading back what the engine writes into the operand
stack (https://github.com/danbri/factoidal/issues/1244; record:
docs/designissues/2026-11-07-wasmvm-engine.md, "Refinement: the state abstraction").

The operand stack is a `ByteArray` of 8-byte little-endian slots (`Slots`). Loads are
`Bytes.ld64` (eight `uget`s), stores `Bytes.st64` (eight `uset`s in the Lean reference
body; the compiled body is the trusted inline C `memcpy`). The theorems here are about the
Lean reference bodies:

- `rd_wr_same`: a slot read after a write of the same slot gives the written value
  (`le64_bytes`: the eight bytes of `v`, put together again, are `v`).
- `rd_wr_ne`: a write leaves every other slot as it was.
- `moveDown_rd`: `moveDown` (the copy of `br` and `return`) moves `k` slots down and
  leaves the others.

Side condition everywhere: the stack is smaller than `USize.size` bytes, so `USize`
indices do not wrap.
-/
import L4Factoidal.WasmVM.Exec.Run

namespace L4Factoidal.WasmVM.Proofs.SlotLemmas
open L4Factoidal.WasmVM

theorem lit (k : Nat) (hk : k < 2^32) : USize.toNat (OfNat.ofNat k) = k :=
  USize.toNat_ofNat_of_lt (by have := USize.le_size; omega)
theorem natU (k : Nat) (h : k < USize.size) : k.toUSize.toNat = k := by
  simp only [Nat.toUSize_eq]; exact USize.toNat_ofNat_of_lt' h
theorem addU (a b : USize) (h : a.toNat + b.toNat < USize.size) : (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add]; exact Nat.mod_eq_of_lt h
theorem subU (a b : USize) (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat :=
  USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr h)
theorem addLit (o : USize) (k : Nat) (hk : k < 2^32) (h : o.toNat + k < USize.size) :
    (o + OfNat.ofNat k).toNat = o.toNat + k := by
  rw [addU _ _ (by rw [lit k hk]; exact h), lit k hk]

theorem or_mul (x y k : Nat) (h : x < 2 ^ k) : x ||| y * 2 ^ k = x + y * 2 ^ k := by
  rw [Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq, Nat.add_comm]

/-- Eight bytes, little-endian, as `Bytes.ld64` reads them. -/
def le64 (b : Nat → UInt8) (o : Nat) : UInt64 :=
  (b (o+0)).toUInt64 ||| ((b (o+1)).toUInt64 <<< 8)
      ||| ((b (o+2)).toUInt64 <<< 16) ||| ((b (o+3)).toUInt64 <<< 24)
      ||| ((b (o+4)).toUInt64 <<< 32) ||| ((b (o+5)).toUInt64 <<< 40)
      ||| ((b (o+6)).toUInt64 <<< 48) ||| ((b (o+7)).toUInt64 <<< 56)

theorem le64_bytes (v : UInt64) :
    (v.toUInt8.toUInt64 ||| ((v >>> 8).toUInt8.toUInt64 <<< 8) ||| ((v >>> 16).toUInt8.toUInt64 <<< 16)
      ||| ((v >>> 24).toUInt8.toUInt64 <<< 24) ||| ((v >>> 32).toUInt8.toUInt64 <<< 32)
      ||| ((v >>> 40).toUInt8.toUInt64 <<< 40) ||| ((v >>> 48).toUInt8.toUInt64 <<< 48)
      ||| ((v >>> 56).toUInt8.toUInt64 <<< 56)) = v := by
  apply UInt64.toNat_inj.mp
  have hv := v.toNat_lt
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, UInt64.toNat_toUInt8,
    UInt64.toNat_shiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  simp only [UInt64.reduceToNat, Nat.reduceMod]
  simp (disch := (simp only [Nat.reducePow] at *; omega)) only [Nat.mod_eq_of_lt]
  simp (disch := (simp only [Nat.reducePow] at *; omega)) only [or_mul]
  simp only [Nat.reducePow]
  omega

theorem uget_eq (s : ByteArray) (i : USize) (h) : s.uget i h = s.data[i.toNat]'h := by
  cases s; rfl

theorem uset_data (s : ByteArray) (i : USize) (v : UInt8) (h) :
    (s.uset i v h).data = s.data.set i.toNat v h := by
  cases s; rfl

/-- The byte at `n` (0 past the end). -/
def byteAt (s : ByteArray) (n : Nat) : UInt8 := (s.data[n]?).getD 0

theorem get_byteAt (s : ByteArray) (n : Nat) (h : n < s.data.size) : s.data[n]'h = byteAt s n := by
  simp [byteAt, Array.getElem?_eq_getElem h]

theorem usize_eq (s : ByteArray) (hS : s.size < USize.size) : s.usize.toNat = s.size := by
  simp only [ByteArray.usize]; exact natU _ hS

theorem ld64_eq (s : ByteArray) (o : USize) (h : o.toNat + 8 ≤ s.usize.toNat) :
    Bytes.ld64 s o h = le64 (byteAt s) o.toNat := by
  have h1 := Bytes.usize_le s
  have h2 := USize.toNat_lt_size s.usize
  unfold Bytes.ld64 le64
  simp only [uget_eq, get_byteAt]
  rw [addLit o 0 (by decide) (by omega), addLit o 1 (by decide) (by omega), addLit o 2 (by decide) (by omega),
    addLit o 3 (by decide) (by omega), addLit o 4 (by decide) (by omega), addLit o 5 (by decide) (by omega),
    addLit o 6 (by decide) (by omega), addLit o 7 (by decide) (by omega)]

theorem st64_size (s : ByteArray) (o : USize) (v : UInt64) (h) : (Bytes.st64 s o v h).size = s.size := by
  simp [Bytes.st64, Bytes.uset_size]

theorem st64_usize (s : ByteArray) (o : USize) (v : UInt64) (h) : (Bytes.st64 s o v h).usize = s.usize := by
  simp only [ByteArray.usize, st64_size]

theorem st64_byte (s : ByteArray) (o : USize) (v : UInt64) (h : o.toNat + 8 ≤ s.usize.toNat) (n : Nat) :
    byteAt (Bytes.st64 s o v h) n =
      if n = o.toNat + 0 then v.toUInt8 else if n = o.toNat + 1 then (v >>> 8).toUInt8
      else if n = o.toNat + 2 then (v >>> 16).toUInt8 else if n = o.toNat + 3 then (v >>> 24).toUInt8
      else if n = o.toNat + 4 then (v >>> 32).toUInt8 else if n = o.toNat + 5 then (v >>> 40).toUInt8
      else if n = o.toNat + 6 then (v >>> 48).toUInt8 else if n = o.toNat + 7 then (v >>> 56).toUInt8
      else byteAt s n := by
  have h1 := Bytes.usize_le s
  have h2 := USize.toNat_lt_size s.usize
  unfold Bytes.st64 byteAt
  simp only [uset_data, Array.getElem?_set]
  rw [addLit o 0 (by decide) (by omega), addLit o 1 (by decide) (by omega), addLit o 2 (by decide) (by omega),
    addLit o 3 (by decide) (by omega), addLit o 4 (by decide) (by omega), addLit o 5 (by decide) (by omega),
    addLit o 6 (by decide) (by omega), addLit o 7 (by decide) (by omega)]
  by_cases e7 : n = o.toNat + 7
  · subst e7; simp
  by_cases e6 : n = o.toNat + 6
  · subst e6; simp
  by_cases e5 : n = o.toNat + 5
  · subst e5; simp
  by_cases e4 : n = o.toNat + 4
  · subst e4; simp
  by_cases e3 : n = o.toNat + 3
  · subst e3; simp
  by_cases e2 : n = o.toNat + 2
  · subst e2; simp
  by_cases e1 : n = o.toNat + 1
  · subst e1; simp
  by_cases e0 : n = o.toNat + 0
  · subst e0; simp
  simp only [Nat.add_zero] at e0
  simp [Ne.symm e0, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6, Ne.symm e7, e0, e1, e2, e3, e4, e5, e6, e7]


theorem le64_congr (b b' : Nat → UInt8) (o : Nat) (h : ∀ k, k < 8 → b (o + k) = b' (o + k)) :
    le64 b o = le64 b' o := by
  unfold le64
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega),
    h 6 (by omega), h 7 (by omega)]

theorem mul8 (i : USize) (h : i.toNat * 8 < USize.size) : (i * 8).toNat = i.toNat * 8 := by
  rw [USize.toNat_mul, lit 8 (by decide)]; exact Nat.mod_eq_of_lt h

theorem slot_iff (s : Slots) (i : USize) (hS : s.size < USize.size) :
    i < s.usize / 8 ↔ i.toNat < s.size / 8 := by
  rw [USize.lt_iff_toNat_lt, USize.toNat_div, usize_eq s hS, lit 8 (by decide)]

theorem wr_size (s : Slots) (i : USize) (v : UInt64) : (Slots.wr s i v).size = s.size := by
  unfold Slots.wr; split
  · exact st64_size _ _ _ _
  · rfl

theorem rd_wr_same (s : Slots) (i : USize) (v : UInt64) (hS : s.size < USize.size)
    (hi : i.toNat < s.size / 8) : Slots.rd (Slots.wr s i v) i = v := by
  have hi' := (slot_iff s i hS).mpr hi
  have hm : (i * 8).toNat = i.toNat * 8 := mul8 i (by omega)
  unfold Slots.wr; rw [dif_pos hi']
  unfold Slots.rd; rw [dif_pos (by rw [st64_usize]; exact hi'), ld64_eq]
  unfold le64
  simp only [st64_byte, hm]
  simpa using le64_bytes v

theorem rd_wr_ne (s : Slots) (i j : USize) (v : UInt64) (hS : s.size < USize.size)
    (hne : i.toNat ≠ j.toNat) : Slots.rd (Slots.wr s i v) j = Slots.rd s j := by
  unfold Slots.wr
  split
  · rename_i hi'
    have hi := (slot_iff s i hS).mp hi'
    have hm : (i * 8).toNat = i.toNat * 8 := mul8 i (by omega)
    unfold Slots.rd
    simp only [st64_usize]
    split
    · rename_i hj'
      have hj := (slot_iff s j hS).mp hj'
      have hn : (j * 8).toNat = j.toNat * 8 := mul8 j (by omega)
      rw [ld64_eq, ld64_eq]
      apply le64_congr
      intro k hk
      rw [st64_byte, hm, hn]
      have : i.toNat < j.toNat ∨ j.toNat < i.toNat := by omega
      rcases this with h | h <;>
      · simp only [show ∀ m, m < 8 → j.toNat * 8 + k ≠ i.toNat * 8 + m from fun m hm' => by omega,
          ne_eq, not_false_eq_true, ↓reduceIte, (by decide : (0:Nat) < 8), (by decide : (1:Nat) < 8),
          (by decide : (2:Nat) < 8), (by decide : (3:Nat) < 8), (by decide : (4:Nat) < 8),
          (by decide : (5:Nat) < 8), (by decide : (6:Nat) < 8), (by decide : (7:Nat) < 8)]
    · rfl
  · rfl

theorem moveDown_size (s : Slots) (src dst : USize) (k : Nat) : (Run.moveDown s src dst k).size = s.size := by
  induction k generalizing s src dst with
  | zero => rfl
  | succ k ih => simp only [Run.moveDown, Run.wr]; rw [ih, wr_size]

/-- `moveDown` copies `k` slots from `src` down to `dst`, lowest first; other slots keep
their values. -/
theorem moveDown_rd (s : Slots) (src dst : USize) (k : Nat) (hS : s.size < USize.size)
    (hk : src.toNat + k ≤ s.size / 8) (hd : dst.toNat ≤ src.toNat) (j : USize) :
    Slots.rd (Run.moveDown s src dst k) j =
      if dst.toNat ≤ j.toNat ∧ j.toNat < dst.toNat + k
      then Slots.rd s (src + (j - dst)) else Slots.rd s j := by
  induction k generalizing s src dst with
  | zero => simp [Run.moveDown]; omega
  | succ k ih =>
    simp only [Run.moveDown, Run.wr, Run.rd]
    have hs1 : (src + 1).toNat = src.toNat + 1 := addLit src 1 (by decide) (by omega)
    have hd1 : (dst + 1).toNat = dst.toNat + 1 := addLit dst 1 (by decide) (by omega)
    rw [ih _ _ _ (by rw [wr_size]; exact hS) (by rw [wr_size]; omega) (by omega)]
    by_cases hj : dst.toNat ≤ j.toNat ∧ j.toNat < dst.toNat + (k + 1)
    · rw [if_pos hj]
      by_cases h0 : j.toNat = dst.toNat
      · have hj0 : j = dst := USize.toNat_inj.mp h0
        subst hj0
        rw [if_neg (by omega), rd_wr_same _ _ _ hS (by omega), USize.sub_self, USize.add_zero]
      · rw [if_pos (by omega)]
        have e1 : ((src + 1) + (j - (dst + 1))) = src + (j - dst) := by
          apply USize.toNat_inj.mp
          rw [addU _ _ (by rw [hs1, subU _ _ (by omega), hd1]; omega), hs1, subU _ _ (by omega), hd1,
            addU _ _ (by rw [subU _ _ (by omega)]; omega), subU _ _ (by omega)]
          omega
        rw [e1, rd_wr_ne _ _ _ _ hS]
        rw [addU _ _ (by rw [subU _ _ (by omega)]; omega), subU _ _ (by omega)]
        omega
    · rw [if_neg hj, if_neg (by omega), rd_wr_ne _ _ _ _ hS (by omega)]

end L4Factoidal.WasmVM.Proofs.SlotLemmas
