/-
L4Factoidal.WasmVM.Proofs.Memory: laws of a linear-memory backend, and their proof for
backend A, `ByteMem` (https://github.com/danbri/factoidal/issues/1244,
https://github.com/danbri/factoidal/issues/1289 section 1; record:
docs/designissues/2026-11-07-wasmvm-engine.md, "Refinement: the state abstraction").

The refinement theorems read a memory through `LinearMemoryLaws.byte` (the byte at an
address). A backend that satisfies the laws gets the theorems: `load32` is the four
bytes little-endian, `store32` writes the four bytes of the value and keeps the size
and every other byte. `ByteMem` satisfies them (instance below), on the Lean reference
body of `Bytes.st32`; the compiled body is the trusted inline C.
-/
import L4Factoidal.WasmVM.Proofs.Slots

namespace L4Factoidal.WasmVM.Proofs.MemLaws
open L4Factoidal.WasmVM SlotLemmas

/-- Four bytes, little-endian, as `Bytes.ld32` reads them. -/
def le32 (b : Nat → UInt8) (o : Nat) : UInt64 :=
  (b (o+0)).toUInt64 ||| ((b (o+1)).toUInt64 <<< 8)
      ||| ((b (o+2)).toUInt64 <<< 16) ||| ((b (o+3)).toUInt64 <<< 24)

/-- The value of `le32` as a number. -/
theorem le32_toNat (b : Nat → UInt8) (o : Nat) :
    (le32 b o).toNat = (b (o+0)).toNat + (b (o+1)).toNat * 2^8 + (b (o+2)).toNat * 2^16
      + (b (o+3)).toNat * 2^24 := by
  have h0 := (b (o+0)).toNat_lt; have h1 := (b (o+1)).toNat_lt
  have h2 := (b (o+2)).toNat_lt; have h3 := (b (o+3)).toNat_lt
  unfold le32
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, Nat.shiftLeft_eq]
  simp only [UInt64.reduceToNat, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  simp (disch := (simp only [Nat.reducePow] at *; omega)) only [or_mul]

/-- What the refinement theorems need of a memory backend. -/
class LinearMemoryLaws (M : Type) [LinearMemory M] where
  /-- The byte at an address. -/
  byte : M → Nat → UInt8
  load32_eq : ∀ (m : M) ea h, LinearMemory.load32 m ea h = le32 (byte m) ea
  store32_size : ∀ (m : M) ea v h, LinearMemory.size (LinearMemory.store32 m ea v h) = LinearMemory.size m
  store32_byte : ∀ (m : M) ea v h n, byte (LinearMemory.store32 m ea v h) n =
    if n = ea + 0 then v.toUInt8 else if n = ea + 1 then (v >>> 8).toUInt8
    else if n = ea + 2 then (v >>> 16).toUInt8 else if n = ea + 3 then (v >>> 24).toUInt8
    else byte m n

theorem ld32_eq (s : ByteArray) (o : USize) (h : o.toNat + 4 ≤ s.usize.toNat) :
    Bytes.ld32 s o h = le32 (byteAt s) o.toNat := by
  have h1 := Bytes.usize_le s
  have h2 := USize.toNat_lt_size s.usize
  unfold Bytes.ld32 le32
  simp only [uget_eq, get_byteAt]
  rw [addLit o 0 (by decide) (by omega), addLit o 1 (by decide) (by omega), addLit o 2 (by decide) (by omega),
    addLit o 3 (by decide) (by omega)]

theorem st32_size (s : ByteArray) (o : USize) (v : UInt64) (h) : (Bytes.st32 s o v h).size = s.size := by
  simp [Bytes.st32, Bytes.uset_size]

theorem st32_usize (s : ByteArray) (o : USize) (v : UInt64) (h) : (Bytes.st32 s o v h).usize = s.usize := by
  simp only [ByteArray.usize, st32_size]

theorem st32_byte (s : ByteArray) (o : USize) (v : UInt64) (h : o.toNat + 4 ≤ s.usize.toNat) (n : Nat) :
    byteAt (Bytes.st32 s o v h) n =
      if n = o.toNat + 0 then v.toUInt8 else if n = o.toNat + 1 then (v >>> 8).toUInt8
      else if n = o.toNat + 2 then (v >>> 16).toUInt8 else if n = o.toNat + 3 then (v >>> 24).toUInt8
      else byteAt s n := by
  have h1 := Bytes.usize_le s
  have h2 := USize.toNat_lt_size s.usize
  unfold Bytes.st32 byteAt
  simp only [uset_data, Array.getElem?_set]
  rw [addLit o 0 (by decide) (by omega), addLit o 1 (by decide) (by omega), addLit o 2 (by decide) (by omega),
    addLit o 3 (by decide) (by omega)]
  by_cases e3 : n = o.toNat + 3
  · subst e3; simp
  by_cases e2 : n = o.toNat + 2
  · subst e2; simp
  by_cases e1 : n = o.toNat + 1
  · subst e1; simp
  by_cases e0 : n = o.toNat + 0
  · subst e0; simp
  simp only [Nat.add_zero] at e0
  simp [Ne.symm e0, Ne.symm e1, Ne.symm e2, Ne.symm e3, e0, e1, e2, e3]

theorem ea_toUSize (s : ByteArray) (ea w : Nat) (h : ea + w ≤ s.usize.toNat) : ea.toUSize.toNat = ea := by
  have := USize.toNat_lt_size s.usize
  exact natU ea (by omega)

instance : LinearMemoryLaws ByteMem where
  byte m n := byteAt m.data n
  load32_eq m ea h := by
    show Bytes.ld32 m.data ea.toUSize (Bytes.nat_ok h) = _
    rw [ld32_eq, ea_toUSize m.data ea 4 h]
  store32_size m ea v h := by
    show (Bytes.st32 m.data ea.toUSize v (Bytes.nat_ok h)).usize.toNat = m.data.usize.toNat
    rw [st32_usize]
  store32_byte m ea v h n := by
    show byteAt (Bytes.st32 m.data ea.toUSize v (Bytes.nat_ok h)) n = _
    rw [st32_byte, ea_toUSize m.data ea 4 h]

end L4Factoidal.WasmVM.Proofs.MemLaws
