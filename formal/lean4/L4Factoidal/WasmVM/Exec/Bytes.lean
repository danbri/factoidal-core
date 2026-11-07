/-
L4Factoidal.WasmVM.Exec.Bytes: little-endian loads and stores on a `ByteArray` at a
`USize` byte offset, with ONE bounds check per access
(https://github.com/danbri/factoidal/issues/1244; record:
docs/designissues/2026-11-07-wasmvm-engine.md, "Slot form").

Loads are Lean: `w` reads `s.uget (o + k)`, each with a proof that `o + k` is in range
(`byte_ok`). With no check between the reads, the C compiler joins them into one load
(checked in the emitted ARM64 code: one `ldr x` per 64-bit read).

Stores are `uset` chains in Lean (the reference definitions, which the theorems use)
with a C body given by `@[extern c inline]`: one `memcpy` of `w` bytes after the
uniqueness check that `lean_byte_array_uset` also makes. Why: eight `uset`s each
check uniqueness again (a byte store may alias the reference count, so the C compiler
must reload it), and a later 8-byte load of the same slot cannot take its value from
eight 1-byte stores. Measured in `Bench/Repr.lean`: 8.5 ns against 3.3 ns per
iteration. The C body is trusted to equal the Lean body: it stores the bytes of `v` in
little-endian order (`__builtin_bswap` on a big-endian host), at the offset the Lean
body writes, and has the same uniqueness rule. It is the same kind of code as
`lean_byte_array_uset` in `lean.h`.

The Lean interpreter cannot run an `extern c inline` declaration, so `#eval` and
`#guard` must not call these stores; compiled code and kernel proofs can.
-/
namespace L4Factoidal.WasmVM.Bytes

theorem usize_le (s : ByteArray) : s.usize.toNat ≤ s.size := by
  simp only [ByteArray.usize]; simp [Nat.toUSize]; exact Nat.mod_le _ _

/-- The byte indices of an access of width `w` are in range when its first byte and
width fit under `s.usize` (which is below `USize.size`, so `o + k` does not wrap). -/
theorem byte_ok {s : ByteArray} {o : USize} {w : Nat} (h : o.toNat + w ≤ s.usize.toNat)
    (k : USize) (hk : k.toNat < w) : (o + k).toNat < s.size := by
  have h1 := usize_le s
  have h2 := USize.toNat_lt_size s.usize
  have hs : USize.size = 2 ^ System.Platform.numBits := rfl
  rw [USize.toNat_add, Nat.mod_eq_of_lt (by omega)]
  omega

theorem uset_usize (s : ByteArray) (i : USize) (v : UInt8) (h) : (s.uset i v h).usize = s.usize := by
  cases s; simp only [ByteArray.uset, ByteArray.usize, ByteArray.size, Array.size_uset]

theorem uset_size (s : ByteArray) (i : USize) (v : UInt8) (h) : (s.uset i v h).size = s.size := by
  cases s; simp only [ByteArray.uset, ByteArray.size, Array.size_uset]

/-! ### Loads -/

@[inline] def ld8 (s : ByteArray) (o : USize) (h : o.toNat + 1 ≤ s.usize.toNat) : UInt64 :=
  (s.uget (o+0) (byte_ok h 0 (by simp))).toUInt64

@[inline] def ld16 (s : ByteArray) (o : USize) (h : o.toNat + 2 ≤ s.usize.toNat) : UInt64 :=
  (s.uget (o+0) (byte_ok h 0 (by simp))).toUInt64
  ||| ((s.uget (o+1) (byte_ok h 1 (by simp))).toUInt64 <<< 8)

@[inline] def ld32 (s : ByteArray) (o : USize) (h : o.toNat + 4 ≤ s.usize.toNat) : UInt64 :=
  (s.uget (o+0) (byte_ok h 0 (by simp))).toUInt64
  ||| ((s.uget (o+1) (byte_ok h 1 (by simp))).toUInt64 <<< 8)
  ||| ((s.uget (o+2) (byte_ok h 2 (by simp))).toUInt64 <<< 16)
  ||| ((s.uget (o+3) (byte_ok h 3 (by simp))).toUInt64 <<< 24)

@[inline] def ld64 (s : ByteArray) (o : USize) (h : o.toNat + 8 ≤ s.usize.toNat) : UInt64 :=
  (s.uget (o+0) (byte_ok h 0 (by simp))).toUInt64
  ||| ((s.uget (o+1) (byte_ok h 1 (by simp))).toUInt64 <<< 8)
  ||| ((s.uget (o+2) (byte_ok h 2 (by simp))).toUInt64 <<< 16)
  ||| ((s.uget (o+3) (byte_ok h 3 (by simp))).toUInt64 <<< 24)
  ||| ((s.uget (o+4) (byte_ok h 4 (by simp))).toUInt64 <<< 32)
  ||| ((s.uget (o+5) (byte_ok h 5 (by simp))).toUInt64 <<< 40)
  ||| ((s.uget (o+6) (byte_ok h 6 (by simp))).toUInt64 <<< 48)
  ||| ((s.uget (o+7) (byte_ok h 7 (by simp))).toUInt64 <<< 56)

/-! ### Stores

Each reference body writes byte `k` of `v` at `o + k`. `keep` carries the bounds fact
across a `uset` (the size does not change). -/

theorem keep {s : ByteArray} {o : USize} {w : Nat} {i : USize} {b : UInt8} {hi}
    (h : o.toNat + w ≤ s.usize.toNat) : o.toNat + w ≤ (s.uset i b hi).usize.toNat := by
  rw [uset_usize]; exact h

@[inline] def st8 (s : ByteArray) (o : USize) (v : UInt64) (h : o.toNat + 1 ≤ s.usize.toNat) : ByteArray :=
  s.uset o v.toUInt8 (by have := byte_ok h 0 (by simp); simpa using this)

@[extern c inline "({ lean_object * r_ = lean_is_exclusive(#1) ? #1 : lean_copy_byte_array(#1); uint16_t v_ = (uint16_t)(#3); if (__BYTE_ORDER__ == __ORDER_BIG_ENDIAN__) v_ = __builtin_bswap16(v_); __builtin_memcpy(lean_sarray_cptr(r_) + (#2), &v_, 2); r_; })"]
def st16 (s : ByteArray) (o : USize) (v : UInt64) (h : o.toNat + 2 ≤ s.usize.toNat) : ByteArray :=
  let s1 := s.uset (o+0) v.toUInt8 (byte_ok h 0 (by simp))
  s1.uset (o+1) (v >>> 8).toUInt8 (byte_ok (keep h) 1 (by simp))

@[extern c inline "({ lean_object * r_ = lean_is_exclusive(#1) ? #1 : lean_copy_byte_array(#1); uint32_t v_ = (uint32_t)(#3); if (__BYTE_ORDER__ == __ORDER_BIG_ENDIAN__) v_ = __builtin_bswap32(v_); __builtin_memcpy(lean_sarray_cptr(r_) + (#2), &v_, 4); r_; })"]
def st32 (s : ByteArray) (o : USize) (v : UInt64) (h : o.toNat + 4 ≤ s.usize.toNat) : ByteArray :=
  let s1 := s.uset (o+0) v.toUInt8 (byte_ok h 0 (by simp))
  let s2 := s1.uset (o+1) (v >>> 8).toUInt8 (byte_ok (keep h) 1 (by simp))
  let s3 := s2.uset (o+2) (v >>> 16).toUInt8 (byte_ok (keep (keep h)) 2 (by simp))
  s3.uset (o+3) (v >>> 24).toUInt8 (byte_ok (keep (keep (keep h))) 3 (by simp))

@[extern c inline "({ lean_object * r_ = lean_is_exclusive(#1) ? #1 : lean_copy_byte_array(#1); uint64_t v_ = (#3); if (__BYTE_ORDER__ == __ORDER_BIG_ENDIAN__) v_ = __builtin_bswap64(v_); __builtin_memcpy(lean_sarray_cptr(r_) + (#2), &v_, 8); r_; })"]
def st64 (s : ByteArray) (o : USize) (v : UInt64) (h : o.toNat + 8 ≤ s.usize.toNat) : ByteArray :=
  let s1 := s.uset (o+0) v.toUInt8 (byte_ok h 0 (by simp))
  let s2 := s1.uset (o+1) (v >>> 8).toUInt8 (byte_ok (keep h) 1 (by simp))
  let s3 := s2.uset (o+2) (v >>> 16).toUInt8 (byte_ok (keep (keep h)) 2 (by simp))
  let s4 := s3.uset (o+3) (v >>> 24).toUInt8 (byte_ok (keep (keep (keep h))) 3 (by simp))
  let s5 := s4.uset (o+4) (v >>> 32).toUInt8 (byte_ok (keep (keep (keep (keep h)))) 4 (by simp))
  let s6 := s5.uset (o+5) (v >>> 40).toUInt8 (byte_ok (keep (keep (keep (keep (keep h))))) 5 (by simp))
  let s7 := s6.uset (o+6) (v >>> 48).toUInt8 (byte_ok (keep (keep (keep (keep (keep (keep h)))))) 6 (by simp))
  s7.uset (o+7) (v >>> 56).toUInt8 (byte_ok (keep (keep (keep (keep (keep (keep (keep h))))))) 7 (by simp))

/-! ### Checked forms at a `Nat` address (memory) -/

/-- `ea` as a `USize` offset, when `ea + w` fits under `s.usize`. -/
theorem nat_ok {s : ByteArray} {ea w : Nat} (h : ea + w ≤ s.usize.toNat) :
    ea.toUSize.toNat + w ≤ s.usize.toNat := by
  have h2 := USize.toNat_lt_size s.usize
  have hs : USize.size = 2 ^ System.Platform.numBits := rfl
  have : ea.toUSize.toNat = ea := by
    simp only [Nat.toUSize, USize.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  rw [this]; exact h

end L4Factoidal.WasmVM.Bytes
