import L4Factoidal.WasmVM.Spec.Builtins

/-!
# The integer built-ins agree with Lean's fixed-width integers

For each built-in of `Spec/Builtins.lean`, a theorem that it equals the matching
`UInt32`/`UInt64` (or `Int32`/`Int64`) operation, read through `toBitVec`. A fast engine
uses these to show that a machine-integer step is a spec step. The engine's numerics
(`WasmVM/Numerics.lean`, owned by the exec work) use the same expressions: for example
rotate as two shifts, `i32.extend8_s` as `toUInt8.toInt8.toInt32.toUInt32`.

Also: little-endian `ibytes_` round-trips for 8, 16, 32 and 64 bits; the bytes of a
`UInt32`/`UInt64` as `toUInt8` of right shifts, which is how an engine stores; and
lemmas that tie the `BitVec` definitions to the spec's arithmetic formulas (`signed_`).

Not proved here: that the engine's branch-free `clz`, `ctz` and `popcnt` formulas equal
`iclz_`, `ictz_`, `ipopcnt_`. Lean core has no `UInt32` operation for them.

Proofs use `simp`, `omega`, `decide` and `rfl` only. Not `bv_decide`: in Lean v4.33.1 a
`bv_decide` proof depends on an extra axiom `<theorem>._native.bv_decide.ax_...`
(checked with `#print axioms`), the same trust in compiled code as `native_decide`.
-/

namespace L4Factoidal.WasmVM.Spec.Builtins

/-! ## Examples, checked by the kernel -/

example : ishl_ (5#32) 33 = 10#32 := by decide
example : ishr_ true (0x80000000#32) 31 = 0xFFFFFFFF#32 := by rfl
example : ishr_ false (0x80000000#32) 63 = 1#32 := by rfl
example : irotl_ (0x80000001#32) 1 = 3#32 := by decide
example : irotr_ (3#32) 33 = 0x80000001#32 := by decide
example : iclz_ (1#32) = 31#32 := by decide
example : iclz_ (0#32) = 32#32 := by decide
example : ictz_ (0x80#8) = 7#8 := by decide
example : ictz_ (0#16) = 16#16 := by decide
example : ipopcnt_ (0xF0F0#32) = 8#32 := by decide
example : ilt_ true (0xFFFFFFFF#32) (0#32) = true := by decide
example : ilt_ false (0xFFFFFFFF#32) (0#32) = false := by decide
example : extend_ 64 true (0x80#8) = 0xFFFFFFFFFFFFFF80#64 := by decide
example : iextend_ 8 true (0x1FF#32) = 0xFFFFFFFF#32 := by decide
example : ibytes_ (0x11223344#32) = [0x44#8, 0x33#8, 0x22#8, 0x11#8] := by decide
example : inv_ibytes_ 32 [0x44#8, 0x33#8, 0x22#8, 0x11#8] = 0x11223344#32 := by decide
example : ibits_ (0b1010#4) = [true, false, true, false] := by decide
example : inv_ibits_ 4 [true, false, true, false] = 0b1010#4 := by decide
example : iadd_sat_ true (0x7F#8) (1#8) = 0x7F#8 := by decide
example : isub_sat_ false (1#8) (2#8) = 0#8 := by decide
example : iq15mulr_sat_ (0x8000#16) (0x8000#16) = 0x7FFF#16 := by decide
example : narrow_ 8 true (0x8000#16) = 0x80#8 := by decide
example : narrow_ 8 false (0x8000#16) = 0#8 := by decide
example : iabs_ (0x80#8) = 0x80#8 := by decide

/-! ## The `BitVec` definitions against the spec's arithmetic formulas -/

/-- `signed_N` is two's complement: the value `BitVec.toInt` gives. -/
theorem signed_toNat {n : Nat} (hn : 0 < n) (x : BitVec n) : signed_ n x.toNat = x.toInt := by
  rw [BitVec.toInt_eq_toNat_cond, signed_]
  have h : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  by_cases hx : x.toNat < 2 ^ (n - 1)
  · rw [if_pos hx, if_pos (by omega)]
  · rw [if_neg hx, if_neg (by omega)]; push_cast; rfl

/-- `ilt_s_N(i_1, i_2) = bool(signed_N(i_1) < signed_N(i_2))`. -/
theorem ilt_s_eq_signed {n : Nat} (hn : 0 < n) (a b : BitVec n) :
    ilt_ true a b = decide (signed_ n a.toNat < signed_ n b.toNat) := by
  simp [ilt_, BitVec.slt, signed_toNat hn]

/-- `ilt_u_N(i_1, i_2) = bool(i_1 < i_2)`. -/
theorem ilt_u_eq_nat {n : Nat} (a b : BitVec n) :
    ilt_ false a b = decide (a.toNat < b.toNat) := by
  simp [ilt_, BitVec.ult]

/-- `ile_s_N(i_1, i_2) = bool(signed_N(i_1) ≤ signed_N(i_2))`. -/
theorem ile_s_eq_signed {n : Nat} (hn : 0 < n) (a b : BitVec n) :
    ile_ true a b = decide (signed_ n a.toNat ≤ signed_ n b.toNat) := by
  simp [ile_, BitVec.sle, signed_toNat hn]

/-- `ile_u_N(i_1, i_2) = bool(i_1 ≤ i_2)`. -/
theorem ile_u_eq_nat {n : Nat} (a b : BitVec n) :
    ile_ false a b = decide (a.toNat ≤ b.toNat) := by
  simp [ile_, BitVec.ule]

/-- `wrap_(M,N)(i) = i mod 2^N`. -/
theorem wrap_toNat {m : Nat} (n : Nat) (x : BitVec m) :
    (wrap_ n x).toNat = x.toNat % 2 ^ n := by
  simp [wrap_]

/-- `extend_u_(M,N)(i) = i` when `M ≤ N`. -/
theorem extend_u_toNat {m n : Nat} (h : m ≤ n) (x : BitVec m) :
    (extend_ n false x).toNat = x.toNat := by
  simp [extend_, BitVec.toNat_setWidth_of_le h]

/-- `extend_s_(M,N)(i) = signed_N^-1(signed_M(i))` when `0 < M ≤ N`. -/
theorem extend_s_eq_spec {m n : Nat} (hm : 0 < m) (h : m ≤ n) (x : BitVec m) :
    (extend_ n true x).toNat = inv_signed_ n (signed_ m x.toNat) := by
  rw [signed_toNat hm]
  simp only [extend_, if_true, BitVec.signExtend, BitVec.toNat_ofInt, inv_signed_]
  have hlo := BitVec.le_toInt x
  have hhi := BitVec.toInt_lt (x := x)
  have hpN : 2 ^ (m - 1) ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hp : (2 : Int) ^ (m - 1) ≤ 2 ^ (n - 1) := by exact_mod_cast hpN
  have h2N : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have h2 : (2 : Int) ^ n = 2 * 2 ^ (n - 1) := by exact_mod_cast h2N
  have hpos : (0 : Int) < 2 ^ (n - 1) := Int.pow_pos (by decide)
  push_cast
  split
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
  · rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]

/-- Shift and rotate counts are taken modulo `N`. -/
theorem ishl_mod {n : Nat} (x : BitVec n) (k : Nat) : ishl_ x (k % n) = ishl_ x k := by
  simp [ishl_]

theorem irotl_mod {n : Nat} (x : BitVec n) (k : Nat) : irotl_ x (k % n) = irotl_ x k := by
  simp [irotl_]

/-! ## Little-endian bytes: round trips -/

theorem inv_ibytes_ibytes_8 (x : BitVec 8) : inv_ibytes_ 8 (ibytes_ x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp [inv_ibytes_, ibytes_, List.range_succ]

theorem inv_ibytes_ibytes_16 (x : BitVec 16) : inv_ibytes_ 16 (ibytes_ x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp [inv_ibytes_, ibytes_, List.range_succ, Nat.shiftRight_eq_div_pow]
  all_goals omega

theorem inv_ibytes_ibytes_32 (x : BitVec 32) : inv_ibytes_ 32 (ibytes_ x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp [inv_ibytes_, ibytes_, List.range_succ, Nat.shiftRight_eq_div_pow]
  all_goals omega

theorem inv_ibytes_ibytes_64 (x : BitVec 64) : inv_ibytes_ 64 (ibytes_ x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp [inv_ibytes_, ibytes_, List.range_succ, Nat.shiftRight_eq_div_pow]
  all_goals omega

/-- `ibytes_N` gives `N / 8` bytes. -/
theorem length_ibytes {n : Nat} (x : BitVec n) : (ibytes_ x).length = n / 8 := by
  simp [ibytes_]

/-! ## `UInt32` -/

section UInt32

theorem ofNat_toNat_32 (a : UInt32) : BitVec.ofNat 32 a.toNat = a.toBitVec := by simp

theorem iand_32 (a b : UInt32) : iand_ a.toBitVec b.toBitVec = (a &&& b).toBitVec := rfl
theorem ior_32 (a b : UInt32) : ior_ a.toBitVec b.toBitVec = (a ||| b).toBitVec := rfl
theorem ixor_32 (a b : UInt32) : ixor_ a.toBitVec b.toBitVec = (a ^^^ b).toBitVec := rfl
theorem inot_32 (a : UInt32) : inot_ a.toBitVec = (~~~a).toBitVec := rfl
theorem iandnot_32 (a b : UInt32) :
    iandnot_ a.toBitVec b.toBitVec = (a &&& ~~~b).toBitVec := rfl

theorem ishl_32 (a b : UInt32) : ishl_ a.toBitVec b.toNat = (a <<< b).toBitVec := by
  simp [ishl_, BitVec.shiftLeft_eq', BitVec.toNat_umod]

theorem ishr_u_32 (a b : UInt32) : ishr_ false a.toBitVec b.toNat = (a >>> b).toBitVec := by
  simp [ishr_, BitVec.ushiftRight_eq', BitVec.toNat_umod]

/-- `Int32`'s shift count is `smod 32`; on a count it is the same as `% 32`. -/
theorem smod_32 (b : BitVec 32) : (b.smod 32#32).toNat = b.toNat % 32 := by
  rw [BitVec.toNat_smod]
  have hm : (32#32).msb = false := by decide
  rw [hm]
  have hlt := b.isLt
  cases hb : b.msb
  · simp [BitVec.toNat_umod]
  · have hpos : b.toNat ≠ 0 := by
      intro h; have : b = 0#32 := BitVec.eq_of_toNat_eq (by simp [h]); subst this; simp at hb
    have hneg : (-b).toNat = 2 ^ 32 - b.toNat := by
      rw [BitVec.toNat_neg, Nat.mod_eq_of_lt (by omega)]
    have hu' : ((-b).umod 32#32).toNat = (2 ^ 32 - b.toNat) % 32 := by
      rw [show ((-b).umod 32#32) = (-b) % 32#32 from rfl, BitVec.toNat_umod, hneg]; rfl
    simp only
    split
    · rename_i hu
      have := congrArg BitVec.toNat hu
      rw [hu'] at this
      rw [hu']
      simp at this
      omega
    · rename_i hu
      have : ((-b).umod 32#32).toNat ≠ 0 :=
        fun h => hu (BitVec.eq_of_toNat_eq (by simpa using h))
      rw [hu'] at this
      rw [BitVec.toNat_sub, hu']
      simp
      omega

theorem ishr_s_32 (a b : UInt32) :
    ishr_ true a.toBitVec b.toNat = (a.toInt32 >>> b.toInt32).toUInt32.toBitVec := by
  have := smod_32 b.toBitVec
  simp only [ishr_, if_true, Int32.toBitVec_shiftRight, BitVec.sshiftRight_eq',
    Int32.toBitVec_toUInt32, UInt32.toBitVec_toInt32]
  simp_all

/-- Rotate left as an engine computes it, with two shifts. -/
theorem irotl_32 (a b : UInt32) :
    irotl_ a.toBitVec b.toNat = ((a <<< (b % 32)) ||| (a >>> (32 - b % 32))).toBitVec := by
  simp [irotl_, BitVec.rotateLeft_def, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
    BitVec.toNat_umod]
  rcases Nat.eq_zero_or_pos (b.toNat % 32) with hk | hk
  · rw [hk]; simp [BitVec.ushiftRight_eq_zero]
  · rw [show (4294967296 - b.toNat % 32) % 32 = 32 - b.toNat % 32 by omega]

/-- Rotate right as an engine computes it, with two shifts. -/
theorem irotr_32 (a b : UInt32) :
    irotr_ a.toBitVec b.toNat = ((a >>> (b % 32)) ||| (a <<< (32 - b % 32))).toBitVec := by
  simp [irotr_, BitVec.rotateRight_def, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
    BitVec.toNat_umod]
  rcases Nat.eq_zero_or_pos (b.toNat % 32) with hk | hk
  · rw [hk]; simp [BitVec.shiftLeft_eq_zero]
  · rw [show (4294967296 - b.toNat % 32) % 32 = 32 - b.toNat % 32 by omega]

theorem ieqz_32 (a : UInt32) : ieqz_ a.toBitVec = (a == 0) := by
  rw [Bool.eq_iff_iff]; simp [ieqz_, ← UInt32.toBitVec_inj]

theorem ilt_u_32 (a b : UInt32) : ilt_ false a.toBitVec b.toBitVec = decide (a < b) := by
  simp [ilt_, BitVec.ult, UInt32.lt_iff_toNat_lt]
theorem ilt_s_32 (a b : UInt32) :
    ilt_ true a.toBitVec b.toBitVec = decide (a.toInt32 < b.toInt32) := by
  simp [ilt_, BitVec.slt, Int32.lt_iff_toInt_lt, Int32.toInt]
theorem igt_u_32 (a b : UInt32) : igt_ false a.toBitVec b.toBitVec = decide (a > b) :=
  ilt_u_32 b a
theorem igt_s_32 (a b : UInt32) :
    igt_ true a.toBitVec b.toBitVec = decide (a.toInt32 > b.toInt32) := ilt_s_32 b a
theorem ile_u_32 (a b : UInt32) : ile_ false a.toBitVec b.toBitVec = decide (a ≤ b) := by
  simp [ile_, BitVec.ule, UInt32.le_iff_toNat_le]
theorem ile_s_32 (a b : UInt32) :
    ile_ true a.toBitVec b.toBitVec = decide (a.toInt32 ≤ b.toInt32) := by
  simp [ile_, BitVec.sle, Int32.le_iff_toInt_le, Int32.toInt]
theorem ige_u_32 (a b : UInt32) : ige_ false a.toBitVec b.toBitVec = decide (a ≥ b) :=
  ile_u_32 b a
theorem ige_s_32 (a b : UInt32) :
    ige_ true a.toBitVec b.toBitVec = decide (a.toInt32 ≥ b.toInt32) := ile_s_32 b a

theorem wrap_64_32 (a : UInt64) : wrap_ 32 a.toBitVec = a.toUInt32.toBitVec := by
  simp [wrap_]
theorem extend_u_32_64 (a : UInt32) : extend_ 64 false a.toBitVec = a.toUInt64.toBitVec := by
  simp [extend_]
theorem extend_s_32_64 (a : UInt32) :
    extend_ 64 true a.toBitVec = a.toInt32.toInt64.toUInt64.toBitVec := by
  simp [extend_]
/-- `i32.extend8_s`. -/
theorem iextend_s_8_32 (a : UInt32) :
    iextend_ 8 true a.toBitVec = a.toUInt8.toInt8.toInt32.toUInt32.toBitVec := by
  simp [iextend_, extend_, wrap_]
/-- `i32.extend16_s`. -/
theorem iextend_s_16_32 (a : UInt32) :
    iextend_ 16 true a.toBitVec = a.toUInt16.toInt16.toInt32.toUInt32.toBitVec := by
  simp [iextend_, extend_, wrap_]
/-- `i32.load8_u` after the byte is read: zero extension of a `UInt8`. -/
theorem extend_u_8_32 (a : UInt8) : extend_ 32 false a.toBitVec = a.toUInt32.toBitVec := by
  simp [extend_]
/-- `i32.load8_s` after the byte is read. -/
theorem extend_s_8_32 (a : UInt8) :
    extend_ 32 true a.toBitVec = a.toInt8.toInt32.toUInt32.toBitVec := by
  simp [extend_]
theorem extend_u_16_32 (a : UInt16) : extend_ 32 false a.toBitVec = a.toUInt32.toBitVec := by
  simp [extend_]
theorem extend_s_16_32 (a : UInt16) :
    extend_ 32 true a.toBitVec = a.toInt16.toInt32.toUInt32.toBitVec := by
  simp [extend_]
/-- `i32.store8` and `i32.store16` store `wrap` of the value. -/
theorem wrap_32_8 (a : UInt32) : wrap_ 8 a.toBitVec = a.toUInt8.toBitVec := by simp [wrap_]
theorem wrap_32_16 (a : UInt32) : wrap_ 16 a.toBitVec = a.toUInt16.toBitVec := by simp [wrap_]

/-- The stored bytes of an `i32`, as an engine writes them: low byte first. -/
theorem ibytes_32 (a : UInt32) :
    ibytes_ a.toBitVec = [a.toUInt8.toBitVec, (a >>> 8).toUInt8.toBitVec,
      (a >>> 16).toUInt8.toBitVec, (a >>> 24).toUInt8.toBitVec] := by
  simp [ibytes_, List.range_succ]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp [Nat.shiftRight_eq_div_pow] <;> omega

end UInt32

/-! ## `UInt64` -/

section UInt64

theorem ofNat_toNat_64 (a : UInt64) : BitVec.ofNat 64 a.toNat = a.toBitVec := by simp

theorem iand_64 (a b : UInt64) : iand_ a.toBitVec b.toBitVec = (a &&& b).toBitVec := rfl
theorem ior_64 (a b : UInt64) : ior_ a.toBitVec b.toBitVec = (a ||| b).toBitVec := rfl
theorem ixor_64 (a b : UInt64) : ixor_ a.toBitVec b.toBitVec = (a ^^^ b).toBitVec := rfl
theorem inot_64 (a : UInt64) : inot_ a.toBitVec = (~~~a).toBitVec := rfl
theorem iandnot_64 (a b : UInt64) :
    iandnot_ a.toBitVec b.toBitVec = (a &&& ~~~b).toBitVec := rfl

theorem ishl_64 (a b : UInt64) : ishl_ a.toBitVec b.toNat = (a <<< b).toBitVec := by
  simp [ishl_, BitVec.shiftLeft_eq', BitVec.toNat_umod]

theorem ishr_u_64 (a b : UInt64) : ishr_ false a.toBitVec b.toNat = (a >>> b).toBitVec := by
  simp [ishr_, BitVec.ushiftRight_eq', BitVec.toNat_umod]

/-- `Int64`'s shift count is `smod 64`; on a count it is the same as `% 64`. -/
theorem smod_64 (b : BitVec 64) : (b.smod 64#64).toNat = b.toNat % 64 := by
  rw [BitVec.toNat_smod]
  have hm : (64#64).msb = false := by decide
  rw [hm]
  have hlt := b.isLt
  cases hb : b.msb
  · simp [BitVec.toNat_umod]
  · have hpos : b.toNat ≠ 0 := by
      intro h; have : b = 0#64 := BitVec.eq_of_toNat_eq (by simp [h]); subst this; simp at hb
    have hneg : (-b).toNat = 2 ^ 64 - b.toNat := by
      rw [BitVec.toNat_neg, Nat.mod_eq_of_lt (by omega)]
    have hu' : ((-b).umod 64#64).toNat = (2 ^ 64 - b.toNat) % 64 := by
      rw [show ((-b).umod 64#64) = (-b) % 64#64 from rfl, BitVec.toNat_umod, hneg]; rfl
    simp only
    split
    · rename_i hu
      have := congrArg BitVec.toNat hu
      rw [hu'] at this
      rw [hu']
      simp at this
      omega
    · rename_i hu
      have : ((-b).umod 64#64).toNat ≠ 0 :=
        fun h => hu (BitVec.eq_of_toNat_eq (by simpa using h))
      rw [hu'] at this
      rw [BitVec.toNat_sub, hu']
      simp
      omega

theorem ishr_s_64 (a b : UInt64) :
    ishr_ true a.toBitVec b.toNat = (a.toInt64 >>> b.toInt64).toUInt64.toBitVec := by
  have := smod_64 b.toBitVec
  simp only [ishr_, if_true, Int64.toBitVec_shiftRight, BitVec.sshiftRight_eq',
    Int64.toBitVec_toUInt64, UInt64.toBitVec_toInt64]
  simp_all

theorem irotl_64 (a b : UInt64) :
    irotl_ a.toBitVec b.toNat = ((a <<< (b % 64)) ||| (a >>> (64 - b % 64))).toBitVec := by
  simp [irotl_, BitVec.rotateLeft_def, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
    BitVec.toNat_umod]
  rcases Nat.eq_zero_or_pos (b.toNat % 64) with hk | hk
  · rw [hk]; simp [BitVec.ushiftRight_eq_zero]
  · rw [show (18446744073709551616 - b.toNat % 64) % 64 = 64 - b.toNat % 64 by omega]

theorem irotr_64 (a b : UInt64) :
    irotr_ a.toBitVec b.toNat = ((a >>> (b % 64)) ||| (a <<< (64 - b % 64))).toBitVec := by
  simp [irotr_, BitVec.rotateRight_def, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
    BitVec.toNat_umod]
  rcases Nat.eq_zero_or_pos (b.toNat % 64) with hk | hk
  · rw [hk]; simp [BitVec.shiftLeft_eq_zero]
  · rw [show (18446744073709551616 - b.toNat % 64) % 64 = 64 - b.toNat % 64 by omega]

theorem ieqz_64 (a : UInt64) : ieqz_ a.toBitVec = (a == 0) := by
  rw [Bool.eq_iff_iff]; simp [ieqz_, ← UInt64.toBitVec_inj]

theorem ilt_u_64 (a b : UInt64) : ilt_ false a.toBitVec b.toBitVec = decide (a < b) := by
  simp [ilt_, BitVec.ult, UInt64.lt_iff_toNat_lt]
theorem ilt_s_64 (a b : UInt64) :
    ilt_ true a.toBitVec b.toBitVec = decide (a.toInt64 < b.toInt64) := by
  simp [ilt_, BitVec.slt, Int64.lt_iff_toInt_lt, Int64.toInt]
theorem igt_u_64 (a b : UInt64) : igt_ false a.toBitVec b.toBitVec = decide (a > b) :=
  ilt_u_64 b a
theorem igt_s_64 (a b : UInt64) :
    igt_ true a.toBitVec b.toBitVec = decide (a.toInt64 > b.toInt64) := ilt_s_64 b a
theorem ile_u_64 (a b : UInt64) : ile_ false a.toBitVec b.toBitVec = decide (a ≤ b) := by
  simp [ile_, BitVec.ule, UInt64.le_iff_toNat_le]
theorem ile_s_64 (a b : UInt64) :
    ile_ true a.toBitVec b.toBitVec = decide (a.toInt64 ≤ b.toInt64) := by
  simp [ile_, BitVec.sle, Int64.le_iff_toInt_le, Int64.toInt]
theorem ige_u_64 (a b : UInt64) : ige_ false a.toBitVec b.toBitVec = decide (a ≥ b) :=
  ile_u_64 b a
theorem ige_s_64 (a b : UInt64) :
    ige_ true a.toBitVec b.toBitVec = decide (a.toInt64 ≥ b.toInt64) := ile_s_64 b a

/-- `i64.extend8_s`. -/
theorem iextend_s_8_64 (a : UInt64) :
    iextend_ 8 true a.toBitVec = a.toUInt8.toInt8.toInt64.toUInt64.toBitVec := by
  simp [iextend_, extend_, wrap_]
/-- `i64.extend16_s`. -/
theorem iextend_s_16_64 (a : UInt64) :
    iextend_ 16 true a.toBitVec = a.toUInt16.toInt16.toInt64.toUInt64.toBitVec := by
  simp [iextend_, extend_, wrap_]
/-- `i64.extend32_s`. -/
theorem iextend_s_32_64 (a : UInt64) :
    iextend_ 32 true a.toBitVec = a.toUInt32.toInt32.toInt64.toUInt64.toBitVec := by
  simp [iextend_, extend_, wrap_]
theorem extend_u_8_64 (a : UInt8) : extend_ 64 false a.toBitVec = a.toUInt64.toBitVec := by
  simp [extend_]
theorem extend_s_8_64 (a : UInt8) :
    extend_ 64 true a.toBitVec = a.toInt8.toInt64.toUInt64.toBitVec := by
  simp [extend_]
theorem extend_u_16_64 (a : UInt16) : extend_ 64 false a.toBitVec = a.toUInt64.toBitVec := by
  simp [extend_]
theorem extend_s_16_64 (a : UInt16) :
    extend_ 64 true a.toBitVec = a.toInt16.toInt64.toUInt64.toBitVec := by
  simp [extend_]
theorem wrap_64_8 (a : UInt64) : wrap_ 8 a.toBitVec = a.toUInt8.toBitVec := by simp [wrap_]
theorem wrap_64_16 (a : UInt64) : wrap_ 16 a.toBitVec = a.toUInt16.toBitVec := by simp [wrap_]

/-- The stored bytes of an `i64`, as an engine writes them: low byte first. -/
theorem ibytes_64 (a : UInt64) :
    ibytes_ a.toBitVec = [a.toUInt8.toBitVec, (a >>> 8).toUInt8.toBitVec,
      (a >>> 16).toUInt8.toBitVec, (a >>> 24).toUInt8.toBitVec,
      (a >>> 32).toUInt8.toBitVec, (a >>> 40).toUInt8.toBitVec,
      (a >>> 48).toUInt8.toBitVec, (a >>> 56).toUInt8.toBitVec] := by
  simp [ibytes_, List.range_succ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp [Nat.shiftRight_eq_div_pow] <;> omega

end UInt64

end L4Factoidal.WasmVM.Spec.Builtins
