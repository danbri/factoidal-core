/-
L4Factoidal.WasmVM.Proofs.SpecWPOps: `Sem` rules for the integer instructions of
`SpecWP`, each proved from the generated spec rules (record:
docs/designissues/2026-11-09-verified-foaf-layout.md).

Values: `i32v k` is the i32 constant `k mod 2^32` (a `Nat`); `i64v x` is the i64
constant whose two's complement value is `x mod 2^64` (an `Int`). Integer addition,
subtraction and multiplication then hold with no side condition (`i64v (x + y)` and so
on); signed comparisons need both operands in the signed range, unsigned ones in
`[0, 2^32)`. Covered: `local.get/set/tee`, `i32.add/mul/ge_u/ne`,
`i64.add/sub/mul/gt_s/lt_s/le_s`, `i64.extend_i32_u`, `select`, `i32.load`, `i32.store`
(memory 0). No float instruction: the generated layer leaves every float operator
opaque, so no theorem about one could say what it computes.
-/
import L4Factoidal.WasmVM.Proofs.SpecWP

namespace L4Factoidal.WasmVM.Proofs.SpecWP
open L4Factoidal.WasmVM Proofs.Refine

/-! ### Encodings -/

/-- The two's complement bits of `x` in 64 bits. -/
def enc64 (x : Int) : Nat := (x % 2^64).toNat

theorem enc64_cast (x : Int) : ((enc64 x : Nat) : Int) = x % 2^64 :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))

theorem enc64_lt (x : Int) : enc64 x < 2^64 := by
  have := enc64_cast x
  have h2 : x % 2^64 < 2^64 := Int.emod_lt_of_pos _ (by decide)
  omega

theorem enc64_toInt (x : Int) (h1 : -2^63 ≤ x) (h2 : x < 2^63) :
    (BitVec.ofNat 64 (enc64 x)).toInt = x := by
  rw [BitVec.toInt_ofNat', enc64_cast]
  simp only [Int.bmod]
  omega

theorem enc64_add (x y : Int) : (enc64 x + enc64 y) % 2^64 = enc64 (x + y) := by
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod, Int.natCast_add, enc64_cast, enc64_cast, enc64_cast]
  simp only [Int.natCast_pow, Int.cast_ofNat_Int]
  omega

theorem enc64_sub (x y : Int) :
    (Int.toNat ((Int.ofNat (2^64 + enc64 x) - Int.ofNat (enc64 y)) % Int.ofNat (2^64))) = enc64 (x - y) := by
  apply Int.ofNat_inj.mp
  have h := Int.emod_nonneg ((Int.ofNat (2^64 + enc64 x) - Int.ofNat (enc64 y))) (by decide : Int.ofNat (2^64) ≠ 0)
  rw [Int.toNat_of_nonneg h, enc64_cast]
  simp only [Int.ofNat_eq_natCast, Int.natCast_add, enc64_cast, Int.natCast_pow, Int.cast_ofNat_Int]
  omega

theorem enc64_mul (x y : Int) : (enc64 x * enc64 y) % 2^64 = enc64 (x * y) := by
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod, Int.natCast_mul, enc64_cast, enc64_cast, enc64_cast]
  simp only [Int.natCast_pow, Int.cast_ofNat_Int]
  rw [← Int.mul_emod]

theorem enc64_nat (k : Nat) (h : k < 2^64) : enc64 k = k := by
  apply Int.ofNat_inj.mp; rw [enc64_cast]; omega

/-- An i32 constant, `k mod 2^32`. -/
noncomputable def i32v (k : Nat) : Spec.val := i32c (k % 2^32)
/-- An i64 constant, `x mod 2^64`. -/
noncomputable def i64v (x : Int) : Spec.val := i64c (enc64 x)

theorem wf_i64 (n : Nat) (h : n < 2^64) : Spec.wf_num_ .I64 (.mk_num__0 .I64 (.mk_uN n)) := by
  refine Spec.wf_num_.num__case_0 _ _ _ ?_ (by rfl)
  refine Spec.wf_uN.uN_case_0 _ _ ?_
  have e : (Int.ofNat (2 ^ 64) - Int.ofNat 1).toNat = 2 ^ 64 - 1 := by decide
  simp only [Spec.size, Spec.numtype_Inn, Spec.sizenn, e, ge_iff_le, Nat.zero_le, decide_true, Bool.true_and,
    decide_eq_true_eq]
  omega

theorem uN_beq_self (u : Spec.uN) : (u == u) = true := by
  cases u; simp [BEq.beq, Spec.instBEqUN.beq]

theorem num_beq_self64 (n : Nat) :
    (Spec.num_.mk_num__0 .I64 (.mk_uN n) == Spec.num_.mk_num__0 .I64 (.mk_uN n)) = true :=
  num64_beq_self n

theorem num_beq_self32 (n : Nat) :
    (Spec.num_.mk_num__0 .I32 (.mk_uN n) == Spec.num_.mk_num__0 .I32 (.mk_uN n)) = true := by
  simp [BEq.beq, Spec.instBEqNum_.beq, Spec.instBEqUN.beq, Spec.instBEqInn.beq]

/-! ### Locals -/

theorem sem_localGet {z pre x v rest Q} {B : BrPost}
    (hv : Spec.fun_local z (.mk_uN x) = some v) (h : Sem z (pre ++ [v]) rest Q B) :
    Sem z pre (.LOCAL_GET (.mk_uN x) :: rest) Q B := by
  have := sem_step (pre := pre) (ws := []) (ws' := [v]) (rest := rest) (Q := Q) (B := B)
    (z := z) (z' := z) (i := .LOCAL_GET (.mk_uN x))
    (Spec.Step.read _ _ _ (Spec.Step_read.local_get _ _ v (by rw [hv]; exact option_val_beq_self _)))
    h
  simpa using this

theorem sem_localSet {z pre x v rest Q} {B : BrPost}
    (h : Sem (Spec.with_local z (.mk_uN x) v) pre rest Q B) :
    Sem z (pre ++ [v]) (.LOCAL_SET (.mk_uN x) :: rest) Q B := by
  have := sem_step (pre := pre) (ws := [v]) (ws' := []) (rest := rest) (Q := Q) (B := B)
    (z := z) (i := .LOCAL_SET (.mk_uN x)) (Spec.Step.local_set z v (.mk_uN x)) (by simpa using h)
  simpa using this

theorem sem_localTee {z pre x v rest Q} {B : BrPost}
    (h : Sem (Spec.with_local z (.mk_uN x) v) (pre ++ [v]) rest Q B) :
    Sem z (pre ++ [v]) (.LOCAL_TEE (.mk_uN x) :: rest) Q B := by
  refine sem_pure_to (ws := [v]) (Spec.Step_pure.local_tee v (.mk_uN x)) ?_
  exact sem_val (sem_val (by simpa using (sem_localSet (pre := pre ++ [v]) h)))

/-- A constant instruction. -/
theorem sem_i32const {z pre k rest Q} {B : BrPost} (h : Sem z (pre ++ [i32v k]) rest Q B) (hk : k < 2^32) :
    Sem z pre (.CONST .I32 (.mk_num__0 .I32 (.mk_uN k)) :: rest) Q B := by
  have e : Spec.instr_val (i32v k) = .CONST .I32 (.mk_num__0 .I32 (.mk_uN k)) := by
    simp [i32v, i32c, Spec.instr_val, Nat.mod_eq_of_lt hk]
  rw [← e]; exact sem_val h

theorem sem_i64const {z pre} {k : Nat} {rest Q} {B : BrPost} (h : Sem z (pre ++ [i64v (k : Int)]) rest Q B) (hk : k < 2^64) :
    Sem z pre (.CONST .I64 (.mk_num__0 .I64 (.mk_uN k)) :: rest) Q B := by
  have e : Spec.instr_val (i64v k) = .CONST .I64 (.mk_num__0 .I64 (.mk_uN k)) := by
    simp [i64v, i64c, Spec.instr_val, enc64_nat k hk]
  rw [← e]; exact sem_val h

/-! ### Binary operations -/

theorem bin64_step (bop : Spec.binop_Inn) (a b r : Nat) (hr : r < 2^64) (ha : a < 2^64) (hb : b < 2^64)
    (hf : Spec.wf_num_ .I64 (.mk_num__0 .I64 (.mk_uN r)) →
      Spec.fun_binop_ .I64 (.mk_binop__0 .I64 bop) (.mk_num__0 .I64 (.mk_uN a)) (.mk_num__0 .I64 (.mk_uN b))
        [.mk_num__0 .I64 (.mk_uN r)]) :
    Spec.Step_pure (vals [i64c a, i64c b] ++ [.BINOP .I64 (.mk_binop__0 .I64 bop)]) (vals [i64c r]) := by
  have := Spec.Step_pure.binop_val .I64 (.mk_num__0 .I64 (.mk_uN a)) (.mk_num__0 .I64 (.mk_uN b))
    (.mk_binop__0 .I64 bop) (.mk_num__0 .I64 (.mk_uN r)) [.mk_num__0 .I64 (.mk_uN r)]
    (hf (wf_i64 r hr)) (wf_i64 a ha) (wf_i64 b hb) (.binop__case_0 _ .I64 _ (by decide)) (wf_i64 r hr)
    (by simp) (by simp [List.contains, List.elem, num64_beq_self])
  simpa [vals, i64c, Spec.instr_val] using this

theorem bin32_step (bop : Spec.binop_Inn) (a b r : Nat) (hr : r < 2^32) (ha : a < 2^32) (hb : b < 2^32)
    (hf : Spec.wf_num_ .I32 (.mk_num__0 .I32 (.mk_uN r)) →
      Spec.fun_binop_ .I32 (.mk_binop__0 .I32 bop) (.mk_num__0 .I32 (.mk_uN a)) (.mk_num__0 .I32 (.mk_uN b))
        [.mk_num__0 .I32 (.mk_uN r)]) :
    Spec.Step_pure (vals [i32c a, i32c b] ++ [.BINOP .I32 (.mk_binop__0 .I32 bop)]) (vals [i32c r]) := by
  have := Spec.Step_pure.binop_val .I32 (.mk_num__0 .I32 (.mk_uN a)) (.mk_num__0 .I32 (.mk_uN b))
    (.mk_binop__0 .I32 bop) (.mk_num__0 .I32 (.mk_uN r)) [.mk_num__0 .I32 (.mk_uN r)]
    (hf (wf_i32 r hr)) (wf_i32 a ha) (wf_i32 b hb) (.binop__case_0 _ .I32 _ (by decide)) (wf_i32 r hr)
    (by simp) (by simp [List.contains, List.elem, num_beq_self32])
  simpa [vals, i32c, Spec.instr_val] using this

theorem sem_i64add {z pre x y rest Q} {B : BrPost} (h : Sem z (pre ++ [i64v (x + y)]) rest Q B) :
    Sem z (pre ++ [i64v x, i64v y]) (.BINOP .I64 (.mk_binop__0 .I64 .ADD) :: rest) Q B := by
  refine sem_pure (ws' := [i64v (x + y)]) ?_ h
  have e : Spec.iadd_ (Spec.sizenn (Spec.numtype_Inn .I64)) (.mk_uN (enc64 x)) (.mk_uN (enc64 y)) = .mk_uN (enc64 (x + y)) := by
    simp only [Spec.iadd_, Spec.sizenn, Spec.size, Spec.numtype_Inn, Spec.proj_uN_0]
    rw [enc64_add]
  exact bin64_step .ADD _ _ _ (enc64_lt _) (enc64_lt _) (enc64_lt _) (fun hw => by
    have := Spec.fun_binop_.fun_binop__case_1 (.mk_uN (enc64 x)) (.mk_uN (enc64 y)) (by rw [e]; exact hw)
    rwa [e] at this)

theorem sem_i64sub {z pre x y rest Q} {B : BrPost} (h : Sem z (pre ++ [i64v (x - y)]) rest Q B) :
    Sem z (pre ++ [i64v x, i64v y]) (.BINOP .I64 (.mk_binop__0 .I64 .SUB) :: rest) Q B := by
  refine sem_pure (ws' := [i64v (x - y)]) ?_ h
  have e : Spec.isub_ (Spec.sizenn (Spec.numtype_Inn .I64)) (.mk_uN (enc64 x)) (.mk_uN (enc64 y)) = .mk_uN (enc64 (x - y)) := by
    simp only [Spec.isub_, Spec.sizenn, Spec.size, Spec.numtype_Inn, Spec.proj_uN_0]
    rw [enc64_sub]
  exact bin64_step .SUB _ _ _ (enc64_lt _) (enc64_lt _) (enc64_lt _) (fun hw => by
    have := Spec.fun_binop_.fun_binop__case_3 (.mk_uN (enc64 x)) (.mk_uN (enc64 y)) (by rw [e]; exact hw)
    rwa [e] at this)

theorem sem_i64mul {z pre x y rest Q} {B : BrPost} (h : Sem z (pre ++ [i64v (x * y)]) rest Q B) :
    Sem z (pre ++ [i64v x, i64v y]) (.BINOP .I64 (.mk_binop__0 .I64 .MUL) :: rest) Q B := by
  refine sem_pure (ws' := [i64v (x * y)]) ?_ h
  have e : Spec.imul_ (Spec.sizenn (Spec.numtype_Inn .I64)) (.mk_uN (enc64 x)) (.mk_uN (enc64 y)) = .mk_uN (enc64 (x * y)) := by
    simp only [Spec.imul_, Spec.sizenn, Spec.size, Spec.numtype_Inn, Spec.proj_uN_0]
    rw [enc64_mul]
  exact bin64_step .MUL _ _ _ (enc64_lt _) (enc64_lt _) (enc64_lt _) (fun hw => by
    have := Spec.fun_binop_.fun_binop__case_5 (.mk_uN (enc64 x)) (.mk_uN (enc64 y)) (by rw [e]; exact hw)
    rwa [e] at this)

theorem mod32_lt (k : Nat) : k % 2^32 < 2^32 := Nat.mod_lt _ (by decide)

theorem sem_i32add {z pre a b rest Q} {B : BrPost} (h : Sem z (pre ++ [i32v (a + b)]) rest Q B) :
    Sem z (pre ++ [i32v a, i32v b]) (.BINOP .I32 (.mk_binop__0 .I32 .ADD) :: rest) Q B := by
  refine sem_pure (ws' := [i32v (a + b)]) ?_ h
  have e : Spec.iadd_ (Spec.sizenn (Spec.numtype_Inn .I32)) (.mk_uN (a % 2^32)) (.mk_uN (b % 2^32)) = .mk_uN ((a + b) % 2^32) := by
    simp [Spec.iadd_, Spec.sizenn, Spec.size, Spec.numtype_Inn, Spec.proj_uN_0]
  exact bin32_step .ADD _ _ _ (mod32_lt _) (mod32_lt _) (mod32_lt _) (fun hw => by
    have := Spec.fun_binop_.fun_binop__case_0 (.mk_uN (a % 2^32)) (.mk_uN (b % 2^32)) (by rw [e]; exact hw)
    rwa [e] at this)

theorem sem_i32mul {z pre a b rest Q} {B : BrPost} (h : Sem z (pre ++ [i32v (a * b)]) rest Q B) :
    Sem z (pre ++ [i32v a, i32v b]) (.BINOP .I32 (.mk_binop__0 .I32 .MUL) :: rest) Q B := by
  refine sem_pure (ws' := [i32v (a * b)]) ?_ h
  have e : Spec.imul_ (Spec.sizenn (Spec.numtype_Inn .I32)) (.mk_uN (a % 2^32)) (.mk_uN (b % 2^32)) = .mk_uN ((a * b) % 2^32) := by
    simp only [Spec.imul_, Spec.sizenn, Spec.size, Spec.numtype_Inn, Spec.proj_uN_0]
    rw [← Nat.mul_mod]
  exact bin32_step .MUL _ _ _ (mod32_lt _) (mod32_lt _) (mod32_lt _) (fun hw => by
    have := Spec.fun_binop_.fun_binop__case_4 (.mk_uN (a % 2^32)) (.mk_uN (b % 2^32)) (by rw [e]; exact hw)
    rwa [e] at this)

/-! ### Comparisons -/

theorem rel_step (nt : Spec.numtype) (rop : Spec.relop_) (c1 c2 : Spec.num_) (r : Nat)
    (hr : Spec.fun_relop_ nt rop c1 c2 = .mk_uN r) (hr32 : r < 2^32)
    (w1 : Spec.wf_num_ nt c1) (w2 : Spec.wf_num_ nt c2) (wr : Spec.wf_relop_ nt rop) :
    Spec.Step_pure [.CONST nt c1, .CONST nt c2, .RELOP nt rop] [.CONST .I32 (.mk_num__0 .I32 (.mk_uN r))] :=
  Spec.Step_pure.relop nt c1 c2 rop _ w1 w2 wr (wf_i32 r hr32) (by rfl)
    (by simp only [Spec.proj_num__0, Option.get!_some, hr]; exact uN_beq_self _)

theorem bool01 (b : Bool) : Spec.Builtins.OnNat.bool b = if b then 1 else 0 := rfl

/-- `i64.gt_s`, `i64.lt_s`, `i64.le_s` on operands in the signed range. -/
theorem sem_i64rel {z pre x y rest Q} {B : BrPost} (rop : Spec.relop_Inn) (p : Prop) [Decidable p]
    (hx1 : -2^63 ≤ x) (hx2 : x < 2^63) (hy1 : -2^63 ≤ y) (hy2 : y < 2^63)
    (hp : Spec.fun_relop_ .I64 (.mk_relop__0 .I64 rop) (.mk_num__0 .I64 (.mk_uN (enc64 x)))
      (.mk_num__0 .I64 (.mk_uN (enc64 y))) = .mk_uN (if p then 1 else 0))
    (h : Sem z (pre ++ [i32v (if p then 1 else 0)]) rest Q B) :
    Sem z (pre ++ [i64v x, i64v y]) (.RELOP .I64 (.mk_relop__0 .I64 rop) :: rest) Q B := by
  refine sem_pure (ws' := [i32v (if p then 1 else 0)]) ?_ h
  have hlt : (if p then 1 else 0) < 2^32 := by split <;> decide
  have := rel_step .I64 (.mk_relop__0 .I64 rop) _ _ _ hp hlt (wf_i64 _ (enc64_lt x)) (wf_i64 _ (enc64_lt y))
    (.relop__case_0 _ .I64 _ (by decide))
  simpa [vals, i64v, i64c, i32v, i32c, Spec.instr_val, Nat.mod_eq_of_lt hlt] using this

theorem gt_s_64 (x y : Int) (hx1 : -2^63 ≤ x) (hx2 : x < 2^63) (hy1 : -2^63 ≤ y) (hy2 : y < 2^63) :
    Spec.fun_relop_ .I64 (.mk_relop__0 .I64 (.GT .S)) (.mk_num__0 .I64 (.mk_uN (enc64 x)))
      (.mk_num__0 .I64 (.mk_uN (enc64 y))) = .mk_uN (if x > y then 1 else 0) := by
  simp only [Spec.fun_relop_, Spec.igt_, Spec.sizenn, Spec.size, Spec.numtype_Inn, Spec.proj_uN_0,
    Spec.Builtins.OnNat.igt_, Spec.Builtins.igt_, Spec.Builtins.ilt_, if_true, bool01]
  have hi : (BitVec.ofNat 64 (enc64 y)).slt (BitVec.ofNat 64 (enc64 x)) = true ↔ x > y := by
    rw [BitVec.slt_iff_toInt_lt, enc64_toInt x hx1 hx2, enc64_toInt y hy1 hy2]
  by_cases h : x > y
  · rw [if_pos (hi.mpr h), if_pos h]
  · rw [if_neg (fun e => h (hi.mp e)), if_neg h]

theorem lt_s_64 (x y : Int) (hx1 : -2^63 ≤ x) (hx2 : x < 2^63) (hy1 : -2^63 ≤ y) (hy2 : y < 2^63) :
    Spec.fun_relop_ .I64 (.mk_relop__0 .I64 (.LT .S)) (.mk_num__0 .I64 (.mk_uN (enc64 x)))
      (.mk_num__0 .I64 (.mk_uN (enc64 y))) = .mk_uN (if x < y then 1 else 0) := by
  simp only [Spec.fun_relop_, Spec.ilt_, Spec.sizenn, Spec.size, Spec.numtype_Inn, Spec.proj_uN_0,
    Spec.Builtins.OnNat.ilt_, Spec.Builtins.ilt_, if_true, bool01]
  have hi : (BitVec.ofNat 64 (enc64 x)).slt (BitVec.ofNat 64 (enc64 y)) = true ↔ x < y := by
    rw [BitVec.slt_iff_toInt_lt, enc64_toInt x hx1 hx2, enc64_toInt y hy1 hy2]
  by_cases h : x < y
  · rw [if_pos (hi.mpr h), if_pos h]
  · rw [if_neg (fun e => h (hi.mp e)), if_neg h]

theorem le_s_64 (x y : Int) (hx1 : -2^63 ≤ x) (hx2 : x < 2^63) (hy1 : -2^63 ≤ y) (hy2 : y < 2^63) :
    Spec.fun_relop_ .I64 (.mk_relop__0 .I64 (.LE .S)) (.mk_num__0 .I64 (.mk_uN (enc64 x)))
      (.mk_num__0 .I64 (.mk_uN (enc64 y))) = .mk_uN (if x ≤ y then 1 else 0) := by
  simp only [Spec.fun_relop_, Spec.ile_, Spec.sizenn, Spec.size, Spec.numtype_Inn, Spec.proj_uN_0,
    Spec.Builtins.OnNat.ile_, Spec.Builtins.ile_, if_true, bool01]
  have hi : (BitVec.ofNat 64 (enc64 x)).sle (BitVec.ofNat 64 (enc64 y)) = true ↔ x ≤ y := by
    rw [BitVec.sle_iff_toInt_le, enc64_toInt x hx1 hx2, enc64_toInt y hy1 hy2]
  by_cases h : x ≤ y
  · rw [if_pos (hi.mpr h), if_pos h]
  · rw [if_neg (fun e => h (hi.mp e)), if_neg h]

theorem sem_i64gts {z pre x y rest Q} {B : BrPost}
    (hx1 : -2^63 ≤ x) (hx2 : x < 2^63) (hy1 : -2^63 ≤ y) (hy2 : y < 2^63)
    (h : Sem z (pre ++ [i32v (if x > y then 1 else 0)]) rest Q B) :
    Sem z (pre ++ [i64v x, i64v y]) (.RELOP .I64 (.mk_relop__0 .I64 (.GT .S)) :: rest) Q B :=
  sem_i64rel _ _ hx1 hx2 hy1 hy2 (gt_s_64 x y hx1 hx2 hy1 hy2) h

theorem sem_i64lts {z pre x y rest Q} {B : BrPost}
    (hx1 : -2^63 ≤ x) (hx2 : x < 2^63) (hy1 : -2^63 ≤ y) (hy2 : y < 2^63)
    (h : Sem z (pre ++ [i32v (if x < y then 1 else 0)]) rest Q B) :
    Sem z (pre ++ [i64v x, i64v y]) (.RELOP .I64 (.mk_relop__0 .I64 (.LT .S)) :: rest) Q B :=
  sem_i64rel _ _ hx1 hx2 hy1 hy2 (lt_s_64 x y hx1 hx2 hy1 hy2) h

theorem sem_i64les {z pre x y rest Q} {B : BrPost}
    (hx1 : -2^63 ≤ x) (hx2 : x < 2^63) (hy1 : -2^63 ≤ y) (hy2 : y < 2^63)
    (h : Sem z (pre ++ [i32v (if x ≤ y then 1 else 0)]) rest Q B) :
    Sem z (pre ++ [i64v x, i64v y]) (.RELOP .I64 (.mk_relop__0 .I64 (.LE .S)) :: rest) Q B :=
  sem_i64rel _ _ hx1 hx2 hy1 hy2 (le_s_64 x y hx1 hx2 hy1 hy2) h

/-- `i32.ge_u` on operands below `2^32`. -/
theorem sem_i32geu {z pre a b rest Q} {B : BrPost} (ha : a < 2^32) (hb : b < 2^32)
    (h : Sem z (pre ++ [i32v (if a ≥ b then 1 else 0)]) rest Q B) :
    Sem z (pre ++ [i32v a, i32v b]) (.RELOP .I32 (.mk_relop__0 .I32 (.GE .U)) :: rest) Q B := by
  refine sem_pure (ws' := [i32v (if a ≥ b then 1 else 0)]) ?_ h
  have hlt : (if a ≥ b then 1 else 0) < 2^32 := by split <;> decide
  have hp : Spec.fun_relop_ .I32 (.mk_relop__0 .I32 (.GE .U)) (.mk_num__0 .I32 (.mk_uN (a % 2^32)))
      (.mk_num__0 .I32 (.mk_uN (b % 2^32))) = .mk_uN (if a ≥ b then 1 else 0) := by
    simp only [Spec.fun_relop_, Spec.ige_, Spec.sizenn, Spec.size, Spec.numtype_Inn, Spec.proj_uN_0,
      Spec.Builtins.OnNat.ige_, Spec.Builtins.ige_, Spec.Builtins.ile_, bool01, Bool.false_eq_true, if_false]
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
    have hi : (BitVec.ofNat 32 b).ule (BitVec.ofNat 32 a) = true ↔ a ≥ b := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
    by_cases h : a ≥ b
    · rw [if_pos (hi.mpr h), if_pos h]
    · rw [if_neg (fun e => h (hi.mp e)), if_neg h]
  have := rel_step .I32 (.mk_relop__0 .I32 (.GE .U)) _ _ _ hp hlt (wf_i32_mod a) (wf_i32_mod b)
    (.relop__case_0 _ .I32 _ (by decide))
  simpa [vals, i32v, i32c, Spec.instr_val, Nat.mod_eq_of_lt hlt] using this

/-- `i32.ne`. -/
theorem sem_i32ne {z pre a b rest Q} {B : BrPost}
    (h : Sem z (pre ++ [i32v (if a % 2^32 ≠ b % 2^32 then 1 else 0)]) rest Q B) :
    Sem z (pre ++ [i32v a, i32v b]) (.RELOP .I32 (.mk_relop__0 .I32 .NE) :: rest) Q B := by
  refine sem_pure (ws' := [i32v (if a % 2^32 ≠ b % 2^32 then 1 else 0)]) ?_ h
  have hlt : (if a % 2^32 ≠ b % 2^32 then 1 else 0) < 2^32 := by split <;> decide
  have hp : Spec.fun_relop_ .I32 (.mk_relop__0 .I32 .NE) (.mk_num__0 .I32 (.mk_uN (a % 2^32)))
      (.mk_num__0 .I32 (.mk_uN (b % 2^32))) = .mk_uN (if a % 2^32 ≠ b % 2^32 then 1 else 0) := by
    simp only [Spec.fun_relop_, Spec.ine_]
    congr 1
    by_cases hab : a % 2^32 = b % 2^32
    · rw [hab]; simp [bne, uN_beq_self, Spec.nat_of_bool]
    · have : (Spec.uN.mk_uN (a % 2^32) == Spec.uN.mk_uN (b % 2^32)) = false := by
        simp [BEq.beq, Spec.instBEqUN.beq, hab]
      simp [bne, this, Spec.nat_of_bool, hab]
  have := rel_step .I32 (.mk_relop__0 .I32 .NE) _ _ _ hp hlt (wf_i32_mod a) (wf_i32_mod b)
    (.relop__case_0 _ .I32 _ (by decide))
  simp only [vals, i32v, i32c, List.map, Spec.instr_val, List.cons_append, List.nil_append]
  rw [Nat.mod_eq_of_lt hlt]; exact this

/-! ### Conversion and select -/

/-- `i64.extend_i32_u`. -/
theorem sem_i64extu {z pre} {k : Nat} {rest Q} {B : BrPost} (hk : k < 2^32) (h : Sem z (pre ++ [i64v (k : Int)]) rest Q B) :
    Sem z (pre ++ [i32v k]) (.CVTOP .I64 .I32 (.mk_cvtop___0 .I32 .I64 (.EXTEND .U)) :: rest) Q B := by
  refine sem_pure (ws' := [i64v (k : Int)]) ?_ h
  have hk64 : k < 2^64 := by omega
  have e : Spec.extend__ (Spec.sizenn1 (Spec.numtype_Inn .I32)) (Spec.sizenn2 (Spec.numtype_Inn .I64)) .U
      (.mk_uN k) = .mk_uN k := by
    simp only [Spec.extend__, Spec.sizenn1, Spec.sizenn2, Spec.size, Spec.numtype_Inn, Spec.proj_uN_0,
      Spec.Builtins.OnNat.extend_, Spec.Builtins.extend_, Bool.false_eq_true, if_false]
    congr 1
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk64]
  have hf := Spec.fun_cvtop__.fun_cvtop___case_2 .U (.mk_uN k) (by rw [e]; exact wf_i64 k hk64)
  rw [e] at hf
  have := Spec.Step_pure.cvtop_val .I32 (.mk_num__0 .I32 (.mk_uN k)) .I64 _ (.mk_num__0 .I64 (.mk_uN k)) _
    hf (wf_i32 k hk) (.cvtop___case_0 _ _ .I32 .I64 _ (.cvtop__Inn_1_Inn_2_case_0 _ _ _ (by decide)) (by decide) (by decide))
    (wf_i64 k hk64) (by simp) (by simp [List.contains, List.elem, num64_beq_self])
  simpa [vals, i32v, i32c, i64v, i64c, Spec.instr_val, Nat.mod_eq_of_lt hk, enc64_nat k hk64] using this

/-- `select` with an i32 condition `c`. -/
theorem sem_select {z pre v1 v2 c rest Q} {B : BrPost}
    (h : Sem z (pre ++ [if c % 2^32 = 0 then v2 else v1]) rest Q B) :
    Sem z (pre ++ [v1, v2, i32v c]) (.SELECT none :: rest) Q B := by
  by_cases hc : c % 2^32 = 0
  · rw [if_pos hc] at h
    refine sem_pure (ws' := [v2]) ?_ h
    have := Spec.Step_pure.select_false v1 v2 (.mk_num__0 .I32 (.mk_uN (c % 2^32))) none (wf_i32_mod c) (by rfl)
      (by simp [Spec.proj_num__0, Spec.proj_uN_0, hc])
    simpa [vals, i32v, i32c, Spec.instr_val] using this
  · rw [if_neg hc] at h
    refine sem_pure (ws' := [v1]) ?_ h
    have := Spec.Step_pure.select_true v1 v2 (.mk_num__0 .I32 (.mk_uN (c % 2^32))) none (wf_i32_mod c) (by rfl)
      (by simp [Spec.proj_num__0, Spec.proj_uN_0, hc])
    simpa [vals, i32v, i32c, Spec.instr_val] using this

/-! ### Memory 0 -/

/-- The memarg of an aligned 4-byte access at offset `off`. -/
def ma4 (off : Nat) : Spec.memarg := ⟨.mk_uN 2, .mk_uN off⟩

/-- `i32.load offset=off` on memory 0: the four bytes at `a + off` are `nbytes_` of `k`. -/
theorem sem_load32 {z pre a off k rest Q} {B : BrPost} (hk : k < 2^32)
    (hbytes : List.take 4 (List.drop (a % 2^32 + off) (Spec.fun_mem z (.mk_uN 0)).BYTES) =
      Spec.nbytes_ .I32 (.mk_num__0 .I32 (.mk_uN k)))
    (h : Sem z (pre ++ [i32v k]) rest Q B) :
    Sem z (pre ++ [i32v a]) (.LOAD .I32 none (.mk_uN 0) (ma4 off) :: rest) Q B := by
  refine sem_step (z' := z) (ws' := [i32v k]) ?_ h
  have := Spec.Step_read.load_num_val z .I32 (.mk_num__0 .I32 (.mk_uN (a % 2^32))) .I32 (.mk_uN 0) (ma4 off)
    (.mk_num__0 .I32 (.mk_uN k)) (wf_i32_mod a) (wf_i32 k hk) (by rfl)
    (by simp only [Spec.proj_num__0, Option.get!_some, Spec.proj_uN_0, ma4, floor4, hbytes]; exact bytes_beq_self _)
  have := Spec.Step.read _ _ _ this
  simpa [vals, i32v, i32c, Spec.instr_val, Spec.numtype_addrtype, Nat.mod_eq_of_lt hk] using this

/-- `i32.store offset=off` on memory 0 of the value `k`. -/
theorem sem_store32 {z pre a off k rest Q} {B : BrPost}
    (h : Sem (Spec.with_mem z (.mk_uN 0) (a % 2^32 + off) 4 (Spec.nbytes_ .I32 (.mk_num__0 .I32 (.mk_uN (k % 2^32)))))
      pre rest Q B) :
    Sem z (pre ++ [i32v a, i32v k]) (.STORE .I32 none (.mk_uN 0) (ma4 off) :: rest) Q B := by
  refine sem_step (ws' := []) ?_ (by simpa using h)
  have := floor4
  have := Spec.Step.store_num_val z .I32 (.mk_num__0 .I32 (.mk_uN (a % 2^32))) .I32
    (.mk_num__0 .I32 (.mk_uN (k % 2^32))) (.mk_uN 0) (ma4 off) _ (by rfl) (wf_i32_mod a) (wf_i32_mod k)
    (bytes_beq_self _)
  simp only [Spec.proj_num__0, Option.get!_some, Spec.proj_uN_0, ma4, floor4] at this
  simpa [vals, i32v, i32c, Spec.instr_val, Spec.numtype_addrtype, ma4] using this

end L4Factoidal.WasmVM.Proofs.SpecWP
