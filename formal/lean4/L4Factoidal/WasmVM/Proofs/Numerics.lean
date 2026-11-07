/-
L4Factoidal.WasmVM.Proofs.Numerics: the first refinements of the fast engine against
the spec layer (https://github.com/danbri/factoidal/issues/1244; proof plan item 5 in
docs/designissues/2026-11-07-wasmvm-engine.md).

`absI32` reads an operand-stack slot as the spec's i32 constant. For each integer
binary operation proved here, one step of the engine (`NumOp.evalBin` on two slots)
is a `Spec.Step_pure` step from the two constants and the instruction to the
constant of the result. The slot of an i32 is zero-extended ("slot normal form",
`Exec/Run.lean`); `absI32` reads its low 32 bits, so the theorems hold for every slot.
-/
import L4Factoidal.WasmVM.Spec
import L4Factoidal.WasmVM.Numerics

namespace L4Factoidal.WasmVM.Proofs
open L4Factoidal.WasmVM

/-- The spec's i32 constant for a slot. -/
noncomputable def absI32 (a : UInt64) : Spec.num_ :=
  .mk_num__0 .I32 (.mk_uN a.toUInt32.toNat)

theorem wf_absI32 (a : UInt64) : Spec.wf_num_ .I32 (absI32 a) := by
  refine Spec.wf_num_.num__case_0 _ _ _ ?_ (by rfl)
  refine Spec.wf_uN.uN_case_0 _ _ ?_
  have := a.toUInt32.toNat_lt
  simp [Spec.size, Spec.numtype_addrtype]
  omega

theorem num_beq_self (n : Nat) :
    (Spec.num_.mk_num__0 .I32 (.mk_uN n) == Spec.num_.mk_num__0 .I32 (.mk_uN n)) = true := by
  simp [BEq.beq, Spec.instBEqNum_.beq, Spec.instBEqUN.beq, Spec.instBEqAddrtype.beq]

/-- The pattern of every i32 binary operation without a trap: when the spec function
`f` on the two read constants gives the read result, the engine step is a spec step. -/
theorem i32_bin_refines (bop : Spec.binop_Inn) (f : Spec.uN → Spec.uN → Spec.uN)
    (op : NumOp) (a b : UInt64)
    (hfun : ∀ i1 i2, Spec.wf_num_ .I32 (.mk_num__0 .I32 (f i1 i2)) →
      Spec.fun_binop_ .I32 (.mk_binop__0 .I32 bop) (.mk_num__0 .I32 i1) (.mk_num__0 .I32 i2)
        [.mk_num__0 .I32 (f i1 i2)])
    (hkey : f (.mk_uN a.toUInt32.toNat) (.mk_uN b.toUInt32.toNat)
      = .mk_uN (op.evalBin a b).toUInt32.toNat) :
    Spec.Step_pure
      [.CONST .I32 (absI32 a), .CONST .I32 (absI32 b), .BINOP .I32 (.mk_binop__0 .I32 bop)]
      [.CONST .I32 (absI32 (op.evalBin a b))] := by
  have hw : Spec.wf_num_ .I32 (.mk_num__0 .I32 (f (.mk_uN a.toUInt32.toNat) (.mk_uN b.toUInt32.toNat))) := by
    rw [hkey]; exact wf_absI32 _
  refine Spec.Step_pure.binop_val .I32 (absI32 a) (absI32 b) (.mk_binop__0 .I32 bop)
    (absI32 (op.evalBin a b))
    [.mk_num__0 .I32 (f (.mk_uN a.toUInt32.toNat) (.mk_uN b.toUInt32.toNat))]
    (hfun _ _ hw) (wf_absI32 a) (wf_absI32 b) (.binop__case_0 _ .I32 _ (by decide))
    (wf_absI32 _) (by simp) ?_
  rw [hkey]
  simp [List.contains, List.elem, absI32, num_beq_self]

theorem i32_add_refines (a b : UInt64) :
    Spec.Step_pure
      [.CONST .I32 (absI32 a), .CONST .I32 (absI32 b), .BINOP .I32 (.mk_binop__0 .I32 .ADD)]
      [.CONST .I32 (absI32 (NumOp.evalBin .i32_add a b))] :=
  i32_bin_refines .ADD (Spec.iadd_ (Spec.sizenn (Spec.numtype_addrtype .I32))) .i32_add a b
    (fun _ _ h => .fun_binop__case_0 _ _ h)
    (by simp [Spec.iadd_, Spec.sizenn, Spec.size, Spec.numtype_addrtype, Spec.proj_uN_0,
              NumOp.evalBin, Num.ofI32, Num.lo])

theorem i32_sub_refines (a b : UInt64) :
    Spec.Step_pure
      [.CONST .I32 (absI32 a), .CONST .I32 (absI32 b), .BINOP .I32 (.mk_binop__0 .I32 .SUB)]
      [.CONST .I32 (absI32 (NumOp.evalBin .i32_sub a b))] :=
  i32_bin_refines .SUB (Spec.isub_ (Spec.sizenn (Spec.numtype_addrtype .I32))) .i32_sub a b
    (fun _ _ h => .fun_binop__case_2 _ _ h)
    (by
      simp [Spec.isub_, Spec.sizenn, Spec.size, Spec.numtype_addrtype, Spec.proj_uN_0,
            NumOp.evalBin, Num.ofI32, Num.lo, UInt64.toNat_sub, UInt64.toNat_mod]
      omega)

theorem i32_mul_refines (a b : UInt64) :
    Spec.Step_pure
      [.CONST .I32 (absI32 a), .CONST .I32 (absI32 b), .BINOP .I32 (.mk_binop__0 .I32 .MUL)]
      [.CONST .I32 (absI32 (NumOp.evalBin .i32_mul a b))] :=
  i32_bin_refines .MUL (Spec.imul_ (Spec.sizenn (Spec.numtype_addrtype .I32))) .i32_mul a b
    (fun _ _ h => .fun_binop__case_4 _ _ h)
    (by simp [Spec.imul_, Spec.sizenn, Spec.size, Spec.numtype_addrtype, Spec.proj_uN_0,
              NumOp.evalBin, Num.ofI32, Num.lo])

end L4Factoidal.WasmVM.Proofs
