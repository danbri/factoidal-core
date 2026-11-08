/-
L4Factoidal.WasmVM.Proofs.AotCheck: the second half of the fuel charge of `WasmVM.Aot`
(record: docs/designissues/2026-11-08-wasmvm-aot.md, section 4).

The last six instructions of `charge g c` test the fuel: `charge_check` says that in
`Spec/Wasm30`, when global `g` holds an i64 that is not negative, they step to the
instructions after them with the state unchanged. With `Proofs.Aot.charge_take`, a
charge with fuel `F ≥ c` left is ten spec steps (and some administrative ones) that
change global `g` from `F` to `F - c` and nothing else.
-/
import L4Factoidal.WasmVM.Proofs.Aot

namespace L4Factoidal.WasmVM.Proofs.Aot
open L4Factoidal.WasmVM
open L4Factoidal.WasmVM.Proofs.Refine
open L4Factoidal.WasmVM.Proofs.Proposals (val_beq_self)

/-- The spec instructions of the last six of `charge g c`. -/
noncomputable def checkInstrs (g : Spec.uN) : List Spec.instr :=
  [.GLOBAL_GET g, .CONST .I64 (absI64 0), .RELOP .I64 (.mk_relop__0 .I64 (.LT .S)),
   .IFELSE (._RESULT none) [.UNREACHABLE] []]

noncomputable def zero32 : Spec.num_ := .mk_num__0 .I32 (.mk_uN 0)

theorem wf_zero32 : Spec.wf_num_ .I32 zero32 := by
  have h := Proofs.wf_absI32 0
  simpa [Proofs.absI32, zero32] using h

/-- `i64.lt_s F 0` is 0 when `F` is under 2^63. -/
theorem relop_lt_nonneg (F : UInt64) (hF : F.toNat < 2 ^ 63) :
    Spec.Step_pure [.CONST .I64 (absI64 F), .CONST .I64 (absI64 0), .RELOP .I64 (.mk_relop__0 .I64 (.LT .S))]
      [.CONST .I32 zero32] := by
  have hpos : ¬ F.toBitVec.toInt < 0 := by
    rw [BitVec.toInt_eq_toNat_cond]; simp only [UInt64.toNat_toBitVec]; split <;> omega
  refine Spec.Step_pure.relop .I64 (absI64 F) (absI64 0) _ zero32 (wf_absI64 F) (wf_absI64 0)
    (Spec.wf_relop_.relop__case_0 _ .I64 _ (by decide)) wf_zero32
    (by first | rfl | decide | simp [zero32, Spec.proj_num__0]) ?_
  (try simp [zero32, absI64, Spec.proj_num__0, Spec.fun_relop_, Spec.ilt_, Spec.Builtins.OnNat.ilt_,
    Spec.Builtins.ilt_, Spec.Builtins.OnNat.bool, BitVec.slt, Spec.proj_uN_0, Spec.sizenn,
    Spec.numtype_Inn, Spec.size, hpos]) <;> (try first | rfl | exact Proofs.Proposals.uN_beq_self _ | decide)

theorem charge_check (z : Spec.state) (g : Spec.uN) (F : UInt64) (rest : List Spec.instr)
    (hg : (Spec.fun_global z g).VALUE = .CONST .I64 (absI64 F)) (hF : F.toNat < 2 ^ 63) :
    Spec.Steps (.mk_config z (checkInstrs g ++ rest)) (.mk_config z rest) := by
  -- global.get
  have s1 : Spec.Step (.mk_config z (checkInstrs g ++ rest))
      (.mk_config z ([.CONST .I64 (absI64 F), .CONST .I64 (absI64 0), .RELOP .I64 (.mk_relop__0 .I64 (.LT .S))] ++
        ([.IFELSE (._RESULT none) [.UNREACHABLE] []] ++ rest))) := by
    have h := step_ctx z z [] [.GLOBAL_GET g] [Spec.instr_val (.CONST .I64 (absI64 F))]
      ([.CONST .I64 (absI64 0), .RELOP .I64 (.mk_relop__0 .I64 (.LT .S)),
        .IFELSE (._RESULT none) [.UNREACHABLE] []] ++ rest)
      (Spec.Step.read _ _ _ (Spec.Step_read.global_get z g _ (by rw [hg]; exact val_beq_self _)))
    simpa [checkInstrs, Spec.instr_val] using h
  -- i64.lt_s: 0
  have s2 : Spec.Step
      (.mk_config z ([.CONST .I64 (absI64 F), .CONST .I64 (absI64 0), .RELOP .I64 (.mk_relop__0 .I64 (.LT .S))] ++
        ([.IFELSE (._RESULT none) [.UNREACHABLE] []] ++ rest)))
      (.mk_config z ([.CONST .I32 zero32] ++ ([.IFELSE (._RESULT none) [.UNREACHABLE] []] ++ rest))) := by
    have h := step_ctx z z [] _ _ ([.IFELSE (._RESULT none) [.UNREACHABLE] []] ++ rest)
      (Spec.Step.pure _ _ _ (relop_lt_nonneg F hF))
    simpa using h
  -- if: the empty else arm
  have s3 : Spec.Step (.mk_config z ([.CONST .I32 zero32] ++ ([.IFELSE (._RESULT none) [.UNREACHABLE] []] ++ rest)))
      (.mk_config z ([.BLOCK (._RESULT none) []] ++ rest)) := by
    have h := step_ctx z z [] [.CONST .I32 zero32, .IFELSE (._RESULT none) [.UNREACHABLE] []]
      [.BLOCK (._RESULT none) []] rest
      (Spec.Step.pure _ _ _ (Spec.Step_pure.if_false zero32 _ _ _ wf_zero32
        (by first | rfl | decide | simp [zero32, Spec.proj_num__0])
        (by first | rfl | decide | simp [zero32, Spec.proj_num__0, Spec.proj_uN_0])))
    simpa using h
  -- block: a label with nothing in it
  have s4 : Spec.Step (.mk_config z ([.BLOCK (._RESULT none) []] ++ rest))
      (.mk_config z ([.LABEL_ 0 [] []] ++ rest)) := by
    have h := step_ctx z z [] [.BLOCK (._RESULT none) []] [.LABEL_ 0 [] []] rest
      (Spec.Step.read _ _ _ (by
        have r := Spec.Step_read.block z [] 0 (._RESULT none) [] 0 [] (none : Option Spec.valtype).toList _
          (Spec.fun_blocktype_.fun_blocktype__case_1 z none) (instrtype_beq _ _)
        simpa using r))
    simpa using h
  -- the label ends with no values
  have s5 : Spec.Step (.mk_config z ([.LABEL_ 0 [] []] ++ rest)) (.mk_config z rest) := by
    have h := step_ctx z z [] [.LABEL_ 0 [] []] [] rest
      (Spec.Step.pure _ _ _ (by simpa using Spec.Step_pure.label_vals 0 [] []))
    simpa using h
  exact .trans _ _ _ _ _ _ s1 (.trans _ _ _ _ _ _ s2 (.trans _ _ _ _ _ _ s3
    (.trans _ _ _ _ _ _ s4 (.trans _ _ _ _ _ _ s5 (.refl _ _)))))

end L4Factoidal.WasmVM.Proofs.Aot
