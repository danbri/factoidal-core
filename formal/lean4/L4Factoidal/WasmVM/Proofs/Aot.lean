/-
L4Factoidal.WasmVM.Proofs.Aot: the fuel charge of `WasmVM.Aot` in the spec semantics
(record: docs/designissues/2026-11-08-wasmvm-aot.md, section 4).

`charge g c` is ten instructions. Its first four take `c` from the fuel global:
`charge_take` says that in `Spec/Wasm30` they step, in any state whose global `g` holds
the i64 `F`, to the same instructions after them with global `g` set to `F - c` (mod
2^64) and nothing else changed (`with_global`). So the instrumentation changes no value
the guest can read but the fuel global, which no instruction of the guest names (it is a
new global, `translate_exports`).
-/
import L4Factoidal.WasmVM.Proofs.Refine
import L4Factoidal.WasmVM.Proofs.Proposals

namespace L4Factoidal.WasmVM.Proofs.Aot
open L4Factoidal.WasmVM
open L4Factoidal.WasmVM.Proofs.Refine
open L4Factoidal.WasmVM.Proofs.Proposals (val_beq_self)

/-- The spec instructions of the first four of `charge g c`. -/
noncomputable def takeInstrs (g : Spec.uN) (c : UInt64) : List Spec.instr :=
  [.GLOBAL_GET g, .CONST .I64 (absI64 c), .BINOP .I64 (.mk_binop__0 .I64 .SUB), .GLOBAL_SET g]

theorem charge_take (z : Spec.state) (g : Spec.uN) (F c : UInt64) (rest : List Spec.instr)
    (hg : (Spec.fun_global z g).VALUE = .CONST .I64 (absI64 F)) :
    Spec.Steps (.mk_config z (takeInstrs g c ++ rest))
      (.mk_config (Spec.with_global z g (.CONST .I64 (absI64 (F - c)))) rest) := by
  -- global.get
  have s1 : Spec.Step (.mk_config z (takeInstrs g c ++ rest))
      (.mk_config z ([.CONST .I64 (absI64 F), .CONST .I64 (absI64 c), .BINOP .I64 (.mk_binop__0 .I64 .SUB)] ++
        ([.GLOBAL_SET g] ++ rest))) := by
    have h := step_ctx z z [] [.GLOBAL_GET g]
      [Spec.instr_val (.CONST .I64 (absI64 F))]
      ([.CONST .I64 (absI64 c), .BINOP .I64 (.mk_binop__0 .I64 .SUB), .GLOBAL_SET g] ++ rest)
      (Spec.Step.read _ _ _ (Spec.Step_read.global_get z g _ (by rw [hg]; exact val_beq_self _)))
    simpa [takeInstrs, Spec.instr_val] using h
  -- i64.sub
  have s2 : Spec.Step
      (.mk_config z ([.CONST .I64 (absI64 F), .CONST .I64 (absI64 c), .BINOP .I64 (.mk_binop__0 .I64 .SUB)] ++
        ([.GLOBAL_SET g] ++ rest)))
      (.mk_config z ([.CONST .I64 (absI64 (F - c))] ++ ([.GLOBAL_SET g] ++ rest))) := by
    have h := step_ctx z z [] _ _ ([.GLOBAL_SET g] ++ rest) (Spec.Step.pure _ _ _ (i64_sub_refines F c))
    simpa [NumOp.evalBin] using h
  -- global.set
  have s3 : Spec.Step (.mk_config z ([.CONST .I64 (absI64 (F - c))] ++ ([.GLOBAL_SET g] ++ rest)))
      (.mk_config (Spec.with_global z g (.CONST .I64 (absI64 (F - c)))) rest) := by
    have h := step_ctx z (Spec.with_global z g (.CONST .I64 (absI64 (F - c)))) []
      [Spec.instr_val (.CONST .I64 (absI64 (F - c))), .GLOBAL_SET g] [] rest
      (Spec.Step.global_set z _ g)
    simpa [Spec.instr_val] using h
  exact .trans _ _ _ _ _ _ s1 (.trans _ _ _ _ _ _ s2 (.trans _ _ _ _ _ _ s3 (.refl _ _)))

end L4Factoidal.WasmVM.Proofs.Aot
