import L4Factoidal.WasmVM.Spec.Wasm30
import L4Factoidal.WasmVM.Spec.BuiltinsTheorems

/-!
Sanity checks for the generated WebAssembly 3.0 spec layer (`Spec/Wasm30.lean`).

They show that the generated relations can be used in kernel-checked proofs: a
constructor of `Step_pure` applied to concrete values, lifted to `Step` and `Steps`,
and a rule that cannot fire. No `native_decide`.
-/

namespace L4Factoidal.WasmVM.Spec.Sanity

open L4Factoidal.WasmVM.Spec

/-- An `i32` constant instruction. -/
abbrev i32c (k : Nat) : instr := .CONST .I32 (.mk_num__0 .I32 (.mk_uN k))

/-- The `i32.add` instruction. -/
abbrev i32add : instr := .BINOP .I32 (.mk_binop__0 .I32 .ADD)

/-- `(i32.const 2) (i32.const 3) i32.add` reduces to `(i32.const 5)` (spec 4.4.1.3, binop). -/
theorem i32_add_2_3 : Step_pure [i32c 2, i32c 3, i32add] [i32c 5] := by
  refine Step_pure.binop_val .I32 _ _ _ _ [.mk_num__0 .I32 (.mk_uN 5)] ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun_binop_.fun_binop__case_0 _ _ (.num__case_0 _ .I32 _ (.uN_case_0 _ _ (by decide)) (by decide))
  all_goals first
    | exact .num__case_0 _ .I32 _ (.uN_case_0 _ _ (by decide)) (by decide)
    | exact .binop__case_0 _ .I32 _ (by decide)
    | decide

/-- Addition wraps modulo 2^32: `0xFFFFFFFF + 1` reduces to `0`. -/
theorem i32_add_wraps : Step_pure [i32c 0xFFFFFFFF, i32c 1, i32add] [i32c 0] := by
  refine Step_pure.binop_val .I32 _ _ _ _ [.mk_num__0 .I32 (.mk_uN 0)] ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun_binop_.fun_binop__case_0 _ _ (.num__case_0 _ .I32 _ (.uN_case_0 _ _ (by decide)) (by decide))
  all_goals first
    | exact .num__case_0 _ .I32 _ (.uN_case_0 _ _ (by decide)) (by decide)
    | exact .binop__case_0 _ .I32 _ (by decide)
    | decide

/-- The same reduction as a step of a whole configuration, in any state. -/
theorem i32_add_2_3_step (z : state) :
    Step (.mk_config z [i32c 2, i32c 3, i32add]) (.mk_config z [i32c 5]) :=
  Step.pure _ _ _ i32_add_2_3

/-- ... and as a reduction sequence `Steps` (the reflexive-transitive closure). -/
theorem i32_add_2_3_steps (z : state) :
    Steps (.mk_config z [i32c 2, i32c 3, i32add]) (.mk_config z [i32c 5]) :=
  Steps.trans _ _ _ _ _ _ (i32_add_2_3_step z) (Steps.refl _ _)

/-- `nop` reduces to the empty sequence. -/
theorem nop_step : Step_pure [.NOP] [] := Step_pure.nop

/-- `unreachable` traps. -/
theorem unreachable_traps : Step_pure [.UNREACHABLE] [.TRAP] := Step_pure.unreachable

/-- Validation: `nop` has type `[] -> []` in every context. -/
theorem nop_ok (C : context) : Instr_ok C .NOP (.mk_instrtype (.mk_list []) [] (.mk_list [])) :=
  Instr_ok.nop C

/-- The spec's `iadd_` is addition modulo 2^N, so it agrees with `UInt32` addition on
every input: the first bridge lemma a refinement proof needs for `i32.add`. -/
theorem iadd_32_eq_uint32 (a b : UInt32) :
    iadd_ 32 (.mk_uN a.toNat) (.mk_uN b.toNat) = .mk_uN (a + b).toNat := by
  simp [iadd_, proj_uN_0, UInt32.toNat_add]

/-- `i32.and` in the spec layer is `UInt32` conjunction: the opaque `iand_` is now the
definition in `Spec/Builtins.lean`, and the lemma there carries over. -/
theorem iand_32_eq_uint32 (a b : UInt32) :
    iand_ 32 (.mk_uN a.toNat) (.mk_uN b.toNat) = .mk_uN (a &&& b).toNat := by
  simp only [iand_, proj_uN_0, Builtins.OnNat.iand_, Builtins.ofNat_toNat_32, Builtins.iand_32]
  rfl

/-- `i32.shl` in the spec layer is `UInt32` shift left (count modulo 32). -/
theorem ishl_32_eq_uint32 (a b : UInt32) :
    ishl_ 32 (.mk_uN a.toNat) (.mk_uN b.toNat) = .mk_uN (a <<< b).toNat := by
  simp only [ishl_, proj_uN_0, Builtins.OnNat.ishl_, Builtins.ofNat_toNat_32, Builtins.ishl_32]
  rfl

/-- `i32.lt_s` in the spec layer is `Int32` comparison. -/
theorem ilt_s_32_eq_int32 (a b : UInt32) :
    ilt_ 32 .S (.mk_uN a.toNat) (.mk_uN b.toNat) =
      .mk_uN (if a.toInt32 < b.toInt32 then 1 else 0) := by
  simp only [ilt_, proj_uN_0, Builtins.OnNat.ilt_, Builtins.OnNat.bool, Builtins.ofNat_toNat_32,
    Builtins.ilt_s_32]
  simp

/-- Little-endian bytes in the spec layer: storing then loading an `i32` gives it back. -/
theorem inv_ibytes_ibytes_32 (a : UInt32) :
    inv_ibytes_ 32 (ibytes_ 32 (.mk_uN a.toNat)) = .mk_uN a.toNat := by
  simp only [ibytes_, inv_ibytes_, proj_uN_0, Builtins.OnNat.ibytes_, Builtins.OnNat.inv_ibytes_,
    List.map_map, Builtins.ofNat_toNat_32]
  congr 1
  rw [show (BitVec.ofNat 8 ∘ proj_byte_0 ∘ byte.mk_byte ∘ BitVec.toNat) =
      (id : BitVec 8 → BitVec 8) by funext x; simp [proj_byte_0],
    List.map_id, Builtins.inv_ibytes_ibytes_32]
  rfl

end L4Factoidal.WasmVM.Spec.Sanity
