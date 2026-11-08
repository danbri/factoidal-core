/-
L4Factoidal.WasmVM.Proofs.AotNames: the translated imports have distinct names
(record: docs/designissues/2026-11-08-wasmvm-aot.md, section 4).

Apart from `Aot/Translate.lean` because it needs `Std.Data.String.ToNat`
(`Nat.repr_injective`), which the engine's Wasm build does not link.
-/
import L4Factoidal.WasmVM.Aot.Translate
import Std.Data.String.ToNat

namespace L4Factoidal.WasmVM.Aot

theorem importName_injective {j k : Nat} (h : importName j = importName k) : j = k :=
  Nat.repr_injective ((String.append_right_inj "i").mp h)

/-- Two translated imports have the same name only when they are the same import. -/
theorem translate_import_names {m : Module} {pages : Nat} {r : Module × Plan} (h : translate m pages = .ok r)
    (j k : Nat) (hj : j < r.1.imports.size) (hk : k < r.1.imports.size)
    (hn : r.1.imports[j].name = r.1.imports[k].name) : j = k := by
  have e := translate_eq h; subst e
  simp [translateModule, renameImport] at hn
  exact importName_injective hn

end L4Factoidal.WasmVM.Aot
