import L4Factoidal.WasmVM.Spec

/-
L4Factoidal.WasmVM: a WebAssembly engine in Lean 4 (https://github.com/danbri/factoidal/issues/1244).

Three layers:
- `WasmVM.Spec`: the WebAssembly 3.0 semantics generated from the official SpecTec
  sources (third_party/wasm-spec), as Lean relations. This is the reference.
- `WasmVM.Exec` and its siblings: the executable engine (binary decoder, validator,
  interpreter, host API), written for speed.
- Theorems that tie the second to the first: each fast form is proved equal to, or a
  refinement of, the spec form, and `@[csimp]` swaps in the fast form where the two are
  equal functions.

This root imports every WasmVM module, so `lake build WasmVM` builds them all.
-/
