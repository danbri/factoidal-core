import L4Factoidal.WasmVM.Spec
import L4Factoidal.WasmVM.Syntax
import L4Factoidal.WasmVM.Binary.Leb
import L4Factoidal.WasmVM.Binary.Decode
import L4Factoidal.WasmVM.Numerics
import L4Factoidal.WasmVM.Valid
import L4Factoidal.WasmVM.Exec.Bytes
import L4Factoidal.WasmVM.Exec.Memory
import L4Factoidal.WasmVM.Exec.Code
import L4Factoidal.WasmVM.Exec.Store
import L4Factoidal.WasmVM.Exec.Run
import L4Factoidal.WasmVM.Exec.Instantiate
import L4Factoidal.WasmVM.Api
import L4Factoidal.WasmVM.Wasi
import L4Factoidal.WasmVM.WasiIO
import L4Factoidal.WasmVM.Hosts.Dom
import L4Factoidal.WasmVM.Hosts.Page
import L4Factoidal.WasmVM.Proofs.Numerics
import L4Factoidal.WasmVM.Proofs.Fuse
import L4Factoidal.WasmVM.Proofs.Cost
import L4Factoidal.WasmVM.Proofs.Proposals
import L4Factoidal.WasmVM.Proofs.Slots
import L4Factoidal.WasmVM.Proofs.Memory
import L4Factoidal.WasmVM.Proofs.Refine
import L4Factoidal.WasmVM.Proofs.RefineRun
import L4Factoidal.WasmVM.Tests.Memory
import L4Factoidal.WasmVM.Tests.Proposals
import L4Factoidal.WasmVM.Tests.Wasi

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
