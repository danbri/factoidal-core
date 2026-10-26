/-
Wasm.CoreExports — the C symbols of the CORE wasm module
(`l4factoidal-core.wasm`, https://github.com/danbri/factoidal/issues/713
stage 4).

The symbol names and the signatures are those of `Wasm/Exports.lean`, so the
same C shim (`Wasm/l4_shim.c`), the same Emscripten exports and the same
JavaScript loader drive both modules. The bodies call the core dispatch
(`Wasm/CoreDispatch.lean`) instead of the full one (`Wasm/Dispatch.lean`).

The two modules define the same C symbols, so no Lean module may import both,
and no link may include both objects: `Wasm/build-wasm.sh` links
`Wasm_Exports.o` into `l4factoidal.wasm` and `Wasm_CoreExports.o` into
`l4factoidal-core.wasm`, and compiles the shim twice, once for each module
initialiser (`initialize_l4factoidal_Wasm_Exports`,
`initialize_l4factoidal_Wasm_CoreExports`). No native executable imports this
module.
-/
import Wasm.Abi
import Wasm.CoreDispatch

/-- C symbol `l4_version`, as in `Wasm/Exports.lean`. -/
@[export l4_version]
def l4CoreVersionExport (_ : Unit) : String :=
  L4Wasm.version

/-- C symbol `l4_bgp_query`, as in `Wasm/Exports.lean`. -/
@[export l4_bgp_query]
def l4CoreBgpQueryExport (dataJson : String) (bgpJson : String) : String :=
  L4Wasm.bgpQuery dataJson bgpJson

/-- C symbol `l4_call`: the pure entry of the core dispatch. -/
@[export l4_call]
def l4CoreCallExport (op : String) (argsJson : String) : String :=
  L4Wasm.Core.call op argsJson

/-- C symbol `l4_call_blob`: the core engine reads no byte region. -/
@[export l4_call_blob]
def l4CoreCallBlobExport (op : String) (argsJson : String) (blob : ByteArray) : String :=
  L4Wasm.Core.callBlob op argsJson blob

/-- C symbol `l4_call_io`: the IO entry of the core dispatch (the wire entry
`l4_call_c` of the shim). -/
@[export l4_call_io]
def l4CoreCallIOExport (op : String) (argsJson : String) : IO String :=
  L4Wasm.Core.callIO op argsJson

/-- C symbol `l4_call_blob_io`: the core engine builds no byte region. -/
@[export l4_call_blob_io]
def l4CoreCallBlobIOExport (op : String) (argsJson : String) (blob : ByteArray) :
    IO (String × ByteArray) :=
  L4Wasm.Core.callBlobIO op argsJson blob
