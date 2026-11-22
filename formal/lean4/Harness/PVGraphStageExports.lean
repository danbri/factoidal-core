import Wasm.Abi
import Harness.PVGraphTestDispatch

/-! Same public C ABI over the explicitly labeled test-only
core-plus-registry profile; no alternate query implementation. -/

@[export l4_version]
def pvgraphTestVersionExport (_ : Unit) : String := L4Wasm.version

@[export l4_bgp_query]
def pvgraphTestBgpExport (dataJson bgpJson : String) : String :=
  L4Wasm.bgpQuery dataJson bgpJson

@[export l4_call]
def pvgraphTestCallExport (op argsJson : String) : String :=
  L4Wasm.PVGraphTest.call op argsJson

@[export l4_call_io]
def pvgraphTestCallIOExport (op argsJson : String) : IO String :=
  L4Wasm.PVGraphTest.callIO op argsJson

@[export l4_call_blob]
def pvgraphTestCallBlobExport (op argsJson : String) (_ : ByteArray) : String :=
  L4Wasm.PVGraphTest.call op argsJson

@[export l4_call_blob_io]
def pvgraphTestCallBlobIOExport (op argsJson : String) (_ : ByteArray) :
    IO (String × ByteArray) := do
  pure (← L4Wasm.PVGraphTest.callIO op argsJson, ByteArray.empty)
