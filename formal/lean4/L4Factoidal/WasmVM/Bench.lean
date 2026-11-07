import L4Factoidal.WasmVM.Bench.Repr
import L4Factoidal.WasmVM.Bench.Engine
import L4Factoidal.WasmVM.Tests.Memory
import L4Factoidal.WasmVM.Bench.Profile

/-! `lake exe wasmvm-bench`: measurements for the WasmVM engine (issue 1244). -/

/-- `wasmvm-bench repr [N]` | `engine [N]` | `decode FILE` -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "repr" :: rest => L4Factoidal.WasmVM.Bench.Repr.run ((rest.head? >>= String.toNat?).getD 20000000)
  | "decode" :: f :: _ => L4Factoidal.WasmVM.Bench.Engine.decodeFile f
  | "profile" :: dir :: _ => do
    L4Factoidal.WasmVM.Bench.Profile.dynamic
    L4Factoidal.WasmVM.Bench.Profile.static dir
  | "memtest" :: _ => return (if (← L4Factoidal.WasmVM.Tests.Memory.run) then 0 else 1)
  | "engine" :: rest => L4Factoidal.WasmVM.Bench.Engine.engine ((rest.head? >>= String.toNat?).getD 10000000)
  | _ => IO.println "usage: wasmvm-bench repr [N] | engine [N] | decode FILE | memtest | profile DIR"
  return 0
