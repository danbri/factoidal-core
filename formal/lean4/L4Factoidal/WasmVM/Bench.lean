import L4Factoidal.WasmVM.Bench.Repr
import L4Factoidal.WasmVM.Bench.Engine
import L4Factoidal.WasmVM.Tests.Memory
import L4Factoidal.WasmVM.Bench.Profile
import L4Factoidal.WasmVM.Bench.Core
import L4Factoidal.WasmVM.Tests.Proposals

/-! `lake exe wasmvm-bench`: measurements for the WasmVM engine (issue 1244). -/

/-- `wasmvm-bench repr [N]` | `engine [N]` | `decode FILE` | `memtest` | `proposals` | `l4core FILE` | `profile DIR` -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "repr" :: rest => L4Factoidal.WasmVM.Bench.Repr.run ((rest.head? >>= String.toNat?).getD 20000000)
  | "decode" :: f :: _ => L4Factoidal.WasmVM.Bench.Engine.decodeFile f
  | "profile" :: dir :: _ => do
    L4Factoidal.WasmVM.Bench.Profile.dynamic
    L4Factoidal.WasmVM.Bench.Profile.static dir
  | "l4core" :: f :: _ => return (← L4Factoidal.WasmVM.Bench.Core.run f)
  | "proposals" :: _ => return (if (← L4Factoidal.WasmVM.Tests.Proposals.run) then 0 else 1)
  | "memtest" :: _ => return (if (← L4Factoidal.WasmVM.Tests.Memory.run) then 0 else 1)
  | "engine" :: rest => L4Factoidal.WasmVM.Bench.Engine.engine ((rest.head? >>= String.toNat?).getD 10000000)
  | _ => IO.println "usage: wasmvm-bench repr [N] | engine [N] | decode FILE | memtest | proposals | l4core FILE | profile DIR"
  return 0
