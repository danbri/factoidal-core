import L4Factoidal.WasmVM.Bench.Repr
import L4Factoidal.WasmVM.Bench.Engine
import L4Factoidal.WasmVM.Tests.Memory
import L4Factoidal.WasmVM.Bench.Profile
import L4Factoidal.WasmVM.Bench.Core
import L4Factoidal.WasmVM.Tests.Proposals
import L4Factoidal.WasmVM.Tests.Wasi
import L4Factoidal.WasmVM.Bench.HarfBuzz
import L4Factoidal.WasmVM.Bench.QuickJS
import L4Factoidal.WasmVM.Bench.Test262
import L4Factoidal.WasmVM.Bench.Page
import L4Factoidal.WasmVM.Tests.Aot

/-! `lake exe wasmvm-bench`: measurements for the WasmVM engine (issue 1244). -/

/-- `wasmvm-bench repr [N]` | `engine [N]` | `decode FILE` | `memtest` | `proposals` | `wasi` | `harfbuzz WASM [N]` | `qjs WASM [REACTOR]` | `test262 WASM DIR [NATIVE [FUEL]]` | `page WASM ROOT FILE...` | `l4core FILE` | `profile DIR` | `aot DIR` | `aot-module WASM OUT [PAGES]` -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "repr" :: rest => L4Factoidal.WasmVM.Bench.Repr.run ((rest.head? >>= String.toNat?).getD 20000000)
  | "decode" :: f :: _ => L4Factoidal.WasmVM.Bench.Engine.decodeFile f
  | "profile" :: dir :: _ => do
    L4Factoidal.WasmVM.Bench.Profile.dynamic
    L4Factoidal.WasmVM.Bench.Profile.static dir
  | "l4core" :: f :: _ => return (← L4Factoidal.WasmVM.Bench.Core.run f)
  | "proposals" :: _ => return (if (← L4Factoidal.WasmVM.Tests.Proposals.run) then 0 else 1)
  | "harfbuzz" :: f :: rest =>
    return (← L4Factoidal.WasmVM.Bench.HarfBuzz.run f ((rest.head? >>= String.toNat?).getD 200))
  | "qjs" :: f :: rest => return (← L4Factoidal.WasmVM.Bench.QuickJS.run f rest.head?)
  | "test262" :: w :: d :: rest =>
    return (← L4Factoidal.WasmVM.Bench.Test262.run w d rest.head? ((rest.drop 1).head? >>= String.toNat? |>.getD 2000000000))
  | "page" :: rest => return (← L4Factoidal.WasmVM.Bench.Page.run rest)
  | "aot" :: dir :: _ => return (if (← L4Factoidal.WasmVM.Tests.Aot.run dir) then 0 else 1)
  | "aot-module" :: w :: o :: rest => return (← L4Factoidal.WasmVM.Tests.Aot.module w o ((rest.head? >>= String.toNat?).getD 2048))
  | "wasi" :: _ => return (if (← L4Factoidal.WasmVM.Tests.Wasi.run) then 0 else 1)
  | "memtest" :: _ => return (if (← L4Factoidal.WasmVM.Tests.Memory.run) then 0 else 1)
  | "engine" :: "--check" :: _ => return (← L4Factoidal.WasmVM.Bench.Engine.check)
  | "engine" :: rest => L4Factoidal.WasmVM.Bench.Engine.engine ((rest.head? >>= String.toNat?).getD 10000000)
  | _ => IO.println "usage: wasmvm-bench repr [N] | engine [N] | engine --check | decode FILE | memtest | proposals | wasi | harfbuzz WASM [N] | qjs WASM [REACTOR] | test262 WASM DIR [NATIVE [FUEL]] | l4core FILE | profile DIR"
  return 0
