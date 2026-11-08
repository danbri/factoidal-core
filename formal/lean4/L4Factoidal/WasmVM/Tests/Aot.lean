/-
L4Factoidal.WasmVM.Tests.Aot: the encoder and the translator on real modules
(record: docs/designissues/2026-11-08-wasmvm-aot.md).

`lake exe wasmvm-bench aot DIR` (DIR: `third_party/wasm-spec/test/core-json`): every
`.wasm` file under DIR that `decode` reads is encoded and decoded again; the second
encoding must equal the first (the encoder writes what `decode` reads back), and the
re-decoded module must validate exactly when the original does. Every module that
validates and that `translate` takes (function imports only, one memory of its own) is
translated; the translated module must decode and validate.

`lake exe wasmvm-bench aot-module WASM OUT [PAGES]`: translate one guest (QuickJS-NG) and
write the host module to OUT, with times and sizes.
-/
import L4Factoidal.WasmVM.Api
import L4Factoidal.WasmVM.Aot.Encode
import L4Factoidal.WasmVM.Aot.Translate

namespace L4Factoidal.WasmVM.Tests.Aot
open L4Factoidal.WasmVM

/-- Encode, decode again, and compare. -/
def roundTrip (m : Module) : Except String Module := do
  let e := Aot.Encode.encode m
  let m2 ← (Binary.decode e).mapError (fun d => s!"re-decode: {d.toString}")
  if Aot.Encode.encode m2 != e then throw "the second encoding differs"
  return m2

def valid (m : Module) : Bool := (validate m).toOption.isSome

/-- Translate a module and check that the host module decodes and validates. -/
def translateChecked (m : Module) (pages : Nat) : Except String (ByteArray × Aot.Plan) := do
  let (t, plan) ← Aot.translate m pages
  let bytes := Aot.Encode.encode t
  let t2 ← (Binary.decode bytes).mapError (fun d => s!"translated module: decode: {d.toString}")
  match validate t2 with
  | .ok _ => pure ()
  | .error e => throw s!"translated module: validate: {e.toString}"
  return (bytes, plan)

def wasmFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  return (← dir.walkDir).filter (·.extension == some "wasm")

def run (dir : String) : IO Bool := do
  let files := (← wasmFiles dir).qsort (·.toString < ·.toString)
  let mut decoded := 0
  let mut same := 0
  let mut translated := 0
  let mut notTaken := 0
  let mut bad : Array String := #[]
  for f in files do
    let bytes ← IO.FS.readBinFile f
    let .ok m := Binary.decode bytes | continue
    decoded := decoded + 1
    match roundTrip m with
    | .error e => bad := bad.push s!"{f}: {e}"
    | .ok m2 =>
      if valid m != valid m2 then bad := bad.push s!"{f}: validation differs after the round trip"
      else
        same := same + 1
        if valid m then
          match Aot.translate m 65536 with
          | .error _ => notTaken := notTaken + 1
          | .ok _ =>
            match translateChecked m 65536 with
            | .ok _ => translated := translated + 1
            | .error e => bad := bad.push s!"{f}: {e}"
  IO.println s!"aot: {files.size} files, {decoded} decode, {same} round trip, {translated} translated and valid, {notTaken} not taken by translate (imports or memories), {bad.size} failures"
  for b in bad.toList.take 30 do IO.println s!"  FAIL {b}"
  return bad.isEmpty

def module (wasm out : String) (pages : Nat) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let bytes ← IO.FS.readBinFile wasm
  let m ← match Binary.decodeParallel bytes with
    | .ok m => pure m
    | .error e => throw (IO.userError e.toString)
  let t1 ← IO.monoNanosNow
  if !valid m then throw (IO.userError "the guest does not validate")
  let t2 ← IO.monoNanosNow
  match roundTrip m with
  | .error e => IO.println s!"FAIL round trip: {e}"; return 1
  | .ok _ => pure ()
  let t3 ← IO.monoNanosNow
  match translateChecked m pages with
  | .error e => IO.println s!"FAIL {e}"; return 1
  | .ok (host, plan) =>
    let t4 ← IO.monoNanosNow
    IO.FS.writeBinFile out host
    IO.println s!"guest {bytes.size} bytes, host module {host.size} bytes, {plan.imports.size} imports, fuel global {plan.fuelGlobal}"
    IO.println s!"decode {(t1 - t0) / 1000000} ms, validate {(t2 - t1) / 1000000} ms, round trip {(t3 - t2) / 1000000} ms, translate+encode+check {(t4 - t3) / 1000000} ms"
    return 0

end L4Factoidal.WasmVM.Tests.Aot
