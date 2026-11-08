/-
L4Factoidal.WasmVM.Bench.Test262: a random sample of Test262 run by QuickJS-NG inside the
WasmVM engine (https://github.com/danbri/factoidal/issues/1244; record:
docs/designissues/2026-11-07-wasmvm-engine.md, "QuickJS in WasmVM").

`lake exe wasmvm-bench test262 WASM DIR [NATIVE [FUEL]]`, from `formal/lean4`.
- WASM: the output of `tools/wasmvm/build-quickjs.sh`.
- DIR: the prepared cases of `tools/wasmvm/quickjs/test262-sample.py`. The first line
  of each case says what to expect: `pass`, `negative <ErrorType>` or `async`.
- NATIVE, when given: the same entry point built natively
  (`tools/wasmvm/quickjs/README.md`). The bench runs it on the same cases, so a failure
  in the VM that native QuickJS does not have is a VM fault, and it is listed.

Each case runs with the export `qjs_test262` in a fresh JavaScript context. A case that
stops the VM (trap or out of fuel; FUEL instructions, default 2e9) fails, and the module is
loaded again for the next case.
-/
import L4Factoidal.WasmVM.Bench.QuickJS

namespace L4Factoidal.WasmVM.Bench.Test262
open L4Factoidal.WasmVM L4Factoidal.WasmVM.Bench.QuickJS

/-- Does a result (status, text) meet the expectation? -/
def verdict (expect : String) (status : Nat) (text : String) : Bool :=
  if expect == "pass" then status == 0
  else if expect == "async" then status == 0 && (text.splitOn "Test262:AsyncTestComplete").length > 1
  else if expect.startsWith "negative " then status == 1 && text.startsWith (expect.drop 9).toString
  else false

def header (src : String) : String × String :=
  let line := (src.splitOn "\n").head!
  match (line.drop 11).toString.splitOn " ; " with
  | e :: p :: _ => (e.trimAscii.toString, p)
  | _ => ("?", "?")

/-- The native runner's (status, text) per file. -/
def native (exe : String) (files : Array String) : IO (Std.HashMap String (Nat × String)) := do
  let mut m : Std.HashMap String (Nat × String) := {}
  -- In chunks, to keep command lines short.
  for i in [0:(files.size + 99) / 100] do
    let chunk := files.extract (100 * i) (100 * i + 100)
    let r ← IO.Process.output { cmd := exe, args := chunk }
    for line in r.stdout.splitOn "\n" do
      match line.splitOn "\t" with
      | f :: s :: rest => m := m.insert f (s.toNat?.getD 9, "\t".intercalate rest)
      | _ => pure ()
  return m

def run (wasm dir : String) (nativeExe : Option String) (fuel : Nat := 2000000000) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile wasm
  let entries ← System.FilePath.readDir dir
  let files := (entries.filter (·.fileName.endsWith ".js")).map (·.path.toString) |>.toList.mergeSort (· ≤ ·) |>.toArray
  let nat ← match nativeExe with
    | some e => native e files
    | none => pure {}
  let restart := fun (_ : Unit) => show IO (Vm × Nat) from do
    let (_, v) ← start bytes "<!doctype html><title>Test262</title>"
    let fa ← match v.store.export? v.inst "qjs_test262" with
      | some (.func a) => pure a
      | _ => throw (IO.userError "the module has no export qjs_test262")
    pure ({ v with limits := { v.limits with fuel } }, fa)
  let (v0, t262) ← restart ()
  let mut v := v0
  let mut pass := 0
  let mut fail := 0
  let mut nativePass := 0
  let mut vmOnly : Array String := #[]
  let mut failures : Array String := #[]
  let mut steps := 0
  let mut ns := 0
  let mut reloads := 0
  for f in files do
    let src ← IO.FS.readFile f
    let (expect, path) := header src
    let b := src.toUTF8
    let t0 ← IO.monoNanosNow
    let n0 := v.steps
    let (v1, p) := v.put b
    let (v2, o) := v1.run t262 #[.i32 (p.getD 0).toUInt32, .i32 b.size.toUInt32]
    let t1 ← IO.monoNanosNow
    steps := steps + (v2.steps - n0); ns := ns + (t1 - t0)
    let (status, text, v3) := match o with
      | .values #[.i32 r] =>
        let v3 := v2.freePtr (p.getD 0)
        let (v3, s, x) := v3.result r.toNat
        (s, x, some v3)
      | o => (2, s!"VM: {o.describe}", none)
    match v3 with
    | some v' => v := v'
    | none => reloads := reloads + 1; v := (← restart ()).1
    let ok := verdict expect status text
    if ok then pass := pass + 1
    else
      fail := fail + 1
      failures := failures.push s!"{path} (expect {expect}): {(text.splitOn "\n").head!.take 160}"
    match nat[f]? with
    | some (ns', nt) =>
      let nok := verdict expect ns' nt
      if nok then nativePass := nativePass + 1
      if nok && !ok then vmOnly := vmOnly.push path
    | none => pure ()
  let total := pass + fail
  IO.println s!"Test262 sample: {total} cases run in WasmVM: {pass} pass, {fail} fail ({if total == 0 then 0 else pass * 1000 / total / 10}.{if total == 0 then 0 else pass * 1000 / total % 10}%)"
  IO.println s!"  {steps} instructions in {ns / 1000000} ms ({if ns == 0 then 0 else steps * 1000 / ns} M instr/s); module loaded again {reloads} times"
  if nativeExe.isSome then
    IO.println s!"  native QuickJS-NG on the same cases: {nativePass} pass; pass natively but fail in the VM: {vmOnly.size}"
    for p in vmOnly do IO.println s!"    VM only: {p}"
  IO.println "failures:"
  for x in failures do IO.println s!"  {x}"
  return if vmOnly.isEmpty then 0 else 1

end L4Factoidal.WasmVM.Bench.Test262
