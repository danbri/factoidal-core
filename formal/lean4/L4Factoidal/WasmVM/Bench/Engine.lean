/-
L4Factoidal.WasmVM.Bench.Engine: speed of the interpreter and the decoder
(https://github.com/danbri/factoidal/issues/1244). Results are recorded in
docs/designissues/2026-11-07-wasmvm-engine.md, "Measurements".

`benchModule` was made by `wat2wasm` from this text:

  (func $sum (param $n i32) (result i64)   ;; sum of 0..n-1 in a loop
  (func $fib (param $n i32) (result i32)   ;; recursive Fibonacci (calls)
  (func $memsum (param $n i32) (result i32) ;; a store and a load per iteration
  (memory 1)

(the full text is in the commit message of the commit that added this file).
-/
import L4Factoidal.WasmVM.Api

namespace L4Factoidal.WasmVM.Bench.Engine
open L4Factoidal.WasmVM

def benchModule : ByteArray := ⟨#[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x0b, 0x02, 0x60, 0x01, 0x7f, 0x01, 0x7e, 0x60, 0x01, 0x7f, 0x01, 0x7f, 0x03, 0x04, 0x03, 0x00, 0x01, 0x01, 0x05, 0x03, 0x01, 0x00, 0x01, 0x07, 0x1c, 0x04, 0x03, 0x73, 0x75, 0x6d, 0x00, 0x00, 0x03, 0x66, 0x69, 0x62, 0x00, 0x01, 0x03, 0x6d, 0x65, 0x6d, 0x02, 0x00, 0x06, 0x6d, 0x65, 0x6d, 0x73, 0x75, 0x6d, 0x00, 0x02, 0x0a, 0x7e, 0x03, 0x26, 0x02, 0x01, 0x7f, 0x01, 0x7e, 0x02, 0x40, 0x03, 0x40, 0x20, 0x01, 0x20, 0x00, 0x4f, 0x0d, 0x01, 0x20, 0x02, 0x20, 0x01, 0xad, 0x7c, 0x21, 0x02, 0x20, 0x01, 0x41, 0x01, 0x6a, 0x21, 0x01, 0x0c, 0x00, 0x0b, 0x0b, 0x20, 0x02, 0x0b, 0x1c, 0x00, 0x20, 0x00, 0x41, 0x02, 0x49, 0x04, 0x7f, 0x20, 0x00, 0x05, 0x20, 0x00, 0x41, 0x01, 0x6b, 0x10, 0x01, 0x20, 0x00, 0x41, 0x02, 0x6b, 0x10, 0x01, 0x6a, 0x0b, 0x0b, 0x38, 0x01, 0x02, 0x7f, 0x03, 0x40, 0x20, 0x01, 0x41, 0x02, 0x74, 0x41, 0xfc, 0xff, 0x03, 0x71, 0x20, 0x01, 0x36, 0x02, 0x00, 0x20, 0x02, 0x20, 0x01, 0x41, 0x02, 0x74, 0x41, 0xfc, 0xff, 0x03, 0x71, 0x28, 0x02, 0x00, 0x6a, 0x21, 0x02, 0x20, 0x01, 0x41, 0x01, 0x6a, 0x21, 0x01, 0x20, 0x01, 0x20, 0x00, 0x49, 0x0d, 0x00, 0x0b, 0x20, 0x02, 0x0b]⟩

def timeIt (f : Unit → α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  return (r, t1 - t0)

/-- Run an export once; gives the instructions run and million instructions a second. -/
def runExport (st : Store) (ia : Nat) (name : String) (arg : Nat) : IO (Nat × Nat) := do
  let some (.func fa) := st.export? ia name | IO.println s!"no export {name}"; return (0, 0)
  let ((_, o, steps), ns) ← timeIt fun _ => invokeSteps st fa #[.i32 arg.toUInt32] { fuel := 100000000000 }
  let mips := if ns == 0 then 0 else steps * 1000 / ns
  IO.println s!"{name}({arg}): {o.describe}; {steps} instructions in {ns / 1000000} ms = {mips} million per second"
  return (steps, mips)

def engine (n : Nat) : IO Unit := do
  let .ok m := decode benchModule | IO.println "decode failed"
  let .ok vm := validate m | IO.println "invalid"
  let (st, r) := instantiateRun (M := ByteMem) (fun _ _ st => (st, .values #[])) {} vm #[]
  let .ok ia := r | IO.println "instantiation failed"
  let _ ← runExport st ia "sum" n
  let _ ← runExport st ia "memsum" n
  let _ ← runExport st ia "fib" (if n ≥ 10000000 then 30 else 25)

/-- The ratchet (`wasmvm-bench engine --check`). Each benchmark must run exactly the
instructions of the unfused code (a fused op charges the fuel of its parts:
`Proofs.Cost.fused_charges_parts`), and at least a floor of million instructions a
second: the speed measured when the floor was set, less a margin for a loaded machine.
Raise a floor when the engine gets faster; never lower one without saying why in the
record (docs/designissues/2026-11-07-wasmvm-engine.md, "Cost model and ratchet"). The
best of `tries` runs counts. -/
def floors : List (String × Nat × Nat × Nat) :=
  -- export, argument, exact instructions, floor (million per second)
  [("sum", 10000000, 140000008, 240), ("memsum", 10000000, 240000004, 140), ("fib", 30, 28271637, 110)]

def check (tries : Nat := 3) : IO UInt32 := do
  let .ok m := decode benchModule | IO.println "decode failed"; return 1
  let .ok vm := validate m | IO.println "invalid"; return 1
  let (st, r) := instantiateRun (M := ByteMem) (fun _ _ st => (st, .values #[])) {} vm #[]
  let .ok ia := r | IO.println "instantiation failed"; return 1
  let mut bad := 0
  for (name, arg, want, floor) in floors do
    let mut best := 0
    let mut steps := 0
    for _ in [0:tries] do
      let (s, mips) ← runExport st ia name arg
      steps := s
      best := max best mips
    if steps != want then
      IO.println s!"FAIL {name}: {steps} instructions, expected exactly {want}"; bad := bad + 1
    else if best < floor then
      IO.println s!"FAIL {name}: best {best} million instructions a second, floor {floor}"; bad := bad + 1
    else IO.println s!"ok   {name}: {steps} instructions; best {best} M/s (floor {floor})"
  return if bad == 0 then 0 else 1

/-- Decode and validate a module file, serial and with function bodies in parallel. -/
def decodeFile (path : String) : IO Unit := do
  let b ← IO.FS.readBinFile path
  let (r, ns) ← timeIt fun _ => decode b
  match r with
  | .error e => IO.println s!"decode: {e.toString}"
  | .ok m =>
    IO.println s!"{path}: {b.size} bytes, {m.funcs.size} functions; decode {ns / 1000000} ms"
    let (r2, ns2) ← timeIt fun _ => Binary.decodeParallel b
    let same := match r2 with
      | .ok m2 => m2.funcs.size == m.funcs.size && (m2.funcs.zip m.funcs).all fun (x, y) => x.body.size == y.body.size && x.locals == y.locals
      | .error _ => false
    IO.println s!"decode with code entries in parallel: {ns2 / 1000000} ms (same functions: {same})"
    let (v, ns) ← timeIt fun _ => validate m
    match v with
    | .error e => IO.println s!"validate: {e.toString}"
    | .ok vm =>
      let ops := vm.code.foldl (fun a c => a + c.code.size) 0
      IO.println s!"validate and compile (serial): {ns / 1000000} ms, {ops} ops"
    let (v, ns) ← timeIt fun _ => validateParallel m
    match v with
    | .error e => IO.println s!"validate (parallel): {e.toString}"
    | .ok _ => IO.println s!"validate and compile (parallel): {ns / 1000000} ms"

end L4Factoidal.WasmVM.Bench.Engine
