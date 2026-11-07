/-
L4Factoidal.WasmVM.Tests.Memory: tests of the linear-memory ownership rule and the
place for the differential test of memory backends
(https://github.com/danbri/factoidal/issues/1244, https://github.com/danbri/factoidal/issues/1289;
record: docs/designissues/2026-11-07-wasmvm-engine.md, "Linear memory").

Run by `lake exe wasmvm-spectest` (after the spec tests) and by
`lake exe wasmvm-bench memtest`. Compiled code only: the stores are `extern c inline`.

1. `noCopyTest`: `memsum` (a store and a load per iteration) runs 10^6 iterations on a
   1-page memory and on a 1024-page (64 MiB) memory. If a store copied the memory,
   the second run would take 10^6 copies of 64 MiB (hours). The test requires the
   second run to take at most 4 times the first plus 200 ms (room for the one copy
   of a store that the caller still holds, and for creating the memory).
2. `differential`: runs an export on two stores over two backends and compares the
   results and the memory bytes. Today both backends are `ByteMem`; backend B (page-
   aligned host memory, issue 1289) plugs in here.
-/
import L4Factoidal.WasmVM.Api
import L4Factoidal.WasmVM.Bench.Engine

namespace L4Factoidal.WasmVM.Tests.Memory
open L4Factoidal.WasmVM

/-- The benchmark module with its memory set to `pages` pages (`pages < 16384`). -/
def withPages (pages : Nat) : ByteArray := Id.run do
  let b := Bench.Engine.benchModule.data
  -- the memory section of `benchModule`: id 5, size 3, one memory, flags 0, min 1
  let old : Array UInt8 := #[0x05, 0x03, 0x01, 0x00, 0x01]
  let leb : Array UInt8 :=
    if pages < 128 then #[pages.toUInt8] else #[(pages % 128 + 128).toUInt8, (pages / 128).toUInt8]
  let new : Array UInt8 := #[0x05, (2 + leb.size).toUInt8, 0x01, 0x00] ++ leb
  let mut i := 0
  for k in [0:b.size] do
    if b.extract k (k + old.size) == old then i := k
  return ⟨b.extract 0 i ++ new ++ b.extract (i + old.size) b.size⟩

/-- Instantiate `bytes` on backend `M` and run export `name` with argument `n`:
the outcome, the memory bytes `[0, 4096)` and the time in ns. -/
def runOn (M : Type) [LinearMemory M] (bytes : ByteArray) (name : String) (n : Nat) :
    IO (Option (String × ByteArray × Nat)) := do
  let .ok m := decode bytes | return none
  let .ok vm := validate m | return none
  let (st, r) := instantiateRun (M := M) (fun _ _ st => (st, .values #[])) {} vm #[]
  let .ok ia := r | return none
  let some (.func fa) := st.export? ia name | return none
  let t0 ← IO.monoNanosNow
  let (st, o) ← IO.lazyPure fun _ => invoke st fa #[.i32 n.toUInt32] { fuel := 100000000000 }
  let d := o.describe
  let t1 ← IO.monoNanosNow
  let mem := match st.readMem 0 0 4096 with | .ok b => b | .error _ => ByteArray.empty
  return some (d, mem, t1 - t0)

/-- One timing round with `n` iterations: 1-page memory against 1024-page memory. -/
def noCopyRound (n : Nat) : IO Bool := do
  let some (r1, _, small) ← runOn ByteMem (withPages 1) "memsum" n | IO.println "memtest: setup failed"; return false
  let some (r2, _, big) ← runOn ByteMem (withPages 1024) "memsum" n | IO.println "memtest: setup failed"; return false
  let ok := r1 == r2 && big ≤ 4 * small + 200000000
  IO.println s!"memtest no-copy: {n} stores, 64 KiB memory {small / 1000000} ms, 64 MiB memory {big / 1000000} ms: {if ok then "pass" else "FAIL"}"
  return ok

/-- 10^3 stores first (a copying store makes this take seconds, not hours), then 10^6. -/
def noCopyTest : IO Bool := do
  if !(← noCopyRound 1000) then return false
  noCopyRound 1000000

/-- Differential test of two backends on the same program. -/
def differential (M N : Type) [LinearMemory M] [LinearMemory N] (bytes : ByteArray) (name : String)
    (n : Nat) : IO Bool := do
  let a ← runOn M bytes name n
  let b ← runOn N bytes name n
  let ok := match a, b with
    | some (ra, ma, _), some (rb, mb, _) => ra == rb && ma.data == mb.data
    | _, _ => false
  IO.println s!"memtest differential {name}({n}): {if ok then "pass" else "FAIL"}"
  return ok

def run : IO Bool := do
  let a ← noCopyTest
  let b ← differential ByteMem ByteMem (withPages 1) "memsum" 100000
  return a && b

end L4Factoidal.WasmVM.Tests.Memory
