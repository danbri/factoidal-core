/-
L4Factoidal.WasmVM.WasiIO: capability sources in `IO` for the WASI host, and a loader
(https://github.com/danbri/factoidal/issues/1244; record:
docs/designissues/2026-11-07-wasmvm-engine.md, "WASI Preview 1").

- Clocks: realtime (0) from `Std.Time.Timestamp.now`, monotonic (1) from
  `IO.monoNanosNow`. The process and thread CPU clocks (2, 3) are not granted.
- Randomness: `systemRandom` is `IO.getRandomBytes` (the operating system's source).
  `seededRandom seed` is a SplitMix64 stream: deterministic and NOT random, for tests
  that say they use it.
- Sinks: `capture ref` appends to a buffer; `forwardStdout`/`forwardStderr` write to
  this process's streams.

`load` decodes, validates, links (`Wasi.link`) and instantiates a module, runs its
start function, and gives the store, the instance and its exported memory. `runExport`
runs one export through `Api.runIO` with the WASI host.
-/
import L4Factoidal.WasmVM.Wasi
import Std.Time.DateTime.Timestamp

namespace L4Factoidal.WasmVM.Wasi
open L4Factoidal.WasmVM

/-- Clock 0 (realtime, nanoseconds since 1970) and 1 (monotonic). -/
def systemClock : UInt32 → Option (IO UInt64)
  | 0 => some do
    let t ← Std.Time.Timestamp.now
    return t.toNanosecondsSinceUnixEpoch.val.toNat.toUInt64
  | 1 => some do return (← IO.monoNanosNow).toUInt64
  | _ => none

/-- The resolution this host states for clocks 0 and 1: 1 microsecond (macOS
`clock_getres` gives 1000 ns for both; Linux gives 1 ns, so this is not finer than the
real one). -/
def systemClockRes : UInt32 → Option UInt64
  | 0 | 1 => some 1000
  | _ => none

/-- Real randomness from the operating system (`IO.getRandomBytes`). -/
def systemRandom (n : Nat) : IO ByteArray := IO.getRandomBytes n.toUSize

/-- SplitMix64 (Steele, Lea and Flood, 2014). -/
def splitmix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9e3779b97f4a7c15
  let z := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (z ^^^ (z >>> 31), s)

/-- A deterministic byte stream from `seed`. NOT random: for tests only, which must
say that they use it. -/
def seededRandom (seed : UInt64) : IO (Nat → IO ByteArray) := do
  let r ← IO.mkRef seed
  return fun n => do
    let mut out := ByteArray.emptyWithCapacity n
    let mut s ← r.get
    for _ in [0:(n + 7) / 8] do
      let (v, s') := splitmix s
      s := s'
      out := out ++ le64 v
    r.set s
    return out.extract 0 n

def capture (r : IO.Ref ByteArray) : ByteArray → IO Unit := fun b => r.modify (· ++ b)
def forwardStdout : ByteArray → IO Unit := fun b => do
  let o ← IO.getStdout; o.write b; o.flush
def forwardStderr : ByteArray → IO Unit := fun b => do
  let o ← IO.getStderr; o.write b; o.flush

/-- An instance with the WASI host. -/
structure Loaded where
  store : Store
  inst : Nat
  /-- Store address of the exported `memory` (a number past the store's memories
  when there is none, so every WASI memory access answers `EFAULT`). -/
  mem : Nat
  bindings : Array Binding

/-- The module's exported memory, from the instance's exports. -/
def memOf (st : Store) (ia : Nat) : Nat :=
  match st.export? ia "memory" with
  | some (.mem a) => a
  | _ => st.mems.size + 1

/-- Decode (code entries in parallel), validate, link and instantiate; run the start
function, if any, with the WASI host. `extra` names and serves the embedder's own
imports. -/
def load (caps : Caps IO) (bytes : ByteArray) (lim : Budget := {})
    (extraNames : String → String → Bool := fun _ _ => false)
    (extra : String → String → Array Value → Store → IO (Store × HostResult) :=
      fun _ _ _ st => pure (st, .trap "no host function")) :
    IO (Except String Loaded) := do
  let md ← match Binary.decodeParallel bytes with
    | .ok md => pure md
    | .error e => return .error s!"decode: {e.toString}"
  let vm ← match validateParallel md with
    | .ok vm => pure vm
    | .error e => return .error s!"validate: {e.toString}"
  let (st, ex, bs) ← match link ({} : Store) md extraNames with
    | .ok r => pure r
    | .error e => return .error s!"link: {e}"
  match instantiate st vm ex with
  | (_, .error e) => return .error s!"instantiate: {e.toString}"
  | (st, .ok (ia, none)) => return .ok { store := st, inst := ia, mem := memOf st ia, bindings := bs }
  | (st, .ok (ia, some s)) =>
    let mem := memOf st ia
    let (st, o) ← runIO st s #[] lim (host caps mem bs extra)
    match o with
    | .values _ => return .ok { store := st, inst := ia, mem, bindings := bs }
    | o => return .error s!"start function: {o.describe}"

/-- Run export `name` with the WASI host. -/
def Loaded.run (l : Loaded) (caps : Caps IO) (name : String) (args : Array Value) (lim : Budget := {})
    (extra : String → String → Array Value → Store → IO (Store × HostResult) :=
      fun _ _ _ st => pure (st, .trap "no host function")) :
    IO (Loaded × Outcome) := do
  -- Take the store out of `l` first: while `l` also held it, the run's first memory
  -- write copied the whole memory.
  let ⟨st, inst, mem, bs⟩ := l
  match st.export? inst name with
  | some (.func fa) =>
    let (st, o) ← runIO st fa args lim (host caps mem bs extra)
    return (⟨st, inst, mem, bs⟩, o)
  | _ => return (⟨st, inst, mem, bs⟩, .trap (.host s!"no export {name}"))

end L4Factoidal.WasmVM.Wasi
