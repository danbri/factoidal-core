/-
L4Factoidal.WasmVM.Tests.AotPage: the AOT path of page scripts, run natively with WasmVM
standing in for the host's WebAssembly engine
(record: docs/designissues/2026-11-08-wasmvm-aot.md, section 5).

`Host` plays the Hub worker, step by step: it instantiates the TRANSLATED module (the
bytes `PageAot.prepare` gives, decoded again), answers each ask of the session program
(`Prog.next`, `Paused.resume`), passes every import call back to `PageAot.serveHost` with
the ranges of `Prepared.reads` copied out of the guest's memory, copies the writes back,
and sets and reads the fuel global around each run. Only the machine differs from the
worker: WasmVM here, the browser's engine there. `wasmvm-bench page ... --aot` runs each
page both ways and compares the results.
-/
import L4Factoidal.WasmVM.Hosts.PageAot

namespace L4Factoidal.WasmVM.Tests.AotPage
open L4Factoidal.WasmVM L4Factoidal.WasmVM.Hosts.Page L4Factoidal.WasmVM.Hosts.PageAot

/-- The stand-in for the host's engine: the translated module, compiled once. -/
structure Engine where
  prepared : Prepared
  valid : ValidModule
  module : Module

def Engine.of (p : Prepared) : Except String Engine := do
  let md ← (Binary.decode p.bytes).mapError (fun e => s!"host module: decode: {e.toString}")
  let v ← (validate md).mapError (fun e => s!"host module: validate: {e.toString}")
  return { prepared := p, valid := v, module := md }

/-- One instance of the translated module, as the worker holds it. -/
structure Instance where
  st : Store
  mem : Nat
  fuel : Nat
  funcs : Array Nat
  /-- Writes Lean answered at once, sent before the next ask (as the worker does). -/
  pending : Array (Nat × ByteArray) := #[]

def Engine.instantiate (e : Engine) : Except String Instance := do
  -- Import `k` (`aot.i{k}`) is host function `k`, as the worker's import object.
  let (st, ex) := e.module.imports.zipIdx.foldl (init := (({} : Store), (#[] : Array ExternVal))) fun (st, ex) (imp, i) =>
    let ft := match imp.desc with | .func t => e.module.types[t]?.getD ⟨#[], #[]⟩ | _ => ⟨#[], #[]⟩
    let (st, a) := st.addHostFunc ft i
    (st, ex.push (.func a))
  let (st, ia) ← match L4Factoidal.WasmVM.instantiate st e.valid ex with
    | (st, .ok (ia, none)) => pure (st, ia)
    | (_, .ok _) => throw "start function"
    | (_, .error err) => throw s!"instantiate: {err.toString}"
  let mem ← match st.export? ia "memory" with | some (.mem a) => pure a | _ => throw "no memory"
  let fuel ← match st.export? ia Aot.fuelExport with | some (.global a) => pure a | _ => throw "no fuel global"
  let funcs ← exportNames.mapM fun n => match st.export? ia n with
    | some (.func a) => Except.ok a
    | _ => .error s!"no export {n}"
  return { st, mem, fuel, funcs }

def memSize (i : Instance) : Nat := match i.st.mems[i.mem]? with
  | some m => LinearMemory.size m.data
  | none => 0

def Instance.flush (i : Instance) : Instance := Id.run do
  let mut st := i.st
  for (p, b) in i.pending do
    st := match st.writeMem i.mem p b with | .ok st => st | .error _ => st
  return { i with st, pending := #[] }

def argNat (args : Array Value) (k : Nat) : Nat := match args[k]? with | some (.i32 v) => v.toNat | _ => 0

/-- Run export `fa` with the host calls passed back to Lean, as the worker's import
functions do. -/
def Instance.invoke (e : Engine) (i : Instance) (p : Paused α) (fa : Nat) (args : Array Value) :
    Instance × Paused α × Outcome × Int := Id.run do
  let i := i.flush
  let fuel := p.session.limits.fuel
  let st := { i.st with globals := Slots.wr i.st.globals i.fuel.toUSize fuel.toUInt64 }
  let budget : Budget := { fuel := 1000000000000 }
  let (st0, o0, _) := invokeSteps st (i.funcs[fa]?.getD 0) args budget
  let mut st := st0
  let mut o := o0
  let mut p := p
  for _ in [0:100000000] do
    match o with
    | .hostCall id vs k =>
      let size := memSize { i with st }
      let segs := ((e.prepared.reads[id]?.getD []).filterMap fun r =>
        let ptr := argNat vs r.ptr
        let len := argNat vs r.len
        if len ≤ r.bound && ptr + len ≤ size then
          match st.readMem i.mem ptr len with | .ok b => some (ptr, b) | .error _ => none
        else none).toArray
      let left := Int.ofNat (st.globalBits i.fuel).toNat
      let left := if left ≥ 9223372036854775808 then left - 18446744073709551616 else left
      let (p', hr, writes) := serveHost p id vs size segs left
      p := p'
      for (q, b) in writes do
        st := match st.writeMem i.mem q b with | .ok st => st | .error _ => st
      let (st', o', _) := resumeSteps st k hr budget
      st := st'; o := o'
    | _ => break
  let left := Int.ofNat (st.globalBits i.fuel).toNat
  let left := if left ≥ 9223372036854775808 then left - 18446744073709551616 else left
  -- A host trap ends the run as a trap; WasmVM's own traps are the host engine's traps.
  ({ i with st }, p, o, left)

/-- Drive a program to its end, as the worker does. -/
def drive (e : Engine) (i : Instance) (prog : Prog α) : Except String (Instance × α) := Id.run do
  let mut i := i
  let mut cur := Prog.next prog
  for _ in [0:100000000] do
    match cur with
    | .inl a => return .ok (i, a)
    | .inr p =>
      match p.ask with
      | .invoke fa args =>
        let (i', p, o, left) := i.invoke e p fa args
        i := i'
        let (p, r) := ranReply p o left
        cur := p.resume r
      | .read ptr len =>
        i := i.flush
        cur := p.resume (.bytes (i.st.readMem i.mem ptr len))
      | .write ptr b =>
        -- Answered at once when it fits; the bytes go with the next ask.
        if ptr + b.size ≤ memSize i then
          i := { i with pending := i.pending.push (ptr, b) }
          cur := p.resume (.wrote (.ok ()))
        else cur := p.resume (.wrote (.error "out of bounds memory access"))
  return .error "drive: too many asks"

/-- Start a page on the AOT path: a fresh instance, `_initialize`, `qjs_new`, page mode,
then `Session.startP`. -/
def start (e : Engine) (dom : Arena) (url : String) (scripts : Array (Nat × String)) (lim : Hosts.Page.Limits := {})
    (frames : Array (Nat × Arena) := #[]) (reads : Reads := {}) (time : ScriptClock := {}) :
    Except String (Instance × Session) := do
  let (dom, framed) := graftFrames dom frames
  let i ← e.instantiate
  let prog := startProg e.prepared dom url scripts lim framed #[] reads time
  let (i, r) ← drive e i prog
  return (i, ← r)

def settle (e : Engine) (i : Instance) (s : Session) (budgetMs : Nat) : Except String (Instance × Session × Bool) :=
  drive e i (s.settleP budgetMs)

end L4Factoidal.WasmVM.Tests.AotPage
