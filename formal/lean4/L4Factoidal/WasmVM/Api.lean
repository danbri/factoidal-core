/-
L4Factoidal.WasmVM.Api: the public surface of the engine
(https://github.com/danbri/factoidal/issues/1244; design:
docs/designissues/2026-11-07-wasmvm-engine.md, "API").

    decode      : ByteArray → Except DecodeError Module
    validate    : Module → Except ValidationError ValidModule
    instantiate : Store → ValidModule → Array ExternVal → Store × Except InstError (Nat × Option Nat)
    invoke      : Store → FuncAddr → Array Value → Budget → Store × Outcome
    resume      : Store → Suspended → HostResult → Budget → Store × Outcome

The engine is pure. A call of a host function stops the run with
`Outcome.hostCall`; the embedder does the work in its own monad (it may read and
write memory with `Store.readMem`/`Store.writeMem`) and calls `resume`. Running out
of fuel stops the run the same way, and `resume` continues it. `runIO` is one
driver loop for `IO` embedders.
-/
import L4Factoidal.WasmVM.Binary.Decode
import L4Factoidal.WasmVM.Valid
import L4Factoidal.WasmVM.Exec.Run
import L4Factoidal.WasmVM.Exec.Instantiate

namespace L4Factoidal.WasmVM

export Binary (decode decodeParallel DecodeError)

section
variable {M : Type} [LinearMemory M]

/-- How much a run may use. -/
structure Budget where
  /-- Instructions to run before `Outcome.outOfFuel`. -/
  fuel : Nat := 1000000000
  run : RunLimits := {}
  deriving Inhabited

/-- A stopped run that can continue. -/
structure Suspended where
  machine : Machine
  /-- Result types of the invoked function. -/
  results : Array ValType
  /-- Result types the host owes, when stopped at a host call. -/
  hostResults : Option (Array ValType)
  deriving Inhabited

inductive Outcome where
  | values (vs : Array Value)
  | trap (t : Trap)
  | outOfFuel (k : Suspended)
  | hostCall (id : Nat) (args : Array Value) (k : Suspended)
  | exit (status : Nat)
  /-- An exception no handler caught: its tag address and payload. -/
  | exception (tag : Nat) (args : Array Value)
  deriving Inhabited

/-- What a host function gives back. -/
inductive HostResult where
  | values (vs : Array Value)
  | trap (msg : String)
  /-- End the whole run (WASI `proc_exit`). -/
  | exit (status : Nat)

def Outcome.describe : Outcome → String
  | .values vs => s!"values {repr vs}"
  | .trap t => s!"trap: {t.message}"
  | .outOfFuel _ => "out of fuel"
  | .hostCall id _ _ => s!"host call {id}"
  | .exit s => s!"exit {s}"
  | .exception t _ => s!"uncaught exception of tag {t}"

private def finish (st : StoreOf M) (results : Array ValType) (r : StoreOf M × Machine × Nat × Event) :
    StoreOf M × Outcome :=
  let (st', m, _, ev) := r
  let _ := st
  match ev with
  | .done =>
    let base := m.sp - results.size.toUSize
    (st', .values ((results.zipIdx).map fun (t, i) => Value.ofBits t (Run.rd m.stack (base + i.toUSize))))
  | .trap t => (st', .trap t)
  | .outOfFuel => (st', .outOfFuel { machine := m, results, hostResults := none })
  | .hostCall id fa args =>
    let ft := (st'.funcs[fa]!).type
    let vs := (ft.params.zip args).map fun (t, b) => Value.ofBits t b
    (st', .hostCall id vs { machine := m, results, hostResults := some ft.results })
  | .exception exn =>
    let e := st'.exc.exns[exn]!
    let ps := (st'.exc.tags[e.tag]?).map (·.params) |>.getD #[]
    (st', .exception e.tag ((ps.zip e.fields).map fun (t, b) => Value.ofBits t b))

@[specialize] def invoke (st : StoreOf M) (fa : Nat) (args : Array Value) (lim : Budget := {}) : StoreOf M × Outcome :=
  match st.funcs[fa]? with
  | none => (st, .trap (.host "unknown function"))
  | some fi =>
    if args.size != fi.type.params.size then (st, .trap (.host "wrong number of arguments")) else
    let n := args.size
    let stack := args.foldl (init := (Slots.zeros (max 1024 (2 * n)), 0))
      (fun (s, i) v => (Run.wr s i.toUSize v.toBits, i + 1)) |>.1
    let code : Array Op := #[.call 0, .return_ fi.type.results.size]
    let inst : ModuleInst := { funcs := #[fa] }
    finish st fi.type.results (Run.run lim.run st stack n.toUSize 0 0 code inst #[] lim.fuel)

/-- `invoke`, also giving the number of instructions run (for measurements). -/
@[specialize] def invokeSteps (st : StoreOf M) (fa : Nat) (args : Array Value) (lim : Budget := {}) : StoreOf M × Outcome × Nat :=
  match st.funcs[fa]? with
  | none => (st, .trap (.host "unknown function"), 0)
  | some fi =>
    let stack := args.foldl (init := (Slots.zeros (max 1024 (2 * args.size)), 0))
      (fun (s, i) v => (Run.wr s i.toUSize v.toBits, i + 1)) |>.1
    let code : Array Op := #[.call 0, .return_ fi.type.results.size]
    let inst : ModuleInst := { funcs := #[fa] }
    let r := Run.run lim.run st stack args.size.toUSize 0 0 code inst #[] lim.fuel
    let (st', o) := finish st fi.type.results r
    (st', o, lim.fuel - r.2.2.1)

@[specialize] def resume (st : StoreOf M) (k : Suspended) (r : HostResult) (lim : Budget := {}) : StoreOf M × Outcome :=
  match r with
  | .trap msg => (st, .trap (.host msg))
  | .exit s => (st, .exit s)
  | .values vs =>
    let m := k.machine
    let m := match k.hostResults with
      | none => m
      | some _ =>
        let (stack, sp) := vs.foldl (init := (m.stack, m.sp.toNat)) fun (s, i) v =>
          ((if i < s.count then Run.wr s i.toUSize v.toBits
            else Slots.wr (Slots.grow s (i + 1 - s.count)) i.toUSize v.toBits), i + 1)
        { m with stack, sp := sp.toUSize }
    finish st k.results (Run.runM lim.run st m lim.fuel)

/-- A pure host: host function id, arguments, store → store and result. -/
abbrev PureHost (M : Type) := Nat → Array Value → StoreOf M → StoreOf M × HostResult

/-- Serve host calls with a pure host, at most `n` of them. -/
@[specialize] def drive (host : PureHost M) (lim : Budget) : Nat → StoreOf M × Outcome → StoreOf M × Outcome
  | 0, r => r
  | n + 1, (st, o) =>
    match o with
    | .hostCall id vs k =>
      let (st, r) := host id vs st
      drive host lim n (resume st k r lim)
    | _ => (st, o)

@[specialize] def invokePure (host : PureHost M) (st : StoreOf M) (fa : Nat) (args : Array Value)
    (lim : Budget := {}) (maxHostCalls : Nat := 1000000) : StoreOf M × Outcome :=
  drive host lim maxHostCalls (invoke st fa args lim)

/-- Instantiate, then run the start function with a pure host. -/
@[specialize] def instantiateRun (host : PureHost M) (st : StoreOf M) (vm : ValidModule) (imports : Array ExternVal)
    (lim : Budget := {}) : StoreOf M × Except InstError Nat :=
  match instantiate st vm imports with
  | (st, .error e) => (st, .error e)
  | (st, .ok (i, none)) => (st, .ok i)
  | (st, .ok (i, some s)) =>
    match invokePure host st s #[] lim with
    | (st, .values _) => (st, .ok i)
    | (st, .trap t) => (st, .error (.trap t))
    | (st, o) => (st, .error (.link s!"start function stopped: {o.describe}"))

/-- A driver for `IO` embedders: runs host calls through `host` until the run ends
or `maxHostCalls` host calls have been served. -/
@[specialize] def runIO (st : StoreOf M) (fa : Nat) (args : Array Value) (lim : Budget)
    (host : Nat → Array Value → StoreOf M → IO (StoreOf M × HostResult)) (maxHostCalls : Nat := 1000000) :
    IO (StoreOf M × Outcome) := do
  let mut (st, o) := invoke st fa args lim
  for _ in [0:maxHostCalls] do
    match o with
    | .hostCall id vs k =>
      let (st', r) ← host id vs st
      (st, o) := resume st' k r lim
    | _ => break
  return (st, o)

end
end L4Factoidal.WasmVM
