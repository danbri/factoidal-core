import L4Factoidal.WasmVM.Api
import L4Factoidal.WasmVM.Wasi
import L4Factoidal.WasmVM.Bench.Engine
import L4Factoidal.WasmVM.Tests.Proposals
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize
import L4Factoidal.Rendering.SfntProfile
import WebWasmSample

/-!
# WebWasm: the Lean WebAssembly engine inside Foafnaut

Document ops of the Foafnaut engine that run WebAssembly with Lean's own engine,
`L4Factoidal.WasmVM` (issue https://github.com/danbri/factoidal/issues/1244). The
host browser's WebAssembly never runs the module: the Foafnaut engine, built to Wasm
for the Hub or native for the Mac app, holds the WasmVM interpreter and runs it.

- `wasmInfo`: the engine, its limits and its ops. Hosts call it first: an engine from
  before these ops answers "unknown document operation".
- `wasmRun`: a module (`wasmBase64`), an `export`, `args` in the spec-test JSON form
  (`{"type":"i32","value":"42"}`, floats as bit patterns) and `fuel`. The answer has
  each stage (decode, validate, instantiate), the exports, and the values, trap or
  exception, with the instructions run and the time.
- `wasmSpecSample`: a sample of the official core tests (`WebWasmSample`), and the
  legacy exception cases of `Tests.Proposals`; pass and fail counts.
- `wasmPage`: the page `foafnaut:wasm`, as HTML that this engine then lays out: the
  demo modules, their results, instruction counts and speed, the spec sample, and a
  given module when the request has one.

Imports: a module that imports from `wasi_snapshot_preview1` gets `WasmVM.Wasi`, deny
by default, with only `fd_write` to stdout and stderr granted (into the page's output)
and one program argument: no clock, randomness, environment or files. Any other module
gets the `spectest` set (print functions, which log their arguments, four globals, a
table and a memory). Every other import is refused, so a module reaches nothing else.

Limits: module size, fuel, host calls, memory pages, table size and the call depth and
operand stack below; the engine checks them, not the host.

Times come from the machine through `timed` (`Machine`): the host clock in `BaseIO`, time 0
in `Id`, the logical model. A time is a measurement, not part of any result that a proof reads.
-/

set_option compiler.extract_closed false

namespace WebWasm
open L4Factoidal
open L4Factoidal.WasmVM

/-! ## Limits -/

def maxModuleBytes : Nat := 4194304
def defaultFuel : Nat := 100000000
def maxFuel : Nat := 2000000000
def maxHostCalls : Nat := 10000
/-- Pages of 64 KiB one memory may have: 32 MiB. -/
def pageLimit : Nat := 512
def maxTableMin : Nat := 1000000
def maxArgs : Nat := 64
def maxPrints : Nat := 64
def runLimits : RunLimits := { maxDepth := 10000, maxSlots := 1 <<< 20 }

/-! ## The machine: time and random bytes (issue 390)

What the engine reads from the machine it runs on. The engine's export runs in `BaseIO`,
which reads the host clock and the host's random bytes; tests and proofs run in `Id`, the
logical model: time 0 and no random bytes. -/

class Machine (m : Type → Type) where
  /-- `f ()` and the nanoseconds it took. -/
  timed {α : Type} : (Unit → α) → m (α × Nat)
  /-- `n` random bytes from the host's generator; empty when it has none. -/
  randomBytes : Nat → m ByteArray

instance : Machine Id where
  timed f := (f (), 0)
  randomBytes _ := ByteArray.empty

/-- `f ()`, evaluated when this action runs (so not moved out of a timed span). -/
@[noinline] def evalNow {α : Type} (f : Unit → α) : BaseIO α := pure (f ())

instance : Machine BaseIO where
  timed f := do
    let t0 ← IO.monoNanosNow
    let r ← evalNow f
    let t1 ← IO.monoNanosNow
    pure (r, t1 - t0)
  randomBytes n := do
    match ← (IO.getRandomBytes n.toUSize).toBaseIO with
    | .ok b => pure b
    | .error _ => pure ByteArray.empty

instance {ε : Type} {m : Type → Type} [Monad m] [Machine m] : Machine (ExceptT ε m) where
  timed f := ExceptT.lift (Machine.timed f)
  randomBytes n := ExceptT.lift (Machine.randomBytes n)

instance {σ : Type} {m : Type → Type} [Monad m] [Machine m] : Machine (StateT σ m) where
  timed f := StateT.lift (Machine.timed f)
  randomBytes n := StateT.lift (Machine.randomBytes n)

/-- `f ()` and the nanoseconds it took on the machine's clock (0 in `Id`). -/
@[inline] def timed {m : Type → Type} [Machine m] {α : Type} (f : Unit → α) : m (α × Nat) := Machine.timed f

/-! ## Values in the spec-test JSON form -/

def num (n : Nat) : JSON.Json := .number (toString n)

private def str (j : JSON.Json) (key : String) : Option String :=
  match j.field? key with | some (.string s) => some s | _ => none

/-- A string or a number field, as its text. -/
private def text (j : JSON.Json) (key : String) : Option String :=
  match j.field? key with | some (.string s) => some s | some (.number n) => some n | _ => none

def wrap (bits : Nat) (i : Int) : Nat := (i % (2 ^ bits : Int)).toNat

def valTypeName : ValType → String
  | .i32 => "i32" | .i64 => "i64" | .f32 => "f32" | .f64 => "f64" | .v128 => "v128"
  | .ref r => match r.heap with
    | .func => "funcref" | .extern => "externref" | .exn => "exnref" | _ => "ref"

/-- A value from `{"type":..,"value":..}`; integers may be signed. -/
def valueOf (j : JSON.Json) : Except String Value := do
  let some ty := str j "type" | throw "argument type required"
  let v := (text j "value").getD "null"
  let int := fun (_ : Unit) => match v.toInt? with
    | some i => Except.ok i
    | none => Except.error s!"argument value {v} is not an integer"
  match ty with
  | "i32" => return .i32 (UInt32.ofNat (wrap 32 (← int ())))
  | "i64" => return .i64 (UInt64.ofNat (wrap 64 (← int ())))
  | "f32" => return .f32 (UInt32.ofNat (wrap 32 (← int ())))
  | "f64" => return .f64 (UInt64.ofNat (wrap 64 (← int ())))
  | "externref" => if v == "null" then return .externRef none else return .externRef (some (wrap 32 (← int ())))
  | "funcref" => if v == "null" then return .funcRef none else throw "funcref arguments must be null"
  | other => throw s!"argument type {other} is not supported"

private def signed (bits : Nat) (n : Nat) : Int :=
  if n ≥ 2 ^ (bits - 1) then (n : Int) - (2 ^ bits : Int) else n

/-- A value as people read it: signed integers, decimal floats. -/
def shown : Value → String
  | .i32 v => toString (signed 32 v.toNat)
  | .i64 v => toString (signed 64 v.toNat)
  | .f32 b => toString (Float32.ofBits b)
  | .f64 b => toString (Float.ofBits b)
  | .funcRef a | .externRef a | .exnRef a => match a with | some n => s!"ref {n}" | none => "null"
  | .v128 lo hi => s!"v128 {lo.toNat} {hi.toNat}"
  | .anyRef a => match a with | some n => s!"ref {n.toNat}" | none => "null"

def valueJSON (v : Value) : JSON.Json :=
  let (ty, bits) := match v with
    | .i32 x => ("i32", toString x.toNat) | .i64 x => ("i64", toString x.toNat)
    | .f32 b => ("f32", toString b.toNat) | .f64 b => ("f64", toString b.toNat)
    | .funcRef a => ("funcref", (a.map toString).getD "null")
    | .externRef a => ("externref", (a.map toString).getD "null")
    | .exnRef a => ("exnref", (a.map toString).getD "null")
    | .v128 lo hi => ("v128", s!"{lo.toNat} {hi.toNat}")
    | .anyRef a => ("anyref", (a.map (toString ·.toNat)).getD "null")
  .object [("type", .string ty), ("value", .string bits), ("shown", .string (shown v))]

/-! ## Imports: the spectest set, and nothing else -/

def specFuncs : Array (String × FuncType) :=
  #[("print", ⟨#[], #[]⟩), ("print_i32", ⟨#[.i32], #[]⟩), ("print_i64", ⟨#[.i64], #[]⟩),
    ("print_f32", ⟨#[.f32], #[]⟩), ("print_f64", ⟨#[.f64], #[]⟩),
    ("print_i32_f32", ⟨#[.i32, .f32], #[]⟩), ("print_f64_f64", ⟨#[.f64, .f64], #[]⟩)]

/-- Host function id of the demo import `host.id` (adds two i64), after the spectest ones. -/
def demoHostId : Nat := specFuncs.size

/-- A store with the `spectest` instance (and, for the built-in demos, `host.id`).
Gives the store, the spectest instance and the demo host instance. -/
def baseStore (_ : Unit) : Store × Nat × Nat := Id.run do
  let mut st : Store := { pageLimit }
  let mut exports : Array (String × ExternVal) := #[]
  let mut i := 0
  for (n, ft) in specFuncs do
    let (st', a) := st.addHostFunc ft i
    st := st'; exports := exports.push (n, .func a); i := i + 1
  for (n, t, v) in [("global_i32", ValType.i32, (666 : UInt64)), ("global_i64", .i64, 666),
      ("global_f32", .f32, (Float32.toBits 666.6).toUInt64), ("global_f64", .f64, (666.6 : Float).toBits)] do
    let (st', a) := st.addGlobal ⟨false, t⟩ v
    st := st'; exports := exports.push (n, .global a)
  let (st', ta) := st.addTable ⟨⟨10, some 20⟩, .funcref⟩ nullRef
  st := st'; exports := exports.push ("table", .table ta)
  let (st', ma) := st.addMem ⟨⟨1, some 2⟩⟩
  st := st'; exports := exports.push ("memory", .mem ma)
  let spec := st.insts.size
  st := { st with insts := st.insts.push { exports } }
  let (st', ha) := st.addHostFunc ⟨#[.i64, .i64], #[.i64]⟩ demoHostId
  st := st'
  let demo := st.insts.size
  st := { st with insts := st.insts.push { exports := #[("id", .func ha)] } }
  return (st, spec, demo)

def resolveImports (st : Store) (spec demo : Nat) (allowDemo : Bool) (m : Module) : Except String (Array ExternVal) :=
  m.imports.mapM fun imp => do
    let inst ← if imp.module == "spectest" then pure spec
      else if allowDemo && imp.module == "host" then pure demo
      else throw s!"import {imp.module}.{imp.name} refused: only spectest imports are given"
    match st.export? inst imp.name with
    | some v => pure v
    | none => throw s!"unknown import {imp.module}.{imp.name}"

/-! ## Running -/

/-- How a run ended, the instructions it ran and what the host printed. -/
structure Ran where
  store : Store
  outcome : Outcome
  steps : Nat
  prints : Array String := #[]

/-- A host for one run: host id, arguments, store and what was printed so far; gives the
store, the result and the prints. Pure: it can do only what this module writes here. -/
abbrev Host := Nat → Array Value → Store → Array String → Store × HostResult × Array String

def addPrint (prints : Array String) (line : String) : Array String :=
  if prints.size ≥ maxPrints then prints else prints.push (String.ofList (line.toList.take 1000))

private def printLine (id : Nat) (vs : Array Value) : String :=
  let name := (specFuncs[id]?.map (·.1)).getD s!"host {id}"
  s!"{name}({", ".intercalate (vs.toList.map shown)})"

/-- The spectest host: the print functions log their arguments; `host.id` (built-in
demos only) adds. -/
def specHost : Host := fun id vs st prints =>
  if id == demoHostId then
    match vs with
    | #[.i64 a, .i64 b] => (st, .values #[.i64 (a + b)], prints)
    | _ => (st, .trap "bad arguments", prints)
  else (st, .values #[], addPrint prints (printLine id vs))

/-- WASI Preview 1 (`WasmVM.Wasi`, deny by default). Granted: `fd_write` to fds 1 and 2,
into the page's output, and one program argument. No clock, no randomness, no
environment, no files. -/
def wasiCaps : Wasi.Caps (StateM (Array String)) :=
  { args := #["module.wasm"],
    stdout := some fun b => modify (addPrint · (String.fromUTF8? b |>.getD "(bytes that are not UTF-8)")),
    stderr := some fun b => modify (addPrint · ("stderr: " ++ (String.fromUTF8? b |>.getD "(bytes that are not UTF-8)"))) }

def wasiHost (mem : Nat) (bs : Array Wasi.Binding) : Host := fun id vs st prints =>
  let ((st, r), prints) := (Wasi.host wasiCaps mem bs (fun mo n _ st => pure (st, .trap s!"no host function {mo}.{n}")) id vs st).run prints
  (st, r, prints)

/-- Serve host calls with `host`. Fuel is shared by the whole run. -/
def serve (host : Host) (lim : Budget) : Nat → Ran → Ran
  | 0, r => r
  | n + 1, r =>
    match r.outcome with
    | .hostCall id vs k =>
      let (st, answer, prints) := host id vs r.store r.prints
      let left := lim.fuel - r.steps
      let (st, o, s) := resumeSteps st k answer { lim with fuel := left }
      serve host lim n { store := st, outcome := o, steps := r.steps + s, prints }
    | _ => r

def call (host : Host) (st : Store) (fa : Nat) (args : Array Value) (fuel : Nat) : Ran :=
  let lim : Budget := { fuel, run := runLimits }
  let (st, o, s) := invokeSteps st fa args lim
  let r := serve host lim maxHostCalls { store := st, outcome := o, steps := s }
  match r.outcome with
  | .hostCall .. => { r with outcome := .trap (.host s!"more than {maxHostCalls} host calls") }
  | _ => r

/-- A module decoded, validated and instantiated, with its start function run. -/
structure Loaded where
  store : Store
  inst : Nat
  module : Module
  host : Host
  /-- `spectest` or `wasi`: the import set it was given. -/
  imports : String
  /-- Nanoseconds of each stage: decode, validate, instantiate. -/
  times : List (String × Nat)
  start : Option Ran := none

/-- The stage that failed and why. -/
abbrev Failed := String × String

def checkLimits (m : Module) : Except String Unit := do
  for t in m.tables do
    if t.type.limits.min > maxTableMin then throw s!"a table of {t.type.limits.min} elements is over the limit of {maxTableMin}"
  for t in m.mems do
    if t.limits.min > pageLimit then throw s!"a memory of {t.limits.min} pages is over the limit of {pageLimit}"

/-- A module that imports from `wasi_snapshot_preview1` gets the WASI host and nothing
else; any other module gets the spectest set. -/
def usesWasi (m : Module) : Bool := m.imports.any (·.module == Wasi.moduleName)

def load {M : Type → Type} [Monad M] [Machine M] (bytes : ByteArray) (fuel : Nat) (allowDemo : Bool := false) :
    ExceptT Failed M Loaded := do
  if bytes.size > maxModuleBytes then throw ("decode", s!"module of {bytes.size} bytes is over the limit of {maxModuleBytes}")
  let (d, tD) ← timed fun _ => decode bytes
  let m ← match d with | .ok m => pure m | .error e => throw ("decode", e.toString)
  match checkLimits m with | .ok () => pure () | .error e => throw ("limits", e)
  let (v, tV) ← timed fun _ => validate m
  let vm ← match v with | .ok vm => pure vm | .error e => throw ("validate", e.toString)
  let wasi := usesWasi m
  let (st0, imps, bindings) ← if wasi then
      match Wasi.link ({ pageLimit } : Store) m with
      | .ok r => pure r
      | .error e => throw ("link", e)
    else
      let (st0, spec, demo) := baseStore ()
      match resolveImports st0 spec demo allowDemo m with
      | .ok i => pure (st0, i, #[])
      | .error e => throw ("link", e)
  let ((st, r), tI) ← timed fun _ => instantiate st0 vm imps
  let times := [("decode", tD), ("validate", tV), ("instantiate", tI)]
  let hostOf := fun (i : Nat) =>
    if wasi then wasiHost (((st.insts[i]?).bind (·.mems[0]?)).getD 0) bindings else specHost
  let importSet := if wasi then "wasi" else "spectest"
  match r with
  | .error e => throw ("instantiate", e.toString)
  | .ok (i, none) => return { store := st, inst := i, module := m, host := hostOf i, imports := importSet, times }
  | .ok (i, some s) =>
    let ran := call (hostOf i) st s #[] fuel
    match ran.outcome with
    | .values _ => return { store := ran.store, inst := i, module := m, host := hostOf i, imports := importSet, times, start := some ran }
    | o => throw ("start", o.describe)

/-! ## Answers -/

def funcTypeOf (m : Module) (i : Nat) : Option FuncType :=
  let imported := m.importedFuncTypes
  let t := if h : i < imported.size then some imported[i] else (m.funcs[i - imported.size]?).map (·.type)
  t >>= fun t => m.types[t]?

def funcTypeFields : Option FuncType → List (String × JSON.Json)
  | some ft => [("params", JSON.Json.array (ft.params.toList.map (.string ∘ valTypeName))),
                ("results", .array (ft.results.toList.map (.string ∘ valTypeName)))]
  | none => []

def exportFields (m : Module) : ExternIdx → String × List (String × JSON.Json)
  | .func i => ("func", funcTypeFields (funcTypeOf m i))
  | .table _ => ("table", []) | .mem _ => ("memory", []) | .global _ => ("global", []) | .tag _ => ("tag", [])

def exportsJSON (m : Module) : JSON.Json :=
  .array (m.exports.toList.map fun e =>
    let (kind, extra) := exportFields m e.desc
    .object ([("name", .string e.name), ("kind", .string kind)] ++ extra))

def importsJSON (m : Module) : JSON.Json :=
  .array (m.imports.toList.map fun i => .object [("module", .string i.module), ("name", .string i.name)])

def outcomeFields : Outcome → List (String × JSON.Json)
  | .values vs => [("outcome", .string "values"), ("values", .array (vs.toList.map valueJSON))]
  | .trap t => [("outcome", .string "trap"), ("message", .string t.message)]
  | .exception tag args => [("outcome", .string "exception"), ("message", .string s!"uncaught exception of tag {tag}"),
      ("values", .array (args.toList.map valueJSON))]
  | .outOfFuel _ => [("outcome", .string "outOfFuel"), ("message", .string "out of fuel")]
  | .exit s => [("outcome", .string "exit"), ("message", .string s!"exit {s}")]
  | .hostCall id _ _ => [("outcome", .string "trap"), ("message", .string s!"host call {id} not served")]

def perSecond (steps ns : Nat) : Nat := if ns == 0 then 0 else steps * 1000000000 / ns

/-- One run: the module, an export and its arguments. Gives the JSON fields. -/
def runFields {M : Type → Type} [Monad M] [Machine M] (bytes : ByteArray) (export_ : Option String)
    (args : Array Value) (fuel : Nat) (allowDemo : Bool := false) : M (List (String × JSON.Json)) := do
  let head := [("engine", JSON.Json.string "WasmVM"), ("bytes", num bytes.size)]
  match ← (load bytes fuel allowDemo).run with
  | .error (stage, msg) => return head ++ [("stage", .string stage), ("outcome", .string "error"), ("message", .string msg)]
  | .ok l =>
    let stages := [("stages", JSON.Json.object (l.times.map fun (k, t) => (k, num t))),
      ("exports", exportsJSON l.module), ("imports", importsJSON l.module), ("importSet", .string l.imports)] ++
      (match l.start with
        | some r => [("startInstructions", num r.steps)]
        | none => [])
    match export_ with
    | none => return head ++ stages ++ [("stage", .string "instantiate"), ("outcome", .string "loaded")]
    | some name =>
      match l.store.export? l.inst name with
      | some (.func fa) =>
        let (r, ns) ← timed fun _ => call l.host l.store fa args fuel
        return head ++ stages ++ [("stage", .string "run"), ("export", .string name)] ++ outcomeFields r.outcome ++
          [("instructions", num r.steps), ("ns", num ns), ("perSecond", num (perSecond r.steps ns)),
           ("fuel", num fuel), ("prints", .array (r.prints.toList.map .string))]
      | some _ => return head ++ stages ++ [("stage", .string "run"), ("outcome", .string "error"), ("message", .string s!"export {name} is not a function")]
      | none => return head ++ stages ++ [("stage", .string "run"), ("outcome", .string "error"), ("message", .string s!"no export {name}")]

def fuelOf (request : JSON.Json) : Except String Nat :=
  match request.field? "fuel" with
  | none => .ok defaultFuel
  | some (.number n) => match n.toNat? with
    | some f => if f ≤ maxFuel then .ok f else .error s!"fuel is over the limit of {maxFuel}"
    | none => .error "fuel must be natural"
  | some _ => .error "fuel must be a number"

def argsOf (request : JSON.Json) : Except String (Array Value) :=
  match request.field? "args" with
  | none => .ok #[]
  | some (.array xs) => if xs.length > maxArgs then .error "too many arguments" else (xs.mapM valueOf).map List.toArray
  | some _ => .error "args must be an array"

def moduleOf (request : JSON.Json) : Except String ByteArray :=
  match str request "wasmBase64" with
  | none => .error "wasmBase64 required"
  | some b64 =>
    if b64.length > (maxModuleBytes / 3 + 1) * 4 then .error s!"module is over the limit of {maxModuleBytes} bytes" else
    match Rendering.SfntProfile.decodeBase64 b64 with
    | some b => .ok b
    | none => .error "wasmBase64: invalid base64"

def run {M : Type → Type} [Monad M] [Machine M] (request : JSON.Json) : ExceptT String M String := do
  let bytes ← moduleOf request
  let fuel ← fuelOf request
  let args ← argsOf request
  return (JSON.Json.object (← runFields bytes (str request "export") args fuel)).toString

/-! ## Built-in demos -/

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none

def ofHex (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let mut out := ByteArray.emptyWithCapacity (cs.size / 2)
  for i in [0:cs.size / 2] do
    out := out.push (((hexDigit cs[2*i]!).getD 0 * 16 + (hexDigit cs[2*i+1]!).getD 0).toUInt8)
  return out


/-- `(module (func (export "add") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add))` -/
def addModule : ByteArray := ⟨#[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x07, 0x01, 0x60, 0x02, 0x7f, 0x7f, 0x01, 0x7f, 0x03, 0x02, 0x01, 0x00,
  0x07, 0x07, 0x01, 0x03, 0x61, 0x64, 0x64, 0x00, 0x00,
  0x0a, 0x09, 0x01, 0x07, 0x00, 0x20, 0x00, 0x20, 0x01, 0x6a, 0x0b]⟩

/-- `pages/hello-wasi.wasm` (source `pages/hello-wasi.wat`): `_start` writes a line with
WASI `fd_write` and ends with `proc_exit 0`. -/
def helloWasi (_ : Unit) : ByteArray := ofHex "0061736d0100000001100360047f7f7f7f017f60017f0060000002460216776173695f736e617073686f745f70726576696577310866645f7772697465000016776173695f736e617073686f745f70726576696577310970726f635f657869740001030201020503010001071302066d656d6f72790200065f737461727400020a21011f00410041103602004104411d360200410141004101410810001a410010010b0b23010041100b1d48656c6c6f2066726f6d20574153492c2072756e206279204c65616e0a0018046e616d65011102000866645f7772697465010465786974"

structure Demo where
  title : String
  what : String
  bytes : ByteArray
  export_ : String
  args : Array Value
  fuel : Nat := defaultFuel
  /-- What the run must give, as `Outcome.describe` writes it after the values. -/
  expect : String

/-- The demos. `n` scales the loops (1 on the page); a larger n runs longer. -/
def demos (n : Nat) : List Demo :=
  [{ title := "add", what := "i32.add of two arguments", bytes := addModule, export_ := "add",
     args := #[.i32 40, .i32 2], expect := "42" },
   { title := "fib", what := "recursive Fibonacci: calls and returns", bytes := Bench.Engine.benchModule,
     export_ := "fib", args := #[.i32 (20 + n.toUInt32 * 2)], expect := if n == 1 then "17711" else "" },
   { title := "sum loop", what := "sum of 0 .. n-1 in a loop (i64)", bytes := Bench.Engine.benchModule,
     export_ := "sum", args := #[.i32 (1000000 * n).toUInt32], expect := if n == 1 then "499999500000" else "" },
   { title := "memory loop", what := "a store and a load per iteration", bytes := Bench.Engine.benchModule,
     export_ := "memsum", args := #[.i32 (1000000 * n).toUInt32], expect := if n == 1 then "1783293664" else "" },
   { title := "throw and catch", what := "legacy try: throw 5 from a callee, catch, add 1",
     bytes := Tests.Proposals.legacyModule, export_ := "catch", args := #[.i32 5], expect := "6" },
   { title := "rethrow", what := "try in try: catch, rethrow, catch again", bytes := Tests.Proposals.legacyModule,
     export_ := "rethrow", args := #[.i32 4], expect := "104" },
   { title := "uncaught", what := "an exception that leaves the module", bytes := Tests.Proposals.legacyModule,
     export_ := "delegate-out", args := #[], expect := "exception" },
   { title := "tail calls", what := "return_call 10^6 times in constant stack", bytes := Tests.Proposals.tailModule,
     export_ := "count", args := #[.i64 (1000000 * n).toUInt64, .i64 0], expect := if n == 1 then "1000000" else "" },
   { title := "tail calls via table", what := "return_call_indirect between two functions",
     bytes := Tests.Proposals.tailModule, export_ := "even", args := #[.i64 100000, .i64 0], expect := "150000" },
   { title := "WASI", what := "fd_write to stdout, then proc_exit (deny-by-default WASI host)",
     bytes := helloWasi (), export_ := "_start", args := #[], expect := "exit 0" },
   { title := "out of fuel", what := "the sum loop with fuel for 1000 instructions", bytes := Bench.Engine.benchModule,
     export_ := "sum", args := #[.i32 1000000], fuel := 1000, expect := "out of fuel" }]

/-- The short result text that `Demo.expect` is compared with. -/
def resultText : Outcome → String
  | .values vs => ", ".intercalate (vs.toList.map shown)
  | .exception .. => "exception"
  | o => o.describe

structure DemoRow where
  demo : Demo
  result : String
  ok : Bool
  steps : Nat
  ns : Nat

def runDemo {M : Type → Type} [Monad M] [Machine M] (d : Demo) : M DemoRow := do
  match ← (load d.bytes d.fuel (allowDemo := true)).run with
  | .error (stage, msg) => return { demo := d, result := s!"{stage}: {msg}", ok := false, steps := 0, ns := 0 }
  | .ok l =>
    match l.store.export? l.inst d.export_ with
    | some (.func fa) =>
      let (r, ns) ← timed fun _ => call l.host l.store fa d.args d.fuel
      let t := resultText r.outcome
      let printed := if r.prints.isEmpty then "" else s!"; printed: {" | ".intercalate (r.prints.toList.map fun line => line.trimAscii.toString)}"
      return { demo := d, result := t ++ printed, ok := d.expect.isEmpty || t == d.expect, steps := r.steps, ns }
    | _ => return { demo := d, result := s!"no export {d.export_}", ok := false, steps := 0, ns := 0 }

/-! ## The spec sample -/

def isNaN32 (b : UInt32) : Bool := (b &&& 0x7F800000) == 0x7F800000 && (b &&& 0x007FFFFF) != 0
def isNaN64 (b : UInt64) : Bool :=
  (b &&& 0x7FF0000000000000) == 0x7FF0000000000000 && (b &&& 0x000FFFFFFFFFFFFF) != 0

/-- Does `got` match the expected value? `none`: a type this sample does not compare. -/
def matches1 (e : JSON.Json) (got : Value) : Option Bool := do
  let ty ← str e "type"
  let v := (str e "value").getD ""
  let int := v.toInt?
  match ty, got with
  | "i32", .i32 x => some (some x.toNat == int.map (wrap 32))
  | "i64", .i64 x => some (some x.toNat == int.map (wrap 64))
  | "f32", .f32 b =>
    if v == "nan:canonical" then some ((b &&& 0x7FFFFFFF) == 0x7FC00000)
    else if v == "nan:arithmetic" then some (isNaN32 b && (b &&& 0x00400000) != 0)
    else some (some b.toNat == int.map (wrap 32))
  | "f64", .f64 b =>
    if v == "nan:canonical" then some ((b &&& 0x7FFFFFFFFFFFFFFF) == 0x7FF8000000000000)
    else if v == "nan:arithmetic" then some (isNaN64 b && (b &&& 0x0008000000000000) != 0)
    else some (some b.toNat == int.map (wrap 64))
  | "i32", _ | "i64", _ | "f32", _ | "f64", _ => some false
  | _, _ => none

structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  notRun : Nat := 0
  fails : Array String := #[]
  ns : Nat := 0

def Tally.add (t : Tally) (r : Except String Bool) (where_ : String) : Tally :=
  match r with
  | .ok true => { t with pass := t.pass + 1 }
  | .ok false => { t with notRun := t.notRun + 1 }
  | .error w => { t with fail := t.fail + 1, fails := if t.fails.size < 20 then t.fails.push s!"{where_}: {w}" else t.fails }

def sampleFuel : Nat := 50000000

/-- One command of a file. `.ok true` pass, `.ok false` not run, `.error` fail. -/
def step (mods : JSON.Json) (current : Option Loaded) (cmd : JSON.Json) : Option Loaded × Except String Bool :=
  let bytesOf := fun (_ : Unit) => match str cmd "filename" with
    | some fn => match mods.field? fn with | some (.string h) => some (ofHex h) | _ => none
    | none => none
  let action := (cmd.field? "action").getD .null
  -- An action changes the store (memory, globals, tables): later commands see it.
  let act : Loaded → Except String (Loaded × Outcome) := fun l => do
    let field := (str action "field").getD ""
    match str action "type", l.store.export? l.inst field with
    | some "get", some (.global a) =>
      let t := (l.store.globalTypes[a]!).type
      pure (l, Outcome.values #[Value.ofBits t (l.store.globalBits a)])
    | _, some (.func fa) =>
      let args ← match action.field? "args" with
        | some (.array xs) => xs.mapM valueOf
        | _ => pure []
      let r := call l.host l.store fa args.toArray sampleFuel
      pure ({ l with store := r.store }, r.outcome)
    | _, _ => throw s!"no export {field}"
  match str cmd "type" with
  | some "module" =>
    match bytesOf () with
    | none => (none, .error "module bytes missing")
    | some b => match Id.run (load b sampleFuel).run with
      | .ok l => (some l, .ok true)
      | .error (stage, msg) => (none, .error s!"{stage}: {msg}")
  | some "assert_return" =>
    match current with
    | none => (none, .ok false)
    | some l => match act l with
      | .error e => (current, .error e)
      | .ok (l, .values vs) => (some l,
        let es := match cmd.field? "expected" with | some (.array es) => es | _ => []
        if es.length != vs.size then .error s!"{vs.size} results, expected {es.length}" else
        let ms := (es.zip vs.toList).map fun (e, v) => matches1 e v
        if ms.any (·.isNone) then .ok false
        else if ms.all (· == some true) then .ok true
        else .error s!"{(str action "field").getD ""}: got {", ".intercalate (vs.toList.map shown)}")
      | .ok (l, o) => (some l, .error s!"{(str action "field").getD ""}: {o.describe}")
  | some "assert_trap" | some "assert_exhaustion" =>
    match current with
    | none => (none, .ok false)
    | some l => match act l with
      | .error e => (current, .error e)
      | .ok (l, .trap _) => (some l, .ok true)
      | .ok (l, o) => (some l, .error s!"expected trap {(str cmd "text").getD ""}, got {o.describe}")
  | some "assert_invalid" =>
    (current, match bytesOf () with
      | none => .error "module bytes missing"
      | some b => match decode b with
        | .error (.unsupported ..) => .ok false
        | .error e => .error s!"decode failed, expected invalid: {e.toString}"
        | .ok m => match validate m with
          | .error _ => .ok true
          | .ok _ => .error s!"validated, expected invalid: {(str cmd "text").getD ""}")
  | some "assert_malformed" =>
    (current, match bytesOf () with
      | none => .error "module bytes missing"
      | some b => match decode b with
        | .error (.unsupported ..) => .ok false
        | .error _ => .ok true
        | .ok _ => .error s!"decoded, expected malformed: {(str cmd "text").getD ""}")
  | _ => (current, .ok false)

def runFile (file : JSON.Json) : Tally := Id.run do
  let name := (str file "name").getD "?"
  let mods := (file.field? "modules").getD .null
  let cmds := match file.field? "commands" with | some (.array cs) => cs | _ => []
  let mut t : Tally := {}
  let mut current : Option Loaded := none
  for c in cmds do
    let (next, r) := step mods current c
    current := next
    let line := match c.field? "line" with | some (.number l) => l | _ => "?"
    t := t.add r s!"{name}.wast line {line}"
  return t

/-- The legacy exception cases of `Tests.Proposals` (expected values from V8). -/
def legacyTally (_ : Unit) : Tally := Id.run do
  let mut t : Tally := {}
  match Tests.Proposals.load Tests.Proposals.legacyModule false with
  | .error e => return t.add (.error e) "legacy module"
  | .ok (st, ia) =>
    for (name, args, expected) in Tests.Proposals.legacyCases do
      let got := Tests.Proposals.call st ia name args
      t := t.add (if got == expected then .ok true else .error s!"got {got}, expected {expected}") s!"legacy {name}"
    return t

/-- The sample: one tally for each spec file, and the legacy exception cases. -/
def specSample {M : Type → Type} [Monad M] [Machine M] (_ : Unit) : ExceptT String M (List (String × Tally)) := do
  let files ← match JSON.parseJsonText WebWasmSample.text with
    | .ok (.array fs, _) => pure fs
    | _ => throw "spec sample: invalid JSON"
  let rows ← files.mapM fun f => do
    let (t, ns) ← timed fun _ => runFile f
    return ((str f "name").getD "?", { t with ns })
  let (l, ns) ← timed fun _ => legacyTally ()
  return rows ++ [("exceptions (legacy try, V8 results)", { l with ns })]

def tallyJSON (name : String) (t : Tally) : JSON.Json :=
  .object [("name", .string name), ("pass", num t.pass), ("fail", num t.fail), ("notRun", num t.notRun),
    ("ns", num t.ns), ("fails", .array (t.fails.toList.map .string))]

def specSampleJSON {M : Type → Type} [Monad M] [Machine M] (_ : Unit) : ExceptT String M String := do
  let rows ← specSample ()
  let total := rows.foldl (fun (p, f, n) (_, t) => (p + t.pass, f + t.fail, n + t.notRun)) (0, 0, 0)
  return (JSON.Json.object [("pass", num total.1), ("fail", num total.2.1), ("notRun", num total.2.2),
    ("files", .array (rows.map fun (n, t) => tallyJSON n t))]).toString

/-! ## The page `foafnaut:wasm` -/

def escape (value : String) : String :=
  String.join (value.toList.map fun c =>
    if c == '&' then "&amp;" else if c == '<' then "&lt;" else if c == '>' then "&gt;"
    else if c == '"' then "&quot;" else if c.toNat < 32 || c.toNat > 126 then "?" else c.toString)

def ms (ns : Nat) : String :=
  let tenths := ns / 100000
  s!"{tenths / 10}.{tenths % 10} ms"

def millions (perSec : Nat) : String :=
  let tenths := perSec / 100000
  s!"{tenths / 10}.{tenths % 10} M/s"

def style : String :=
  "body{margin:16px;font-size:14px;line-height:20px;color:#203040;background:#f4f4ee}" ++
  "h1{margin:0 0 4px 0;font-size:22px;line-height:28px;color:#a0186a}" ++
  "h2{margin:16px 0 6px 0;font-size:16px;line-height:22px;color:#a0186a}" ++
  "p{margin:0 0 8px 0}table{border-collapse:collapse}" ++
  "th{text-align:left;padding:3px 10px 3px 0;border-bottom:1px solid #8090a0;font-size:13px}" ++
  "td{padding:3px 10px 3px 0;border-bottom:1px solid #d0d4d8;font-size:13px}" ++
  ".ok{color:#1a7a30}.bad{color:#b02020}.dim{color:#607080}"

def cell (s : String) (cls : String := "") : String :=
  if cls.isEmpty then s!"<td>{escape s}</td>" else s!"<td class=\"{cls}\">{escape s}</td>"

def demoTable (rows : List DemoRow) : String :=
  "<table><tr><th>Demo</th><th>What it runs</th><th>Result</th><th>Instructions</th><th>Time</th><th>Speed</th></tr>" ++
  String.join (rows.map fun r =>
    "<tr>" ++ cell r.demo.title ++ cell r.demo.what ++ cell r.result (if r.ok then "ok" else "bad") ++
    cell (toString r.steps) ++ cell (ms r.ns) ++ cell (if r.steps < 10000 then "" else millions (perSecond r.steps r.ns)) ++ "</tr>") ++
  "</table>"

def sampleTable (rows : List (String × Tally)) : String :=
  let total := rows.foldl (fun (p, f, n) (_, t) => (p + t.pass, f + t.fail, n + t.notRun)) (0, 0, 0)
  s!"<p>Passed <b>{total.1}</b>, failed <b>{total.2.1}</b>, not run {total.2.2} (commands of a kind this sample does not run).</p>" ++
  "<table><tr><th>File</th><th>Pass</th><th>Fail</th><th>Not run</th><th>Time</th></tr>" ++
  String.join (rows.map fun (name, t) =>
    "<tr>" ++ cell name ++ cell (toString t.pass) "ok" ++ cell (toString t.fail) (if t.fail == 0 then "" else "bad") ++
    cell (toString t.notRun) "dim" ++ cell (ms t.ns) ++ "</tr>") ++ "</table>" ++
  String.join (rows.map fun (_, t) => String.join (t.fails.toList.map fun f => s!"<p class=\"bad\">{escape f}</p>"))

/-- The section for a module the page was given: its stages and, with an export, its run. -/
def givenSection {M : Type → Type} [Monad M] [Machine M] (request : JSON.Json) : M String := do
  match moduleOf request with
  | .error _ => return ""
  | .ok bytes =>
    let url := (str request "url").getD "the given module"
    let fuel := (fuelOf request).toOption.getD defaultFuel
    let args := (argsOf request).toOption.getD #[]
    let fields ← runFields bytes (str request "export") args fuel
    let get := fun (k : String) => (fields.find? (·.1 == k)).map (·.2)
    let s := fun (k : String) => match get k with | some (.string v) => v | some (.number v) => v | _ => ""
    let exportsText := match get "exports" with
      | some (.array es) => ", ".intercalate (es.map fun e => match e.field? "name", e.field? "kind" with
        | some (.string n), some (.string k) => s!"{n} ({k})" | _, _ => "?")
      | _ => "none"
    let result := match get "values" with
      | some (.array vs) => ", ".intercalate (vs.map fun v => (str v "shown").getD "?")
      | _ => s "message"
    return s!"<h2>Module {escape url}</h2><p>{s "bytes"} bytes. Stage reached: {escape (s "stage")}. Outcome: <b>{escape (s "outcome")}</b> {escape result}</p>" ++
    s!"<p>Exports: {escape exportsText}</p>" ++
    (if (str request "export").isSome then s!"<p>Instructions: {s "instructions"}. Time: {ms ((s "ns").toNat?.getD 0)}.</p>" else "")

def page {M : Type → Type} [Monad M] [Machine M] (request : JSON.Json) : M String := do
  let n := match request.field? "scale" with
    | some (.number v) => max 1 (min 100 (v.toNat?.getD 1))
    | _ => 1
  let rows ← (demos n).mapM runDemo
  let sample := match ← (specSample ()).run with
    | .ok rows => sampleTable rows
    | .error e => s!"<p class=\"bad\">{escape e}</p>"
  return "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\"><title>WebAssembly in Lean</title><style>" ++ style ++
  "</style></head><body><h1>WebAssembly, run by Lean</h1>" ++
  "<p>Every module on this page runs in WasmVM, the WebAssembly engine written in Lean, inside this Foafnaut engine. " ++
  "The host browser's own WebAssembly does not run them. Imports: WASI Preview 1, deny by default (only writes to stdout and stderr are granted), or the spectest set; every other import is refused.</p>" ++
  (← givenSection request) ++
  "<h2>Demo modules</h2>" ++ demoTable rows ++
  "<h2>Official core tests, a sample</h2>" ++
  "<p>Files of the WebAssembly core test suite (fac, i32, i64, conversions, call, loop), run here, and the legacy exception cases.</p>" ++
  sample ++
  s!"<h2>Limits</h2><p>Module {maxModuleBytes / 1048576} MiB; fuel {defaultFuel} instructions by default, at most {maxFuel}; " ++
  s!"memory {pageLimit} pages ({pageLimit / 16} MiB); call depth {runLimits.maxDepth}; {maxHostCalls} host calls.</p>" ++
  "<p class=\"dim\">Address bar: :wasm opens this page; :wasm NAME.wasm runs a module from the Foafnaut pages folder (same origin only).</p>" ++
  "</body></html>"

def info : String :=
  (JSON.Json.object [("engine", .string "WasmVM"), ("ops", .array ([("wasmInfo" : String), "wasmRun", "wasmSpecSample", "wasmPage"].map .string)),
    ("maxModuleBytes", num maxModuleBytes), ("defaultFuel", num defaultFuel), ("maxFuel", num maxFuel),
    ("pageLimit", num pageLimit), ("imports", .array [.string "wasi_snapshot_preview1", .string "spectest"])]).toString

/-- The ops of this module, or `none` for another op. -/
def op {M : Type → Type} [Monad M] [Machine M] (name : String) (request : JSON.Json) : ExceptT String M (Option String) := do
  if name == "wasmInfo" then return some info
  if name == "wasmRun" then return some (← run request)
  if name == "wasmSpecSample" then return some (← specSampleJSON ())
  if name == "wasmPage" then
    -- A given module that is not valid base64 is an error, not a page without it.
    if (request.field? "wasmBase64").isSome then
      let _ ← moduleOf request
      pure ()
    return some (JSON.Json.object [("source", .string (← page request)), ("title", .string "WebAssembly in Lean")]).toString
  return none

end WebWasm
