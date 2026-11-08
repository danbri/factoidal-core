/-
`lake exe wasmvm-spectest [--serial] [-v] [DIR] [NAME...]`: runs the official WebAssembly
core test suite against the engine (https://github.com/danbri/factoidal/issues/1244).

Input: the JSON command lists and `.wasm` files that `wasm-tools json-from-wast` made
from the `.wast` files, under `third_party/wasm-spec/test/core-json/` (default DIR:
`../../third_party/wasm-spec/test/core-json`, from `formal/lean4`). NAME limits the
run to files whose directory is NAME.

Each command counts as pass, fail or not run. Not run: a text-format module (the
engine reads the binary format only), a construct of a proposal the engine does not
run yet (the decoder says `unsupported`), v128 values, and assertions on a module that
was not run. Files run in parallel (one task each, each with its own store) unless
`--serial` is given; both times are printed.

Not part of the verified library: it does file I/O and prints scores.
-/
import L4Factoidal.WasmVM.Tests.Memory
import Lean.Data.Json
import L4Factoidal.WasmVM.Api

open Lean (Json)
open L4Factoidal.WasmVM

namespace L4Factoidal.WasmVM.SpecTest

inductive Res where
  | pass | fail (why : String) | notRun (why : String)

structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  notRun : Nat := 0
  fails : Array String := #[]
  notRunWhy : Array String := #[]

def Tally.add (t : Tally) (line : Nat) : Res → Tally
  | .pass => { t with pass := t.pass + 1 }
  | .fail w => { t with fail := t.fail + 1, fails := t.fails.push s!"line {line}: {w}" }
  | .notRun w => { t with notRun := t.notRun + 1, notRunWhy := t.notRunWhy.push w }

/-! ### The spectest host module -/

def specFuncs : Array (String × FuncType) :=
  #[("print", ⟨#[], #[]⟩), ("print_i32", ⟨#[.i32], #[]⟩), ("print_i64", ⟨#[.i64], #[]⟩),
    ("print_f32", ⟨#[.f32], #[]⟩), ("print_f64", ⟨#[.f64], #[]⟩),
    ("print_i32_f32", ⟨#[.i32, .f32], #[]⟩), ("print_f64_f64", ⟨#[.f64, .f64], #[]⟩)]

/-- A store holding the `spectest` instance; returns its instance address. -/
def specStore : Store × Nat := Id.run do
  let mut st : Store := {}
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
  let ia := st.insts.size
  st := { st with insts := st.insts.push { exports } }
  return (st, ia)

def specHost : PureHost ByteMem := fun _ _ st => (st, .values #[])

/-! ### JSON values -/

def str (j : Json) (k : String) : Option String := (j.getObjValAs? String k).toOption
def num (j : Json) (k : String) : Nat := ((j.getObjValAs? Nat k).toOption).getD 0

def parseInt (s : String) : Option Int := s.toInt?

def wrap (bits : Nat) (i : Int) : Nat := (i % (2 ^ bits : Int)).toNat

/-- An argument value, or none when the engine has no such value (v128). -/
def argValue (j : Json) : Option Value := do
  let ty ← str j "type"
  let v := (str j "value").getD "null"
  match ty with
  | "i32" => some (.i32 (UInt32.ofNat (wrap 32 (← parseInt v))))
  | "i64" => some (.i64 (UInt64.ofNat (wrap 64 (← parseInt v))))
  | "f32" => some (.f32 (UInt32.ofNat (wrap 32 (← parseInt v))))
  | "f64" => some (.f64 (UInt64.ofNat (wrap 64 (← parseInt v))))
  | "externref" => if v == "null" then some (.externRef none) else (v.toNat?).map (.externRef ∘ some)
  | "funcref" => if v == "null" then some (.funcRef none) else (v.toNat?).map (.funcRef ∘ some)
  | _ => none

def isNaN32 (b : UInt32) : Bool := (b &&& 0x7F800000) == 0x7F800000 && (b &&& 0x007FFFFF) != 0
def isNaN64 (b : UInt64) : Bool :=
  (b &&& 0x7FF0000000000000) == 0x7FF0000000000000 && (b &&& 0x000FFFFFFFFFFFFF) != 0

/-- Does `got` match the expected JSON value? `none`: the engine cannot tell (v128). -/
def matches1 (e : Json) (got : Value) : Option Bool := do
  let ty ← str e "type"
  -- A reference with no value means any non-null reference of the type.
  let v := (str e "value").getD "nonnull"
  match ty with
  | "i32" => some (got == .i32 (UInt32.ofNat (wrap 32 (← parseInt v))))
  | "i64" => some (got == .i64 (UInt64.ofNat (wrap 64 (← parseInt v))))
  | "f32" =>
    match got with
    | .f32 b =>
      if v == "nan:canonical" then some ((b &&& 0x7FFFFFFF) == 0x7FC00000)
      else if v == "nan:arithmetic" then some (isNaN32 b && (b &&& 0x00400000) != 0)
      else some (b == UInt32.ofNat (wrap 32 (← parseInt v)))
    | _ => some false
  | "f64" =>
    match got with
    | .f64 b =>
      if v == "nan:canonical" then some ((b &&& 0x7FFFFFFFFFFFFFFF) == 0x7FF8000000000000)
      else if v == "nan:arithmetic" then some (isNaN64 b && (b &&& 0x0008000000000000) != 0)
      else some (b == UInt64.ofNat (wrap 64 (← parseInt v)))
    | _ => some false
  | "externref" =>
    match got with
    | .externRef a => some (if v == "null" then a.isNone else if v == "nonnull" then a.isSome else a == v.toNat?)
    | _ => some false
  | "funcref" =>
    match got with
    | .funcRef a => some (if v == "null" then a.isNone else a.isSome)
    | _ => some false
  | "refnull" | "nullfuncref" | "nullexternref" | "nullref" =>
    match got with
    | .funcRef none | .externRef none => some true
    | _ => some false
  | _ => none

/-- `matches1`, and "either" (any of several values). -/
def valueMatches (e : Json) (got : Value) : Option Bool :=
  if str e "type" == some "either" then
    let vs := ((e.getObjValAs? (Array Json) "values").toOption).getD #[]
    some (vs.any fun x => (matches1 x got).getD false)
  else matches1 e got

/-! ### Running a file -/

structure St where
  store : Store
  spectest : Nat
  current : Option Nat := none
  /-- The current module was not run (unsupported); its assertions are not run. -/
  currentSkipped : Option String := none
  named : Std.HashMap String Nat := {}
  registry : Std.HashMap String Nat := {}
  /-- Names registered for a module that was not run. -/
  skippedRegs : Std.HashSet String := {}

def budget : Budget := { fuel := 200000000 }

def readModule (dir : System.FilePath) (cmd : Json) : IO (Except Res Module) := do
  if str cmd "module_type" == some "text" then return .error (.notRun "text-format module")
  let some fn := str cmd "filename" | return .error (.fail "no filename")
  let bytes ← IO.FS.readBinFile (dir / fn)
  -- Differential check of the parallel code-section decoder on every module.
  let same := match decode bytes, Binary.decodeParallel bytes with
    | .ok a, .ok b => a.funcs == b.funcs
    | .error a, .error b => a.toString == b.toString
    | _, _ => false
  if !same then return .error (.fail s!"decodeParallel differs from decode on {fn}")
  match decode bytes with
  | .ok m => return .ok m
  | .error e@(.unsupported ..) => return .error (.notRun e.toString)
  | .error e => return .error (.fail e.toString)

def resolveImports (s : St) (m : Module) : Except String (Array ExternVal) :=
  m.imports.mapM fun imp => do
    let inst ← if imp.module == "spectest" then pure s.spectest else
      match s.registry[imp.module]? with
      | some i => pure i
      | none =>
        if s.skippedRegs.contains imp.module then throw s!"SKIP imports from module not run: {imp.module}"
        throw s!"unknown import module {imp.module}"
    match s.store.export? inst imp.name with
    | some v => pure v
    | none => throw s!"unknown import {imp.module}.{imp.name}"

/-- Load and instantiate; returns the new state and how it went. -/
def loadModule (s : St) (dir : System.FilePath) (cmd : Json) :
    IO (St × Except Res (Except InstError Nat)) := do
  match ← readModule dir cmd with
  | .error r => return (s, .error r)
  | .ok m =>
    match validate m with
    | .error e => return (s, .error (.fail e.toString))
    | .ok vm =>
      match resolveImports s m with
      | .error e =>
        if e.startsWith "SKIP " then return (s, .error (.notRun (e.drop 5).toString))
        return (s, .ok (.error (.link e)))
      | .ok imps =>
        let (store, r) := instantiateRun specHost s.store vm imps budget
        return ({ s with store }, .ok r)

def targetInst (s : St) (act : Json) : Except Res Nat :=
  match str act "module" with
  | some n => match s.named[n]? with
    | some i => .ok i
    | none => .error (.fail s!"unknown module {n}")
  | none => match s.current, s.currentSkipped with
    | some i, _ => .ok i
    | none, some w => .error (.notRun s!"module not run: {w}")
    | none, none => .error (.fail "no current module")

/-- Perform an action: values, or a trap, or a Res when it could not run. -/
def doAction (s : St) (act : Json) : Except Res (St × Except Trap (Array Value)) := do
  let inst ← targetInst s act
  let field := (str act "field").getD ""
  match str act "type" with
  | some "get" =>
    match s.store.export? inst field with
    | some (.global a) =>
      let t := (s.store.globalTypes[a]!).type
      .ok (s, .ok #[Value.ofBits t (s.store.globalBits a)])
    | _ => .error (.fail s!"no global {field}")
  | _ =>
    let args := ((act.getObjValAs? (Array Json) "args").toOption).getD #[]
    let some vs := args.mapM argValue | .error (.notRun "argument type not supported")
    match s.store.export? inst field with
    | some (.func fa) =>
      let (store, o) := invokePure specHost s.store fa vs budget
      let s := { s with store }
      match o with
      | .values r => .ok (s, .ok r)
      | .trap t => .ok (s, .error t)
      | o => .error (.fail s!"run stopped: {o.describe}")
    | _ => .error (.fail s!"no function {field}")

def expectedList (cmd : Json) : Array Json := ((cmd.getObjValAs? (Array Json) "expected").toOption).getD #[]

def step (dir : System.FilePath) (s : St) (cmd : Json) : IO (St × Res) := do
  let ty := (str cmd "type").getD ""
  let act := (cmd.getObjVal? "action").toOption.getD Json.null
  match ty with
  | "module" =>
    let (s, r) ← loadModule s dir cmd
    match r with
    | .ok (.ok i) =>
      let s := { s with current := some i, currentSkipped := none }
      let s := match str cmd "name" with
        | some n => { s with named := s.named.insert n i }
        | none => s
      return (s, .pass)
    | .ok (.error e) => return ({ s with current := none, currentSkipped := none }, .fail e.toString)
    | .error (.notRun w) => return ({ s with current := none, currentSkipped := some w }, .notRun w)
    | .error r => return ({ s with current := none, currentSkipped := none }, r)
  | "register" =>
    let inst := match str cmd "name" with
      | some n => s.named[n]?
      | none => s.current
    match inst, str cmd "as" with
    | some i, some a => return ({ s with registry := s.registry.insert a i }, .pass)
    | none, some a =>
      if s.currentSkipped.isSome || (str cmd "name").isSome then
        return ({ s with skippedRegs := s.skippedRegs.insert a }, .notRun "module not run")
      return (s, .fail "register: no module")
    | _, none => return (s, .fail "register: no name")
  | "action" =>
    match doAction s act with
    | .ok (s, _) => return (s, .pass)
    | .error r => return (s, r)
  | "assert_return" =>
    match doAction s act with
    | .error r => return (s, r)
    | .ok (s, .error t) => return (s, .fail s!"trap: {t.message}")
    | .ok (s, .ok vs) =>
      let es := expectedList cmd
      if es.size != vs.size then return (s, .fail s!"{vs.size} results, expected {es.size}")
      let ms := (es.zip vs).map fun (e, v) => valueMatches e v
      if ms.any (·.isNone) then return (s, .notRun "result type not supported")
      if ms.all (· == some true) then return (s, .pass)
      return (s, .fail s!"got {repr vs}, expected {(Json.arr es).compress}")
  | "assert_trap" | "assert_exhaustion" =>
    match doAction s act with
    | .error r => return (s, r)
    | .ok (s, .error _) => return (s, .pass)
    | .ok (s, .ok vs) => return (s, .fail s!"expected trap {(str cmd "text").getD ""}, got {repr vs}")
  | "assert_invalid" =>
    match ← readModule dir cmd with
    | .error (.notRun w) => return (s, .notRun w)
    | .error (.fail w) => return (s, .fail s!"decode failed, expected invalid: {w}")
    | .error r => return (s, r)
    | .ok m => match validate m with
      | .error _ => return (s, .pass)
      | .ok _ => return (s, .fail s!"validated, expected invalid: {(str cmd "text").getD ""}")
  | "assert_malformed" =>
    match ← readModule dir cmd with
    | .error (.fail _) => return (s, .pass)
    | .error r => return (s, r)
    | .ok _ => return (s, .fail s!"decoded, expected malformed: {(str cmd "text").getD ""}")
  | "assert_unlinkable" | "assert_uninstantiable" =>
    let (s', r) ← loadModule s dir cmd
    match r with
    | .ok (.error _) => return (s', .pass)
    | .ok (.ok _) => return (s', .fail s!"instantiated, expected {ty}")
    | .error r => return (s, r)
  | _ => return (s, .notRun s!"command {ty}")

def runFile (path : System.FilePath) : IO Tally := do
  let txt ← IO.FS.readFile path
  let some dir := path.parent | return { fail := 1, fails := #["no directory"] }
  match Json.parse txt with
  | .error e => return { fail := 1, fails := #[s!"bad JSON: {e}"] }
  | .ok j =>
    let cmds := ((j.getObjValAs? (Array Json) "commands").toOption).getD #[]
    let (store, spectest) := specStore
    let mut s : St := { store, spectest }
    let mut t : Tally := {}
    for c in cmds do
      let (s', r) ← step dir s c
      s := s'
      t := t.add (num c "line") r
    return t

/-- Every `*.json` file under `dir`, sorted. -/
def jsonFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let all ← dir.walkDir
  let fs := all.filter fun p => p.extension == some "json"
  return fs.insertionSort (·.toString < ·.toString)

def main (args : List String) : IO UInt32 := do
  let serial := args.contains "--serial"
  let verbose := args.contains "-v"
  let rest := args.filter fun a => !a.startsWith "-"
  let (dir, names) := match rest with
    | d :: ns => if d.endsWith "core-json" then (System.FilePath.mk d, ns) else ("../../third_party/wasm-spec/test/core-json", d :: ns)
    | [] => ("../../third_party/wasm-spec/test/core-json", [])
  let files ← jsonFiles dir
  let files := if names.isEmpty then files else
    files.filter fun f => names.any fun n => (f.parent.bind (·.fileName)) == some n
  let t0 ← IO.monoMsNow
  let tallies ← if serial then files.mapM runFile else do
    let tasks ← files.mapM fun f => IO.asTask (runFile f)
    tasks.mapM fun task => do
      match ← IO.wait task with
      | .ok t => pure t
      | .error e => pure { fail := 1, fails := #[s!"exception: {e}"] }
  let t1 ← IO.monoMsNow
  let mut tot : Tally := {}
  for (f, t) in files.zip tallies do
    let name := (f.fileStem).getD f.toString
    IO.println s!"{name}: pass {t.pass} fail {t.fail} not-run {t.notRun}"
    if verbose then
      for w in t.fails.extract 0 20 do IO.println s!"  FAIL {w}"
      let whys := t.notRunWhy.foldl (fun (acc : Std.HashMap String Nat) w => acc.insert w (acc.getD w 0 + 1)) {}
      for (w, n) in whys.toList.take 5 do IO.println s!"  not run ×{n}: {w}"
    tot := { tot with pass := tot.pass + t.pass, fail := tot.fail + t.fail, notRun := tot.notRun + t.notRun }
  IO.println s!"TOTAL files {files.size}: pass {tot.pass} fail {tot.fail} not-run {tot.notRun} ({t1 - t0} ms, {if serial then "serial" else "parallel"})"
  let memOk ← if names.isEmpty then Tests.Memory.run else pure true
  return if tot.fail == 0 && memOk then 0 else 1

end L4Factoidal.WasmVM.SpecTest

def main (args : List String) : IO UInt32 := L4Factoidal.WasmVM.SpecTest.main args
