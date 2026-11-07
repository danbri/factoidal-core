/-
L4Factoidal.WasmVM.Exec.Instantiate: linking a validated module into a store
(https://github.com/danbri/factoidal/issues/1244; specification section 4.5.4).

`instantiate` checks the imports against their declared types, allocates the
module's functions, tables, memories, globals and segments, then runs the active
element and data segments in order. A segment out of bounds stops instantiation with
a trap; the writes before it stay in the store, as the specification says. The start
function is returned, not run: the API runs it, so a host call in it goes through
the same suspension as any other.
-/
import L4Factoidal.WasmVM.Valid
import L4Factoidal.WasmVM.Exec.Store

namespace L4Factoidal.WasmVM

inductive InstError where
  | link (msg : String)
  | trap (t : Trap)
  deriving Inhabited, Repr

def InstError.toString : InstError → String
  | .link m => s!"unlinkable: {m}"
  | .trap t => s!"trap: {t.message}"

/-- Value of a constant expression (validated, so the stack has one value). -/
def evalConst (st : Store) (inst : ModuleInst) (e : Expr) : UInt64 :=
  let stack := e.foldl (init := (#[] : Array UInt64)) fun s i =>
    match i with
    | .i32Const v => s.push v.toUInt64
    | .i64Const v => s.push v
    | .f32Const v => s.push v.toUInt64
    | .f64Const v => s.push v
    | .refNull _ => s.push nullRef
    | .refFunc f => s.push (inst.funcs[f]!).toUInt64
    | .globalGet x => s.push (st.globalBits inst.globals[x]!)
    | .num op =>
      let b := s.back!; let s := s.pop; let a := s.back!; let s := s.pop
      s.push (op.evalBin a b)
    | _ => s
  stack.back!

def limitsMatch (actualMin : Nat) (actualMax : Option Nat) (decl : Limits) : Bool :=
  actualMin ≥ decl.min &&
  match decl.max with
  | none => true
  | some dm => match actualMax with
    | some am => am ≤ dm
    | none => false

def checkImport (st : Store) (types : Array FuncType) (d : ImportDesc) (v : ExternVal) :
    Except String Unit :=
  match d, v with
  | .func t, .func a =>
    match st.funcs[a]?, types[t]? with
    | some fi, some ft => if fi.type == ft then .ok () else .error "incompatible import type"
    | _, _ => .error "unknown import"
  | .table tt, .table a =>
    match st.tables[a]? with
    | some ti =>
      if ti.elem == tt.elem && limitsMatch ti.elems.size ti.max tt.limits then .ok ()
      else .error "incompatible import type"
    | none => .error "unknown import"
  | .mem mt, .mem a =>
    match st.mems[a]? with
    | some mi =>
      if limitsMatch (mi.data.size / pageSize) mi.max mt.limits then .ok ()
      else .error "incompatible import type"
    | none => .error "unknown import"
  | .global gt, .global a =>
    match st.globalTypes[a]? with
    | some t => if t == gt then .ok () else .error "incompatible import type"
    | none => .error "unknown import"
  | _, _ => .error "incompatible import type"

/-- Write `vals` into table `ta` at `d`. -/
def initTable (st : Store) (ta d : Nat) (vals : Array UInt64) : Except Trap Store :=
  let t := st.tables[ta]!
  if d + vals.size > t.elems.size then .error .tableOOB
  else .ok { st with tables := st.tables.modify ta fun t => { t with elems := vals.foldl (init := (t.elems, d)) (fun (a, i) v => (a.set! i v, i + 1)) |>.1 } }

def initMem (st : Store) (ma d : Nat) (bytes : ByteArray) : Except Trap Store :=
  let m := st.mems[ma]!
  if d + bytes.size > m.data.size then .error .memOOB
  else .ok { st with mems := st.mems.modify ma fun mi => { mi with data := bytes.copySlice 0 mi.data d bytes.size } }

/-- Instantiate. Returns the store (changed even on a trap) and either the instance
address with the start function's address, or the error. -/
def instantiate (st : Store) (vm : ValidModule) (imports : Array ExternVal) :
    Store × Except InstError (Nat × Option Nat) := Id.run do
  let m := vm.module
  if imports.size != m.imports.size then return (st, .error (.link "wrong number of imports"))
  let mut inst : ModuleInst := { types := m.types }
  for (imp, v) in m.imports.zip imports do
    match checkImport st m.types imp.desc v with
    | .error e => return (st, .error (.link e))
    | .ok () => pure ()
    match v with
    | .func a => inst := { inst with funcs := inst.funcs.push a }
    | .table a => inst := { inst with tables := inst.tables.push a }
    | .mem a => inst := { inst with mems := inst.mems.push a }
    | .global a => inst := { inst with globals := inst.globals.push a }
  let mut st := st
  let mut typeIds := #[]
  for ft in m.types do
    let (st', i) := st.typeId ft
    st := st'
    typeIds := typeIds.push i
  inst := { inst with typeIds }
  let instAddr := st.insts.size
  for (f, cf) in m.funcs.zip vm.code do
    let ft := m.types[f.type]!
    inst := { inst with funcs := inst.funcs.push st.funcs.size }
    st := { st with funcs := st.funcs.push { type := ft, typeId := typeIds[f.type]!, kind := .wasm instAddr cf } }
  for g in m.globals do
    let (st', a) := st.addGlobal g.type (evalConst st inst g.init)
    st := st'
    inst := { inst with globals := inst.globals.push a }
  for t in m.tables do
    let init := match t.init with | some e => evalConst st inst e | none => nullRef
    let (st', a) := st.addTable t.type init
    st := st'
    inst := { inst with tables := inst.tables.push a }
  for mt in m.mems do
    let (st', a) := st.addMem mt
    st := st'
    inst := { inst with mems := inst.mems.push a }
  for el in m.elems do
    let vals := el.init.map (evalConst st inst)
    inst := { inst with elems := inst.elems.push st.elems.size }
    st := { st with elems := st.elems.push vals }
  for d in m.datas do
    inst := { inst with datas := inst.datas.push st.datas.size }
    st := { st with datas := st.datas.push d.init }
  let exports := m.exports.map fun x => (x.name, match x.desc with
    | .func i => ExternVal.func inst.funcs[i]!
    | .table i => .table inst.tables[i]!
    | .mem i => .mem inst.mems[i]!
    | .global i => .global inst.globals[i]!)
  inst := { inst with exports }
  st := { st with insts := st.insts.push inst }
  let mut ei := 0
  for el in m.elems do
    match el.mode with
    | .active x off =>
      let d := (evalConst st inst off).toUInt32.toNat
      match initTable st inst.tables[x]! d (st.elems[inst.elems[ei]!]!) with
      | .error t => return (st, .error (.trap t))
      | .ok st' => st := st'
      st := { st with elems := st.elems.set! inst.elems[ei]! #[] }
    | .declarative => st := { st with elems := st.elems.set! inst.elems[ei]! #[] }
    | .passive => pure ()
    ei := ei + 1
  let mut di := 0
  for d in m.datas do
    match d.mode with
    | .active x off =>
      let o := (evalConst st inst off).toUInt32.toNat
      match initMem st inst.mems[x]! o d.init with
      | .error t => return (st, .error (.trap t))
      | .ok st' => st := st'
      st := { st with datas := st.datas.set! inst.datas[di]! ByteArray.empty }
    | .passive => pure ()
    di := di + 1
  let start := m.start.map fun s => inst.funcs[s]!
  return (st, .ok (instAddr, start))

end L4Factoidal.WasmVM
