/-
L4Factoidal.WasmVM.Exec.Store: the run-time store, module instances and values
(https://github.com/danbri/factoidal/issues/1244; specification section 4.2).

Values in the store and on the operand stack are 64-bit slots of bits: i32 and f32
zero-extended, i64 and f64 whole, a reference is a store address with all-ones
(`nullRef`) for null. A global's slot lives in the store-wide slot array `globals`,
read and written as bits.
-/
import L4Factoidal.WasmVM.Syntax
import L4Factoidal.WasmVM.Numerics
import L4Factoidal.WasmVM.Exec.Code
import L4Factoidal.WasmVM.Exec.Memory

namespace L4Factoidal.WasmVM

/-- A value at the API. -/
inductive Value where
  | i32 (v : UInt32) | i64 (v : UInt64)
  | f32 (bits : UInt32) | f64 (bits : UInt64)
  /-- A function reference: a function address, or `none` for null. -/
  | funcRef (a : Option Nat)
  /-- An external reference: a host-chosen number, or `none` for null. -/
  | externRef (a : Option Nat)
  /-- An exception reference: an exception address in the store, or `none` for null. -/
  | exnRef (a : Option Nat)
  deriving BEq, Repr, Inhabited

def Value.toBits : Value → UInt64
  | .i32 v => v.toUInt64 | .i64 v => v | .f32 b => b.toUInt64 | .f64 b => b
  | .funcRef none | .externRef none | .exnRef none => nullRef
  | .funcRef (some a) | .externRef (some a) | .exnRef (some a) => a.toUInt64

def Value.ofBits (t : ValType) (b : UInt64) : Value :=
  match t with
  | .i32 => .i32 b.toUInt32 | .i64 => .i64 b | .f32 => .f32 b.toUInt32 | .f64 => .f64 b
  | .v128 => .i64 b
  | .ref r =>
    let a := if b == nullRef then none else some b.toNat
    match r.heap with
    | .extern | .noextern => .externRef a
    | .exn | .noexn => .exnRef a
    | _ => .funcRef a

def Value.type : Value → ValType
  | .i32 _ => .i32 | .i64 _ => .i64 | .f32 _ => .f32 | .f64 _ => .f64
  | .funcRef _ => .ref .funcref | .externRef _ => .ref .externref
  | .exnRef _ => .ref ⟨true, .exn⟩

inductive ExternVal where
  | func (a : Nat) | table (a : Nat) | mem (a : Nat) | global (a : Nat) | tag (a : Nat)
  deriving BEq, Repr, Inhabited

/-- A module instance: maps from the module's index spaces to store addresses. -/
structure ModuleInst where
  types : Array FuncType := #[]
  /-- Canonical type id (index in `Store.typeTable`) of each module type. -/
  typeIds : Array Nat := #[]
  funcs : Array Nat := #[]
  tables : Array Nat := #[]
  mems : Array Nat := #[]
  globals : Array Nat := #[]
  elems : Array Nat := #[]
  datas : Array Nat := #[]
  tags : Array Nat := #[]
  exports : Array (String × ExternVal) := #[]
  deriving Inhabited

inductive FuncKind where
  | wasm (inst : Nat) (code : CompiledFunc)
  /-- A host function; the id is the embedder's. -/
  | host (id : Nat)
  deriving Inhabited

structure FuncInst where
  type : FuncType
  typeId : Nat
  kind : FuncKind
  deriving Inhabited

structure TableInst where
  elems : Array UInt64
  max : Option Nat
  elem : RefType
  deriving Inhabited

/-- An exception: its tag address and payload bits (spec: exninst). -/
structure ExnInst where
  tag : Nat
  fields : Array UInt64
  deriving Inhabited

/-- The exception part of the store. -/
structure ExcStore where
  /-- Tag instances: the canonical type of each tag (results empty). -/
  tags : Array FuncType := #[]
  /-- Exceptions thrown so far. An exception reference is an index here. They are
  never freed: the store grows with each `throw` (record, "Exception handling"). -/
  exns : Array ExnInst := #[]
  deriving Inhabited

/-- A memory instance; `M` is the backend (`Exec/Memory.lean`). -/
structure MemInst (M : Type) where
  data : M
  max : Option Nat

instance [LinearMemory M] : Inhabited (MemInst M) := ⟨⟨LinearMemory.empty, none⟩⟩

def pageSize : Nat := 65536

/-- The store, over memory backend `M`. `Store` is the store over backend A. -/
structure StoreOf (M : Type) where
  funcs : Array FuncInst := #[]
  tables : Array TableInst := #[]
  mems : Array (MemInst M) := #[]
  globals : Slots := ByteArray.empty
  globalTypes : Array GlobalType := #[]
  elems : Array (Array UInt64) := #[]
  datas : Array ByteArray := #[]
  insts : Array ModuleInst := #[]
  /-- Tags and exceptions. One field, not two: each extra store field is one more
  word that every `{ st with .. }` in the loop copies (measured 2026-11-08). -/
  exc : ExcStore := {}
  /-- Distinct function types; a type's id is its index here. -/
  typeTable : Array FuncType := #[]
  /-- Most pages one memory may have here (an engine limit under the module's own). -/
  pageLimit : Nat := 16384

instance : Inhabited (StoreOf M) := ⟨{}⟩

abbrev Store := StoreOf ByteMem

namespace StoreOf
variable {M : Type} [LinearMemory M]

/-- The canonical id of a function type, adding it when new. -/
def typeId (st : StoreOf M) (ft : FuncType) : StoreOf M × Nat :=
  match st.typeTable.findIdx? (· == ft) with
  | some i => (st, i)
  | none => ({ st with typeTable := st.typeTable.push ft }, st.typeTable.size)

def addHostFunc (st : StoreOf M) (ft : FuncType) (id : Nat) : StoreOf M × Nat :=
  let (st, tid) := st.typeId ft
  ({ st with funcs := st.funcs.push { type := ft, typeId := tid, kind := .host id } }, st.funcs.size)

def addTag (st : StoreOf M) (ft : FuncType) : StoreOf M × Nat :=
  ({ st with exc := { st.exc with tags := st.exc.tags.push ft } }, st.exc.tags.size)

def addGlobal (st : StoreOf M) (t : GlobalType) (v : UInt64) : StoreOf M × Nat :=
  ({ st with globals := st.globals.push v, globalTypes := st.globalTypes.push t },
   st.globalTypes.size)

def addMem (st : StoreOf M) (t : MemType) : StoreOf M × Nat :=
  let maxBytes := (min (t.limits.max.getD 65536) st.pageLimit) * pageSize
  let data := LinearMemory.create (t.limits.min * pageSize) maxBytes
  ({ st with mems := st.mems.push { data, max := t.limits.max } }, st.mems.size)

def addTable (st : StoreOf M) (t : TableType) (init : UInt64) : StoreOf M × Nat :=
  ({ st with tables := st.tables.push { elems := Array.replicate t.limits.min init, max := t.limits.max, elem := t.elem } },
   st.tables.size)

def globalBits (st : StoreOf M) (a : Nat) : UInt64 := Slots.rd st.globals a.toUSize

/-- Bounds-checked read of `n` bytes of memory `a` (for host functions). -/
def readMem (st : StoreOf M) (a off n : Nat) : Except String ByteArray :=
  match st.mems[a]? with
  | none => .error "unknown memory"
  | some m => if off + n ≤ LinearMemory.size m.data then .ok (LinearMemory.readBytes m.data off n)
    else .error "out of bounds memory access"

/-- Whether `n` bytes at `off` are inside memory `a`. -/
def memFits (st : StoreOf M) (a off n : Nat) : Bool :=
  match st.mems[a]? with
  | some mi => off + n ≤ LinearMemory.size mi.data
  | none => false

/-- Bounds-checked write into memory `a`, giving back the store on both paths: the
store and whether the bytes were written. A caller that needs the old store when the
write fails must use this, not `writeMem` with the old store kept: a store held twice
makes the write copy the whole memory. (`l4_init` of `l4factoidal.wasm` spent 97% of
its 18 s copying 16 MiB at each WASI `clock_time_get`, measured 2026-11-08.) The
memory instance is taken apart (`⟨data, max⟩`), as in `Run.storeMem`. -/
def writeMemS (st : StoreOf M) (a off : Nat) (bytes : ByteArray) : StoreOf M × Bool :=
  if st.memFits a off bytes.size then
    ({ st with mems := st.mems.modify a fun ⟨data, max⟩ =>
        ⟨LinearMemory.writeBytes data off bytes 0 bytes.size, max⟩ }, true)
  else (st, false)

/-- Bounds-checked write into memory `a` (for host functions). -/
def writeMem (st : StoreOf M) (a off : Nat) (bytes : ByteArray) : Except String (StoreOf M) :=
  if st.mems.size ≤ a then .error "unknown memory" else
  match st.writeMemS a off bytes with
  | (st, true) => .ok st
  | (_, false) => .error "out of bounds memory access"

theorem writeMemS_false {st st' : StoreOf M} {a off : Nat} {b : ByteArray}
    (h : st.writeMemS a off b = (st', false)) : st' = st := by
  unfold writeMemS at h; split at h <;> simp_all

theorem writeMem_of_writeMemS {st st' : StoreOf M} {a off : Nat} {b : ByteArray}
    (h : st.writeMemS a off b = (st', true)) : st.writeMem a off b = .ok st' := by
  have hf : st.memFits a off b.size = true := by
    unfold writeMemS at h; split at h <;> simp_all
  have ha : ¬ st.mems.size ≤ a := by
    intro hle; unfold memFits at hf; simp [Array.getElem?_eq_none hle] at hf
  unfold writeMem; rw [if_neg ha, h]

/-- Grow memory `a` by `delta` pages (for host functions such as Emscripten's
`emscripten_resize_heap`); `none` when the memory's maximum or the store's page limit
does not allow it. Gives the store and the old size in pages. -/
def growMem (st : StoreOf M) (a delta : Nat) : Option (StoreOf M × Nat) :=
  match st.mems[a]? with
  | none => none
  | some m =>
    let old := LinearMemory.size m.data / pageSize
    if old + delta ≤ min (m.max.getD 65536) st.pageLimit then
      some ({ st with mems := st.mems.modify a fun ⟨data, max⟩ => ⟨LinearMemory.grow data (delta * pageSize), max⟩ }, old)
    else none

def export? (st : StoreOf M) (inst : Nat) (name : String) : Option ExternVal :=
  st.insts[inst]? >>= fun i => (i.exports.find? (·.1 == name)).map (·.2)

end StoreOf
end L4Factoidal.WasmVM
