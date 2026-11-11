/-
L4Factoidal.WasmVM.Exec.Store: the run-time store, module instances and values
(https://github.com/danbri/factoidal/issues/1244; specification section 4.2).

Values in the store and on the operand stack are 64-bit slots of bits: i32 and f32
zero-extended, i64 and f64 whole, a reference is a store address with all-ones
(`nullRef`) for null (the forms of a reference of the `any` hierarchy: `Exec/Code.lean`,
"Reference bits"). A global's slot lives in the store-wide slot array `globals`,
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
  /-- A 128-bit vector: bits 0 to 63 and bits 64 to 127. -/
  | v128 (lo hi : UInt64)
  /-- A reference of the `any` hierarchy (garbage collection): its slot bits, or `none`
  for null. The bits say what it is: an i31 value, a host value or the address of a
  struct or an array (`Exec/Code.lean`, "Reference bits"). -/
  | anyRef (bits : Option UInt64)
  deriving BEq, Repr, Inhabited

def Value.toBits : Value → UInt64
  | .i32 v => v.toUInt64 | .i64 v => v | .f32 b => b.toUInt64 | .f64 b => b
  | .v128 lo _ => lo
  | .funcRef none | .externRef none | .exnRef none | .anyRef none => nullRef
  | .anyRef (some b) => b
  | .funcRef (some a) | .externRef (some a) | .exnRef (some a) => a.toUInt64

def Value.ofBits (t : ValType) (b : UInt64) : Value :=
  match t with
  | .i32 => .i32 b.toUInt32 | .i64 => .i64 b | .f32 => .f32 b.toUInt32 | .f64 => .f64 b
  | .v128 => .v128 b 0
  | .ref r =>
    let a := if b == nullRef then none else some b.toNat
    match r.heap with
    | .extern | .noextern => .externRef a
    | .exn | .noexn => .exnRef a
    | .any | .eq | .i31 | .struct | .array | .none => .anyRef (if b == nullRef then none else some b)
    -- A defined type: a function address or an object address; the store says which.
    | _ => .funcRef a

/-- The value of type `t` whose slot bits are `b`, and whose high half is `hi` when it
is a v128. -/
def Value.ofSlot (t : ValType) (b hi : UInt64) : Value :=
  match t with
  | .v128 => .v128 b hi
  | t => Value.ofBits t b

/-- The high half of a v128 value; 0 for every other value. -/
def Value.hiBits : Value → UInt64
  | .v128 _ hi => hi
  | _ => 0

def Value.type : Value → ValType
  | .i32 _ => .i32 | .i64 _ => .i64 | .f32 _ => .f32 | .f64 _ => .f64
  | .v128 .. => .v128
  | .funcRef _ => .ref .funcref | .externRef _ => .ref .externref
  | .exnRef _ => .ref ⟨true, .exn⟩
  | .anyRef _ => .ref ⟨true, .any⟩

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

/-- What the store knows of a type id that a recursion group made (garbage collection):
the id of its declared supertype and its composite type, with type ids for indices. -/
structure GcType where
  super : Option Nat
  comp : CompType
  deriving Inhabited

/-- A struct or an array: its type id and its fields or elements, one 64-bit slot each
(an i8 or i16 field holds its 8 or 16 bits). -/
structure Obj where
  type : Nat
  data : Slots
  deriving Inhabited

/-- The garbage-collection part of the store (record, "GC"). -/
structure GcStore where
  /-- By type id (an index of `StoreOf.typeTable`). `none`, and every id past the end:
  a final function type alone in its recursion group with no supertype, the only kind
  that `StoreOf.typeId` makes. -/
  types : Array (Option GcType) := #[]
  /-- The other recursion groups: canonical form (`canonSubIn`) and the id of the
  first type. -/
  groups : Array (Array SubType × Nat) := #[]
  /-- Structs and arrays. A reference to one is its index here. They are never freed:
  there is no collector yet, so the store grows with each allocation. -/
  objs : Array Obj := #[]
  /-- The type id of each tag, by tag address; `none` for a tag that the embedder
  added with a function type only (`StoreOf.addTag`). -/
  tagIds : Array (Option Nat) := #[]
  deriving Inhabited

/-- The exception part of the store (and, since each new field of the store costs time
in the loop, the parts that later proposals added: `hi`, `ghi`, `gc`). -/
structure ExcStore where
  /-- Tag instances: the canonical type of each tag (results empty). -/
  tags : Array FuncType := #[]
  /-- Exceptions thrown so far. An exception reference is an index here. They are
  never freed: the store grows with each `throw` (record, "Exception handling"). -/
  exns : Array ExnInst := #[]
  /-- The hi stack: the high 64 bits of the v128 value whose low 64 bits are in the
  operand-stack slot of the same index. It is here, not a register of `run`, so that
  only the cold ops pay for it (record, "SIMD"). A slot past its end reads as 0; a
  write grows it. -/
  hi : Slots := ByteArray.empty
  /-- The high 64 bits of the v128 globals, by global address (as `hi`). -/
  ghi : Slots := ByteArray.empty
  gc : GcStore := {}
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

def addTag (st : StoreOf M) (ft : FuncType) (typeId : Option Nat := none) : StoreOf M × Nat :=
  ({ st with exc := { st.exc with tags := st.exc.tags.push ft,
                                  gc := { st.exc.gc with tagIds := st.exc.gc.tagIds.push typeId } } },
   st.exc.tags.size)

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

/-- Change the hi stack and the high halves of the globals. The store and its `exc`
field are taken apart first, so each has one reference when `f` and `g` run and they
write in place. -/
@[inline] def modHi (st : StoreOf M) (f g : Slots → Slots) : StoreOf M :=
  match st with
  | { funcs, tables, mems, globals, globalTypes, elems, datas, insts, exc, typeTable, pageLimit } =>
    match exc with
    | { tags, exns, hi, ghi, gc } =>
      { funcs, tables, mems, globals, globalTypes, elems, datas, insts,
        exc := { tags, exns, hi := f hi, ghi := g ghi, gc }, typeTable, pageLimit }

/-- Change the garbage-collection part. The store and its `exc` field are taken apart
first (as in `modHi`), so the part has one reference when `f` runs. -/
@[inline] def modGc (st : StoreOf M) (f : GcStore → GcStore) : StoreOf M :=
  match st with
  | { funcs, tables, mems, globals, globalTypes, elems, datas, insts, exc, typeTable, pageLimit } =>
    match exc with
    | { tags, exns, hi, ghi, gc } =>
      { funcs, tables, mems, globals, globalTypes, elems, datas, insts,
        exc := { tags, exns, hi, ghi, gc := f gc }, typeTable, pageLimit }

/-- What a recursion group said of type id `id`; none for a plain function type. -/
def gcType? (st : StoreOf M) (id : Nat) : Option GcType := (st.exc.gc.types[id]?).join

/-- 0 for a function type, 1 for a struct type, 2 for an array type. -/
def idKind (st : StoreOf M) (id : Nat) : Nat :=
  match st.gcType? id with
  | some { comp := .struct _, .. } => 1
  | some { comp := .array _, .. } => 2
  | _ => 0

/-- Declared subtyping of type ids: `a` is `b`, or the supertype chain of `a` reaches
`b`. Equivalent types have one id, so equality of ids is type equivalence. -/
def isSubId (st : StoreOf M) (a b : Nat) : Bool :=
  if a == b then true else go (st.exc.gc.types.size + 1) a
where
  go : Nat → Nat → Bool
    | 0, _ => false
    | fuel + 1, a =>
      if a == b then true else
      match (st.gcType? a).bind (·.super) with
      | some s => go fuel s
      | none => false

/-- Add a struct or an array; gives its address. -/
def allocObj (st : StoreOf M) (type : Nat) (data : Slots) : StoreOf M × Nat :=
  let a := st.exc.gc.objs.size
  (st.modGc fun g => match g with
    | { types, groups, objs, tagIds } => { types, groups, objs := objs.push { type, data }, tagIds }, a)

def obj? (st : StoreOf M) (a : Nat) : Option Obj := st.exc.gc.objs[a]?

/-- Change the slots of object `a`, in place: each structure on the way is taken apart
before the change. -/
@[inline] def modObj (st : StoreOf M) (a : Nat) (f : Slots → Slots) : StoreOf M :=
  st.modGc fun g => match g with
    | { types, groups, objs, tagIds } => { types, groups, objs := objs.modify a fun ⟨t, d⟩ => ⟨t, f d⟩, tagIds }

/-- The high half of v128 global `a`. -/
def globalHi (st : StoreOf M) (a : Nat) : UInt64 := Slots.rd st.exc.ghi a.toUSize

/-- Set the high half of v128 global `a`. -/
def setGlobalHi (st : StoreOf M) (a : Nat) (v : UInt64) : StoreOf M :=
  st.modHi id fun g => Slots.wrGrow g a.toUSize v

/-- The value of global `a`. -/
def globalValue (st : StoreOf M) (a : Nat) : Value :=
  Value.ofSlot ((st.globalTypes[a]?.map (·.type)).getD .i64) (st.globalBits a) (st.globalHi a)

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
