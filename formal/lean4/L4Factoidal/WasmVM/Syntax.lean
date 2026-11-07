/-
L4Factoidal.WasmVM.Syntax: the abstract syntax of WebAssembly modules, as the
executable engine uses it (https://github.com/danbri/factoidal/issues/1244).

Instructions are FLAT, as in the binary format: `block`, `loop`, `if`, `else` and
`end` are single instructions, and a function body is an `Array Instr` that ends with
`end`. The spec layer (`WasmVM.Spec`) uses nested instruction lists; the function
that nests a flat body is the bridge for the refinement proofs
(docs/designissues/2026-11-07-wasmvm-engine.md, "Proof plan"). Flat code keeps the
decoder and the validator as loops, with no recursion on nesting depth.

Scope now: WebAssembly 2.0 plus multi-memory and the reference types of 3.0 without
GC types. Constructors for SIMD, GC, exceptions, memory64 and tail calls come later;
`ValType.v128` and `HeapType.idx` already exist so that the types do not change shape.
-/
namespace L4Factoidal.WasmVM

/-- Heap types. The abstract ones of WebAssembly 3.0, and a type index. -/
inductive HeapType where
  | func | extern | any | eq | i31 | struct | array | none | nofunc | noextern
  | exn | noexn
  | idx (i : Nat)
  deriving BEq, Repr, Inhabited, DecidableEq

structure RefType where
  nullable : Bool
  heap : HeapType
  deriving BEq, Repr, Inhabited, DecidableEq

def RefType.funcref : RefType := ⟨true, .func⟩
def RefType.externref : RefType := ⟨true, .extern⟩

inductive ValType where
  | i32 | i64 | f32 | f64 | v128
  | ref (r : RefType)
  deriving BEq, Repr, Inhabited, DecidableEq

def ValType.isNum : ValType → Bool
  | .i32 | .i64 | .f32 | .f64 => true
  | _ => false

def ValType.isRef : ValType → Bool
  | .ref _ => true
  | _ => false

structure FuncType where
  params : Array ValType
  results : Array ValType
  deriving BEq, Repr, Inhabited, DecidableEq

structure Limits where
  min : Nat
  max : Option Nat
  deriving BEq, Repr, Inhabited

structure TableType where
  limits : Limits
  elem : RefType
  deriving BEq, Repr, Inhabited

structure MemType where
  limits : Limits
  deriving BEq, Repr, Inhabited

structure GlobalType where
  «mutable» : Bool
  type : ValType
  deriving BEq, Repr, Inhabited

inductive BlockType where
  | empty
  | val (t : ValType)
  | idx (i : Nat)
  deriving BEq, Repr, Inhabited

structure MemArg where
  align : Nat
  mem : Nat
  offset : Nat
  deriving BEq, Repr, Inhabited

/-- Loads. A float load is an integer load of the same width on the slot bits. -/
inductive LoadOp where
  | i32 | i64 | f32 | f64
  | i32_8s | i32_8u | i32_16s | i32_16u
  | i64_8s | i64_8u | i64_16s | i64_16u | i64_32s | i64_32u
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Width in bytes, whether the value is sign-extended, and whether the result is 64-bit. -/
def LoadOp.shape : LoadOp → Nat × Bool × Bool
  | .i32 => (4, false, false) | .i64 => (8, false, true)
  | .f32 => (4, false, false) | .f64 => (8, false, true)
  | .i32_8s => (1, true, false) | .i32_8u => (1, false, false)
  | .i32_16s => (2, true, false) | .i32_16u => (2, false, false)
  | .i64_8s => (1, true, true) | .i64_8u => (1, false, true)
  | .i64_16s => (2, true, true) | .i64_16u => (2, false, true)
  | .i64_32s => (4, true, true) | .i64_32u => (4, false, true)

def LoadOp.type : LoadOp → ValType
  | .i32 | .i32_8s | .i32_8u | .i32_16s | .i32_16u => .i32
  | .f32 => .f32 | .f64 => .f64
  | _ => .i64

inductive StoreOp where
  | i32 | i64 | f32 | f64 | i32_8 | i32_16 | i64_8 | i64_16 | i64_32
  deriving BEq, Repr, Inhabited, DecidableEq

def StoreOp.width : StoreOp → Nat
  | .i32 | .f32 | .i64_32 => 4 | .i64 | .f64 => 8
  | .i32_8 | .i64_8 => 1 | .i32_16 | .i64_16 => 2

def StoreOp.type : StoreOp → ValType
  | .i32 | .i32_8 | .i32_16 => .i32 | .f32 => .f32 | .f64 => .f64
  | _ => .i64

/-- Numeric instructions with no immediate: opcodes 0x45 to 0xC4 and 0xFC 0 to 7, in
opcode order. -/
inductive NumOp where
  -- 0x45
  | i32_eqz | i32_eq | i32_ne | i32_lt_s | i32_lt_u | i32_gt_s | i32_gt_u
  | i32_le_s | i32_le_u | i32_ge_s | i32_ge_u
  -- 0x50
  | i64_eqz | i64_eq | i64_ne | i64_lt_s | i64_lt_u | i64_gt_s | i64_gt_u
  | i64_le_s | i64_le_u | i64_ge_s | i64_ge_u
  -- 0x5B
  | f32_eq | f32_ne | f32_lt | f32_gt | f32_le | f32_ge
  | f64_eq | f64_ne | f64_lt | f64_gt | f64_le | f64_ge
  -- 0x67
  | i32_clz | i32_ctz | i32_popcnt | i32_add | i32_sub | i32_mul | i32_div_s | i32_div_u
  | i32_rem_s | i32_rem_u | i32_and | i32_or | i32_xor | i32_shl | i32_shr_s | i32_shr_u
  | i32_rotl | i32_rotr
  -- 0x79
  | i64_clz | i64_ctz | i64_popcnt | i64_add | i64_sub | i64_mul | i64_div_s | i64_div_u
  | i64_rem_s | i64_rem_u | i64_and | i64_or | i64_xor | i64_shl | i64_shr_s | i64_shr_u
  | i64_rotl | i64_rotr
  -- 0x8B
  | f32_abs | f32_neg | f32_ceil | f32_floor | f32_trunc | f32_nearest | f32_sqrt
  | f32_add | f32_sub | f32_mul | f32_div | f32_min | f32_max | f32_copysign
  -- 0x99
  | f64_abs | f64_neg | f64_ceil | f64_floor | f64_trunc | f64_nearest | f64_sqrt
  | f64_add | f64_sub | f64_mul | f64_div | f64_min | f64_max | f64_copysign
  -- 0xA7
  | i32_wrap_i64 | i32_trunc_f32_s | i32_trunc_f32_u | i32_trunc_f64_s | i32_trunc_f64_u
  | i64_extend_i32_s | i64_extend_i32_u | i64_trunc_f32_s | i64_trunc_f32_u
  | i64_trunc_f64_s | i64_trunc_f64_u
  | f32_convert_i32_s | f32_convert_i32_u | f32_convert_i64_s | f32_convert_i64_u
  | f32_demote_f64
  | f64_convert_i32_s | f64_convert_i32_u | f64_convert_i64_s | f64_convert_i64_u
  | f64_promote_f32
  | i32_reinterpret_f32 | i64_reinterpret_f64 | f32_reinterpret_i32 | f64_reinterpret_i64
  -- 0xC0
  | i32_extend8_s | i32_extend16_s | i64_extend8_s | i64_extend16_s | i64_extend32_s
  -- 0xFC 0..7
  | i32_trunc_sat_f32_s | i32_trunc_sat_f32_u | i32_trunc_sat_f64_s | i32_trunc_sat_f64_u
  | i64_trunc_sat_f32_s | i64_trunc_sat_f32_u | i64_trunc_sat_f64_s | i64_trunc_sat_f64_u
  deriving BEq, Repr, Inhabited, DecidableEq

/-- The instructions. Flat: structure is in `block`/`loop`/`if_`/`else_`/`end_`. -/
inductive Instr where
  | unreachable | nop
  | block (bt : BlockType) | loop (bt : BlockType) | if_ (bt : BlockType)
  | else_ | end_
  | br (l : Nat) | brIf (l : Nat) | brTable (ls : Array Nat) (d : Nat) | return_
  | call (f : Nat) | callIndirect (type : Nat) (table : Nat)
  | drop | select (t : Option (Array ValType))
  | localGet (x : Nat) | localSet (x : Nat) | localTee (x : Nat)
  | globalGet (x : Nat) | globalSet (x : Nat)
  | tableGet (x : Nat) | tableSet (x : Nat) | tableSize (x : Nat) | tableGrow (x : Nat)
  | tableFill (x : Nat) | tableCopy (dst src : Nat) | tableInit (table elem : Nat)
  | elemDrop (x : Nat)
  | load (op : LoadOp) (m : MemArg) | store (op : StoreOp) (m : MemArg)
  | memorySize (mem : Nat) | memoryGrow (mem : Nat) | memoryInit (data mem : Nat)
  | dataDrop (x : Nat) | memoryCopy (dst src : Nat) | memoryFill (mem : Nat)
  | i32Const (v : UInt32) | i64Const (v : UInt64)
  | f32Const (bits : UInt32) | f64Const (bits : UInt64)
  | refNull (h : HeapType) | refIsNull | refFunc (f : Nat)
  | num (op : NumOp)
  deriving BEq, Repr, Inhabited

/-- A constant expression or a function body: flat instructions ending in `end_`. -/
abbrev Expr := Array Instr

inductive ImportDesc where
  | func (type : Nat) | table (t : TableType) | mem (t : MemType) | global (t : GlobalType)
  deriving BEq, Repr, Inhabited

structure Import where
  module : String
  name : String
  desc : ImportDesc
  deriving BEq, Repr, Inhabited

inductive ExternIdx where
  | func (i : Nat) | table (i : Nat) | mem (i : Nat) | global (i : Nat)
  deriving BEq, Repr, Inhabited

structure Export where
  name : String
  desc : ExternIdx
  deriving BEq, Repr, Inhabited

structure Global where
  type : GlobalType
  init : Expr
  deriving BEq, Repr, Inhabited

structure Table where
  type : TableType
  /-- The element initialiser (3.0); `none` means null. -/
  init : Option Expr
  deriving BEq, Repr, Inhabited

inductive ElemMode where
  | passive | declarative
  | active (table : Nat) (offset : Expr)
  deriving BEq, Repr, Inhabited

structure Elem where
  type : RefType
  init : Array Expr
  mode : ElemMode
  deriving BEq, Repr, Inhabited

inductive DataMode where
  | passive
  | active (mem : Nat) (offset : Expr)
  deriving BEq, Repr, Inhabited

structure Data where
  init : ByteArray
  mode : DataMode
  deriving Inhabited

structure Func where
  /-- Index into `Module.types`. -/
  type : Nat
  /-- Declared locals, expanded (one entry per local). -/
  locals : Array ValType
  body : Expr
  deriving BEq, Repr, Inhabited

structure Module where
  types : Array FuncType := #[]
  imports : Array Import := #[]
  funcs : Array Func := #[]
  tables : Array Table := #[]
  mems : Array MemType := #[]
  globals : Array Global := #[]
  exports : Array Export := #[]
  start : Option Nat := none
  elems : Array Elem := #[]
  datas : Array Data := #[]
  dataCount : Option Nat := none
  deriving Inhabited

namespace Module
def importedFuncTypes (m : Module) : Array Nat :=
  m.imports.filterMap fun i => match i.desc with | .func t => some t | _ => none
def importedTables (m : Module) : Array TableType :=
  m.imports.filterMap fun i => match i.desc with | .table t => some t | _ => none
def importedMems (m : Module) : Array MemType :=
  m.imports.filterMap fun i => match i.desc with | .mem t => some t | _ => none
def importedGlobals (m : Module) : Array GlobalType :=
  m.imports.filterMap fun i => match i.desc with | .global t => some t | _ => none
end Module

end L4Factoidal.WasmVM
