/-
L4Factoidal.WasmVM.Aot.Encode: the binary format written back, `Module → ByteArray`
(record: docs/designissues/2026-11-08-wasmvm-aot.md).

The inverse of `Binary.decode` on the modules it gives: every construct that `decode`
reads is written in the form `decode` reads back to the same value. Where the format has
two forms for one value, the encoder picks the one that `decode` maps back exactly:

- an element segment of `ref.func` expressions with the type `(ref func)` is written in
  the function-index form (flags 0 to 3), which `decode` reads as that type; any other
  segment in the expression form (flags 4 to 7);
- a nullable reference type with an abstract heap type is written as its one-byte form;
- a memory argument names its memory only when it is not memory 0;
- a run of locals of one type is one entry.

Custom sections are not written (`decode` skips them). `Tests/Aot.lean` checks
`decode (encode m)` against `m` on every module of the spec tests and on the guests.
-/
import L4Factoidal.WasmVM.Syntax
import L4Factoidal.WasmVM.Simd

namespace L4Factoidal.WasmVM.Aot.Encode

/-- Unsigned LEB128. -/
def uleb (out : ByteArray) (n : Nat) : ByteArray :=
  go out n (n + 1)
where
  go (out : ByteArray) (n : Nat) : Nat → ByteArray
    | 0 => out
    | fuel + 1 =>
      if n < 128 then out.push n.toUInt8
      else go (out.push ((n % 128) + 128).toUInt8) (n / 128) fuel

/-- Signed LEB128 (two's complement, as `Leb.sFast` reads it). -/
def sleb (out : ByteArray) (i : Int) : ByteArray :=
  go out i (i.natAbs + 2)
where
  go (out : ByteArray) (i : Int) : Nat → ByteArray
    | 0 => out
    | fuel + 1 =>
      let low := (i % 128).toNat
      let rest := (i - low) / 128
      -- Done when the rest is the sign extension of bit 6 of this byte.
      if (rest == 0 && low < 64) || (rest == -1 && low ≥ 64) then out.push low.toUInt8
      else go (out.push (low + 128).toUInt8) rest fuel

/-- The i32 constant as `decode` stored it, back to a signed value. -/
def signed32 (v : UInt32) : Int := if v.toNat < 2147483648 then v.toNat else (v.toNat : Int) - 4294967296
def signed64 (v : UInt64) : Int :=
  if v.toNat < 9223372036854775808 then v.toNat else (v.toNat : Int) - 18446744073709551616

def fixedLE (out : ByteArray) (v n : Nat) : ByteArray := Id.run do
  let mut out := out
  let mut v := v
  for _ in [0:n] do
    out := out.push (v % 256).toUInt8
    v := v / 256
  return out

def nameB (out : ByteArray) (s : String) : ByteArray :=
  let b := s.toUTF8
  uleb out b.size ++ b

def vecB (out : ByteArray) (xs : Array α) (f : ByteArray → α → ByteArray) : ByteArray :=
  xs.foldl f (uleb out xs.size)

def absHeapByte : HeapType → Option UInt8
  | .nofunc => some 0x73 | .noextern => some 0x72 | .none => some 0x71
  | .func => some 0x70 | .extern => some 0x6F | .any => some 0x6E | .eq => some 0x6D
  | .i31 => some 0x6C | .struct => some 0x6B | .array => some 0x6A
  | .exn => some 0x69 | .noexn => some 0x74
  | .idx _ => none

def heapType (out : ByteArray) (h : HeapType) : ByteArray :=
  match absHeapByte h, h with
  | some b, _ => out.push b
  | none, .idx i => sleb out i
  | none, _ => out

def refType (out : ByteArray) (r : RefType) : ByteArray :=
  match r.nullable, absHeapByte r.heap with
  | true, some b => out.push b
  | true, none => heapType (out.push 0x63) r.heap
  | false, _ => heapType (out.push 0x64) r.heap

def valType (out : ByteArray) : ValType → ByteArray
  | .i32 => out.push 0x7F | .i64 => out.push 0x7E | .f32 => out.push 0x7D | .f64 => out.push 0x7C
  | .v128 => out.push 0x7B
  | .ref r => refType out r

def blockType (out : ByteArray) : BlockType → ByteArray
  | .empty => out.push 0x40
  | .val t => valType out t
  | .idx i => sleb out i

def limits (out : ByteArray) (l : Limits) : ByteArray :=
  match l.max with
  | none => uleb (out.push 0x00) l.min
  | some m => uleb (uleb (out.push 0x01) l.min) m

def tableType (out : ByteArray) (t : TableType) : ByteArray := limits (refType out t.elem) t.limits

def globalType (out : ByteArray) (g : GlobalType) : ByteArray :=
  (valType out g.type).push (if g.mutable then 1 else 0)

def memArg (out : ByteArray) (m : MemArg) : ByteArray :=
  let out := if m.mem == 0 then uleb out m.align else uleb (uleb out (m.align + 64)) m.mem
  uleb out m.offset

def loadCode : LoadOp → UInt8
  | .i32 => 0x28 | .i64 => 0x29 | .f32 => 0x2A | .f64 => 0x2B
  | .i32_8s => 0x2C | .i32_8u => 0x2D | .i32_16s => 0x2E | .i32_16u => 0x2F
  | .i64_8s => 0x30 | .i64_8u => 0x31 | .i64_16s => 0x32 | .i64_16u => 0x33
  | .i64_32s => 0x34 | .i64_32u => 0x35

def storeCode : StoreOp → UInt8
  | .i32 => 0x36 | .i64 => 0x37 | .f32 => 0x38 | .f64 => 0x39
  | .i32_8 => 0x3A | .i32_16 => 0x3B | .i64_8 => 0x3C | .i64_16 => 0x3D | .i64_32 => 0x3E

/-- A numeric op: `NumOp` is in opcode order, 0x45 to 0xC4, then 0xFC 0 to 7. -/
def numOp (out : ByteArray) (o : NumOp) : ByteArray :=
  let k := o.ctorIdx
  if k < 128 then out.push (0x45 + k).toUInt8 else uleb (out.push 0xFC) (k - 128)

def catchClause (out : ByteArray) : Catch → ByteArray
  | .catch_ x l => uleb (uleb (out.push 0) x) l
  | .catchRef x l => uleb (uleb (out.push 1) x) l
  | .catchAll l => uleb (out.push 2) l
  | .catchAllRef l => uleb (out.push 3) l

def fc (out : ByteArray) (sub : Nat) : ByteArray := uleb (out.push 0xFC) sub

def instr (out : ByteArray) : Instr → ByteArray
  | .unreachable => out.push 0x00
  | .nop => out.push 0x01
  | .block bt => blockType (out.push 0x02) bt
  | .loop bt => blockType (out.push 0x03) bt
  | .if_ bt => blockType (out.push 0x04) bt
  | .else_ => out.push 0x05
  | .end_ => out.push 0x0B
  | .br l => uleb (out.push 0x0C) l
  | .brIf l => uleb (out.push 0x0D) l
  | .brTable ls d => uleb (vecB (out.push 0x0E) ls uleb) d
  | .return_ => out.push 0x0F
  | .call f => uleb (out.push 0x10) f
  | .callIndirect t x => uleb (uleb (out.push 0x11) t) x
  | .drop => out.push 0x1A
  | .select none => out.push 0x1B
  | .select (some ts) => vecB (out.push 0x1C) ts valType
  | .localGet x => uleb (out.push 0x20) x
  | .localSet x => uleb (out.push 0x21) x
  | .localTee x => uleb (out.push 0x22) x
  | .globalGet x => uleb (out.push 0x23) x
  | .globalSet x => uleb (out.push 0x24) x
  | .tableGet x => uleb (out.push 0x25) x
  | .tableSet x => uleb (out.push 0x26) x
  | .tableSize x => uleb (fc out 16) x
  | .tableGrow x => uleb (fc out 15) x
  | .tableFill x => uleb (fc out 17) x
  | .tableCopy d s => uleb (uleb (fc out 14) d) s
  | .tableInit t e => uleb (uleb (fc out 12) e) t
  | .elemDrop x => uleb (fc out 13) x
  | .load op m => memArg (out.push (loadCode op)) m
  | .store op m => memArg (out.push (storeCode op)) m
  | .memorySize m => uleb (out.push 0x3F) m
  | .memoryGrow m => uleb (out.push 0x40) m
  | .memoryInit d m => uleb (uleb (fc out 8) d) m
  | .dataDrop d => uleb (fc out 9) d
  | .memoryCopy d s => uleb (uleb (fc out 10) d) s
  | .memoryFill m => uleb (fc out 11) m
  | .i32Const v => sleb (out.push 0x41) (signed32 v)
  | .i64Const v => sleb (out.push 0x42) (signed64 v)
  | .f32Const b => fixedLE (out.push 0x43) b.toNat 4
  | .f64Const b => fixedLE (out.push 0x44) b.toNat 8
  | .refNull h => heapType (out.push 0xD0) h
  | .refIsNull => out.push 0xD1
  | .refFunc f => uleb (out.push 0xD2) f
  | .num o => numOp out o
  | .throw x => uleb (out.push 0x08) x
  | .throwRef => out.push 0x0A
  | .tryTable bt cs => vecB (blockType (out.push 0x1F) bt) cs catchClause
  | .try_ bt => blockType (out.push 0x06) bt
  | .catch_ x => uleb (out.push 0x07) x
  | .catchAll => out.push 0x19
  | .delegate l => uleb (out.push 0x18) l
  | .rethrow l => uleb (out.push 0x09) l
  | .returnCall f => uleb (out.push 0x12) f
  | .returnCallIndirect t x => uleb (uleb (out.push 0x13) t) x
  | .returnCallRef t => uleb (out.push 0x15) t
  | .callRef t => uleb (out.push 0x14) t
  | .refAsNonNull => out.push 0xD4
  | .brOnNull l => uleb (out.push 0xD5) l
  | .brOnNonNull l => uleb (out.push 0xD6) l
  | .simd k m lane lo hi =>
    let out := uleb (out.push 0xFD) k
    match simdShape k with
    | some (.load _) | some .store => memArg out m
    | some (.loadLane _) | some (.storeLane _) => (memArg out m).push lane.toUInt8
    | some (.extract ..) | some (.replace ..) => out.push lane.toUInt8
    | some .const | some .shuffle => fixedLE (fixedLE out lo.toNat 8) hi.toNat 8
    | _ => out

def expr (out : ByteArray) (e : Expr) : ByteArray := e.foldl instr out

/-- Runs of equal types: the locals entries of a code entry. -/
def localRuns (ls : Array ValType) : Array (Nat × ValType) :=
  ls.foldl (init := #[]) fun acc t =>
    match acc.back? with
    | some (n, u) => if u == t then acc.pop.push (n + 1, t) else acc.push (1, t)
    | none => acc.push (1, t)

def code (out : ByteArray) (f : Func) : ByteArray :=
  let body := expr (vecB ByteArray.empty (localRuns f.locals) fun o (n, t) => valType (uleb o n) t) f.body
  uleb out body.size ++ body

def importDesc (out : ByteArray) : ImportDesc → ByteArray
  | .func t => uleb (out.push 0) t
  | .table t => tableType (out.push 1) t
  | .mem t => limits (out.push 2) t.limits
  | .global g => globalType (out.push 3) g
  | .tag t => uleb ((out.push 4).push 0) t

def import_ (out : ByteArray) (i : Import) : ByteArray := importDesc (nameB (nameB out i.module) i.name) i.desc

def funcType (out : ByteArray) (t : FuncType) : ByteArray :=
  vecB (vecB (out.push 0x60) t.params valType) t.results valType

def table (out : ByteArray) (t : Table) : ByteArray :=
  match t.init with
  | none => tableType out t.type
  | some e => expr (tableType ((out.push 0x40).push 0) t.type) e

def global (out : ByteArray) (g : Global) : ByteArray := expr (globalType out g.type) g.init

def export_ (out : ByteArray) (e : Export) : ByteArray :=
  let out := nameB out e.name
  match e.desc with
  | .func i => uleb (out.push 0) i | .table i => uleb (out.push 1) i | .mem i => uleb (out.push 2) i
  | .global i => uleb (out.push 3) i | .tag i => uleb (out.push 4) i

/-- The function indices of a segment whose every expression is `ref.func f; end`. -/
def funcIndices? (es : Array Expr) : Option (Array Nat) :=
  es.foldl (init := some #[]) fun acc e =>
    match acc, e.toList with
    | some fs, [.refFunc f, .end_] => some (fs.push f)
    | _, _ => none

def elem (out : ByteArray) (e : Elem) : ByteArray :=
  let short : Option (Array Nat) := if e.type == ⟨false, .func⟩ then funcIndices? e.init else none
  let funcs := fun (out : ByteArray) (fs : Array Nat) => vecB out fs uleb
  let exprs := fun (out : ByteArray) => vecB out e.init expr
  match e.mode, short with
  | .active 0 off, some fs => funcs (expr (uleb out 0) off) fs
  | .active x off, some fs => funcs ((expr (uleb (uleb out 2) x) off).push 0) fs
  | .passive, some fs => funcs ((uleb out 1).push 0) fs
  | .declarative, some fs => funcs ((uleb out 3).push 0) fs
  | .active 0 off, none =>
    if e.type == .funcref then exprs (expr (uleb out 4) off)
    else exprs (refType (expr (uleb (uleb out 6) 0) off) e.type)
  | .active x off, none => exprs (refType (expr (uleb (uleb out 6) x) off) e.type)
  | .passive, none => exprs (refType (uleb out 5) e.type)
  | .declarative, none => exprs (refType (uleb out 7) e.type)

def data (out : ByteArray) (d : Data) : ByteArray :=
  let bytes := fun (out : ByteArray) => uleb out d.init.size ++ d.init
  match d.mode with
  | .passive => bytes (uleb out 1)
  | .active 0 off => bytes (expr (uleb out 0) off)
  | .active m off => bytes (expr (uleb (uleb out 2) m) off)

/-- A section: its id, its size, its content. -/
def sect (out : ByteArray) (id : UInt8) (content : ByteArray) : ByteArray :=
  uleb (out.push id) content.size ++ content

def encode (m : Module) : ByteArray := Id.run do
  let mut out : ByteArray := ⟨#[0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00]⟩
  let e := ByteArray.empty
  if !m.types.isEmpty then out := sect out 1 (vecB e m.types funcType)
  if !m.imports.isEmpty then out := sect out 2 (vecB e m.imports import_)
  if !m.funcs.isEmpty then out := sect out 3 (vecB e m.funcs fun o f => uleb o f.type)
  if !m.tables.isEmpty then out := sect out 4 (vecB e m.tables table)
  if !m.mems.isEmpty then out := sect out 5 (vecB e m.mems fun o t => limits o t.limits)
  if !m.tags.isEmpty then out := sect out 13 (vecB e m.tags fun o t => uleb (o.push 0) t)
  if !m.globals.isEmpty then out := sect out 6 (vecB e m.globals global)
  if !m.exports.isEmpty then out := sect out 7 (vecB e m.exports export_)
  if let some s := m.start then out := sect out 8 (uleb e s)
  if !m.elems.isEmpty then out := sect out 9 (vecB e m.elems elem)
  if let some n := m.dataCount then out := sect out 12 (uleb e n)
  if !m.funcs.isEmpty then out := sect out 10 (vecB e m.funcs code)
  if !m.datas.isEmpty then out := sect out 11 (vecB e m.datas data)
  return out

end L4Factoidal.WasmVM.Aot.Encode
