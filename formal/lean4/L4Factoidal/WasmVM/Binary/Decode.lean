/-
L4Factoidal.WasmVM.Binary.Decode: the binary format, `ByteArray → Except DecodeError
Module` (https://github.com/danbri/factoidal/issues/1244; specification chapter 5).

Every reader takes the bytes and a position and returns the value and the next
position. Every loop is bounded by the input: a vector of `n` elements is refused
when `n` is more than the bytes left (each element takes at least one byte), and an
instruction sequence is read with the bytes left as its fuel. The loops are tail
calls, so they compile to C loops.

`DecodeError.unsupported` marks a construct of a proposal that this engine does not
run yet (SIMD, GC types, exceptions, memory64, threads, tail calls); the spec-test
runner counts those as not run, not as failures.
-/
import L4Factoidal.WasmVM.Syntax
import L4Factoidal.WasmVM.Binary.Leb

namespace L4Factoidal.WasmVM.Binary

inductive DecodeError where
  | malformed (msg : String) (pos : Nat)
  | unsupported (what : String) (pos : Nat)
  deriving Repr, Inhabited, BEq

def DecodeError.toString : DecodeError → String
  | .malformed m p => s!"malformed: {m} at byte {p}"
  | .unsupported m p => s!"unsupported: {m} at byte {p}"

/-- A reader's result: the value and the next position. -/

@[inline] def bad (msg : String) (p : Nat) : Except DecodeError α := .error (.malformed msg p)
@[inline] def unsup (msg : String) (p : Nat) : Except DecodeError α := .error (.unsupported msg p)

@[inline] def byte (b : ByteArray) (p : Nat) : Except DecodeError (UInt8 × Nat) :=
  if h : p < b.size then .ok (b[p], p + 1) else bad "unexpected end" p

@[inline] def peek (b : ByteArray) (p : Nat) : Except DecodeError UInt8 :=
  if h : p < b.size then .ok b[p] else bad "unexpected end" p

def u32 (b : ByteArray) (p : Nat) : Except DecodeError (Nat × Nat) :=
  match Leb.u32 b p with
  | some r => .ok r
  | none => if p + 5 ≤ b.size || p ≥ b.size then bad "integer representation too long or too large" p
    else bad "unexpected end" p

def u64 (b : ByteArray) (p : Nat) : Except DecodeError (Nat × Nat) :=
  match Leb.u64 b p with
  | some r => .ok r
  | none => bad "integer representation too long or too large" p

def s32 (b : ByteArray) (p : Nat) : Except DecodeError (Int × Nat) :=
  match Leb.s32 b p with
  | some r => .ok r
  | none => bad "integer representation too long or too large" p

def s33 (b : ByteArray) (p : Nat) : Except DecodeError (Int × Nat) :=
  match Leb.s33 b p with
  | some r => .ok r
  | none => bad "integer representation too long or too large" p

def s64 (b : ByteArray) (p : Nat) : Except DecodeError (Int × Nat) :=
  match Leb.s64 b p with
  | some r => .ok r
  | none => bad "integer representation too long or too large" p

/-- `n` little-endian bytes as a natural number. -/
def fixedLE (b : ByteArray) (p n : Nat) : Except DecodeError (Nat × Nat) :=
  if p + n ≤ b.size then
    .ok ((List.range n).foldr (fun i acc => acc * 256 + (b.get! (p + i)).toNat) 0, p + n)
  else bad "unexpected end" p

/-- A vector: a `u32` count, then that many elements. -/
def vec (f : ByteArray → Nat → Except DecodeError (α × Nat)) (b : ByteArray) (p : Nat) : Except DecodeError ((Array α) × Nat) := do
  let (n, p) ← u32 b p
  if n > b.size - p then bad "length out of bounds" p else
  loop n p (Array.mkEmpty n)
where
  loop : Nat → Nat → Array α → Except DecodeError ((Array α) × Nat)
    | 0, p, acc => .ok (acc, p)
    | k + 1, p, acc => do
      let (x, p) ← f b p
      loop k p (acc.push x)

def name (b : ByteArray) (p : Nat) : Except DecodeError (String × Nat) := do
  let (n, p) ← u32 b p
  if p + n > b.size then bad "unexpected end" p else
  match String.fromUTF8? (b.extract p (p + n)) with
  | some s => .ok (s, p + n)
  | none => bad "malformed UTF-8 encoding" p

def absHeap? (t : UInt8) : Option HeapType :=
  match t with
  | 0x73 => some .nofunc | 0x72 => some .noextern | 0x71 => some .none
  | 0x70 => some .func | 0x6F => some .extern | 0x6E => some .any | 0x6D => some .eq
  | 0x6C => some .i31 | 0x6B => some .struct | 0x6A => some .array
  | 0x69 => some .exn | 0x74 => some .noexn
  | _ => none

def heapType (b : ByteArray) (p : Nat) : Except DecodeError (HeapType × Nat) := do
  let t ← peek b p
  match absHeap? t with
  | some h => .ok (h, p + 1)
  | none =>
    let (i, q) ← s33 b p
    if i < 0 then bad "malformed heap type" p else .ok (.idx i.toNat, q)

def refType (b : ByteArray) (p : Nat) : Except DecodeError (RefType × Nat) := do
  let (t, q) ← byte b p
  match t with
  | 0x63 => let (h, q) ← heapType b q; .ok (⟨true, h⟩, q)
  | 0x64 => let (h, q) ← heapType b q; .ok (⟨false, h⟩, q)
  | _ => match absHeap? t with
    | some h => .ok (⟨true, h⟩, q)
    | none => bad "malformed reference type" p

def valType (b : ByteArray) (p : Nat) : Except DecodeError (ValType × Nat) := do
  let t ← peek b p
  match t with
  | 0x7F => .ok (.i32, p + 1) | 0x7E => .ok (.i64, p + 1)
  | 0x7D => .ok (.f32, p + 1) | 0x7C => .ok (.f64, p + 1)
  | 0x7B => .ok (.v128, p + 1)
  | _ =>
    if t == 0x63 || t == 0x64 || (absHeap? t).isSome then
      let (r, q) ← refType b p; .ok (.ref r, q)
    else bad "malformed value type" p

def blockType (b : ByteArray) (p : Nat) : Except DecodeError (BlockType × Nat) := do
  let t ← peek b p
  if t == 0x40 then .ok (.empty, p + 1)
  else if (t ≥ 0x7B && t ≤ 0x7F) || t == 0x63 || t == 0x64 || (absHeap? t).isSome then
    let (v, q) ← valType b p; .ok (.val v, q)
  else
    let (i, q) ← s33 b p
    if i < 0 then bad "malformed block type" p else .ok (.idx i.toNat, q)

def limits (b : ByteArray) (p : Nat) : Except DecodeError (Limits × Nat) := do
  let (f, p1) ← byte b p
  match f with
  | 0x00 => let (n, q) ← u32 b p1; .ok (⟨n, none⟩, q)
  | 0x01 => let (n, q) ← u32 b p1; let (m, q) ← u32 b q; .ok (⟨n, some m⟩, q)
  | 0x02 | 0x03 => unsup "shared memory (threads)" p
  | 0x04 | 0x05 | 0x06 | 0x07 => unsup "64-bit address type (memory64)" p
  | _ => bad "integer too large" p

def tableType (b : ByteArray) (p : Nat) : Except DecodeError (TableType × Nat) := do
  let (r, p) ← refType b p
  let (l, p) ← limits b p
  .ok (⟨l, r⟩, p)

def globalType (b : ByteArray) (p : Nat) : Except DecodeError (GlobalType × Nat) := do
  let (t, p) ← valType b p
  let (m, q) ← byte b p
  match m with
  | 0 => .ok (⟨false, t⟩, q)
  | 1 => .ok (⟨true, t⟩, q)
  | _ => bad "malformed mutability" p

def memArg (b : ByteArray) (p : Nat) : Except DecodeError (MemArg × Nat) := do
  let (a, p) ← u32 b p
  if a ≥ 128 then bad "malformed memop flags" p else
  let (mem, a, p) ← if a ≥ 64 then do
      let (m, p) ← u32 b p; pure (m, a - 64, p)
    else pure (0, a, p)
  let (o, p) ← u32 b p
  .ok (⟨a, mem, o⟩, p)

@[inline] def ofIntU32 (i : Int) : UInt32 := UInt32.ofNat (i % 4294967296).toNat
@[inline] def ofIntU64 (i : Int) : UInt64 := UInt64.ofNat (i % 18446744073709551616).toNat

def loadOps : Array LoadOp :=
  #[.i32, .i64, .f32, .f64, .i32_8s, .i32_8u, .i32_16s, .i32_16u,
    .i64_8s, .i64_8u, .i64_16s, .i64_16u, .i64_32s, .i64_32u]
def storeOps : Array StoreOp :=
  #[.i32, .i64, .f32, .f64, .i32_8, .i32_16, .i64_8, .i64_16, .i64_32]

/-- One instruction. `usesData` is set when the instruction names a data segment
(the data-count section is then required). -/
def instr (b : ByteArray) (p : Nat) : Except DecodeError (Instr × Nat × Bool) := do
  let (op, q) ← byte b p
  let r := fun (i : Instr) (q : Nat) => (Except.ok (i, q, false) : Except DecodeError _)
  match op with
  | 0x00 => r .unreachable q
  | 0x01 => r .nop q
  | 0x02 => let (bt, q) ← blockType b q; r (.block bt) q
  | 0x03 => let (bt, q) ← blockType b q; r (.loop bt) q
  | 0x04 => let (bt, q) ← blockType b q; r (.if_ bt) q
  | 0x05 => r .else_ q
  | 0x0B => r .end_ q
  | 0x0C => let (l, q) ← u32 b q; r (.br l) q
  | 0x0D => let (l, q) ← u32 b q; r (.brIf l) q
  | 0x0E => let (ls, q) ← vec u32 b q; let (d, q) ← u32 b q; r (.brTable ls d) q
  | 0x0F => r .return_ q
  | 0x10 => let (f, q) ← u32 b q; r (.call f) q
  | 0x11 => let (t, q) ← u32 b q; let (x, q) ← u32 b q; r (.callIndirect t x) q
  | 0x1A => r .drop q
  | 0x1B => r (.select none) q
  | 0x1C => let (ts, q) ← vec valType b q; r (.select (some ts)) q
  | 0x20 => let (x, q) ← u32 b q; r (.localGet x) q
  | 0x21 => let (x, q) ← u32 b q; r (.localSet x) q
  | 0x22 => let (x, q) ← u32 b q; r (.localTee x) q
  | 0x23 => let (x, q) ← u32 b q; r (.globalGet x) q
  | 0x24 => let (x, q) ← u32 b q; r (.globalSet x) q
  | 0x25 => let (x, q) ← u32 b q; r (.tableGet x) q
  | 0x26 => let (x, q) ← u32 b q; r (.tableSet x) q
  | 0x3F => let (m, q) ← u32 b q; r (.memorySize m) q
  | 0x40 => let (m, q) ← u32 b q; r (.memoryGrow m) q
  | 0x41 => let (v, q) ← s32 b q; r (.i32Const (ofIntU32 v)) q
  | 0x42 => let (v, q) ← s64 b q; r (.i64Const (ofIntU64 v)) q
  | 0x43 => let (v, q) ← fixedLE b q 4; r (.f32Const (UInt32.ofNat v)) q
  | 0x44 => let (v, q) ← fixedLE b q 8; r (.f64Const (UInt64.ofNat v)) q
  | 0xD0 => let (h, q) ← heapType b q; r (.refNull h) q
  | 0xD1 => r .refIsNull q
  | 0xD2 => let (f, q) ← u32 b q; r (.refFunc f) q
  | 0xFC =>
    let (sub, q) ← u32 b q
    match sub with
    | 8 => let (d, q) ← u32 b q; let (m, q) ← u32 b q; .ok (.memoryInit d m, q, true)
    | 9 => let (d, q) ← u32 b q; .ok (.dataDrop d, q, true)
    | 10 => let (d, q) ← u32 b q; let (s, q) ← u32 b q; r (.memoryCopy d s) q
    | 11 => let (m, q) ← u32 b q; r (.memoryFill m) q
    | 12 => let (e, q) ← u32 b q; let (t, q) ← u32 b q; r (.tableInit t e) q
    | 13 => let (e, q) ← u32 b q; r (.elemDrop e) q
    | 14 => let (d, q) ← u32 b q; let (s, q) ← u32 b q; r (.tableCopy d s) q
    | 15 => let (x, q) ← u32 b q; r (.tableGrow x) q
    | 16 => let (x, q) ← u32 b q; r (.tableSize x) q
    | 17 => let (x, q) ← u32 b q; r (.tableFill x) q
    | k =>
      if k < 8 then r (.num (NumOp.ofNat (128 + k))) q
      else if k ≤ 19 then unsup "0xFC instruction" p
      else bad "illegal opcode" p
  | 0xFD => unsup "SIMD instruction" p
  | 0xFB => unsup "GC instruction" p
  | 0xFE => unsup "atomic instruction" p
  | 0x06 | 0x07 | 0x08 | 0x09 | 0x0A | 0x18 | 0x19 | 0x1F => unsup "exception instruction" p
  | 0x12 | 0x13 => unsup "tail call" p
  | 0x14 | 0x15 | 0xD3 | 0xD4 | 0xD5 | 0xD6 => unsup "typed function reference" p
  | _ =>
    if op ≥ 0x28 && op ≤ 0x35 then
      let (m, q) ← memArg b q; r (.load loadOps[(op - 0x28).toNat]! m) q
    else if op ≥ 0x36 && op ≤ 0x3E then
      let (m, q) ← memArg b q; r (.store storeOps[(op - 0x36).toNat]! m) q
    else if op ≥ 0x45 && op ≤ 0xC4 then r (.num (NumOp.ofNat (op - 0x45).toNat)) q
    else bad "illegal opcode" p

/-- An expression: instructions up to the `end` that closes depth 0. Fuel is the
number of bytes left; each instruction takes at least one. Returns the
instructions (with the final `end_`), the next position and whether a data index
was used. -/
def exprLoop (b : ByteArray) : Nat → Nat → Nat → Array Instr → Bool →
    Except DecodeError (Array Instr × Nat × Bool)
  | 0, p, _, _, _ => bad "unexpected end" p
  | fuel + 1, p, depth, acc, ud => do
    let (i, q, u) ← instr b p
    let acc := acc.push i
    let ud := ud || u
    match i with
    | .end_ =>
      if depth == 0 then .ok (acc, q, ud) else exprLoop b fuel q (depth - 1) acc ud
    | .block _ | .loop _ | .if_ _ => exprLoop b fuel q (depth + 1) acc ud
    | _ => exprLoop b fuel q depth acc ud

def expr (b : ByteArray) (p : Nat) : Except DecodeError (Expr × Nat × Bool) :=
  exprLoop b (b.size - p + 1) p 0 #[] false

def constExpr (b : ByteArray) (p : Nat) : Except DecodeError (Expr × Nat) := do
  let (e, q, _) ← expr b p
  .ok (e, q)

/-! ### Sections -/

structure DState where
  m : Module := {}
  funcTypes : Array Nat := #[]
  codes : Array (Array ValType × Expr) := #[]
  usesData : Bool := false
  sawCode : Bool := false
  sawFunc : Bool := false

def importDesc (b : ByteArray) (p : Nat) : Except DecodeError (ImportDesc × Nat) := do
  let (k, q) ← byte b p
  match k with
  | 0 => let (t, q) ← u32 b q; .ok (.func t, q)
  | 1 => let (t, q) ← tableType b q; .ok (.table t, q)
  | 2 => let (l, q) ← limits b q; .ok (.mem ⟨l⟩, q)
  | 3 => let (g, q) ← globalType b q; .ok (.global g, q)
  | 4 => unsup "tag import (exceptions)" p
  | _ => bad "malformed import kind" p

def import_ (b : ByteArray) (p : Nat) : Except DecodeError (Import × Nat) := do
  let (mod, p) ← name b p
  let (nm, p) ← name b p
  let (d, p) ← importDesc b p
  .ok (⟨mod, nm, d⟩, p)

def funcType (b : ByteArray) (p : Nat) : Except DecodeError (FuncType × Nat) := do
  let (t, q) ← byte b p
  match t with
  | 0x60 =>
    let (ps, q) ← vec valType b q
    let (rs, q) ← vec valType b q
    .ok (⟨ps, rs⟩, q)
  | 0x4E | 0x50 | 0x4F | 0x5F | 0x5E => unsup "GC type definition" p
  | _ => bad "integer representation too long" p

def table (b : ByteArray) (p : Nat) : Except DecodeError (Table × Nat) := do
  let t ← peek b p
  if t == 0x40 then
    let (z, q) ← byte b (p + 1)
    if z != 0 then bad "malformed table" p else
    let (tt, q) ← tableType b q
    let (e, q) ← constExpr b q
    .ok (⟨tt, some e⟩, q)
  else
    let (tt, q) ← tableType b p
    .ok (⟨tt, none⟩, q)

def global (b : ByteArray) (p : Nat) : Except DecodeError (Global × Nat) := do
  let (t, p) ← globalType b p
  let (e, p) ← constExpr b p
  .ok (⟨t, e⟩, p)

def export_ (b : ByteArray) (p : Nat) : Except DecodeError (Export × Nat) := do
  let (nm, p) ← name b p
  let (k, q) ← byte b p
  let (i, q) ← u32 b q
  match k with
  | 0 => .ok (⟨nm, .func i⟩, q)
  | 1 => .ok (⟨nm, .table i⟩, q)
  | 2 => .ok (⟨nm, .mem i⟩, q)
  | 3 => .ok (⟨nm, .global i⟩, q)
  | 4 => unsup "tag export (exceptions)" p
  | _ => bad "malformed export kind" p

def funcRefExpr (f : Nat) : Expr := #[.refFunc f, .end_]

def elem (b : ByteArray) (p : Nat) : Except DecodeError (Elem × Nat) := do
  let (flags, p) ← u32 b p
  let elemKind := fun (p : Nat) => (do
    let (k, q) ← byte b p
    if k == 0 then .ok (RefType.funcref, q) else bad "malformed element kind" p : Except DecodeError (RefType × Nat))
  let funcs := fun (p : Nat) => (do
    let (fs, q) ← vec u32 b p
    .ok (fs.map funcRefExpr, q) : Except DecodeError ((Array Expr) × Nat))
  match flags with
  | 0 =>
    let (off, p) ← constExpr b p
    let (es, p) ← funcs p
    .ok (⟨.funcref, es, .active 0 off⟩, p)
  | 1 =>
    let (t, p) ← elemKind p
    let (es, p) ← funcs p
    .ok (⟨t, es, .passive⟩, p)
  | 2 =>
    let (x, p) ← u32 b p
    let (off, p) ← constExpr b p
    let (t, p) ← elemKind p
    let (es, p) ← funcs p
    .ok (⟨t, es, .active x off⟩, p)
  | 3 =>
    let (t, p) ← elemKind p
    let (es, p) ← funcs p
    .ok (⟨t, es, .declarative⟩, p)
  | 4 =>
    let (off, p) ← constExpr b p
    let (es, p) ← vec constExpr b p
    .ok (⟨.funcref, es, .active 0 off⟩, p)
  | 5 =>
    let (t, p) ← refType b p
    let (es, p) ← vec constExpr b p
    .ok (⟨t, es, .passive⟩, p)
  | 6 =>
    let (x, p) ← u32 b p
    let (off, p) ← constExpr b p
    let (t, p) ← refType b p
    let (es, p) ← vec constExpr b p
    .ok (⟨t, es, .active x off⟩, p)
  | 7 =>
    let (t, p) ← refType b p
    let (es, p) ← vec constExpr b p
    .ok (⟨t, es, .declarative⟩, p)
  | _ => bad "malformed elements segment kind" p

def bytes (b : ByteArray) (p : Nat) : Except DecodeError (ByteArray × Nat) := do
  let (n, p) ← u32 b p
  if p + n > b.size then bad "unexpected end of section or function" p
  else .ok (b.extract p (p + n), p + n)

def data (b : ByteArray) (p : Nat) : Except DecodeError (Data × Nat) := do
  let (flags, p) ← u32 b p
  match flags with
  | 0 =>
    let (off, p) ← constExpr b p
    let (d, p) ← bytes b p
    .ok (⟨d, .active 0 off⟩, p)
  | 1 =>
    let (d, p) ← bytes b p
    .ok (⟨d, .passive⟩, p)
  | 2 =>
    let (x, p) ← u32 b p
    let (off, p) ← constExpr b p
    let (d, p) ← bytes b p
    .ok (⟨d, .active x off⟩, p)
  | _ => bad "malformed data segment kind" p

/-- Most locals of one function that the engine materialises. -/
def maxLocals : Nat := 50000

def localsLoop (b : ByteArray) : Nat → Nat → Nat → Array ValType → Except DecodeError ((Array ValType) × Nat)
  | 0, p, _, acc => .ok (acc, p)
  | k + 1, p, total, acc => do
    let (n, p) ← u32 b p
    let (t, p) ← valType b p
    let total := total + n
    if total ≥ 4294967296 then bad "too many locals" p
    else if total > maxLocals then unsup "more locals than the engine limit" p
    else localsLoop b k p total (acc ++ Array.replicate n t)

def code (b : ByteArray) (p : Nat) : Except DecodeError ((Array ValType × Expr) × Nat × Bool) := do
  let (size, p) ← u32 b p
  let e := p + size
  if e > b.size then bad "unexpected end of section or function" p else
  let (n, p) ← u32 b p
  if n > e - p then bad "unexpected end" p else
  let (ls, p) ← localsLoop b n p 0 #[]
  let (body, q, ud) ← exprLoop b (e - p + 1) p 0 #[] false
  if q != e then bad "section size mismatch" q else
  .ok ((ls, body), q, ud)

def codesLoop (b : ByteArray) : Nat → Nat → Array (Array ValType × Expr) → Bool →
    Except DecodeError (Array (Array ValType × Expr) × Nat × Bool)
  | 0, p, acc, ud => .ok (acc, p, ud)
  | k + 1, p, acc, ud => do
    let (c, p, u) ← code b p
    codesLoop b k p (acc.push c) (ud || u)

/-- The rank of a section id in the required order; custom sections (0) have none. -/
def sectionRank : Nat → Option Nat
  | 1 => some 1 | 2 => some 2 | 3 => some 3 | 4 => some 4 | 5 => some 5 | 13 => some 6
  | 6 => some 7 | 7 => some 8 | 8 => some 9 | 9 => some 10 | 12 => some 11
  | 10 => some 12 | 11 => some 13
  | _ => none

def readSection (b : ByteArray) (id : Nat) (p e : Nat) (s : DState) : Except DecodeError (DState × Nat) := do
  let m := s.m
  match id with
  | 0 => let (_, q) ← name b p; if q > e then bad "unexpected end" p else .ok (s, e)
  | 1 => let (ts, q) ← vec funcType b p; .ok ({ s with m := { m with types := ts } }, q)
  | 2 => let (is, q) ← vec import_ b p; .ok ({ s with m := { m with imports := is } }, q)
  | 3 => let (fs, q) ← vec u32 b p; .ok ({ s with funcTypes := fs, sawFunc := true }, q)
  | 4 => let (ts, q) ← vec table b p; .ok ({ s with m := { m with tables := ts } }, q)
  | 5 => let (ls, q) ← vec limits b p
         .ok ({ s with m := { m with mems := ls.map MemType.mk } }, q)
  | 13 => unsup "tag section (exceptions)" p
  | 6 => let (gs, q) ← vec global b p; .ok ({ s with m := { m with globals := gs } }, q)
  | 7 => let (es, q) ← vec export_ b p; .ok ({ s with m := { m with exports := es } }, q)
  | 8 => let (f, q) ← u32 b p; .ok ({ s with m := { m with start := some f } }, q)
  | 9 => let (es, q) ← vec elem b p; .ok ({ s with m := { m with elems := es } }, q)
  | 12 => let (n, q) ← u32 b p; .ok ({ s with m := { m with dataCount := some n } }, q)
  | 10 =>
    let (n, p) ← u32 b p
    if n > e - p then bad "length out of bounds" p else
    let (cs, q, ud) ← codesLoop b n p #[] false
    .ok ({ s with codes := cs, usesData := s.usesData || ud, sawCode := true }, q)
  | 11 => let (ds, q) ← vec data b p; .ok ({ s with m := { m with datas := ds } }, q)
  | _ => bad "malformed section id" p

def sectionsLoop (b : ByteArray) : Nat → Nat → Nat → DState → Except DecodeError DState
  | 0, p, _, _ => bad "unexpected end" p
  | fuel + 1, p, last, s => do
    if p ≥ b.size then return s
    let (id, p1) ← byte b p
    let (size, p2) ← u32 b p1
    let e := p2 + size
    if e > b.size then bad "section size mismatch: unexpected end" p2 else
    let rank ← match sectionRank id.toNat with
      | some r => if r ≤ last then bad "unexpected content after last section" p else pure r
      | none => if id == 0 then pure last else bad "malformed section id" p
    -- Only the bytes of the section are visible to its reader.
    let (s, q) ← readSection (b.extract 0 e) id.toNat p2 e s
    if q != e then bad "section size mismatch" q else
    sectionsLoop b fuel e rank s

def decode (b : ByteArray) : Except DecodeError Module := do
  if b.size < 4 then bad "unexpected end" 0
  if b.extract 0 4 != ⟨#[0x00, 0x61, 0x73, 0x6D]⟩ then bad "magic header not detected" 0
  if b.size < 8 then bad "unexpected end" 4
  if b.extract 4 8 != ⟨#[0x01, 0x00, 0x00, 0x00]⟩ then bad "unknown binary version" 4
  let s ← sectionsLoop b (b.size + 1) 8 0 {}
  if s.funcTypes.size != s.codes.size then
    bad "function and code section have inconsistent lengths" b.size
  if s.usesData && s.m.dataCount.isNone then bad "data count section required" b.size
  if let some n := s.m.dataCount then
    if n != s.m.datas.size then bad "data count and data section have inconsistent lengths" b.size
  let funcs := (s.funcTypes.zip s.codes).map fun (t, (ls, body)) => ({ type := t, locals := ls, body } : Func)
  return { s.m with funcs }

end L4Factoidal.WasmVM.Binary
