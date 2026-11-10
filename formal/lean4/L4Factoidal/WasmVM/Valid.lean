/-
L4Factoidal.WasmVM.Valid: validation, and compilation to flat code in the same pass
(https://github.com/danbri/factoidal/issues/1244; specification chapter 3 and the
algorithm of its appendix "Validation Algorithm").

The operand stack holds `Option ValType` (`none` is the unknown type of
unreachable code). Each control frame records its label: the label id that branches
name, the operand height at entry and whether the rest of the frame is unreachable.
The pass emits `Op`s with label ids in the pc fields; when the body ends, `resolve`
replaces each id by the pc where the label was placed.

`validate` returns a `ValidModule`, whose constructor is private: holding one is the
certificate that the module passed. The soundness theorem against the spec typing
relation is item 4 of the proof plan in docs/designissues/2026-11-07-wasmvm-engine.md.
-/
import Std.Data.HashSet
import L4Factoidal.WasmVM.Syntax
import L4Factoidal.WasmVM.Numerics
import L4Factoidal.WasmVM.Exec.Code
import L4Factoidal.WasmVM.Simd

namespace L4Factoidal.WasmVM

structure ValidationError where
  msg : String
  /-- Function index (in the function index space) or none for module level. -/
  func : Option Nat := none
  /-- Instruction index in the body. -/
  at_ : Nat := 0
  deriving Repr, Inhabited

def ValidationError.toString (e : ValidationError) : String :=
  match e.func with
  | some f => s!"invalid: {e.msg} (function {f}, instruction {e.at_})"
  | none => s!"invalid: {e.msg}"

/-- The context of a module (spec: C). -/
structure Ctx where
  types : Array FuncType
  /-- Type index of each function, imports first. -/
  funcs : Array Nat
  tables : Array TableType
  mems : Array MemType
  globals : Array GlobalType
  elems : Array RefType
  dataCount : Option Nat
  /-- Functions that `ref.func` may name. -/
  refs : Std.HashSet Nat
  /-- For each type index, the least index of an equivalent type. -/
  reps : Array Nat := #[]
  /-- Type index of each tag, imports first. -/
  tags : Array Nat := #[]
  /-- The full definition of each type (`Module.defs`). -/
  defs : Array TypeDef := #[]
  deriving Inhabited

namespace Ctx

def comp? (c : Ctx) (i : Nat) : Option CompType := c.defs[i]?.map (·.sub.comp)

/-- The function type of type index `i`; none when `i` is a struct or an array type
(the entry of `types` is then a placeholder). -/
def funcT? (c : Ctx) (i : Nat) : Option FuncType :=
  match c.comp? i with
  | some (.struct _) | some (.array _) => none
  | _ => c.types[i]?

def structT? (c : Ctx) (i : Nat) : Option (Array FieldType) :=
  match c.comp? i with
  | some (.struct fs) => some fs
  | _ => none

def arrayT? (c : Ctx) (i : Nat) : Option FieldType :=
  match c.comp? i with
  | some (.array f) => some f
  | _ => none

def isStructIdx (c : Ctx) (i : Nat) : Bool := (c.structT? i).isSome
def isArrayIdx (c : Ctx) (i : Nat) : Bool := (c.arrayT? i).isSome
def isFuncIdx (c : Ctx) (i : Nat) : Bool := !(c.isStructIdx i || c.isArrayIdx i)

/-- A type with no declared subtype: a call through it compares type ids for equality. -/
def isFinal (c : Ctx) (i : Nat) : Bool := (c.defs[i]?.map (·.sub.final)).getD true

/-- Declared subtyping of defined types: `i` is equivalent to `j`, or the supertype
chain of `i` reaches a type equivalent to `j`. A declared supertype has a smaller
index, so `i + 1` steps are enough. -/
def subIdx (c : Ctx) (j : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, i =>
    if c.reps[i]? == c.reps[j]? && (c.reps[i]?).isSome then true else
    match (c.defs[i]?).bind (·.sub.supers[0]?) with
    | some s => if s < i then subIdx c j fuel s else false
    | none => false

def heapSub (c : Ctx) : HeapType → HeapType → Bool
  | a, b =>
    if a == b then true else
    match a, b with
    | .idx i, .idx j => c.subIdx j (i + 1) i
    | .idx i, .func => c.isFuncIdx i
    | .idx i, .struct => c.isStructIdx i
    | .idx i, .array => c.isArrayIdx i
    | .idx i, .eq | .idx i, .any => !c.isFuncIdx i
    | .nofunc, .func => true
    | .nofunc, .idx j => c.isFuncIdx j
    | .none, .idx j => !c.isFuncIdx j
    | .noextern, .extern => true
    | .noexn, .exn => true
    | .none, .any | .none, .eq | .none, .i31 | .none, .struct | .none, .array => true
    | .eq, .any | .i31, .any | .struct, .any | .array, .any => true
    | .i31, .eq | .struct, .eq | .array, .eq => true
    | _, _ => false

/-- The top type of the hierarchy of a heap type. -/
def top (c : Ctx) : HeapType → HeapType
  | .func | .nofunc => .func
  | .extern | .noextern => .extern
  | .exn | .noexn => .exn
  | .idx i => if c.isFuncIdx i then .func else .any
  | _ => .any

def refSub (c : Ctx) (a b : RefType) : Bool :=
  (b.nullable || !a.nullable) && c.heapSub a.heap b.heap

def valSub (c : Ctx) : ValType → ValType → Bool
  | .ref a, .ref b => c.refSub a b
  | a, b => a == b

def heapOk (c : Ctx) : HeapType → Bool
  | .idx i => i < c.types.size
  | _ => true

def valOk (c : Ctx) : ValType → Bool
  | .ref r => c.heapOk r.heap
  | _ => true

def resultSub (c : Ctx) (ts us : Array ValType) : Bool :=
  ts.size == us.size && (ts.zip us).all fun (a, b) => c.valSub a b

/-- The payload types of tag `x`. -/
def tagParams (c : Ctx) (x : Nat) : Option (Array ValType) :=
  c.tags[x]? >>= fun ti => c.funcT? ti |>.map (·.params)

def blockSig (c : Ctx) : BlockType → Option (Array ValType × Array ValType)
  | .empty => some (#[], #[])
  | .val t => if c.valOk t then some (#[], #[t]) else none
  | .idx i => (c.funcT? i).map fun ft => (ft.params, ft.results)

def storageSub (c : Ctx) : StorageType → StorageType → Bool
  | .val a, .val b => c.valSub a b
  | a, b => a == b

/-- Field subtyping: a mutable field needs equivalent types, a constant one a subtype. -/
def fieldSub (c : Ctx) (a b : FieldType) : Bool :=
  a.mutable == b.mutable && c.storageSub a.type b.type && (!a.mutable || c.storageSub b.type a.type)

/-- Whether composite type `a` may be declared a subtype of `b`. -/
def compSub (c : Ctx) : CompType → CompType → Bool
  | .func f, .func g => c.resultSub g.params f.params && c.resultSub f.results g.results
  | .struct fs, .struct gs => gs.size ≤ fs.size && (gs.zipIdx.all fun (g, i) => c.fieldSub fs[i]! g)
  | .array a, .array b => c.fieldSub a b
  | _, _ => false

end Ctx

/-- `try_` is a legacy `try` before its first clause, `catch_` a legacy `catch` or
`catch_all` clause. A `try_table` is a `block` with a handler entry. -/
inductive CtrlKind where
  | block | loop | if_ | else_ | func | try_ | catch_
  deriving BEq, Inhabited

structure Ctrl where
  kind : CtrlKind
  params : Array ValType
  results : Array ValType
  height : Nat
  unreachable : Bool := false
  label : Nat
  elseLabel : Nat := 0
  /-- Which locals were set at entry (only tracked when a local has no default). -/
  inits : Array Bool := #[]
  /-- Operand height that branches to this label cut back to. It is `height` except
  in a legacy catch clause, where the exception slot sits between the two. -/
  base : Nat := 0
  /-- The handler entry that applies to code directly in this frame. -/
  handler : Option Nat := none
  /-- The handler entry whose range ends where this frame's body ends (`try_table`,
  legacy `try` before its first clause). -/
  closeEntry : Option Nat := none
  /-- Legacy catch clause: the `try`'s entry, and whether this clause is `catch_all`. -/
  tryEntry : Option Nat := none
  sawCatchAll : Bool := false
  deriving Inhabited

def Ctrl.labelTypes (f : Ctrl) : Array ValType :=
  if f.kind == .loop then f.params else f.results

/-- The state of the pass over one body. -/
structure VState where
  vals : Array (Option ValType) := #[]
  ctrls : Array Ctrl := #[]
  ops : Array Op := #[]
  labels : Array Nat := #[]
  maxH : Nat := 0
  /-- Which locals are set; empty when every local has a default value. -/
  inits : Array Bool := #[]
  /-- The handler table, with label ids for the catch pcs. -/
  handlers : Array Handler := #[]
  deriving Inhabited

abbrev V := Except String

namespace VState

@[inline] def push (s : VState) (nLocals : Nat) (t : Option ValType) : VState :=
  let vals := s.vals.push t
  { s with vals, maxH := max s.maxH (nLocals + vals.size) }

def pushAll (s : VState) (nLocals : Nat) (ts : Array ValType) : VState :=
  ts.foldl (fun s t => s.push nLocals (some t)) s

def top (s : VState) : Ctrl := s.ctrls.back!

/-- Pop one operand of any type. -/
def popAny (s : VState) : V (VState × Option ValType) :=
  let f := s.top
  if s.vals.size == f.height then
    if f.unreachable then .ok (s, none) else .error "type mismatch: operand stack is empty"
  else .ok ({ s with vals := s.vals.pop }, s.vals.back!)

def pop (c : Ctx) (s : VState) (t : ValType) : V VState := do
  let (s, a) ← s.popAny
  match a with
  | none => .ok s
  | some a => if c.valSub a t then .ok s else .error s!"type mismatch: expected {repr t}, got {repr a}"

def popAll (c : Ctx) (s : VState) (ts : Array ValType) : V VState :=
  ts.foldr (fun t acc => acc >>= fun s => s.pop c t) (.ok s)

def popRef (s : VState) : V (VState × Option ValType) := do
  let (s, a) ← s.popAny
  match a with
  | none | some (.ref _) => .ok (s, a)
  | some t => .error s!"type mismatch: expected a reference, got {repr t}"

def newLabel (s : VState) : VState × Nat := ({ s with labels := s.labels.push 0 }, s.labels.size)

def place (s : VState) (l : Nat) : VState := { s with labels := s.labels.set! l s.ops.size }

def emit (s : VState) (o : Op) : VState := { s with ops := s.ops.push o }

def pushCtrl (s : VState) (nLocals : Nat) (k : CtrlKind) (ps rs : Array ValType)
    (label elseLabel : Nat) : VState :=
  let fr : Ctrl := { kind := k, params := ps, results := rs, height := s.vals.size,
                     label := label, elseLabel := elseLabel, inits := s.inits,
                     base := s.vals.size, handler := if s.ctrls.isEmpty then none else s.top.handler }
  let s := { s with ctrls := s.ctrls.push fr }
  s.pushAll nLocals ps

/-- Check that the frame's results are exactly on the stack, then remove the frame. -/
def popCtrl (c : Ctx) (s : VState) : V (VState × Ctrl) := do
  if s.ctrls.isEmpty then .error "unexpected end"
  let f := s.top
  let s ← s.popAll c f.results
  if s.vals.size != f.height then .error "type mismatch: values left on the stack at end of block"
  .ok ({ s with ctrls := s.ctrls.pop, inits := f.inits }, f)

def setUnreachable (s : VState) : VState :=
  let f := s.top
  { s with vals := s.vals.extract 0 f.height,
           ctrls := s.ctrls.set! (s.ctrls.size - 1) { f with unreachable := true } }

/-- Change the frame on top. -/
def modTop (s : VState) (g : Ctrl → Ctrl) : VState :=
  { s with ctrls := s.ctrls.modify (s.ctrls.size - 1) g }

/-- Close handler entry `i`: its range ends at the next pc. -/
def setStop (s : VState) (i : Nat) : VState :=
  { s with handlers := s.handlers.modify i fun h => { h with stop := s.ops.size } }

/-- Start a handler entry at the next pc; returns its index. -/
def newEntry (s : VState) (cs : Array CatchTarget) (next : Option Nat) : VState × Nat :=
  ({ s with handlers := s.handlers.push { start := s.ops.size, stop := s.ops.size, catches := cs, next } },
   s.handlers.size)

/-- The control frame for label `l`. -/
def label? (s : VState) (l : Nat) : Option Ctrl :=
  if l < s.ctrls.size then s.ctrls[s.ctrls.size - 1 - l]? else none

end VState

/-- What one function needs besides the module context. -/
structure FnCtx where
  locals : Array ValType
  results : Array ValType

def target (nLocals : Nat) (f : Ctrl) : BrTarget :=
  { pc := f.label, keep := f.labelTypes.size, height := nLocals + f.base }

/-- Whether a v128 is among `ts`. -/
def hasV128 (ts : Array ValType) : Bool := ts.any (· == .v128)

/-- Emit `br t`, which moves values of types `ts`. When a v128 is among them, a
`hiMove` goes first: it moves their high halves (record, "SIMD"). -/
def emitBr (s : VState) (ts : Array ValType) (t : BrTarget) : VState :=
  let s := if hasV128 ts then s.emit (.hiMove 0 t.keep t.height) else s
  s.emit (.br t)

/-- Emit `return_` of values of types `ts` (with a `hiMove` first, as `emitBr`). -/
def emitReturn (s : VState) (ts : Array ValType) : VState :=
  let s := if hasV128 ts then s.emit (.hiMove 0 ts.size 0) else s
  s.emit (.return_ ts.size)

/-- Emit a tail call op whose callee takes `ps`, with `skip` slots above the
arguments (the table index or the function reference). -/
def emitTail (s : VState) (ps : Array ValType) (skip : Nat) (o : Op) : VState :=
  let s := if hasV128 ps then s.emit (.hiMove skip ps.size 0) else s
  s.emit o

/-- Validate and compile a SIMD instruction (`Simd.lean` has the shapes). -/
def stepSimd (c : Ctx) (nL : Nat) (s : VState) (k : Nat) (m : MemArg) (lane : Nat) (lo hi : UInt64) :
    V VState := do
  let some sh := simdShape k | .error "unknown SIMD instruction"
  let memOk := fun (w : Nat) => (show V Unit from do
    if m.mem ≥ c.mems.size then .error "unknown memory"
    if m.offset ≥ 4294967296 then .error "offset out of range"
    if 2 ^ m.align > w then .error "alignment must not be larger than natural")
  let laneOk := fun (n : Nat) => (show V Unit from
    if lane < n then .ok () else .error "invalid lane index")
  match sh with
  | .load w =>
    memOk w
    let s ← s.pop c .i32
    .ok ((s.push nL (some .v128)).emit (.simd k m.mem m.offset 0))
  | .store =>
    memOk 16
    let s ← s.pop c .v128
    let s ← s.pop c .i32
    .ok (s.emit (.simd k m.mem m.offset 0))
  | .const => .ok ((s.push nL (some .v128)).emit (.simdImm k lo hi))
  | .shuffle =>
    if !((List.range 16).all fun i => (V128.mk lo hi).lane 8 i < 32) then .error "invalid lane index"
    let s ← s.popAll c #[.v128, .v128]
    .ok ((s.push nL (some .v128)).emit (.simdImm k lo hi))
  | .un =>
    let s ← s.pop c .v128
    .ok ((s.push nL (some .v128)).emit (.simd k 0 0 0))
  | .bin =>
    let s ← s.popAll c #[.v128, .v128]
    .ok ((s.push nL (some .v128)).emit (.simd k 0 0 0))
  | .tern =>
    let s ← s.popAll c #[.v128, .v128, .v128]
    .ok ((s.push nL (some .v128)).emit (.simd k 0 0 0))
  | .test =>
    let s ← s.pop c .v128
    .ok ((s.push nL (some .i32)).emit (.simd k 0 0 0))
  | .shift =>
    let s ← s.popAll c #[.v128, .i32]
    .ok ((s.push nL (some .v128)).emit (.simd k 0 0 0))
  | .splat t =>
    let s ← s.pop c t
    .ok ((s.push nL (some .v128)).emit (.simd k 0 0 0))
  | .extract t n =>
    laneOk n
    let s ← s.pop c .v128
    .ok ((s.push nL (some t)).emit (.simd k 0 0 lane))
  | .replace t n =>
    laneOk n
    let s ← s.popAll c #[.v128, t]
    .ok ((s.push nL (some .v128)).emit (.simd k 0 0 lane))
  | .loadLane w =>
    memOk w
    laneOk (16 / w)
    let s ← s.popAll c #[.i32, .v128]
    .ok ((s.push nL (some .v128)).emit (.simd k m.mem m.offset lane))
  | .storeLane w =>
    memOk w
    laneOk (16 / w)
    let s ← s.popAll c #[.i32, .v128]
    .ok (s.emit (.simd k m.mem m.offset lane))

/-- Whether a field of this type has a default value. -/
def StorageType.defaultable : StorageType → Bool
  | .val (.ref r) => r.nullable
  | _ => true

/-- Bytes of one array element in a data segment; none for a reference type. -/
def StorageType.dataWidth : StorageType → Option Nat
  | .i8 => some 1 | .i16 => some 2
  | .val .i32 | .val .f32 => some 4
  | .val .i64 | .val .f64 => some 8
  | _ => none

/-- Validate and compile a garbage-collection instruction with index immediates
(`Instr.gc`; the numbers are `GcCode`). What each op's fields hold: `Run.gcStep`. -/
def stepGc (c : Ctx) (nL : Nat) (s : VState) (k x y : Nat) : V VState := do
  let refN := fun (h : HeapType) => ValType.ref ⟨true, h⟩
  let dataOk := fun (d : Nat) => (show V Unit from
    match c.dataCount with
    | none => .error "data count section required"
    | some n => if d ≥ n then .error "unknown data segment" else .ok ())
  if k ≤ 5 then
    let some fs := c.structT? x | .error "unknown type: not a struct type"
    if k == 0 then
      let s ← s.popAll c (fs.map (·.type.unpack))
      .ok ((s.push nL (some (.ref ⟨false, .idx x⟩))).emit (.gc k x fs.size 0))
    else if k == 1 then
      if !fs.all (·.type.defaultable) then .error "type mismatch: field is not defaultable"
      .ok ((s.push nL (some (.ref ⟨false, .idx x⟩))).emit (.gc k x 0 0))
    else
      let some f := fs[y]? | .error "unknown field"
      if k == 5 then
        if !f.mutable then .error "field is immutable"
        let s ← s.pop c f.type.unpack
        let s ← s.pop c (refN (.idx x))
        .ok (s.emit (.gc k y (packCode f.type) 0))
      else
        if f.type.isPacked != (k != 2) then .error "field is packed: struct.get_s or struct.get_u needed for it only"
        let s ← s.pop c (refN (.idx x))
        .ok ((s.push nL (some f.type.unpack)).emit (.gc k y (packCode f.type) 0))
  else if k == 15 then
    let s ← s.pop c (refN .array)
    .ok ((s.push nL (some .i32)).emit (.gc k 0 0 0))
  else if k ≤ 19 then
    let some f := c.arrayT? x | .error "unknown type: not an array type"
    let t := f.type.unpack
    let p := packCode f.type
    let rx := refN (.idx x)
    let new := some (ValType.ref ⟨false, .idx x⟩)
    if k == 6 then
      let s ← s.popAll c #[t, .i32]
      .ok ((s.push nL new).emit (.gc k x p 0))
    else if k == 7 then
      if !f.type.defaultable then .error "type mismatch: element is not defaultable"
      let s ← s.pop c .i32
      .ok ((s.push nL new).emit (.gc k x (if t.isRef then 1 else 0) 0))
    else if k == 8 then
      let s ← s.popAll c (Array.replicate y t)
      .ok ((s.push nL new).emit (.gc k x y p))
    else if k == 9 then
      let some w := f.type.dataWidth | .error "array type is not numeric or vector"
      dataOk y
      let s ← s.popAll c #[.i32, .i32]
      .ok ((s.push nL new).emit (.gc k x y w))
    else if k == 10 then
      let some et := c.elems[y]? | .error "unknown elem segment"
      if !c.valSub (.ref et) t then .error "type mismatch: element segment type"
      let s ← s.popAll c #[.i32, .i32]
      .ok ((s.push nL new).emit (.gc k x y 0))
    else if k ≤ 13 then
      if f.type.isPacked != (k != 11) then .error "element is packed: array.get_s or array.get_u needed for it only"
      let s ← s.popAll c #[rx, .i32]
      .ok ((s.push nL (some t)).emit (.gc k 0 p 0))
    else
      -- The ops from here on write the array.
      if !f.mutable then .error "array is immutable"
      if k == 14 then
        let s ← s.popAll c #[rx, .i32, t]
        .ok (s.emit (.gc k 0 p 0))
      else if k == 16 then
        let s ← s.popAll c #[rx, .i32, t, .i32]
        .ok (s.emit (.gc k 0 p 0))
      else if k == 17 then
        let some g := c.arrayT? y | .error "unknown type: not an array type"
        if !c.storageSub g.type f.type then .error "array types do not match"
        let s ← s.popAll c #[rx, .i32, refN (.idx y), .i32, .i32]
        .ok (s.emit (.gc k 0 0 0))
      else if k == 18 then
        let some w := f.type.dataWidth | .error "array type is not numeric or vector"
        dataOk y
        let s ← s.popAll c #[rx, .i32, .i32, .i32]
        .ok (s.emit (.gc k 0 y w))
      else
        let some et := c.elems[y]? | .error "unknown elem segment"
        if !c.valSub (.ref et) t then .error "type mismatch: element segment type"
        let s ← s.popAll c #[rx, .i32, .i32, .i32]
        .ok (s.emit (.gc k 0 y 0))
  else if k == 26 || k == 27 then
    let (src, dst) := if k == 26 then (HeapType.extern, HeapType.any) else (HeapType.any, HeapType.extern)
    let (s, a) ← s.popRef
    let nullable ← match a with
      | some (.ref r) => if c.heapSub r.heap src then pure r.nullable else .error "type mismatch"
      | _ => pure false
    .ok ((s.push nL (some (.ref ⟨nullable, dst⟩))).emit (.gc k 0 0 0))
  else if k == 28 then
    let s ← s.pop c .i32
    .ok ((s.push nL (some (.ref ⟨false, .i31⟩))).emit (.gc k 0 0 0))
  else if k == 29 || k == 30 then
    let s ← s.pop c (refN .i31)
    .ok ((s.push nL (some .i32)).emit (.gc k 0 0 0))
  else .error "unknown GC instruction"

/-- Check `ts` against the top of the stack without popping it. -/
def checkTop (c : Ctx) (s : VState) (ts : Array ValType) : V Unit := do
  let s' ← s.popAll c ts
  let _ := s'
  pure ()

/-- One instruction. -/
def step (c : Ctx) (fc : FnCtx) (s : VState) (i : Instr) : V VState := do
  let nL := fc.locals.size
  match i with
  | .unreachable => .ok ((s.emit .unreachable).setUnreachable)
  | .nop => .ok s
  | .block bt | .loop bt =>
    let some (ps, rs) := c.blockSig bt | .error "unknown type"
    let s ← s.popAll c ps
    let (s, l) := s.newLabel
    let isLoop := match i with | .loop _ => true | _ => false
    let s := if isLoop then s.place l else s
    .ok (s.pushCtrl nL (if isLoop then .loop else .block) ps rs l 0)
  | .if_ bt =>
    let some (ps, rs) := c.blockSig bt | .error "unknown type"
    let s ← s.pop c .i32
    let s ← s.popAll c ps
    let (s, l) := s.newLabel
    let (s, le) := s.newLabel
    let s := s.emit (.jumpUnless le)
    .ok (s.pushCtrl nL .if_ ps rs l le)
  | .else_ =>
    if s.ctrls.isEmpty || s.top.kind != .if_ then .error "else without if"
    let (s, f) ← s.popCtrl c
    let s := s.emit (.jump f.label)
    let s := s.place f.elseLabel
    .ok (s.pushCtrl nL .else_ f.params f.results f.label 0)
  | .end_ =>
    let (s, f) ← s.popCtrl c
    let s := match f.closeEntry with | some i => s.setStop i | none => s
    -- A legacy catch clause: move the results down over the exception slot.
    let s := if f.kind == .catch_ then
        { (emitBr s f.results { pc := f.label, keep := f.results.size, height := nL + f.base }) with
          vals := s.vals.pop }
      else s
    let s ← if f.kind == .if_ then
        if f.params == f.results then .ok (s.place f.elseLabel)
        else .error "type mismatch: if without else must not change the stack"
      else .ok s
    let s := if f.kind == .loop then s else s.place f.label
    if f.kind == .func then
      .ok ((emitReturn s f.results).pushAll nL f.results)
    else .ok (s.pushAll nL f.results)
  | .br l =>
    let some f := s.label? l | .error "unknown label"
    let s ← s.popAll c f.labelTypes
    .ok ((emitBr s f.labelTypes (target nL f)).setUnreachable)
  | .brIf l =>
    let some f := s.label? l | .error "unknown label"
    let s ← s.pop c .i32
    let ts := f.labelTypes
    let s ← s.popAll c ts
    let s := s.pushAll nL ts
    let t := target nL f
    -- When the kept values already sit at the label's height, nothing moves.
    if s.vals.size == f.base + ts.size then .ok (s.emit (.jumpIf t.pc))
    else if hasV128 ts then
      -- Values with a v128 move: skip a `hiMove` and a `br` when the condition is 0.
      let (s, skip) := s.newLabel
      let s := emitBr (s.emit (.jumpUnless skip)) ts t
      .ok (s.place skip)
    else .ok (s.emit (.brIf t))
  | .brTable ls d =>
    let some fd := s.label? d | .error "unknown label"
    let s ← s.pop c .i32
    let n := fd.labelTypes.size
    let mut ts : Array BrTarget := #[]
    for l in ls do
      let some f := s.label? l | .error "unknown label"
      if f.labelTypes.size != n then .error "type mismatch: br_table arity"
      checkTop c s f.labelTypes
      ts := ts.push (target nL f)
    let s ← s.popAll c fd.labelTypes
    let o := if hasV128 fd.labelTypes then Op.vBrTable ts (target nL fd) else Op.brTable ts (target nL fd)
    .ok ((s.emit o).setUnreachable)
  | .return_ =>
    let s ← s.popAll c fc.results
    .ok ((emitReturn s fc.results).setUnreachable)
  | .call f =>
    let some ti := c.funcs[f]? | .error "unknown function"
    let some ft := c.funcT? ti | .error "unknown type"
    let s ← s.popAll c ft.params
    .ok ((s.pushAll nL ft.results).emit (.call f))
  | .callIndirect ti x =>
    let some tt := c.tables[x]? | .error "unknown table"
    if !c.refSub tt.elem ⟨true, .func⟩ then .error "type mismatch: call_indirect table is not funcref"
    let some ft := c.funcT? ti | .error "unknown type"
    let s ← s.pop c .i32
    let s ← s.popAll c ft.params
    .ok ((s.pushAll nL ft.results).emit (if c.isFinal ti then .callIndirect ti x else .gc GcOp.callIndirectSub ti x 0))
  | .drop =>
    let (s, _) ← s.popAny
    .ok (s.emit .drop)
  | .select none =>
    let s ← s.pop c .i32
    let (s, a) ← s.popAny
    let (s, b) ← s.popAny
    let t ← match a, b with
      | some a, some b =>
        if a != b then .error "type mismatch: select operands differ"
        else if a.isNum || a == .v128 then .ok (some a) else .error "type mismatch: select needs a type"
      | some a, none | none, some a =>
        if a.isNum || a == .v128 then .ok (some a) else .error "type mismatch: select needs a type"
      | none, none => .ok none
    .ok ((s.push nL t).emit (if t == some .v128 then .vSelect else .select))
  | .select (some ts) =>
    if ts.size != 1 then .error "invalid result arity"
    let t := ts[0]!
    if !c.valOk t then .error "unknown type"
    let s ← s.pop c .i32
    let s ← s.pop c t
    let s ← s.pop c t
    .ok ((s.push nL (some t)).emit (if t == .v128 then .vSelect else .select))
  | .localGet x =>
    let some t := fc.locals[x]? | .error "unknown local"
    if s.inits.size > 0 && !s.inits[x]! then .error "uninitialized local"
    .ok ((s.push nL (some t)).emit (if t == .v128 then .vLocalGet x else .localGet x))
  | .localSet x =>
    let some t := fc.locals[x]? | .error "unknown local"
    let s ← s.pop c t
    let s := if s.inits.size > 0 then { s with inits := s.inits.set! x true } else s
    .ok (s.emit (if t == .v128 then .vLocalSet x else .localSet x))
  | .localTee x =>
    let some t := fc.locals[x]? | .error "unknown local"
    let s ← s.pop c t
    let s := if s.inits.size > 0 then { s with inits := s.inits.set! x true } else s
    .ok ((s.push nL (some t)).emit (if t == .v128 then .vLocalTee x else .localTee x))
  | .globalGet x =>
    let some g := c.globals[x]? | .error "unknown global"
    .ok ((s.push nL (some g.type)).emit (if g.type == .v128 then .vGlobalGet x else .globalGet x))
  | .globalSet x =>
    let some g := c.globals[x]? | .error "unknown global"
    if !g.mutable then .error "global is immutable"
    let s ← s.pop c g.type
    .ok (s.emit (if g.type == .v128 then .vGlobalSet x else .globalSet x))
  | .tableGet x =>
    let some t := c.tables[x]? | .error "unknown table"
    let s ← s.pop c .i32
    .ok ((s.push nL (some (.ref t.elem))).emit (.tableGet x))
  | .tableSet x =>
    let some t := c.tables[x]? | .error "unknown table"
    let s ← s.pop c (.ref t.elem)
    let s ← s.pop c .i32
    .ok (s.emit (.tableSet x))
  | .tableSize x =>
    if c.tables[x]?.isNone then .error "unknown table"
    .ok ((s.push nL (some .i32)).emit (.tableSize x))
  | .tableGrow x =>
    let some t := c.tables[x]? | .error "unknown table"
    let s ← s.pop c .i32
    let s ← s.pop c (.ref t.elem)
    .ok ((s.push nL (some .i32)).emit (.tableGrow x))
  | .tableFill x =>
    let some t := c.tables[x]? | .error "unknown table"
    let s ← s.pop c .i32
    let s ← s.pop c (.ref t.elem)
    let s ← s.pop c .i32
    .ok (s.emit (.tableFill x))
  | .tableCopy d sx =>
    let some td := c.tables[d]? | .error "unknown table"
    let some ts := c.tables[sx]? | .error "unknown table"
    if !c.refSub ts.elem td.elem then .error "type mismatch: table.copy element types"
    let s ← s.popAll c #[.i32, .i32, .i32]
    .ok (s.emit (.tableCopy d sx))
  | .tableInit x e =>
    let some t := c.tables[x]? | .error "unknown table"
    let some et := c.elems[e]? | .error "unknown elem segment"
    if !c.refSub et t.elem then .error "type mismatch: table.init element types"
    let s ← s.popAll c #[.i32, .i32, .i32]
    .ok (s.emit (.tableInit x e))
  | .elemDrop e =>
    if c.elems[e]?.isNone then .error "unknown elem segment"
    .ok (s.emit (.elemDrop e))
  | .load op m =>
    if m.mem ≥ c.mems.size then .error "unknown memory"
    if m.offset ≥ 4294967296 then .error "offset out of range"
    let (w, _, _) := op.shape
    if 2 ^ m.align > w then .error "alignment must not be larger than natural"
    let s ← s.pop c .i32
    .ok ((s.push nL (some op.type)).emit (.load op m.mem m.offset))
  | .store op m =>
    if m.mem ≥ c.mems.size then .error "unknown memory"
    if m.offset ≥ 4294967296 then .error "offset out of range"
    if 2 ^ m.align > op.width then .error "alignment must not be larger than natural"
    let s ← s.pop c op.type
    let s ← s.pop c .i32
    .ok (s.emit (.store op m.mem m.offset))
  | .memorySize m =>
    if m ≥ c.mems.size then .error "unknown memory"
    .ok ((s.push nL (some .i32)).emit (.memorySize m))
  | .memoryGrow m =>
    if m ≥ c.mems.size then .error "unknown memory"
    let s ← s.pop c .i32
    .ok ((s.push nL (some .i32)).emit (.memoryGrow m))
  | .memoryInit d m =>
    if m ≥ c.mems.size then .error "unknown memory"
    match c.dataCount with
    | none => .error "data count section required"
    | some n => if d ≥ n then .error "unknown data segment" else
      let s ← s.popAll c #[.i32, .i32, .i32]
      .ok (s.emit (.memoryInit d m))
  | .dataDrop d =>
    match c.dataCount with
    | none => .error "data count section required"
    | some n => if d ≥ n then .error "unknown data segment" else .ok (s.emit (.dataDrop d))
  | .memoryCopy d sm =>
    if d ≥ c.mems.size || sm ≥ c.mems.size then .error "unknown memory"
    let s ← s.popAll c #[.i32, .i32, .i32]
    .ok (s.emit (.memoryCopy d sm))
  | .memoryFill m =>
    if m ≥ c.mems.size then .error "unknown memory"
    let s ← s.popAll c #[.i32, .i32, .i32]
    .ok (s.emit (.memoryFill m))
  | .i32Const v => .ok ((s.push nL (some .i32)).emit (.const v.toUInt64))
  | .i64Const v => .ok ((s.push nL (some .i64)).emit (.const v))
  | .f32Const v => .ok ((s.push nL (some .f32)).emit (.const v.toUInt64))
  | .f64Const v => .ok ((s.push nL (some .f64)).emit (.const v))
  | .refNull h =>
    if !c.heapOk h then .error "unknown type"
    .ok ((s.push nL (some (.ref ⟨true, h⟩))).emit (.const nullRef))
  | .refIsNull =>
    let (s, _) ← s.popRef
    .ok ((s.push nL (some .i32)).emit .refIsNull)
  | .refFunc f =>
    let some ti := c.funcs[f]? | .error "unknown function"
    if !c.refs.contains f then .error "undeclared function reference"
    .ok ((s.push nL (some (.ref ⟨false, .idx ti⟩))).emit (.refFunc f))
  | .num op =>
    let (a, r) := op.sig
    let s ← if op.isBinary then s.popAll c #[a, a] else s.pop c a
    .ok ((s.push nL (some r)).emit (.num op))
  -- Exception handling.
  | .throw x =>
    let some ps := c.tagParams x | .error "unknown tag"
    let s ← s.popAll c ps
    .ok ((s.emit (.throw x ps.size)).setUnreachable)
  | .throwRef =>
    let s ← s.pop c (.ref ⟨true, .exn⟩)
    .ok ((s.emit .throwRef).setUnreachable)
  | .tryTable bt cs =>
    let some (ps, rs) := c.blockSig bt | .error "unknown type"
    let s ← s.popAll c ps
    -- Catch labels are seen from outside the `try_table`.
    let mut cts : Array CatchTarget := #[]
    for cl in cs do
      let (tag, l, ref) := match cl with
        | .catch_ x l => (some x, l, false) | .catchRef x l => (some x, l, true)
        | .catchAll l => (none, l, false) | .catchAllRef l => (none, l, true)
      let some f := s.label? l | .error "unknown label"
      let vals ← match tag with
        | some x => match c.tagParams x with
          | some ps => pure ps
          | none => .error "unknown tag"
        | none => pure #[]
      let vals := if ref then vals.push (.ref ⟨false, .exn⟩) else vals
      if !c.resultSub vals f.labelTypes then .error "type mismatch: catch label"
      cts := cts.push { tag := tag, pc := f.label, height := nL + f.base, payload := tag.isSome, exnAbove := ref }
    let (s, l) := s.newLabel
    let (s, e) := s.newEntry cts s.top.handler
    let s := s.pushCtrl nL .block ps rs l 0
    .ok (s.modTop fun f => { f with handler := some e, closeEntry := some e })
  | .try_ bt =>
    let some (ps, rs) := c.blockSig bt | .error "unknown type"
    let s ← s.popAll c ps
    let (s, l) := s.newLabel
    let (s, e) := s.newEntry #[] s.top.handler
    let s := s.pushCtrl nL .try_ ps rs l 0
    .ok (s.modTop fun f => { f with handler := some e, closeEntry := some e })
  | .catch_ _ | .catchAll =>
    if s.ctrls.isEmpty then .error "catch without try"
    let f0 := s.top
    if f0.kind != .try_ && f0.kind != .catch_ then .error "catch without try"
    if f0.kind == .catch_ && f0.sawCatchAll then .error "catch after catch_all"
    let tag := match i with | .catch_ x => some x | _ => none
    let payload ← match tag with
      | some x => match c.tagParams x with
        | some ps => pure ps
        | none => .error "unknown tag"
      | none => pure #[]
    let (s, f) ← s.popCtrl c
    let (s, e) ← if f.kind == .try_ then
        match f.closeEntry with
        | some e => pure ((s.setStop e).emit (.jump f.label), e)
        | none => .error "catch without try"
      else
        match f.tryEntry with
        | some e =>
          pure ({ (emitBr s f.results { pc := f.label, keep := f.results.size, height := nL + f.base }) with
                  vals := s.vals.pop }, e)
        | none => .error "catch without try"
    let base := s.vals.size
    let (s, cl) := s.newLabel
    let s := s.place cl
    let s := { s with handlers := s.handlers.modify e fun h =>
      let ct : CatchTarget := { tag := tag, pc := cl, height := nL + base, exnBelow := true, payload := tag.isSome }
      { h with catches := h.catches.push ct } }
    let outer := (s.handlers[e]?).bind (·.next)
    -- The exception slot, below the clause's frame.
    let s := s.push nL (some (.ref ⟨false, .exn⟩))
    let s := s.pushCtrl nL .catch_ #[] f.results f.label 0
    let s := s.modTop fun g => { g with base, handler := outer, tryEntry := some e,
                                        sawCatchAll := tag.isNone, params := f.params }
    .ok (s.pushAll nL payload)
  | .delegate l =>
    if s.ctrls.isEmpty || s.top.kind != .try_ then .error "delegate without try"
    let (s, f) ← s.popCtrl c
    let some e := f.closeEntry | .error "delegate without try"
    let some g := s.label? l | .error "unknown label"
    let s := s.setStop e
    let s := { s with handlers := s.handlers.modify e fun h => { h with next := g.handler } }
    .ok ((s.place f.label).pushAll nL f.results)
  | .rethrow l =>
    let some f := s.label? l | .error "unknown label"
    if f.kind != .catch_ then .error "invalid rethrow label"
    .ok ((s.emit (.rethrow (nL + f.base))).setUnreachable)
  -- Tail calls.
  | .returnCall f =>
    let some ti := c.funcs[f]? | .error "unknown function"
    let some ft := c.funcT? ti | .error "unknown type"
    if !c.resultSub ft.results fc.results then .error "type mismatch: tail call results"
    let s ← s.popAll c ft.params
    .ok (((emitTail s ft.params 0 (.returnCall f)).emit (.return_ fc.results.size)).setUnreachable)
  | .returnCallIndirect ti x =>
    let some tt := c.tables[x]? | .error "unknown table"
    if !c.refSub tt.elem ⟨true, .func⟩ then .error "type mismatch: call_indirect table is not funcref"
    let some ft := c.funcT? ti | .error "unknown type"
    if !c.resultSub ft.results fc.results then .error "type mismatch: tail call results"
    let s ← s.pop c .i32
    let s ← s.popAll c ft.params
    let o := if c.isFinal ti then Op.returnCallIndirect ti x else .gc GcOp.returnCallIndirectSub ti x 0
    .ok (((emitTail s ft.params 1 o).emit (.return_ fc.results.size)).setUnreachable)
  -- Typed function references.
  | .callRef ti =>
    let some ft := c.funcT? ti | .error "unknown type"
    let s ← s.pop c (.ref ⟨true, .idx ti⟩)
    let s ← s.popAll c ft.params
    .ok ((s.pushAll nL ft.results).emit .callRef)
  | .returnCallRef ti =>
    let some ft := c.funcT? ti | .error "unknown type"
    if !c.resultSub ft.results fc.results then .error "type mismatch: tail call results"
    let s ← s.pop c (.ref ⟨true, .idx ti⟩)
    let s ← s.popAll c ft.params
    .ok (((emitTail s ft.params 1 .returnCallRef).emit (.return_ fc.results.size)).setUnreachable)
  | .refAsNonNull =>
    let (s, a) ← s.popRef
    let t := a.map fun | .ref r => .ref { r with nullable := false } | t => t
    .ok ((s.push nL t).emit .refAsNonNull)
  | .brOnNull l =>
    let some f := s.label? l | .error "unknown label"
    let (s, a) ← s.popRef
    let ts := f.labelTypes
    let s ← s.popAll c ts
    let s := s.pushAll nL ts
    let t := a.map fun | .ref r => .ref { r with nullable := false } | t => t
    .ok ((s.push nL t).emit (.brOnNull (target nL f)))
  | .brOnNonNull l =>
    let some f := s.label? l | .error "unknown label"
    let ts := f.labelTypes
    if ts.isEmpty then .error "type mismatch: br_on_non_null label has no values"
    let last := ts.back!
    if !last.isRef then .error "type mismatch: br_on_non_null label must end in a reference"
    let (s, a) ← s.popRef
    match a with
    | some (.ref r) =>
      if !c.valSub (.ref { r with nullable := false }) last then .error "type mismatch: br_on_non_null"
    | _ => pure ()
    let rest := ts.pop
    let s ← s.popAll c rest
    let s := s.pushAll nL rest
    .ok (s.emit (.brOnNonNull (target nL f)))
  | .simd k m lane lo hi => stepSimd c nL s k m lane lo hi
  -- Garbage collection.
  | .gc k x y => stepGc c nL s k x y
  | .refTest r | .refCast r =>
    if !c.heapOk r.heap then .error "unknown type"
    let s ← s.pop c (.ref ⟨true, c.top r.heap⟩)
    let isTest := match i with | .refTest _ => true | _ => false
    let o := Op.gc (if isTest then GcCode.refTest else GcCode.refCast) (heapCode r.heap) (if r.nullable then 1 else 0) 0
    .ok ((s.push nL (some (if isTest then .i32 else .ref r))).emit o)
  | .brOnCast fail l r1 r2 =>
    let some f := s.label? l | .error "unknown label"
    if !c.heapOk r1.heap || !c.heapOk r2.heap then .error "unknown type"
    if !c.refSub r2 r1 then .error "type mismatch: br_on_cast target is not a subtype"
    let diff : RefType := ⟨r1.nullable && !r2.nullable, r1.heap⟩
    let (onBr, onFall) := if fail then (diff, r2) else (r2, diff)
    let ts := f.labelTypes
    if ts.isEmpty then .error "type mismatch: br_on_cast label has no values"
    if !c.valSub (.ref onBr) ts.back! then .error "type mismatch: br_on_cast label"
    let s ← s.pop c (.ref r1)
    let rest := ts.pop
    let s ← s.popAll c rest
    let s := s.pushAll nL rest
    let s := s.push nL (some (.ref onBr))
    let s := s.emit (.gcBr (target nL f) ((if fail then 1 else 0) + (if r2.nullable then 2 else 0)) (heapCode r2.heap))
    .ok ({ s with vals := s.vals.pop }.push nL (some (.ref onFall)))
  | .refEq =>
    let s ← s.popAll c #[.ref ⟨true, .eq⟩, .ref ⟨true, .eq⟩]
    .ok ((s.push nL (some .i32)).emit (.gc GcOp.refEq 0 0 0))

/-- Replace label ids by pcs. -/
def resolveT (labels : Array Nat) (t : BrTarget) : BrTarget := { t with pc := labels[t.pc]! }

def resolve (labels : Array Nat) : Op → Op
  | .br t => .br (resolveT labels t)
  | .brIf t => .brIf (resolveT labels t)
  | .jump l => .jump labels[l]!
  | .jumpIf l => .jumpIf labels[l]!
  | .jumpUnless l => .jumpUnless labels[l]!
  | .brTable ts d => .brTable (ts.map (resolveT labels)) (resolveT labels d)
  | .vBrTable ts d => .vBrTable (ts.map (resolveT labels)) (resolveT labels d)
  | .brOnNull t => .brOnNull (resolveT labels t)
  | .brOnNonNull t => .brOnNonNull (resolveT labels t)
  | .gcBr t f h => .gcBr (resolveT labels t) f h
  | o => o

/-- Replace label ids by pcs in the handler table. -/
def resolveH (labels : Array Nat) (h : Handler) : Handler :=
  { h with catches := h.catches.map fun ct => { ct with pc := labels[ct.pc]! } }

def bodyLoop (c : Ctx) (fc : FnCtx) (body : Array Instr) (i : Nat) (s : VState) :
    Except (Nat × String) VState :=
  if h : i < body.size then
    if s.ctrls.isEmpty then .error (i, "instructions after the end of the function") else
    match step c fc s body[i] with
    | .ok s => bodyLoop c fc body (i + 1) s
    | .error e => .error (i, e)
  else
    if s.ctrls.isEmpty then .ok s else .error (i, "unexpected end of function")
termination_by body.size - i

/-- Validate and compile one function body. -/
def compileFunc (c : Ctx) (fIdx : Nat) (f : Func) : Except ValidationError CompiledFunc := do
  let some ft := c.funcT? f.type | .error { msg := "unknown type", func := some fIdx }
  for t in f.locals do
    if !c.valOk t then .error { msg := "unknown type", func := some fIdx }
  let locals := ft.params ++ f.locals
  let fc : FnCtx := { locals, results := ft.results }
  let defaultable := fun (t : ValType) => match t with | .ref r => r.nullable | _ => true
  let inits := if f.locals.all defaultable then #[] else
    ft.params.map (fun _ => true) ++ f.locals.map defaultable
  let s0 : VState := { maxH := locals.size, inits }
  let (s0, l) := s0.newLabel
  let s0 := { s0 with ctrls := #[{ kind := .func, params := #[], results := ft.results,
                                     height := 0, label := l }] }
  -- The high halves of the declared locals start at zero, when one is a v128.
  let s0 := if hasV128 f.locals then s0.emit (.hiZero ft.params.size f.locals.size) else s0
  match bodyLoop c fc f.body 0 s0 with
  | .error (i, e) => .error { msg := e, func := some fIdx, at_ := i }
  | .ok s =>
    let code := fuse (s.ops.map (resolve s.labels))
    -- The handler table goes after the last op, where no pc reaches it.
    let code := if s.handlers.isEmpty then code else code.push (.handlers (s.handlers.map (resolveH s.labels)))
    .ok { type := f.type, nParams := ft.params.size, localInit := f.locals.map ValType.zeroBits,
          maxHeight := s.maxH, code }

/-! ### Constant expressions -/

/-- Type of a constant expression; `nGlobals` is how many globals it may read. -/
def constType (c : Ctx) (nGlobals : Nat) (e : Expr) : V ValType := do
  let mut st : Array ValType := #[]
  for i in e do
    match i with
    | .i32Const _ => st := st.push .i32
    | .i64Const _ => st := st.push .i64
    | .f32Const _ => st := st.push .f32
    | .f64Const _ => st := st.push .f64
    | .simd k .. => if k == 0x0c then st := st.push .v128 else .error "constant expression required"
    | .refNull h => if !c.heapOk h then .error "unknown type"
                    st := st.push (.ref ⟨true, h⟩)
    | .refFunc f =>
      let some ti := c.funcs[f]? | .error "unknown function"
      st := st.push (.ref ⟨false, .idx ti⟩)
    | .globalGet x =>
      if x ≥ nGlobals then .error "unknown global"
      let some g := c.globals[x]? | .error "unknown global"
      if g.mutable then .error "constant expression required"
      st := st.push g.type
    | .num op =>
      if op == .i32_add || op == .i32_sub || op == .i32_mul then
        if st.size < 2 || st[st.size-1]! != .i32 || st[st.size-2]! != .i32 then .error "type mismatch"
        st := st.pop
      else if op == .i64_add || op == .i64_sub || op == .i64_mul then
        if st.size < 2 || st[st.size-1]! != .i64 || st[st.size-2]! != .i64 then .error "type mismatch"
        st := st.pop
      else .error "constant expression required"
    | .end_ => pure ()
    | _ => .error "constant expression required"
  if st.size != 1 then .error "type mismatch"
  .ok st[0]!

/-- Whether a constant expression has a garbage-collection instruction. Such an
expression is typed by the pass over function bodies and run by the interpreter
(`constCode`); every other one goes through `constType` and `evalConst`, as before. -/
def hasGc (e : Expr) : Bool :=
  e.any fun i => match i with | .gc .. => true | _ => false

/-- The garbage-collection instructions that are constant: `struct.new`,
`struct.new_default`, `array.new`, `array.new_default`, `array.new_fixed`,
`any.convert_extern`, `extern.convert_any`, `ref.i31`. -/
def constGc (k : Nat) : Bool :=
  k == 0 || k == 1 || k == 6 || k == 7 || k == 8 || k == 26 || k == 27 || k == 28

/-- Compile a constant expression of type `t` that has a garbage-collection
instruction, as a function body with no parameter and one result. -/
def constCode (c : Ctx) (nGlobals : Nat) (e : Expr) (t : ValType) : V CompiledFunc := do
  for i in e do
    match i with
    | .i32Const _ | .i64Const _ | .f32Const _ | .f64Const _ | .refNull _ | .refFunc _ | .end_ => pure ()
    | .simd k .. => if k != 0x0c then .error "constant expression required"
    | .globalGet x =>
      if x ≥ nGlobals then .error "unknown global"
      let some g := c.globals[x]? | .error "unknown global"
      if g.mutable then .error "constant expression required"
    | .num op =>
      if !(op == .i32_add || op == .i32_sub || op == .i32_mul || op == .i64_add || op == .i64_sub
          || op == .i64_mul) then .error "constant expression required"
    | .gc k _ _ => if !constGc k then .error "constant expression required"
    | _ => .error "constant expression required"
  let fc : FnCtx := { locals := #[], results := #[t] }
  let s0 : VState := {}
  let (s0, l) := s0.newLabel
  let s0 := { s0 with ctrls := #[{ kind := .func, params := #[], results := #[t], height := 0, label := l }] }
  match bodyLoop c fc e 0 s0 with
  | .error (_, m) => .error m
  | .ok s => .ok { type := 0, nParams := 0, localInit := #[], maxHeight := s.maxH, code := s.ops.map (resolve s.labels) }

def checkConst (c : Ctx) (nGlobals : Nat) (e : Expr) (t : ValType) : V Unit := do
  if hasGc e then
    let _ ← constCode c nGlobals e t
  else
    let t' ← constType c nGlobals e
    if !c.valSub t' t then .error "type mismatch"

/-! ### Modules -/

/-- A module that passed validation, with its compiled functions. Only `validate`
makes one. -/
structure ValidModule where
  private mk ::
  module : Module
  ctx : Ctx
  /-- Compiled code of the module's own functions (not the imports). -/
  code : Array CompiledFunc
  deriving Inhabited

def limitsOk (l : Limits) (bound : Nat) : Bool :=
  l.min ≤ bound && (match l.max with | some m => m ≤ bound && l.min ≤ m | none => true)

def funcRefs (m : Module) : Std.HashSet Nat := Id.run do
  let mut r : Std.HashSet Nat := {}
  let scan := fun (r : Std.HashSet Nat) (e : Expr) =>
    e.foldl (fun r i => match i with | .refFunc f => r.insert f | _ => r) r
  for g in m.globals do r := scan r g.init
  for t in m.tables do
    if let some e := t.init then r := scan r e
  for el in m.elems do
    for e in el.init do r := scan r e
  for x in m.exports do
    if let .func f := x.desc then r := r.insert f
  return r

/-- The index that stands for "the first type of this recursion group" inside the
group's canonical form; type `k` of the group is `selfIdx + k`. -/
def selfIdx : Nat := 0xFFFFFFFFFFFF

/-! ### Canonical recursion groups

Two types are equivalent when their recursion groups are equal after each type index
is replaced: an index inside the group by its position (`selfIdx + k`), an earlier
index by the canonical name of that type (`names`), and the two types have the same
position. The validator's names are the least equivalent type index of the module
(`typeReps`); the store's names are its type ids (`Exec/Instantiate.lean`). -/

def canonIdx (names : Array Nat) (start : Nat) (i : Nat) : Nat :=
  if i ≥ start then selfIdx + (i - start) else names[i]?.getD i

def canonHeapIn (names : Array Nat) (start : Nat) : HeapType → HeapType
  | .idx i => .idx (canonIdx names start i)
  | h => h

def canonValIn (names : Array Nat) (start : Nat) : ValType → ValType
  | .ref r => .ref { r with heap := canonHeapIn names start r.heap }
  | t => t

def canonFieldIn (names : Array Nat) (start : Nat) (f : FieldType) : FieldType :=
  match f.type with
  | .val t => { f with type := .val (canonValIn names start t) }
  | _ => f

def canonCompIn (names : Array Nat) (start : Nat) : CompType → CompType
  | .func ft => .func ⟨ft.params.map (canonValIn names start), ft.results.map (canonValIn names start)⟩
  | .struct fs => .struct (fs.map (canonFieldIn names start))
  | .array f => .array (canonFieldIn names start f)

def canonSubIn (names : Array Nat) (start : Nat) (t : SubType) : SubType :=
  { final := t.final, supers := t.supers.map (canonIdx names start), comp := canonCompIn names start t.comp }

/-- For each type index, the least index of an equivalent type. -/
def typeReps (defs : Array TypeDef) : Array Nat := Id.run do
  let mut reps : Array Nat := #[]
  -- The canonical form of each distinct group, with the index of its first type.
  let mut seen : Array (Array SubType × Nat) := #[]
  for x in [0:defs.size] do
    let d := defs[x]!
    if d.recStart == x then
      let key := (defs.extract x (x + d.recSize)).map fun t => canonSubIn reps x t.sub
      match seen.find? (·.1 == key) with
      | some (_, first) => reps := reps ++ (Array.range d.recSize).map (first + ·)
      | none =>
        reps := reps ++ (Array.range d.recSize).map (x + ·)
        seen := seen.push (key, x)
  return reps

def mkCtx (m : Module) : Ctx :=
  { types := m.types
    funcs := m.importedFuncTypes ++ m.funcs.map (·.type)
    tables := m.importedTables ++ m.tables.map (·.type)
    mems := m.importedMems ++ m.mems
    globals := m.importedGlobals ++ m.globals.map (·.type)
    elems := m.elems.map (·.type)
    dataCount := m.dataCount
    refs := funcRefs m
    reps := typeReps m.defs
    tags := m.importedTags ++ m.tags
    defs := m.defs }

/-- The message for a field of type v128 (record, "GC", "Refused"). -/
def v128FieldMsg : String := "unsupported: v128 field in a struct or array type"

/-- Validate the type definitions: every type index is in range (a type may name the
types of its own recursion group and earlier ones), and a declared supertype is an
earlier type that is not final and that the composite type matches. -/
def checkTypes (c : Ctx) : V Unit := do
  for x in [0:c.defs.size] do
    let d := c.defs[x]!
    let lim := d.recStart + d.recSize
    let okV := fun (t : ValType) => match t with
      | .ref ⟨_, .idx i⟩ => i < lim
      | _ => true
    let okF := fun (f : FieldType) => match f.type with
      | .val t => okV t
      | _ => true
    let noV := fun (f : FieldType) => f.type != .val .v128
    match d.sub.comp with
    | .func ft => if !(ft.params.all okV && ft.results.all okV) then .error "unknown type"
    | .struct fs =>
      if !fs.all okF then .error "unknown type"
      if !fs.all noV then .error v128FieldMsg
    | .array f =>
      if !okF f then .error "unknown type"
      if !noV f then .error v128FieldMsg
    if d.sub.supers.size > 1 then .error "sub type has more than one supertype"
    if let some y := d.sub.supers[0]? then
      if y ≥ x then .error "unknown type"
      let sd := c.defs[y]!
      if sd.sub.final then .error "sub type: the supertype is final"
      if !c.compSub d.sub.comp sd.sub.comp then .error "sub type does not match its supertype"

/-- Compile functions `lo` to `hi` (module-local indices), in order. -/
def compileRange (c : Ctx) (m : Module) (nImp lo hi : Nat) : Except ValidationError (Array CompiledFunc) :=
  go lo (Array.mkEmpty (hi - lo))
where
  go (i : Nat) (acc : Array CompiledFunc) : Except ValidationError (Array CompiledFunc) :=
    if h : i < hi ∧ i < m.funcs.size then
      match compileFunc c (nImp + i) m.funcs[i] with
      | .ok cf => go (i + 1) (acc.push cf)
      | .error e => .error e
    else .ok acc
  termination_by hi - i

/-- Compile all functions. With `parallel`, bodies are compiled in chunks, one
`Task` each; the chunks are joined in order, so the result (and the first error) is
the same as the serial one. Each body needs only the read-only context `c`. -/
def compileAll (c : Ctx) (m : Module) (nImp : Nat) (parallel : Bool) :
    Except ValidationError (Array CompiledFunc) :=
  let n := m.funcs.size
  if !parallel || n < 64 then compileRange c m nImp 0 n else
  let chunk := max 16 (n / 64)
  let starts := (List.range ((n + chunk - 1) / chunk)).map (· * chunk)
  let tasks := starts.map fun lo => Task.spawn fun _ => compileRange c m nImp lo (min n (lo + chunk))
  tasks.foldl (init := .ok (Array.mkEmpty n)) fun acc t =>
    match acc with
    | .error e => .error e
    | .ok a => match t.get with
      | .ok b => .ok (a ++ b.map CompiledFunc.fresh)
      | .error e => .error e

def validateWith (parallel : Bool) (m : Module) : Except ValidationError ValidModule := do
  let c := mkCtx m
  let err := fun (s : String) => (Except.error { msg := s } : Except ValidationError Unit)
  let lift := fun (x : V Unit) => match x with
    | .ok () => (Except.ok () : Except ValidationError Unit)
    | .error e => .error { msg := e }
  lift (checkTypes c)
  for i in m.imports do
    match i.desc with
    | .func t => if (c.funcT? t).isNone then err "unknown type"
    | .table t => if !limitsOk t.limits 4294967295 then err "size minimum must not be greater than maximum"
    | .mem t => if !limitsOk t.limits 65536 then err "memory size must be at most 65536 pages (4GiB)"
    | .global g => if !c.valOk g.type then err "unknown type"
    | .tag t => match c.funcT? t with
      | none => err "unknown type"
      | some ft =>
        if !ft.results.isEmpty then err "non-empty tag result type"
        if hasV128 ft.params then err "unsupported: v128 in a tag type"
  let nImpFuncs := m.importedFuncTypes.size
  let nImpGlobals := m.importedGlobals.size
  for t in m.tables do
    if !limitsOk t.type.limits 4294967295 then err "size minimum must not be greater than maximum"
    if !c.heapOk t.type.elem.heap then err "unknown type"
    match t.init with
    | some e => lift (checkConst c nImpGlobals e (.ref t.type.elem))
    | none => if !t.type.elem.nullable then err "type mismatch"
  for t in m.tags do
    match c.funcT? t with
    | none => err "unknown type"
    | some ft =>
      if !ft.results.isEmpty then err "non-empty tag result type"
      if hasV128 ft.params then err "unsupported: v128 in a tag type"
  for mt in m.mems do
    if !limitsOk mt.limits 65536 then err "memory size must be at most 65536 pages (4GiB)"
  let mut gi := nImpGlobals
  for g in m.globals do
    if !c.valOk g.type.type then err "unknown type"
    lift (checkConst c gi g.init g.type.type)
    gi := gi + 1
  let mut names : Std.HashSet String := {}
  for x in m.exports do
    if names.contains x.name then err "duplicate export name"
    names := names.insert x.name
    match x.desc with
    | .func i => if i ≥ c.funcs.size then err "unknown function"
    | .table i => if i ≥ c.tables.size then err "unknown table"
    | .mem i => if i ≥ c.mems.size then err "unknown memory"
    | .global i => if i ≥ c.globals.size then err "unknown global"
    | .tag i => if i ≥ c.tags.size then err "unknown tag"
  if let some s := m.start then
    match c.funcs[s]? with
    | none => err "unknown function"
    | some ti => if c.funcT? ti != some ⟨#[], #[]⟩ then err "start function"
  for el in m.elems do
    if !c.heapOk el.type.heap then err "unknown type"
    for e in el.init do lift (checkConst c c.globals.size e (.ref el.type))
    match el.mode with
    | .active x off =>
      match c.tables[x]? with
      | none => err "unknown table"
      | some t =>
        if !c.refSub el.type t.elem then err "type mismatch"
        lift (checkConst c c.globals.size off .i32)
    | _ => pure ()
  for d in m.datas do
    match d.mode with
    | .active x off =>
      if x ≥ c.mems.size then err "unknown memory"
      lift (checkConst c c.globals.size off .i32)
    | .passive => pure ()
  let code ← compileAll c m nImpFuncs parallel
  return ⟨m, c, code⟩

def validate (m : Module) : Except ValidationError ValidModule := validateWith false m
def validateParallel (m : Module) : Except ValidationError ValidModule := validateWith true m

end L4Factoidal.WasmVM
