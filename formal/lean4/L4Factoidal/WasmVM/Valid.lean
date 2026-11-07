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
  deriving Inhabited

namespace Ctx

def heapSub (c : Ctx) : HeapType → HeapType → Bool
  | a, b =>
    if a == b then true else
    match a, b with
    | .idx i, .idx j => c.reps[i]? == c.reps[j]? && (c.reps[i]?).isSome
    | .idx _, .func => true
    | .nofunc, .func | .nofunc, .idx _ => true
    | .noextern, .extern => true
    | .noexn, .exn => true
    | .none, .any | .none, .eq | .none, .i31 | .none, .struct | .none, .array => true
    | .eq, .any | .i31, .any | .struct, .any | .array, .any => true
    | .i31, .eq | .struct, .eq | .array, .eq => true
    | _, _ => false

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

def blockSig (c : Ctx) : BlockType → Option (Array ValType × Array ValType)
  | .empty => some (#[], #[])
  | .val t => if c.valOk t then some (#[], #[t]) else none
  | .idx i => c.types[i]?.map fun ft => (ft.params, ft.results)

end Ctx

inductive CtrlKind where
  | block | loop | if_ | else_ | func
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
                     label := label, elseLabel := elseLabel, inits := s.inits }
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

/-- The control frame for label `l`. -/
def label? (s : VState) (l : Nat) : Option Ctrl :=
  if l < s.ctrls.size then s.ctrls[s.ctrls.size - 1 - l]? else none

end VState

/-- What one function needs besides the module context. -/
structure FnCtx where
  locals : Array ValType
  results : Array ValType

def target (nLocals : Nat) (f : Ctrl) : BrTarget :=
  { pc := f.label, keep := f.labelTypes.size, height := nLocals + f.height }

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
    let s ← if f.kind == .if_ then
        if f.params == f.results then .ok (s.place f.elseLabel)
        else .error "type mismatch: if without else must not change the stack"
      else .ok s
    let s := if f.kind == .loop then s else s.place f.label
    if f.kind == .func then
      .ok ((s.emit (.return_ f.results.size)).pushAll nL f.results)
    else .ok (s.pushAll nL f.results)
  | .br l =>
    let some f := s.label? l | .error "unknown label"
    let s ← s.popAll c f.labelTypes
    .ok ((s.emit (.br (target nL f))).setUnreachable)
  | .brIf l =>
    let some f := s.label? l | .error "unknown label"
    let s ← s.pop c .i32
    let ts := f.labelTypes
    let s ← s.popAll c ts
    let s := s.pushAll nL ts
    let t := target nL f
    -- When the kept values already sit at the label's height, nothing moves.
    let o := if s.vals.size == f.height + ts.size then Op.jumpIf t.pc else Op.brIf t
    .ok (s.emit o)
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
    .ok ((s.emit (.brTable ts (target nL fd))).setUnreachable)
  | .return_ =>
    let s ← s.popAll c fc.results
    .ok ((s.emit (.return_ fc.results.size)).setUnreachable)
  | .call f =>
    let some ti := c.funcs[f]? | .error "unknown function"
    let some ft := c.types[ti]? | .error "unknown type"
    let s ← s.popAll c ft.params
    .ok ((s.pushAll nL ft.results).emit (.call f))
  | .callIndirect ti x =>
    let some tt := c.tables[x]? | .error "unknown table"
    if !c.refSub tt.elem ⟨true, .func⟩ then .error "type mismatch: call_indirect table is not funcref"
    let some ft := c.types[ti]? | .error "unknown type"
    let s ← s.pop c .i32
    let s ← s.popAll c ft.params
    .ok ((s.pushAll nL ft.results).emit (.callIndirect ti x))
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
    .ok ((s.push nL t).emit .select)
  | .select (some ts) =>
    if ts.size != 1 then .error "invalid result arity"
    let t := ts[0]!
    if !c.valOk t then .error "unknown type"
    let s ← s.pop c .i32
    let s ← s.pop c t
    let s ← s.pop c t
    .ok ((s.push nL (some t)).emit .select)
  | .localGet x =>
    let some t := fc.locals[x]? | .error "unknown local"
    if s.inits.size > 0 && !s.inits[x]! then .error "uninitialized local"
    .ok ((s.push nL (some t)).emit (.localGet x))
  | .localSet x =>
    let some t := fc.locals[x]? | .error "unknown local"
    let s ← s.pop c t
    let s := if s.inits.size > 0 then { s with inits := s.inits.set! x true } else s
    .ok (s.emit (.localSet x))
  | .localTee x =>
    let some t := fc.locals[x]? | .error "unknown local"
    let s ← s.pop c t
    let s := if s.inits.size > 0 then { s with inits := s.inits.set! x true } else s
    .ok ((s.push nL (some t)).emit (.localTee x))
  | .globalGet x =>
    let some g := c.globals[x]? | .error "unknown global"
    .ok ((s.push nL (some g.type)).emit (.globalGet x))
  | .globalSet x =>
    let some g := c.globals[x]? | .error "unknown global"
    if !g.mutable then .error "global is immutable"
    let s ← s.pop c g.type
    .ok (s.emit (.globalSet x))
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

/-- Replace label ids by pcs. -/
def resolveT (labels : Array Nat) (t : BrTarget) : BrTarget := { t with pc := labels[t.pc]! }

def resolve (labels : Array Nat) : Op → Op
  | .br t => .br (resolveT labels t)
  | .brIf t => .brIf (resolveT labels t)
  | .jump l => .jump labels[l]!
  | .jumpIf l => .jumpIf labels[l]!
  | .jumpUnless l => .jumpUnless labels[l]!
  | .brTable ts d => .brTable (ts.map (resolveT labels)) (resolveT labels d)
  | o => o

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
  let some ft := c.types[f.type]? | .error { msg := "unknown type", func := some fIdx }
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
  match bodyLoop c fc f.body 0 s0 with
  | .error (i, e) => .error { msg := e, func := some fIdx, at_ := i }
  | .ok s =>
    let code := s.ops.map (resolve s.labels)
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

def checkConst (c : Ctx) (nGlobals : Nat) (e : Expr) (t : ValType) : V Unit := do
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

/-- The index that stands for "this type" inside a type's own definition. -/
def selfIdx : Nat := 0xFFFFFFFFFFFF

/-- Replace each type index by its representative; the type being defined (index
`self`, a one-type recursion group) by `selfIdx`. -/
def repHeap (reps : Array Nat) (self : Nat) : HeapType → HeapType
  | .idx i => .idx (if i == self then selfIdx else reps[i]?.getD i)
  | h => h

def repVal (reps : Array Nat) (self : Nat) : ValType → ValType
  | .ref r => .ref { r with heap := repHeap reps self r.heap }
  | t => t

/-- Type equivalence without recursion groups: a type may name only earlier types, so
two types are equivalent when they are equal after earlier indices are replaced by
their representatives and a reference to the type itself by `selfIdx`. -/
def typeReps (types : Array FuncType) : Array Nat := Id.run do
  let mut reps : Array Nat := #[]
  let mut seen : Array FuncType := #[]
  for ft in types do
    let self := reps.size
    let k : FuncType := ⟨ft.params.map (repVal reps self), ft.results.map (repVal reps self)⟩
    match seen.findIdx? (· == k) with
    | some j => reps := reps.push j
    | none => reps := reps.push seen.size
    seen := seen.push k
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
    reps := typeReps m.types }

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
      | .ok b => .ok (a ++ b)
      | .error e => .error e

def validateWith (parallel : Bool) (m : Module) : Except ValidationError ValidModule := do
  let c := mkCtx m
  let err := fun (s : String) => (Except.error { msg := s } : Except ValidationError Unit)
  let lift := fun (x : V Unit) => match x with
    | .ok () => (Except.ok () : Except ValidationError Unit)
    | .error e => .error { msg := e }
  let mut tyIx := 0
  for ft in m.types do
    let earlier := fun (t : ValType) => match t with
      | .ref ⟨_, .idx i⟩ => i ≤ tyIx
      | _ => true
    if !(ft.params.all earlier && ft.results.all earlier) then err "unknown type"
    tyIx := tyIx + 1
  for i in m.imports do
    match i.desc with
    | .func t => if t ≥ m.types.size then err "unknown type"
    | .table t => if !limitsOk t.limits 4294967295 then err "size minimum must not be greater than maximum"
    | .mem t => if !limitsOk t.limits 65536 then err "memory size must be at most 65536 pages (4GiB)"
    | .global g => if !c.valOk g.type then err "unknown type"
  let nImpFuncs := m.importedFuncTypes.size
  let nImpGlobals := m.importedGlobals.size
  for t in m.tables do
    if !limitsOk t.type.limits 4294967295 then err "size minimum must not be greater than maximum"
    if !c.heapOk t.type.elem.heap then err "unknown type"
    match t.init with
    | some e => lift (checkConst c nImpGlobals e (.ref t.type.elem))
    | none => if !t.type.elem.nullable then err "type mismatch"
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
  if let some s := m.start then
    match c.funcs[s]? with
    | none => err "unknown function"
    | some ti => if c.types[ti]? != some ⟨#[], #[]⟩ then err "start function"
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
