/-
L4Factoidal.WasmVM.Exec.Run: the interpreter loop
(https://github.com/danbri/factoidal/issues/1244).

`run` is ONE function, tail-recursive on its fuel: every case ends in a tail call of
`run` or in a result. Lean compiles it to a C loop with a `switch` on the op, so the
C stack does not grow with Wasm calls (they push a `Frame`) and
`tools/lean-tail-recursion-audit.py` passes it.

The registers are separate arguments of `run`, not fields of a structure: the
operand stack, `sp`, `fp` and `pc` (`USize`, so unboxed in C), the code, the instance
and the frames. A structure updated with `{ m with .. }` in each step cost a
reference-count increment and decrement of each of its seven fields per instruction
(seen in the emitted C, 2026-11-07). The `Machine` structure exists only at the API,
when a run stops.

Invariants that validation gives and the loop relies on (proof plan, items 4 and 5,
docs/designissues/2026-11-07-wasmvm-engine.md):
- Operand types: slots are untagged bits; an i32 or f32 slot is zero-extended
  ("slot normal form"), so an i32 condition is tested with `!= 0` on the whole slot.
- Heights: a function never uses more than `maxHeight` slots above `fp`, so stack
  room is checked once, at the call. Each slot access still makes one compare
  (`Slots.rd`); removing it needs `maxHeight_sound` (record, "Next").
- Branch targets are in range.

The memory is reached only through `LinearMemory` (`Exec/Memory.lean`); `run` is
`@[specialize]`, so each backend gets its own compiled loop.

Uniqueness: the store and the stack are passed along and never kept twice, so
stores and `Array.modify` update in place.
-/
import L4Factoidal.WasmVM.Exec.Store

namespace L4Factoidal.WasmVM

structure Frame where
  code : Array Op
  pc : USize
  fp : USize
  inst : ModuleInst
  deriving Inhabited

/-- The registers of a stopped run. -/
structure Machine where
  stack : Slots
  sp : USize
  fp : USize
  pc : USize
  code : Array Op
  inst : ModuleInst
  frames : Array Frame
  deriving Inhabited

/-- Why `run` stopped. (`run` also returns the fuel left.) -/
inductive Event where
  | done
  | trap (t : Trap)
  | outOfFuel
  /-- A call of host function `id` (store address `fa`) with these argument bits.
  The machine is ready to take the results. -/
  | hostCall (id : Nat) (fa : Nat) (args : Array UInt64)
  deriving Inhabited

/-- Engine limits of a run. -/
structure RunLimits where
  maxDepth : Nat := 10000
  /-- Most operand-stack slots. -/
  maxSlots : Nat := 1 <<< 22
  deriving Inhabited

namespace Run

@[inline] def rd (s : Slots) (i : USize) : UInt64 := Slots.rd s i
@[inline] def wr (s : Slots) (i : USize) (v : UInt64) : Slots := Slots.wr s i v

theorem pc_ok {code : Array Op} {pc : USize} (h : pc < code.usize) : pc.toNat < code.size := by
  rw [USize.lt_iff_toNat_lt] at h
  have : code.usize.toNat ≤ code.size := by
    simp only [Array.usize, Nat.toUSize, USize.toNat_ofNat]; exact Nat.mod_le _ _
  omega

/-! ### Straight-line operations

`run` executes these ops through `Simple.exec`, alone and inside fused ops, so a
fused op is by definition its parts in sequence (`Proofs/Fuse.lean`). -/

/-- An op that only reads and writes the operand stack and locals, and goes to the
next pc. `bin` and `un` are numeric ops that cannot trap. -/
inductive Simple where
  | localGet (x : USize) | localSet (x : USize) | localTee (x : USize)
  | const (v : UInt64) | bin (op : NumOp) | un (op : NumOp) | drop
  deriving Inhabited

/-- The operand-stack part of the engine state: the slots and `sp`. -/
structure SP where
  stack : Slots
  sp : USize

@[inline] def Simple.exec (fp : USize) : Simple → SP → SP
  | .localGet x, ⟨s, sp⟩ => ⟨wr s sp (rd s (fp + x)), sp + 1⟩
  | .localSet x, ⟨s, sp⟩ => ⟨wr s (fp + x) (rd s (sp - 1)), sp - 1⟩
  | .localTee x, ⟨s, sp⟩ => ⟨wr s (fp + x) (rd s (sp - 1)), sp⟩
  | .const v, ⟨s, sp⟩ => ⟨wr s sp v, sp + 1⟩
  | .bin op, ⟨s, sp⟩ => ⟨wr s (sp - 2) (op.evalBin (rd s (sp - 2)) (rd s (sp - 1))), sp - 1⟩
  | .un op, ⟨s, sp⟩ => ⟨wr s (sp - 1) (op.evalUn (rd s (sp - 1))), sp⟩
  | .drop, ⟨s, sp⟩ => ⟨s, sp - 1⟩

/-- Run a list of simple ops in order. -/
def Simple.execAll (fp : USize) (ops : List Simple) (x : SP) : SP :=
  ops.foldl (fun x o => o.exec fp x) x

/-- The pc after a conditional jump on `c` (`onZero`: `jumpUnless`, else `jumpIf`). -/
@[inline] def jumpTo (c : UInt64) (onZero : Bool) (t next : USize) : USize :=
  if onZero then (if c == 0 then t else next) else (if c != 0 then t else next)

/-- Copy `k` slots from `src` to `dst` (`dst ≤ src`), lowest first. -/
def moveDown (s : Slots) (src dst : USize) : Nat → Slots
  | 0 => s
  | k + 1 => moveDown (wr s dst (rd s src)) (src + 1) (dst + 1) k

def initLocals (s : Slots) (base : USize) (init : Array UInt64) (i : Nat) : Slots :=
  if h : i < init.size then initLocals (wr s (base + i.toUSize) init[i]) base init (i + 1) else s
termination_by init.size - i

/-! ### Memory -/

def LoadOp.width : LoadOp → Nat
  | .i32 | .f32 | .i64_32s | .i64_32u => 4
  | .i64 | .f64 => 8
  | .i32_8s | .i32_8u | .i64_8s | .i64_8u => 1
  | .i32_16s | .i32_16u | .i64_16s | .i64_16u => 2

section
variable {M : Type} [LinearMemory M]
open LinearMemory

/-- The slot bits that a load gives, the access proved in range. -/
@[inline] def loadVal (d : M) (ea : Nat) : (op : LoadOp) → ea + LoadOp.width op ≤ size d → UInt64
  | .i32, h | .f32, h | .i64_32u, h => load32 d ea h
  | .i64, h | .f64, h => load64 d ea h
  | .i32_8u, h | .i64_8u, h => load8 d ea h
  | .i32_16u, h | .i64_16u, h => load16 d ea h
  | .i32_8s, h => (load8 d ea h).toUInt8.toInt8.toInt32.toUInt32.toUInt64
  | .i32_16s, h => (load16 d ea h).toUInt16.toInt16.toInt32.toUInt32.toUInt64
  | .i64_8s, h => (load8 d ea h).toUInt8.toInt8.toInt64.toUInt64
  | .i64_16s, h => (load16 d ea h).toUInt16.toInt16.toInt64.toUInt64
  | .i64_32s, h => (load32 d ea h).toUInt32.toInt32.toInt64.toUInt64

@[inline] def storeVal (d : M) (ea : Nat) (v : UInt64) : (op : StoreOp) → ea + op.width ≤ size d → M
  | .i32, h | .f32, h | .i64_32, h => store32 d ea v h
  | .i64, h | .f64, h => store64 d ea v h
  | .i32_8, h | .i64_8, h => store8 d ea v h
  | .i32_16, h | .i64_16, h => store16 d ea v h

/-- Write a value into memory `ma` of the store, checked against its size. The memory
instance is taken apart before the store, so the memory has one reference and is
changed in place (with `{ mi with data := .. }` under the dependent `if` the compiler
kept a second reference and copied the whole memory at each store: measured
2026-11-07, `memsum` fell from 29 to 11 million instructions per second). -/
@[inline] def storeMem (st : StoreOf M) (ma ea : Nat) (v : UInt64) (op : StoreOp) : StoreOf M :=
  { st with mems := st.mems.modify ma fun ⟨data, max⟩ =>
      if h : ea + op.width ≤ size data then ⟨storeVal data ea v op h, max⟩ else ⟨data, max⟩ }

@[inline] def memData (st : StoreOf M) (inst : ModuleInst) (k : Nat) : M := (st.mems[inst.mems[k]!]!).data

end

def fillArr (a : Array UInt64) (i : Nat) (v : UInt64) : Nat → Array UInt64
  | 0 => a
  | k + 1 => fillArr (a.set! i v) (i + 1) v k

/-- Write `src[s .. s+n)` into `a` at `d`. `src` is a separate array. -/
def copyArr (a : Array UInt64) (src : Array UInt64) (s d : Nat) : Nat → Array UInt64
  | 0 => a
  | k + 1 => copyArr (a.set! d (src[s]!)) src (s + 1) (d + 1) k

/-! ### Branches and calls -/

/-- Move `keep` values down to `fp + height`; gives the new stack and `sp`. -/
@[inline] def brMove (s : Slots) (sp fp : USize) (t : BrTarget) : SP :=
  let keep := t.keep.toUSize
  let dst := fp + t.height.toUSize
  let s := if sp - keep == dst then s else moveDown s (sp - keep) dst t.keep
  ⟨s, dst + keep⟩

def argBits (s : Slots) (base : USize) (n : Nat) : Array UInt64 :=
  (Array.range n).map fun i => rd s (base + i.toUSize)

/-- What entering a function gives. -/
inductive Enter where
  | ok (stack : Slots) (sp fp : USize) (code : Array Op) (inst : ModuleInst) (frames : Array Frame)
  | host (id fa : Nat) (args : Array UInt64) (stack : Slots) (sp : USize)
  | trap (t : Trap) (stack : Slots)

section
variable {M : Type} [LinearMemory M]

/-- Enter function `fa`; the arguments are the top slots; the caller resumes at `retPc`. -/
@[inline] def enter (lim : RunLimits) (st : StoreOf M) (stack : Slots) (sp fp : USize) (code : Array Op)
    (inst : ModuleInst) (frames : Array Frame) (fa : Nat) (retPc : USize) : Enter :=
  match st.funcs[fa]? with
  | none => .trap (.host "unknown function address") stack
  | some fi =>
    match fi.kind with
    | .host id =>
      let n := fi.type.params.size
      .host id fa (argBits stack (sp - n.toUSize) n) stack (sp - n.toUSize)
    | .wasm ia cf =>
      if frames.size ≥ lim.maxDepth then .trap .callStackExhausted stack else
      let nfp := sp - cf.nParams.toUSize
      let need := nfp.toNat + cf.maxHeight + 1
      if need > lim.maxSlots then .trap .callStackExhausted stack else
      let stack := if need > stack.count then Slots.grow stack (max need (2 * stack.count) - stack.count)
        else stack
      let stack := initLocals stack (nfp + cf.nParams.toUSize) cf.localInit 0
      .ok stack (nfp + cf.nLocals.toUSize) nfp cf.code (st.insts[ia]!)
        (frames.push { code, pc := retPc, fp, inst })

/-! ### The loop -/

@[specialize] def run (lim : RunLimits) (st : StoreOf M) (stack : Slots) (sp fp pc : USize)
    (code : Array Op) (inst : ModuleInst) (frames : Array Frame) :
    Nat → StoreOf M × Machine × Nat × Event
  | 0 => (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, 0, .outOfFuel)
  | fuel + 1 =>
    if h : pc < code.usize then
    match code.uget pc (pc_ok h) with
    | .unreachable => (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, .trap .unreachable)
    | .jump t => run lim st stack sp fp t.toUSize code inst frames fuel
    | .jumpIf t =>
      let c := rd stack (sp - 1)
      run lim st stack (sp - 1) fp (if c != 0 then t.toUSize else pc + 1) code inst frames fuel
    | .jumpUnless t =>
      let c := rd stack (sp - 1)
      run lim st stack (sp - 1) fp (if c == 0 then t.toUSize else pc + 1) code inst frames fuel
    | .br t =>
      let x := brMove stack sp fp t
      run lim st x.stack x.sp fp t.pc.toUSize code inst frames fuel
    | .brIf t =>
      let c := rd stack (sp - 1)
      if c != 0 then
        let x := brMove stack (sp - 1) fp t
        run lim st x.stack x.sp fp t.pc.toUSize code inst frames fuel
      else run lim st stack (sp - 1) fp (pc + 1) code inst frames fuel
    | .brTable ts d =>
      let i := (rd stack (sp - 1)).toNat
      let t := if h : i < ts.size then ts[i] else d
      let x := brMove stack (sp - 1) fp t
      run lim st x.stack x.sp fp t.pc.toUSize code inst frames fuel
    | .return_ k =>
      let ku := k.toUSize
      let stack := if sp - ku == fp then stack else moveDown stack (sp - ku) fp k
      let sp := fp + ku
      if frames.isEmpty then (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, .done) else
      let f := frames.back!
      run lim st stack sp f.fp f.pc f.code f.inst frames.pop fuel
    | .call f =>
      let fa := inst.funcs[f]!
      match enter lim st stack sp fp code inst frames fa (pc + 1) with
      | .ok stack sp fp code inst frames => run lim st stack sp fp 0 code inst frames fuel
      | .host id fa args stack sp =>
        (st, ⟨stack, sp, fp, pc + 1, code, inst, frames⟩, fuel, .hostCall id fa args)
      | .trap t stack => (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, .trap t)
    | .callIndirect ti x =>
      let i := (rd stack (sp - 1)).toNat
      let tab := st.tables[inst.tables[x]!]!
      if i ≥ tab.elems.size then (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, .trap .undefinedElement) else
      let r := tab.elems[i]!
      if r == nullRef then (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, .trap .uninitializedElement) else
      let fa := r.toNat
      if (st.funcs[fa]!).typeId != inst.typeIds[ti]! then
        (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, .trap .indirectTypeMismatch) else
      match enter lim st stack (sp - 1) fp code inst frames fa (pc + 1) with
      | .ok stack sp fp code inst frames => run lim st stack sp fp 0 code inst frames fuel
      | .host id fa args stack sp =>
        (st, ⟨stack, sp, fp, pc + 1, code, inst, frames⟩, fuel, .hostCall id fa args)
      | .trap t stack => (st, ⟨stack, sp - 1, fp, pc, code, inst, frames⟩, fuel, .trap t)
    | .drop =>
      let x := Simple.exec fp .drop ⟨stack, sp⟩
      run lim st x.stack x.sp fp (pc + 1) code inst frames fuel
    | .select =>
      let c := rd stack (sp - 1)
      let stack := if c != 0 then stack else wr stack (sp - 3) (rd stack (sp - 2))
      run lim st stack (sp - 2) fp (pc + 1) code inst frames fuel
    | .localGet x =>
      let x := Simple.exec fp (.localGet x.toUSize) ⟨stack, sp⟩
      run lim st x.stack x.sp fp (pc + 1) code inst frames fuel
    | .localSet x =>
      let x := Simple.exec fp (.localSet x.toUSize) ⟨stack, sp⟩
      run lim st x.stack x.sp fp (pc + 1) code inst frames fuel
    | .localTee x =>
      let x := Simple.exec fp (.localTee x.toUSize) ⟨stack, sp⟩
      run lim st x.stack x.sp fp (pc + 1) code inst frames fuel
    | .globalGet x =>
      let v := st.globalBits inst.globals[x]!
      run lim st (wr stack sp v) (sp + 1) fp (pc + 1) code inst frames fuel
    | .globalSet x =>
      let v := rd stack (sp - 1)
      let st := { st with globals := Slots.wr st.globals inst.globals[x]!.toUSize v }
      run lim st stack (sp - 1) fp (pc + 1) code inst frames fuel
    | .tableGet x =>
      let i := (rd stack (sp - 1)).toNat
      let tab := st.tables[inst.tables[x]!]!
      if h : i < tab.elems.size then
        run lim st (wr stack (sp - 1) tab.elems[i]) sp fp (pc + 1) code inst frames fuel
      else (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, .trap .tableOOB)
    | .tableSet x =>
      let v := rd stack (sp - 1)
      let i := (rd stack (sp - 2)).toNat
      let ta := inst.tables[x]!
      if i < (st.tables[ta]!).elems.size then
        let st := { st with tables := st.tables.modify ta fun t => { t with elems := t.elems.set! i v } }
        run lim st stack (sp - 2) fp (pc + 1) code inst frames fuel
      else (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, .trap .tableOOB)
    | .tableSize x =>
      let n := (st.tables[inst.tables[x]!]!).elems.size
      run lim st (wr stack sp n.toUInt64) (sp + 1) fp (pc + 1) code inst frames fuel
    | .tableGrow x =>
      let n := (rd stack (sp - 1)).toNat
      let v := rd stack (sp - 2)
      let ta := inst.tables[x]!
      let tab := st.tables[ta]!
      let old := tab.elems.size
      let cap := min (tab.max.getD 4294967295) 10000000
      if old + n ≤ cap then
        let st := { st with tables := st.tables.modify ta fun t => { t with elems := t.elems ++ Array.replicate n v } }
        run lim st (wr stack (sp - 2) old.toUInt64) (sp - 1) fp (pc + 1) code inst frames fuel
      else
        run lim st (wr stack (sp - 2) 0xFFFFFFFF) (sp - 1) fp (pc + 1) code inst frames fuel
    | .tableFill x =>
      let n := (rd stack (sp - 1)).toNat
      let v := rd stack (sp - 2)
      let i := (rd stack (sp - 3)).toNat
      let ta := inst.tables[x]!
      if i + n > (st.tables[ta]!).elems.size then
        (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, .trap .tableOOB) else
      let st := { st with tables := st.tables.modify ta fun t => { t with elems := fillArr t.elems i v n } }
      run lim st stack (sp - 3) fp (pc + 1) code inst frames fuel
    | .tableCopy dx sx =>
      let n := (rd stack (sp - 1)).toNat
      let s := (rd stack (sp - 2)).toNat
      let d := (rd stack (sp - 3)).toNat
      let td := inst.tables[dx]!
      let src := (st.tables[inst.tables[sx]!]!).elems
      if s + n > src.size || d + n > (st.tables[td]!).elems.size then
        (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, .trap .tableOOB) else
      let slice := src.extract s (s + n)
      let st := { st with tables := st.tables.modify td fun t => { t with elems := copyArr t.elems slice 0 d n } }
      run lim st stack (sp - 3) fp (pc + 1) code inst frames fuel
    | .tableInit x e =>
      let n := (rd stack (sp - 1)).toNat
      let s := (rd stack (sp - 2)).toNat
      let d := (rd stack (sp - 3)).toNat
      let ta := inst.tables[x]!
      let seg := st.elems[inst.elems[e]!]!
      if s + n > seg.size || d + n > (st.tables[ta]!).elems.size then
        (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, .trap .tableOOB) else
      let st := { st with tables := st.tables.modify ta fun t => { t with elems := copyArr t.elems seg s d n } }
      run lim st stack (sp - 3) fp (pc + 1) code inst frames fuel
    | .elemDrop e =>
      let st := { st with elems := st.elems.set! inst.elems[e]! #[] }
      run lim st stack sp fp (pc + 1) code inst frames fuel
    | .load op mem off =>
      let ea := (rd stack (sp - 1)).toNat + off
      let d := memData st inst mem
      if h : ea + LoadOp.width op ≤ LinearMemory.size d then
        run lim st (wr stack (sp - 1) (loadVal d ea op h)) sp fp (pc + 1) code inst frames fuel
      else (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, .trap .memOOB)
    | .store op mem off =>
      let v := rd stack (sp - 1)
      let ea := (rd stack (sp - 2)).toNat + off
      let ma := inst.mems[mem]!
      if ea + op.width ≤ LinearMemory.size (st.mems[ma]!).data then
        run lim (storeMem st ma ea v op) stack (sp - 2) fp (pc + 1) code inst frames fuel
      else (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, .trap .memOOB)
    | .memorySize mem =>
      let n := LinearMemory.size (memData st inst mem) / pageSize
      run lim st (wr stack sp n.toUInt64) (sp + 1) fp (pc + 1) code inst frames fuel
    | .memoryGrow mem =>
      let n := (rd stack (sp - 1)).toNat
      let ma := inst.mems[mem]!
      let mi := st.mems[ma]!
      let old := LinearMemory.size mi.data / pageSize
      let cap := min (mi.max.getD 65536) st.pageLimit
      if old + n ≤ cap then
        let st := if n == 0 then st else
          { st with mems := st.mems.modify ma fun mi => { mi with data := LinearMemory.grow mi.data (n * pageSize) } }
        run lim st (wr stack (sp - 1) old.toUInt64) sp fp (pc + 1) code inst frames fuel
      else
        run lim st (wr stack (sp - 1) 0xFFFFFFFF) sp fp (pc + 1) code inst frames fuel
    | .memoryInit di mem =>
      let n := (rd stack (sp - 1)).toNat
      let s := (rd stack (sp - 2)).toNat
      let d := (rd stack (sp - 3)).toNat
      let ma := inst.mems[mem]!
      let src := st.datas[inst.datas[di]!]!
      if s + n > src.size || d + n > LinearMemory.size (st.mems[ma]!).data then
        (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, .trap .memOOB) else
      let st := { st with mems := st.mems.modify ma fun mi =>
        { mi with data := LinearMemory.writeBytes mi.data d src s n } }
      run lim st stack (sp - 3) fp (pc + 1) code inst frames fuel
    | .dataDrop di =>
      let st := { st with datas := st.datas.set! inst.datas[di]! ByteArray.empty }
      run lim st stack sp fp (pc + 1) code inst frames fuel
    | .memoryCopy dm sm =>
      let n := (rd stack (sp - 1)).toNat
      let s := (rd stack (sp - 2)).toNat
      let d := (rd stack (sp - 3)).toNat
      let da := inst.mems[dm]!
      let sa := inst.mems[sm]!
      if s + n > LinearMemory.size (st.mems[sa]!).data || d + n > LinearMemory.size (st.mems[da]!).data then
        (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, .trap .memOOB) else
      let st := if da == sa then
          { st with mems := st.mems.modify da fun mi => { mi with data := LinearMemory.copyWithin mi.data s d n } }
        else
          let src := (st.mems[sa]!).data
          { st with mems := st.mems.modify da fun mi => { mi with data := LinearMemory.copyInto src s mi.data d n } }
      run lim st stack (sp - 3) fp (pc + 1) code inst frames fuel
    | .memoryFill mem =>
      let n := (rd stack (sp - 1)).toNat
      let v := (rd stack (sp - 2)).toUInt8
      let d := (rd stack (sp - 3)).toNat
      let ma := inst.mems[mem]!
      if d + n > LinearMemory.size (st.mems[ma]!).data then
        (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, .trap .memOOB) else
      let st := { st with mems := st.mems.modify ma fun mi => { mi with data := LinearMemory.fill mi.data d v n } }
      run lim st stack (sp - 3) fp (pc + 1) code inst frames fuel
    | .const v =>
      let x := Simple.exec fp (.const v) ⟨stack, sp⟩
      run lim st x.stack x.sp fp (pc + 1) code inst frames fuel
    | .refIsNull =>
      let v := rd stack (sp - 1)
      run lim st (wr stack (sp - 1) (if v == nullRef then 1 else 0)) sp fp (pc + 1) code inst frames fuel
    | .refFunc f =>
      let a := inst.funcs[f]!
      run lim st (wr stack sp a.toUInt64) (sp + 1) fp (pc + 1) code inst frames fuel
    | .num op =>
      if op.isBinary then
        match (if op.mayTrap then op.trapBin (rd stack (sp - 2)) (rd stack (sp - 1)) else none) with
        | some t => (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, .trap t)
        | none =>
          let x := Simple.exec fp (.bin op) ⟨stack, sp⟩
          run lim st x.stack x.sp fp (pc + 1) code inst frames fuel
      else
        match (if op.mayTrap then op.trapUn (rd stack (sp - 1)) else none) with
        | some t => (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, .trap t)
        | none =>
          let x := Simple.exec fp (.un op) ⟨stack, sp⟩
          run lim st x.stack x.sp fp (pc + 1) code inst frames fuel
    -- Fused ops: `k` parts take `k` fuel. With less fuel, run the first part only
    -- (the others follow it in the code).
    | .llBin x y op =>
      match fuel with
      | f + 2 =>
        let s := Simple.exec fp (.bin op) (Simple.exec fp (.localGet y.toUSize)
          (Simple.exec fp (.localGet x.toUSize) ⟨stack, sp⟩))
        run lim st s.stack s.sp fp (pc + 3) code inst frames f
      | g =>
        let s := Simple.exec fp (.localGet x.toUSize) ⟨stack, sp⟩
        run lim st s.stack s.sp fp (pc + 1) code inst frames g
    | .lcBin x c op =>
      match fuel with
      | f + 2 =>
        let s := Simple.exec fp (.bin op) (Simple.exec fp (.const c)
          (Simple.exec fp (.localGet x.toUSize) ⟨stack, sp⟩))
        run lim st s.stack s.sp fp (pc + 3) code inst frames f
      | g =>
        let s := Simple.exec fp (.localGet x.toUSize) ⟨stack, sp⟩
        run lim st s.stack s.sp fp (pc + 1) code inst frames g
    | .cBin c op =>
      match fuel with
      | f + 1 =>
        let s := Simple.exec fp (.bin op) (Simple.exec fp (.const c) ⟨stack, sp⟩)
        run lim st s.stack s.sp fp (pc + 2) code inst frames f
      | g =>
        let s := Simple.exec fp (.const c) ⟨stack, sp⟩
        run lim st s.stack s.sp fp (pc + 1) code inst frames g
    | .lUn x op =>
      match fuel with
      | f + 1 =>
        let s := Simple.exec fp (.un op) (Simple.exec fp (.localGet x.toUSize) ⟨stack, sp⟩)
        run lim st s.stack s.sp fp (pc + 2) code inst frames f
      | g =>
        let s := Simple.exec fp (.localGet x.toUSize) ⟨stack, sp⟩
        run lim st s.stack s.sp fp (pc + 1) code inst frames g
    | .binSet op z =>
      match fuel with
      | f + 1 =>
        let s := Simple.exec fp (.localSet z.toUSize) (Simple.exec fp (.bin op) ⟨stack, sp⟩)
        run lim st s.stack s.sp fp (pc + 2) code inst frames f
      | g =>
        let s := Simple.exec fp (.bin op) ⟨stack, sp⟩
        run lim st s.stack s.sp fp (pc + 1) code inst frames g
    | .lcBinSet x c op z =>
      match fuel with
      | f + 3 =>
        let s := Simple.exec fp (.localSet z.toUSize) (Simple.exec fp (.bin op) (Simple.exec fp (.const c)
          (Simple.exec fp (.localGet x.toUSize) ⟨stack, sp⟩)))
        run lim st s.stack s.sp fp (pc + 4) code inst frames f
      | g =>
        let s := Simple.exec fp (.localGet x.toUSize) ⟨stack, sp⟩
        run lim st s.stack s.sp fp (pc + 1) code inst frames g
    | .llBinJump x y op t z =>
      match fuel with
      | f + 3 =>
        let s := Simple.exec fp (.bin op) (Simple.exec fp (.localGet y.toUSize)
          (Simple.exec fp (.localGet x.toUSize) ⟨stack, sp⟩))
        let c := rd s.stack (s.sp - 1)
        run lim st s.stack (s.sp - 1) fp (jumpTo c z t.toUSize (pc + 4)) code inst frames f
      | g =>
        let s := Simple.exec fp (.localGet x.toUSize) ⟨stack, sp⟩
        run lim st s.stack s.sp fp (pc + 1) code inst frames g
    | .lcBinJump x v op t z =>
      match fuel with
      | f + 3 =>
        let s := Simple.exec fp (.bin op) (Simple.exec fp (.const v)
          (Simple.exec fp (.localGet x.toUSize) ⟨stack, sp⟩))
        let c := rd s.stack (s.sp - 1)
        run lim st s.stack (s.sp - 1) fp (jumpTo c z t.toUSize (pc + 4)) code inst frames f
      | g =>
        let s := Simple.exec fp (.localGet x.toUSize) ⟨stack, sp⟩
        run lim st s.stack s.sp fp (pc + 1) code inst frames g
    | .binJump op t z =>
      match fuel with
      | f + 1 =>
        let s := Simple.exec fp (.bin op) ⟨stack, sp⟩
        let c := rd s.stack (s.sp - 1)
        run lim st s.stack (s.sp - 1) fp (jumpTo c z t.toUSize (pc + 2)) code inst frames f
      | g =>
        let s := Simple.exec fp (.bin op) ⟨stack, sp⟩
        run lim st s.stack s.sp fp (pc + 1) code inst frames g
    else (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, .trap (.host "pc out of range"))

/-- Run from a stopped machine. -/
@[inline] def runM (lim : RunLimits) (st : StoreOf M) (m : Machine) (fuel : Nat) :
    StoreOf M × Machine × Nat × Event :=
  run lim st m.stack m.sp m.fp m.pc m.code m.inst m.frames fuel

end
end Run
end L4Factoidal.WasmVM
