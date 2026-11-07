/-
L4Factoidal.WasmVM.Exec.Run: the interpreter loop
(https://github.com/danbri/factoidal/issues/1244).

`run` is ONE function, tail-recursive on its fuel: every case ends in a tail call of
`run` or in a result. Lean compiles it to a C loop with a `switch` on the op, so the
C stack does not grow with Wasm calls (they push a `Frame` on `Machine.frames`) and
`tools/lean-tail-recursion-audit.py` passes it.

Invariants that validation gives and the loop relies on (proof plan, items 4 and 5,
docs/designissues/2026-11-07-wasmvm-engine.md):
- Operand types: slots are untagged bits; an i32 or f32 slot is zero-extended
  ("slot normal form"), so an i32 condition is tested with `!= 0` on the whole slot.
- Heights: a function never uses more than `maxHeight` slots above `fp`, so stack
  room is checked once, at the call.
- Branch targets are in range.

Uniqueness: the store and the machine are passed along and never kept twice, so
`ByteArray.set!` and `Array.modify` update in place (measured in
`Bench/Repr.lean`: a structure updated with `{ m with .. }` costs the same as separate
arguments). The operand stack is `Slots` (see `Exec/Code.lean` for why not `FloatArray`).
-/
import L4Factoidal.WasmVM.Exec.Store

namespace L4Factoidal.WasmVM

structure Frame where
  code : Array Op
  pc : Nat
  fp : Nat
  inst : ModuleInst
  deriving Inhabited

/-- The registers of a run. -/
structure Machine where
  stack : Slots
  sp : Nat
  fp : Nat
  pc : Nat
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

@[inline] def rd (s : Slots) (i : Nat) : UInt64 := Slots.rd s i
@[inline] def wr (s : Slots) (i : Nat) (v : UInt64) : Slots := Slots.wr s i v

/-- Copy `k` slots from `src` to `dst` (`dst ≤ src`), lowest first. -/
def moveDown (s : Slots) (src dst : Nat) : Nat → Slots
  | 0 => s
  | k + 1 => moveDown (wr s dst (rd s src)) (src + 1) (dst + 1) k


def initLocals (s : Slots) (base : Nat) (init : Array UInt64) (i : Nat) : Slots :=
  if h : i < init.size then initLocals (wr s (base + i) init[i]) base init (i + 1) else s
termination_by init.size - i

/-! ### Memory, little-endian -/

@[inline] def rd8 (d : ByteArray) (ea : Nat) : UInt64 :=
  if h : ea < d.size then d[ea].toUInt64 else 0
@[inline] def rd16 (d : ByteArray) (ea : Nat) : UInt64 :=
  if h : ea + 2 ≤ d.size then d[ea].toUInt64 ||| (d[ea + 1].toUInt64 <<< 8) else 0
@[inline] def rd32 (d : ByteArray) (ea : Nat) : UInt64 :=
  if h : ea + 4 ≤ d.size then
    d[ea].toUInt64 ||| (d[ea + 1].toUInt64 <<< 8) ||| (d[ea + 2].toUInt64 <<< 16)
      ||| (d[ea + 3].toUInt64 <<< 24)
  else 0
@[inline] def rd64 (d : ByteArray) (ea : Nat) : UInt64 :=
  if h : ea + 8 ≤ d.size then
    d[ea].toUInt64 ||| (d[ea + 1].toUInt64 <<< 8) ||| (d[ea + 2].toUInt64 <<< 16)
      ||| (d[ea + 3].toUInt64 <<< 24) ||| (d[ea + 4].toUInt64 <<< 32)
      ||| (d[ea + 5].toUInt64 <<< 40) ||| (d[ea + 6].toUInt64 <<< 48)
      ||| (d[ea + 7].toUInt64 <<< 56)
  else 0

def LoadOp.width : LoadOp → Nat
  | .i32 | .f32 | .i64_32s | .i64_32u => 4
  | .i64 | .f64 => 8
  | .i32_8s | .i32_8u | .i64_8s | .i64_8u => 1
  | .i32_16s | .i32_16u | .i64_16s | .i64_16u => 2

/-- The slot bits that a load gives (bounds already checked). -/
def loadVal (d : ByteArray) (ea : Nat) : LoadOp → UInt64
  | .i32 | .f32 | .i64_32u => rd32 d ea
  | .i64 | .f64 => rd64 d ea
  | .i32_8u | .i64_8u => rd8 d ea
  | .i32_16u | .i64_16u => rd16 d ea
  | .i32_8s => (rd8 d ea).toUInt8.toInt8.toInt32.toUInt32.toUInt64
  | .i32_16s => (rd16 d ea).toUInt16.toInt16.toInt32.toUInt32.toUInt64
  | .i64_8s => (rd8 d ea).toUInt8.toInt8.toInt64.toUInt64
  | .i64_16s => (rd16 d ea).toUInt16.toInt16.toInt64.toUInt64
  | .i64_32s => (rd32 d ea).toUInt32.toInt32.toInt64.toUInt64

def wrLE (d : ByteArray) (ea : Nat) (v : UInt64) : Nat → ByteArray
  | 0 => d
  | k + 1 => wrLE (d.set! ea v.toUInt8) (ea + 1) (v >>> 8) k

def fillBytes (d : ByteArray) (ea : Nat) (v : UInt8) : Nat → ByteArray
  | 0 => d
  | k + 1 => fillBytes (d.set! ea v) (ea + 1) v k

/-- Copy within one byte array; correct for overlapping ranges. -/
def copyFwd (d : ByteArray) (src dst : Nat) : Nat → ByteArray
  | 0 => d
  | k + 1 => copyFwd (d.set! dst (d.get! src)) (src + 1) (dst + 1) k
def copyBwd (d : ByteArray) (src dst : Nat) : Nat → ByteArray
  | 0 => d
  | k + 1 => copyBwd (d.set! (dst + k) (d.get! (src + k))) src dst k
def copyWithin (d : ByteArray) (src dst n : Nat) : ByteArray :=
  if dst ≤ src then copyFwd d src dst n else copyBwd d src dst n

def fillArr (a : Array UInt64) (i : Nat) (v : UInt64) : Nat → Array UInt64
  | 0 => a
  | k + 1 => fillArr (a.set! i v) (i + 1) v k

/-- Write `src[s .. s+n)` into `a` at `d`. `src` is a separate array. -/
def copyArr (a : Array UInt64) (src : Array UInt64) (s d : Nat) : Nat → Array UInt64
  | 0 => a
  | k + 1 => copyArr (a.set! d (src[s]!)) src (s + 1) (d + 1) k

def memAddr (m : Machine) (k : Nat) : Nat := m.inst.mems[k]!

/-! ### Branches and calls -/

@[inline] def doBr (m : Machine) (t : BrTarget) : Machine :=
  let dst := m.fp + t.height
  let stack := if m.sp - t.keep == dst then m.stack else moveDown m.stack (m.sp - t.keep) dst t.keep
  { m with stack, sp := dst + t.keep, pc := t.pc }

inductive Enter where
  | ok (m : Machine)
  | host (id fa : Nat) (args : Array UInt64) (m : Machine)
  | trap (t : Trap) (m : Machine)

def argBits (s : Slots) (base n : Nat) : Array UInt64 :=
  (Array.range n).map fun i => rd s (base + i)

/-- Enter function `fa`; the arguments are the top slots; the caller resumes at `retPc`. -/
def enter (lim : RunLimits) (st : Store) (m : Machine) (fa retPc : Nat) : Enter :=
  match st.funcs[fa]? with
  | none => .trap (.host "unknown function address") m
  | some fi =>
    match fi.kind with
    | .host id =>
      let n := fi.type.params.size
      .host id fa (argBits m.stack (m.sp - n) n) { m with sp := m.sp - n, pc := retPc }
    | .wasm ia cf =>
      if m.frames.size ≥ lim.maxDepth then .trap .callStackExhausted m else
      let fp := m.sp - cf.nParams
      let need := fp + cf.maxHeight + 1
      if need > lim.maxSlots then .trap .callStackExhausted m else
      let stack := if need > m.stack.count then Slots.grow m.stack (max need (2 * m.stack.count) - m.stack.count)
        else m.stack
      let stack := initLocals stack (fp + cf.nParams) cf.localInit 0
      .ok { stack, sp := fp + cf.nLocals, fp, pc := 0, code := cf.code, inst := st.insts[ia]!,
            frames := m.frames.push { code := m.code, pc := retPc, fp := m.fp, inst := m.inst } }

/-! ### The loop -/

def run (lim : RunLimits) (st : Store) (m : Machine) : Nat → Store × Machine × Nat × Event
  | 0 => (st, m, 0, .outOfFuel)
  | fuel + 1 =>
    if h : m.pc < m.code.size then
    let sp := m.sp
    match m.code[m.pc] with
    | .unreachable => (st, m, fuel, .trap .unreachable)
    | .jump pc => run lim st { m with pc } fuel
    | .jumpIf pc =>
      let c := rd m.stack (sp - 1)
      run lim st { m with sp := sp - 1, pc := if c != 0 then pc else m.pc + 1 } fuel
    | .jumpUnless pc =>
      let c := rd m.stack (sp - 1)
      run lim st { m with sp := sp - 1, pc := if c == 0 then pc else m.pc + 1 } fuel
    | .br t => run lim st (doBr m t) fuel
    | .brIf t =>
      let c := rd m.stack (sp - 1)
      let m := { m with sp := sp - 1 }
      if c != 0 then run lim st (doBr m t) fuel else run lim st { m with pc := m.pc + 1 } fuel
    | .brTable ts d =>
      let i := (rd m.stack (sp - 1)).toNat
      let t := if h : i < ts.size then ts[i] else d
      run lim st (doBr { m with sp := sp - 1 } t) fuel
    | .return_ k =>
      let stack := if sp - k == m.fp then m.stack else moveDown m.stack (sp - k) m.fp k
      let sp := m.fp + k
      if m.frames.isEmpty then (st, { m with stack, sp }, fuel, .done) else
      let f := m.frames.back!
      run lim st { m with stack, sp, frames := m.frames.pop, code := f.code, pc := f.pc,
                          fp := f.fp, inst := f.inst } fuel
    | .call f =>
      let fa := m.inst.funcs[f]!
      match enter lim st m fa (m.pc + 1) with
      | .ok m => run lim st m fuel
      | .host id fa args m => (st, m, fuel, .hostCall id fa args)
      | .trap t m => (st, m, fuel, .trap t)
    | .callIndirect ti x =>
      let i := (rd m.stack (sp - 1)).toNat
      let tab := st.tables[m.inst.tables[x]!]!
      if i ≥ tab.elems.size then (st, m, fuel, .trap .undefinedElement) else
      let r := tab.elems[i]!
      if r == nullRef then (st, m, fuel, .trap .uninitializedElement) else
      let fa := r.toNat
      if (st.funcs[fa]!).typeId != m.inst.typeIds[ti]! then (st, m, fuel, .trap .indirectTypeMismatch) else
      match enter lim st { m with sp := sp - 1 } fa (m.pc + 1) with
      | .ok m => run lim st m fuel
      | .host id fa args m => (st, m, fuel, .hostCall id fa args)
      | .trap t m => (st, m, fuel, .trap t)
    | .drop => run lim st { m with sp := sp - 1, pc := m.pc + 1 } fuel
    | .select =>
      let c := rd m.stack (sp - 1)
      let stack := if c != 0 then m.stack else wr m.stack (sp - 3) (rd m.stack (sp - 2))
      run lim st { m with stack, sp := sp - 2, pc := m.pc + 1 } fuel
    | .localGet x =>
      run lim st { m with stack := wr m.stack sp (rd m.stack (m.fp + x)), sp := sp + 1,
                          pc := m.pc + 1 } fuel
    | .localSet x =>
      run lim st { m with stack := wr m.stack (m.fp + x) (rd m.stack (sp - 1)), sp := sp - 1,
                          pc := m.pc + 1 } fuel
    | .localTee x =>
      run lim st { m with stack := wr m.stack (m.fp + x) (rd m.stack (sp - 1)),
                          pc := m.pc + 1 } fuel
    | .globalGet x =>
      let v := st.globalBits m.inst.globals[x]!
      run lim st { m with stack := wr m.stack sp v, sp := sp + 1, pc := m.pc + 1 } fuel
    | .globalSet x =>
      let v := rd m.stack (sp - 1)
      let st := { st with globals := Slots.wr st.globals m.inst.globals[x]! v }
      run lim st { m with sp := sp - 1, pc := m.pc + 1 } fuel
    | .tableGet x =>
      let i := (rd m.stack (sp - 1)).toNat
      let tab := st.tables[m.inst.tables[x]!]!
      if h : i < tab.elems.size then
        run lim st { m with stack := wr m.stack (sp - 1) tab.elems[i], pc := m.pc + 1 } fuel
      else (st, m, fuel, .trap .tableOOB)
    | .tableSet x =>
      let v := rd m.stack (sp - 1)
      let i := (rd m.stack (sp - 2)).toNat
      let ta := m.inst.tables[x]!
      if i < (st.tables[ta]!).elems.size then
        let st := { st with tables := st.tables.modify ta fun t => { t with elems := t.elems.set! i v } }
        run lim st { m with sp := sp - 2, pc := m.pc + 1 } fuel
      else (st, m, fuel, .trap .tableOOB)
    | .tableSize x =>
      let n := (st.tables[m.inst.tables[x]!]!).elems.size
      run lim st { m with stack := wr m.stack sp n.toUInt64, sp := sp + 1, pc := m.pc + 1 } fuel
    | .tableGrow x =>
      let n := (rd m.stack (sp - 1)).toNat
      let v := rd m.stack (sp - 2)
      let ta := m.inst.tables[x]!
      let tab := st.tables[ta]!
      let old := tab.elems.size
      let cap := min (tab.max.getD 4294967295) 10000000
      if old + n ≤ cap then
        let st := { st with tables := st.tables.modify ta fun t => { t with elems := t.elems ++ Array.replicate n v } }
        run lim st { m with stack := wr m.stack (sp - 2) old.toUInt64, sp := sp - 1, pc := m.pc + 1 } fuel
      else
        run lim st { m with stack := wr m.stack (sp - 2) 0xFFFFFFFF, sp := sp - 1, pc := m.pc + 1 } fuel
    | .tableFill x =>
      let n := (rd m.stack (sp - 1)).toNat
      let v := rd m.stack (sp - 2)
      let i := (rd m.stack (sp - 3)).toNat
      let ta := m.inst.tables[x]!
      if i + n > (st.tables[ta]!).elems.size then (st, m, fuel, .trap .tableOOB) else
      let st := { st with tables := st.tables.modify ta fun t => { t with elems := fillArr t.elems i v n } }
      run lim st { m with sp := sp - 3, pc := m.pc + 1 } fuel
    | .tableCopy dx sx =>
      let n := (rd m.stack (sp - 1)).toNat
      let s := (rd m.stack (sp - 2)).toNat
      let d := (rd m.stack (sp - 3)).toNat
      let td := m.inst.tables[dx]!
      let src := (st.tables[m.inst.tables[sx]!]!).elems
      if s + n > src.size || d + n > (st.tables[td]!).elems.size then (st, m, fuel, .trap .tableOOB) else
      let slice := src.extract s (s + n)
      let st := { st with tables := st.tables.modify td fun t => { t with elems := copyArr t.elems slice 0 d n } }
      run lim st { m with sp := sp - 3, pc := m.pc + 1 } fuel
    | .tableInit x e =>
      let n := (rd m.stack (sp - 1)).toNat
      let s := (rd m.stack (sp - 2)).toNat
      let d := (rd m.stack (sp - 3)).toNat
      let ta := m.inst.tables[x]!
      let seg := st.elems[m.inst.elems[e]!]!
      if s + n > seg.size || d + n > (st.tables[ta]!).elems.size then (st, m, fuel, .trap .tableOOB) else
      let st := { st with tables := st.tables.modify ta fun t => { t with elems := copyArr t.elems seg s d n } }
      run lim st { m with sp := sp - 3, pc := m.pc + 1 } fuel
    | .elemDrop e =>
      let st := { st with elems := st.elems.set! m.inst.elems[e]! #[] }
      run lim st { m with pc := m.pc + 1 } fuel
    | .load op mem off =>
      let ea := (rd m.stack (sp - 1)).toNat + off
      let d := (st.mems[memAddr m mem]!).data
      if ea + LoadOp.width op ≤ d.size then
        run lim st { m with stack := wr m.stack (sp - 1) (loadVal d ea op), pc := m.pc + 1 } fuel
      else (st, m, fuel, .trap .memOOB)
    | .store op mem off =>
      let v := rd m.stack (sp - 1)
      let ea := (rd m.stack (sp - 2)).toNat + off
      let ma := memAddr m mem
      let w := op.width
      if ea + w ≤ (st.mems[ma]!).data.size then
        let st := { st with mems := st.mems.modify ma fun mi => { mi with data := wrLE mi.data ea v w } }
        run lim st { m with sp := sp - 2, pc := m.pc + 1 } fuel
      else (st, m, fuel, .trap .memOOB)
    | .memorySize mem =>
      let n := (st.mems[memAddr m mem]!).data.size / pageSize
      run lim st { m with stack := wr m.stack sp n.toUInt64, sp := sp + 1, pc := m.pc + 1 } fuel
    | .memoryGrow mem =>
      let n := (rd m.stack (sp - 1)).toNat
      let ma := memAddr m mem
      let mi := st.mems[ma]!
      let old := mi.data.size / pageSize
      let cap := min (mi.max.getD 65536) st.pageLimit
      if old + n ≤ cap then
        let st := if n == 0 then st else
          { st with mems := st.mems.modify ma fun mi => { mi with data := mi.data ++ Store.zeros (n * pageSize) } }
        run lim st { m with stack := wr m.stack (sp - 1) old.toUInt64, pc := m.pc + 1 } fuel
      else
        run lim st { m with stack := wr m.stack (sp - 1) 0xFFFFFFFF, pc := m.pc + 1 } fuel
    | .memoryInit di mem =>
      let n := (rd m.stack (sp - 1)).toNat
      let s := (rd m.stack (sp - 2)).toNat
      let d := (rd m.stack (sp - 3)).toNat
      let ma := memAddr m mem
      let src := st.datas[m.inst.datas[di]!]!
      if s + n > src.size || d + n > (st.mems[ma]!).data.size then (st, m, fuel, .trap .memOOB) else
      let st := { st with mems := st.mems.modify ma fun mi => { mi with data := src.copySlice s mi.data d n } }
      run lim st { m with sp := sp - 3, pc := m.pc + 1 } fuel
    | .dataDrop di =>
      let st := { st with datas := st.datas.set! m.inst.datas[di]! ByteArray.empty }
      run lim st { m with pc := m.pc + 1 } fuel
    | .memoryCopy dm sm =>
      let n := (rd m.stack (sp - 1)).toNat
      let s := (rd m.stack (sp - 2)).toNat
      let d := (rd m.stack (sp - 3)).toNat
      let da := memAddr m dm
      let sa := memAddr m sm
      if s + n > (st.mems[sa]!).data.size || d + n > (st.mems[da]!).data.size then
        (st, m, fuel, .trap .memOOB) else
      let st := if da == sa then
          { st with mems := st.mems.modify da fun mi => { mi with data := copyWithin mi.data s d n } }
        else
          let src := (st.mems[sa]!).data
          { st with mems := st.mems.modify da fun mi => { mi with data := src.copySlice s mi.data d n } }
      run lim st { m with sp := sp - 3, pc := m.pc + 1 } fuel
    | .memoryFill mem =>
      let n := (rd m.stack (sp - 1)).toNat
      let v := (rd m.stack (sp - 2)).toUInt8
      let d := (rd m.stack (sp - 3)).toNat
      let ma := memAddr m mem
      if d + n > (st.mems[ma]!).data.size then (st, m, fuel, .trap .memOOB) else
      let st := { st with mems := st.mems.modify ma fun mi => { mi with data := fillBytes mi.data d v n } }
      run lim st { m with sp := sp - 3, pc := m.pc + 1 } fuel
    | .const v => run lim st { m with stack := wr m.stack sp v, sp := sp + 1, pc := m.pc + 1 } fuel
    | .refIsNull =>
      let v := rd m.stack (sp - 1)
      run lim st { m with stack := wr m.stack (sp - 1) (if v == nullRef then 1 else 0), pc := m.pc + 1 } fuel
    | .refFunc f =>
      let a := m.inst.funcs[f]!
      run lim st { m with stack := wr m.stack sp a.toUInt64, sp := sp + 1, pc := m.pc + 1 } fuel
    | .num op =>
      if op.isBinary then
        let b := rd m.stack (sp - 1)
        let a := rd m.stack (sp - 2)
        match (if op.mayTrap then op.trapBin a b else none) with
        | some t => (st, m, fuel, .trap t)
        | none =>
          run lim st { m with stack := wr m.stack (sp - 2) (op.evalBin a b), sp := sp - 1,
                              pc := m.pc + 1 } fuel
      else
        let a := rd m.stack (sp - 1)
        match (if op.mayTrap then op.trapUn a else none) with
        | some t => (st, m, fuel, .trap t)
        | none => run lim st { m with stack := wr m.stack (sp - 1) (op.evalUn a), pc := m.pc + 1 } fuel
    else (st, m, fuel, .trap (.host "pc out of range"))

end Run
end L4Factoidal.WasmVM
