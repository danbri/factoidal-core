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
import L4Factoidal.WasmVM.Simd

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
  /-- An exception (store address `exn`) that no handler caught. -/
  | exception (exn : Nat)
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

/-- One straight-line op. The slots and `sp` are separate arguments: with an `SP`
argument the compiler allocated the pair on one path (`lUn`, seen in the C). -/
@[inline] def Simple.exec (fp : USize) : Simple → Slots → USize → SP
  | .localGet x, s, sp => ⟨wr s sp (rd s (fp + x)), sp + 1⟩
  | .localSet x, s, sp => ⟨wr s (fp + x) (rd s (sp - 1)), sp - 1⟩
  | .localTee x, s, sp => ⟨wr s (fp + x) (rd s (sp - 1)), sp⟩
  | .const v, s, sp => ⟨wr s sp v, sp + 1⟩
  | .bin op, s, sp => ⟨wr s (sp - 2) (op.evalBin (rd s (sp - 2)) (rd s (sp - 1))), sp - 1⟩
  | .un op, s, sp => ⟨wr s (sp - 1) (op.evalUn (rd s (sp - 1))), sp⟩
  | .drop, s, sp => ⟨s, sp - 1⟩

/-- One straight-line op after others. -/
@[inline] def Simple.next (fp : USize) (o : Simple) (x : SP) : SP := o.exec fp x.stack x.sp

/-- Run a list of simple ops in order. -/
def Simple.execAll (fp : USize) (ops : List Simple) (x : SP) : SP :=
  ops.foldl (fun x o => o.next fp x) x

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

/-! ### Exceptions

A function's handler table (`handlersOf`, built by the validator) lists its `try`
ranges. To raise exception `exn` at pc `pc`: take the innermost entry that holds `pc`,
test its catches in order, then the entries its `next` links name; when none catches,
pop a frame and search the caller from its call site (the frame's return pc minus 1).
Nothing of this runs unless an exception is raised: the normal path has no handler
stack to push or pop. Record: "Exception handling" in
docs/designissues/2026-11-07-wasmvm-engine.md. -/

/-- The innermost entry among `hs[0..i)` whose range holds `pc`. Entries are in the
order their `try` starts and ranges nest, so it is the last one that holds `pc`. -/
def innermost (hs : Array Handler) (pc : Nat) : Nat → Option Nat
  | 0 => none
  | i + 1 =>
    match hs[i]? with
    | some h => if h.start ≤ pc && pc < h.stop then some i else innermost hs pc i
    | none => none

/-- The first catch that takes an exception of tag address `ta`. -/
def catchFor (ta : Nat) (inst : ModuleInst) (cs : Array CatchTarget) : Option CatchTarget :=
  cs.find? fun c => match c.tag with
    | none => true
    | some x => inst.tags[x]? == some ta

/-- Test entry `e`, then the entries its `next` links name (each names an earlier
entry; `k` bounds the walk). -/
def searchChain (ta : Nat) (inst : ModuleInst) (hs : Array Handler) : Nat → Option Nat → Option CatchTarget
  | 0, _ => none
  | _, none => none
  | k + 1, some e =>
    match hs[e]? with
    | none => none
    | some h =>
      match catchFor ta inst h.catches with
      | some c => some c
      | none => searchChain ta inst hs k h.next

/-- Write `vs[i..]` into slots from `p`; gives the slots and the next slot. -/
def writeVals (s : Slots) (vs : Array UInt64) (p : USize) (i : Nat) : Slots × USize :=
  if h : i < vs.size then writeVals (wr s p vs[i]) vs (p + 1) (i + 1) else (s, p)
termination_by vs.size - i

/-- Put a caught exception's values where its handler wants them; gives the slots and `sp`. -/
def deliver (s : Slots) (fp : USize) (c : CatchTarget) (exn : Nat) (fields : Array UInt64) : Slots × USize :=
  let p := fp + c.height.toUSize
  let (s, p) := if c.exnBelow then (wr s p exn.toUInt64, p + 1) else (s, p)
  let (s, p) := if c.payload then writeVals s fields p 0 else (s, p)
  if c.exnAbove then (wr s p exn.toUInt64, p + 1) else (s, p)

/-- Where an exception went. -/
inductive Unwound where
  | caught (stack : Slots) (sp fp pc : USize) (code : Array Op) (inst : ModuleInst) (frames : Array Frame)
  | uncaught

/-- Unwind exception `exn` (tag address `ta`, payload `fields`) from pc `pc` of the
running function; `k` bounds the frames popped. -/
def unwind (exn ta : Nat) (fields : Array UInt64) (stack : Slots) (fp : USize) (pc : Nat)
    (code : Array Op) (inst : ModuleInst) (frames : Array Frame) : Nat → Unwound
  | 0 => .uncaught
  | k + 1 =>
    let hs := handlersOf code
    match searchChain ta inst hs (hs.size + 1) (innermost hs pc hs.size) with
    | some c =>
      let (stack, sp) := deliver stack fp c exn fields
      .caught stack sp fp c.pc.toUSize code inst frames
    | none =>
      if frames.isEmpty then .uncaught else
      let f := frames.back!
      unwind exn ta fields stack f.fp (f.pc.toNat - 1) f.code f.inst frames.pop k

section
variable {M : Type} [LinearMemory M]

/-- Raise exception `exn` of the store at pc `pc`. -/
@[noinline] def raise (st : StoreOf M) (exn : Nat) (stack : Slots) (fp pc : USize)
    (code : Array Op) (inst : ModuleInst) (frames : Array Frame) : Unwound :=
  match st.exc.exns[exn]? with
  | some e => unwind exn e.tag e.fields stack fp pc.toNat code inst frames (frames.size + 1)
  | none => .uncaught

/-- What a tail call gives: the frame stack and `fp` stay as they are. -/
inductive TailEnter where
  | ok (stack : Slots) (sp : USize) (code : Array Op) (inst : ModuleInst)
  | host (id fa : Nat) (args : Array UInt64) (stack : Slots) (sp : USize)
  | trap (t : Trap) (stack : Slots)

/-- Tail call of function `fa`: the arguments (the top slots) move down to `fp`, and
the callee runs in the caller's frame. The frame stack does not grow. A host callee
is an ordinary host call; the `return_` after the tail call op returns its results. -/
@[noinline] def enterTail (lim : RunLimits) (st : StoreOf M) (stack : Slots) (sp fp : USize) (fa : Nat) : TailEnter :=
  match st.funcs[fa]? with
  | none => .trap (.host "unknown function address") stack
  | some fi =>
    match fi.kind with
    | .host id =>
      let n := fi.type.params.size
      .host id fa (argBits stack (sp - n.toUSize) n) stack (sp - n.toUSize)
    | .wasm ia cf =>
      let n := cf.nParams.toUSize
      let need := fp.toNat + cf.maxHeight + 1
      if need > lim.maxSlots then .trap .callStackExhausted stack else
      let stack := if sp - n == fp then stack else moveDown stack (sp - n) fp cf.nParams
      let stack := if need > stack.count then Slots.grow stack (max need (2 * stack.count) - stack.count)
        else stack
      let stack := initLocals stack (fp + n) cf.localInit 0
      .ok stack (fp + cf.nLocals.toUSize) cf.code (st.insts[ia]!)

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

/-- `enter`, not inlined: for the calls that are not on the hot path (`call_ref`). -/
@[noinline] def enterCold (lim : RunLimits) (st : StoreOf M) (stack : Slots) (sp fp : USize) (code : Array Op)
    (inst : ModuleInst) (frames : Array Frame) (fa : Nat) (retPc : USize) : Enter :=
  enter lim st stack sp fp code inst frames fa retPc

/-! ### Fixed-width SIMD

A v128 value at slot `i` has its low half in the operand stack and its high half in
slot `i` of the hi stack (`st.exc.hi`). Everything here is reached from `cold`.
Record: "SIMD" in docs/designissues/2026-11-07-wasmvm-engine.md. -/

@[inline] def hiRd (st : StoreOf M) (i : USize) : UInt64 := Slots.rd st.exc.hi i

@[inline] def hiWr (st : StoreOf M) (i : USize) (v : UInt64) : StoreOf M :=
  st.modHi (fun h => Slots.wrGrow h i v) id

/-- The v128 value at slot `i`. -/
@[inline] def vAt (st : StoreOf M) (stack : Slots) (i : USize) : V128 := ⟨rd stack i, hiRd st i⟩

/-- Move the high halves of `n` slots from `src` down to `dst`. A slot past the end
of the hi stack is 0, and `dst ≤ src`, so nothing is lost when the hi stack is short;
when it is empty no v128 was ever written and there is nothing to move. -/
def hiMoveDown (st : StoreOf M) (src dst : USize) (n : Nat) : StoreOf M :=
  if st.exc.hi.size == 0 || src == dst then st else st.modHi (fun h => moveDown h src dst n) id

/-- Write 0 into `n` slots from `i`. -/
def zeroSlots (s : Slots) (i : USize) : Nat → Slots
  | 0 => s
  | k + 1 => zeroSlots (wr s i 0) (i + 1) k

def hiZero (st : StoreOf M) (i : USize) (n : Nat) : StoreOf M :=
  if st.exc.hi.size == 0 then st else st.modHi (fun h => zeroSlots h i n) id

/-- What a SIMD instruction gives. -/
inductive SimdRes (M : Type) where
  | ok (st : StoreOf M) (stack : Slots) (sp : USize)
  | trap (st : StoreOf M) (stack : Slots) (t : Trap)

/-- The scalar load and store of `w` bytes (1, 2, 4 or 8), zero-extended. -/
def simdLoadOp (w : Nat) : LoadOp :=
  if w == 1 then .i32_8u else if w == 2 then .i32_16u else if w == 4 then .i32 else .i64
def simdStoreOp (w : Nat) : StoreOp :=
  if w == 1 then .i32_8 else if w == 2 then .i32_16 else if w == 4 then .i32 else .i64

/-- A checked load. -/
def loadW (d : M) (ea : Nat) (op : LoadOp) : Option UInt64 :=
  if h : ea + LoadOp.width op ≤ LinearMemory.size d then some (loadVal d ea op h) else none

/-- Write the v128 `r` at slot `i`. -/
@[inline] def putV (st : StoreOf M) (stack : Slots) (i sp : USize) (r : V128) : SimdRes M :=
  .ok (hiWr st i r.hi) (wr stack i r.lo) sp

/-- One SIMD instruction with no 16-byte immediate (`Op.simd`). -/
@[noinline] def simdStepGeneric (st : StoreOf M) (stack : Slots) (sp : USize) (inst : ModuleInst)
    (c mem off lane : Nat) : SimdRes M :=
  match simdShape c with
  | some .un => putV st stack (sp - 1) sp (V128.evalUn c (vAt st stack (sp - 1)))
  | some .bin => putV st stack (sp - 2) (sp - 1) (V128.evalBin c (vAt st stack (sp - 2)) (vAt st stack (sp - 1)))
  | some .tern =>
    putV st stack (sp - 3) (sp - 2)
      (V128.bitselect (vAt st stack (sp - 3)) (vAt st stack (sp - 2)) (vAt st stack (sp - 1)))
  | some .test => .ok st (wr stack (sp - 1) (V128.evalTest c (vAt st stack (sp - 1)))) sp
  | some .shift => putV st stack (sp - 2) (sp - 1) (V128.evalShift c (vAt st stack (sp - 2)) (rd stack (sp - 1)))
  | some (.splat _) => putV st stack (sp - 1) sp (V128.splat c (rd stack (sp - 1)))
  | some (.extract ..) => .ok st (wr stack (sp - 1) (V128.extract c lane (vAt st stack (sp - 1)))) sp
  | some (.replace ..) =>
    putV st stack (sp - 2) (sp - 1) (V128.replace c lane (vAt st stack (sp - 2)) (rd stack (sp - 1)))
  | some (.load w) =>
    let ea := (rd stack (sp - 1)).toNat + off
    let d := memData st inst mem
    if w == 16 then
      match loadW d ea .i64, loadW d (ea + 8) .i64 with
      | some lo, some hi => putV st stack (sp - 1) sp ⟨lo, hi⟩
      | _, _ => .trap st stack .memOOB
    else
      match loadW d ea (simdLoadOp w) with
      | some x => putV st stack (sp - 1) sp (V128.ofLoad c x)
      | none => .trap st stack .memOOB
  | some .store =>
    let v := vAt st stack (sp - 1)
    let ea := (rd stack (sp - 2)).toNat + off
    let ma := inst.mems[mem]!
    if ea + 16 ≤ LinearMemory.size (st.mems[ma]!).data then
      .ok (storeMem (storeMem st ma ea v.lo .i64) ma (ea + 8) v.hi .i64) stack (sp - 2)
    else .trap st stack .memOOB
  | some (.loadLane w) =>
    let v := vAt st stack (sp - 1)
    let ea := (rd stack (sp - 2)).toNat + off
    match loadW (memData st inst mem) ea (simdLoadOp w) with
    | some x => putV st stack (sp - 2) (sp - 1) (v.setLane (8 * w) lane x)
    | none => .trap st stack .memOOB
  | some (.storeLane w) =>
    let v := vAt st stack (sp - 1)
    let ea := (rd stack (sp - 2)).toNat + off
    let ma := inst.mems[mem]!
    if ea + w ≤ LinearMemory.size (st.mems[ma]!).data then
      .ok (storeMem st ma ea (v.lane (8 * w) lane) (simdStoreOp w)) stack (sp - 2)
    else .trap st stack .memOOB
  | _ => .trap st stack .unreachable

/-- The reference SIMD step, kept separate from the dispatch implementation so
its compiled replacement can reuse the generic fallback without replacing itself. -/
@[inline] def simdStep (st : StoreOf M) (stack : Slots) (sp : USize) (inst : ModuleInst)
    (c mem off lane : Nat) : SimdRes M :=
  simdStepGeneric st stack sp inst c mem off lane

/-- Bitwise SIMD instructions avoid the shape and lane-operation dispatchers.
All other instructions retain the plain interpreter, including its traps. -/
@[noinline] def simdStepFast (st : StoreOf M) (stack : Slots) (sp : USize) (inst : ModuleInst)
    (c mem off lane : Nat) : SimdRes M :=
  match c with
  | 0x4d =>
    let a := vAt st stack (sp - 1)
    putV st stack (sp - 1) sp ⟨~~~a.lo, ~~~a.hi⟩
  | 0x4e =>
    let a := vAt st stack (sp - 2)
    let b := vAt st stack (sp - 1)
    putV st stack (sp - 2) (sp - 1) ⟨a.lo &&& b.lo, a.hi &&& b.hi⟩
  | 0x4f =>
    let a := vAt st stack (sp - 2)
    let b := vAt st stack (sp - 1)
    putV st stack (sp - 2) (sp - 1) ⟨a.lo &&& ~~~b.lo, a.hi &&& ~~~b.hi⟩
  | 0x50 =>
    let a := vAt st stack (sp - 2)
    let b := vAt st stack (sp - 1)
    putV st stack (sp - 2) (sp - 1) ⟨a.lo ||| b.lo, a.hi ||| b.hi⟩
  | 0x51 =>
    let a := vAt st stack (sp - 2)
    let b := vAt st stack (sp - 1)
    putV st stack (sp - 2) (sp - 1) ⟨a.lo ^^^ b.lo, a.hi ^^^ b.hi⟩
  | _ => simdStepGeneric st stack sp inst c mem off lane

/-- Optimization refinement.
Says: specialized bitwise dispatch returns exactly the same store, both stack
halves, stack pointer and trap as `simdStep`, for every input and memory backend.
Does not say: SIMD follows an external Wasm specification or any host is faster. -/
@[csimp] theorem simdStep_eq_fast : @simdStep = @simdStepFast := by
  funext M lm st stack sp inst c mem off lane
  unfold simdStepFast
  split
  · simp [simdStep, simdStepGeneric, simdShape, V128.evalUn]
  · simp [simdStep, simdStepGeneric, simdShape, V128.evalBin]
  · simp [simdStep, simdStepGeneric, simdShape, V128.evalBin]
  · simp [simdStep, simdStepGeneric, simdShape, V128.evalBin]
  · simp [simdStep, simdStepGeneric, simdShape, V128.evalBin]
  · rfl

/-! ### Garbage collection

Structs and arrays are `Obj`s in `st.exc.gc.objs`; a reference is one slot
(`Exec/Code.lean`, "Reference bits"). Everything here is reached from `cold`. Record:
"GC" in docs/designissues/2026-11-07-wasmvm-engine.md. -/

/-- Most elements of one array (an engine limit: 512 MiB of slots). -/
def maxArrayLen : Nat := 1 <<< 26

/-- The bits kept in an object slot for pack code `p` (`packCode`). -/
@[inline] def packBits (p : Nat) (v : UInt64) : UInt64 :=
  if p == 1 then v &&& 0xFF else if p == 2 then v &&& 0xFFFF else v

/-- A packed slot sign-extended to an i32. -/
def unpackSigned (p : Nat) (v : UInt64) : UInt64 :=
  if p == 1 then v.toUInt8.toInt8.toInt32.toUInt32.toUInt64
  else if p == 2 then v.toUInt16.toInt16.toInt32.toUInt32.toUInt64 else v

/-- Write `v` into `n` slots from `i`. -/
def fillSlots (s : Slots) (i : USize) (v : UInt64) : Nat → Slots
  | 0 => s
  | k + 1 => fillSlots (wr s i v) (i + 1) v k

/-- `n` slots that all hold `v`. -/
def newSlots (n : Nat) (v : UInt64) : Slots :=
  if v == 0 then Slots.zeros n else fillSlots (Slots.zeros n) 0 v n

/-- Copy `fs.size` operand-stack slots from `base` into `d`, each cut to its field's
storage type. -/
def packFields (d stack : Slots) (base : USize) (fs : Array FieldType) (i : Nat) : Slots :=
  if h : i < fs.size then
    packFields (wr d i.toUSize (packBits (packCode fs[i].type) (rd stack (base + i.toUSize)))) stack base fs (i + 1)
  else d
termination_by fs.size - i

/-- Copy `n` operand-stack slots from `base` into `d` at `i`, cut for pack code `p`. -/
def packSlots (d stack : Slots) (base : USize) (p : Nat) (i : USize) : Nat → Slots
  | 0 => d
  | k + 1 => packSlots (wr d i (packBits p (rd stack (base + i)))) stack base p (i + 1) k

/-- `w` little-endian bytes of `b` at `p` (0 for a byte past the end). -/
def leBytes (b : ByteArray) (p : Nat) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => leBytes b p k ((acc <<< 8) ||| (b.get! (p + k)).toUInt64)

/-- Write `n` elements of `w` bytes each, read from `src` at byte `off`, into `d` at `i`. -/
def dataSlots (d : Slots) (src : ByteArray) (off w : Nat) (i : USize) : Nat → Slots
  | 0 => d
  | k + 1 => dataSlots (wr d i (leBytes src off w 0)) src (off + w) w (i + 1) k

/-- Write `seg[s .. s+n)` into `d` at `i`. -/
def elemSlots (d : Slots) (seg : Array UInt64) (s : Nat) (i : USize) : Nat → Slots
  | 0 => d
  | k + 1 => elemSlots (wr d i seg[s]!) seg (s + 1) (i + 1) k

/-- The composite type of module type `x`, from the store. -/
def gcComp (st : StoreOf M) (inst : ModuleInst) (x : Nat) : CompType :=
  match st.gcType? inst.typeIds[x]! with
  | some t => t.comp
  | none => .struct #[]

/-- The default bits of a field. -/
def defaultBits : StorageType → UInt64
  | .val t => t.zeroBits
  | _ => 0

/-- Whether reference `r` has heap type `h` (a `heapCode`), or is null and `nullable`.
Validation gives that `r` is of the hierarchy of `h`. -/
def refMatches (st : StoreOf M) (inst : ModuleInst) (r : UInt64) (nullable : Bool) (h : Nat) : Bool :=
  if r == nullRef then nullable
  -- func, extern, any, exn: every value of the hierarchy.
  else if h == 0 || h == 1 || h == 2 || h == 10 then true
  -- none, nofunc, noextern, noexn: no value.
  else if h == 7 || h == 8 || h == 9 || h == 11 then false
  else if h == 3 then r &&& hostTag == 0
  else if h == 4 then r &&& i31Tag != 0
  else if h == 5 || h == 6 then
    refIsObj r && (match st.obj? r.toNat with
      | some o => st.idKind o.type == h - 4
      | none => false)
  else
    let id := inst.typeIds[h - 12]!
    if st.idKind id == 0 then
      match st.funcs[r.toNat]? with
      | some fi => st.isSubId fi.typeId id
      | none => false
    else
      refIsObj r && (match st.obj? r.toNat with
        | some o => st.isSubId o.type id
        | none => false)

def trapNullStruct : Trap := .host "null structure reference"
def trapNullArray : Trap := .host "null array reference"
def trapNullI31 : Trap := .host "null i31 reference"
def trapArrayOOB : Trap := .host "out of bounds array access"
def trapCast : Trap := .host "cast failure"
def trapArrayLimit : Trap := .host "array larger than the engine limit"

/-- One garbage-collection op (`Op.gc code a b c`). The fields, by code (`GcCode`):
`struct.new`: type, field count. `struct.new_default`: type. `struct.get*`, `struct.set`:
field index, pack code. `array.new`: type, pack code. `array.new_default`: type, 1 when
the element is a reference. `array.new_fixed`: type, length, pack code. `array.new_data`:
type, data index, element bytes. `array.new_elem`: type, element segment.
`array.get*`, `array.set`, `array.fill`: nothing, pack code. `array.init_data`: nothing,
data index, element bytes. `array.init_elem`: nothing, element segment. `ref.test`,
`ref.cast`: heap code, 1 when null matches. -/
@[noinline] def gcStep (st : StoreOf M) (stack : Slots) (sp : USize) (inst : ModuleInst)
    (c a b x : Nat) : SimdRes M :=
  if c == GcCode.structNew then
    let base := sp - b.toUSize
    let fs := match gcComp st inst a with | .struct fs => fs | _ => #[]
    let (st, addr) := st.allocObj inst.typeIds[a]! (packFields (Slots.zeros b) stack base fs 0)
    .ok st (wr stack base addr.toUInt64) (base + 1)
  else if c == GcCode.structNewDefault then
    let fs := match gcComp st inst a with | .struct fs => fs | _ => #[]
    let (st, addr) := st.allocObj inst.typeIds[a]! (fs.foldl (fun d f => d.push (defaultBits f.type)) ByteArray.empty)
    .ok st (wr stack sp addr.toUInt64) (sp + 1)
  else if c == GcCode.structGet || c == GcCode.structGetS || c == GcCode.structGetU then
    let r := rd stack (sp - 1)
    if r == nullRef then .trap st stack trapNullStruct else
    match st.obj? r.toNat with
    | none => .trap st stack trapNullStruct
    | some o =>
      let v := rd o.data a.toUSize
      .ok st (wr stack (sp - 1) (if c == GcCode.structGetS then unpackSigned b v else v)) sp
  else if c == GcCode.structSet then
    let r := rd stack (sp - 2)
    let v := packBits b (rd stack (sp - 1))
    if r == nullRef then .trap st stack trapNullStruct else
    .ok (st.modObj r.toNat fun d => wr d a.toUSize v) stack (sp - 2)
  else if c == GcCode.arrayNew then
    let n := (rd stack (sp - 1)).toNat
    if n > maxArrayLen then .trap st stack trapArrayLimit else
    let (st, addr) := st.allocObj inst.typeIds[a]! (newSlots n (packBits b (rd stack (sp - 2))))
    .ok st (wr stack (sp - 2) addr.toUInt64) (sp - 1)
  else if c == GcCode.arrayNewDefault then
    let n := (rd stack (sp - 1)).toNat
    if n > maxArrayLen then .trap st stack trapArrayLimit else
    let (st, addr) := st.allocObj inst.typeIds[a]! (newSlots n (if b == 1 then nullRef else 0))
    .ok st (wr stack (sp - 1) addr.toUInt64) sp
  else if c == GcCode.arrayNewFixed then
    let base := sp - b.toUSize
    let (st, addr) := st.allocObj inst.typeIds[a]! (packSlots (Slots.zeros b) stack base x 0 b)
    .ok st (wr stack base addr.toUInt64) (base + 1)
  else if c == GcCode.arrayNewData then
    let n := (rd stack (sp - 1)).toNat
    let off := (rd stack (sp - 2)).toNat
    let src := st.datas[inst.datas[b]!]!
    if off + n * x > src.size then .trap st stack .memOOB else
    let (st, addr) := st.allocObj inst.typeIds[a]! (dataSlots (Slots.zeros n) src off x 0 n)
    .ok st (wr stack (sp - 2) addr.toUInt64) (sp - 1)
  else if c == GcCode.arrayNewElem then
    let n := (rd stack (sp - 1)).toNat
    let off := (rd stack (sp - 2)).toNat
    let seg := st.elems[inst.elems[b]!]!
    if off + n > seg.size then .trap st stack .tableOOB else
    let (st, addr) := st.allocObj inst.typeIds[a]! (elemSlots (Slots.zeros n) seg off 0 n)
    .ok st (wr stack (sp - 2) addr.toUInt64) (sp - 1)
  else if c == GcCode.arrayGet || c == GcCode.arrayGetS || c == GcCode.arrayGetU then
    let r := rd stack (sp - 2)
    let i := (rd stack (sp - 1)).toNat
    if r == nullRef then .trap st stack trapNullArray else
    match st.obj? r.toNat with
    | none => .trap st stack trapNullArray
    | some o =>
      if i ≥ o.data.count then .trap st stack trapArrayOOB else
      let v := rd o.data i.toUSize
      .ok st (wr stack (sp - 2) (if c == GcCode.arrayGetS then unpackSigned b v else v)) (sp - 1)
  else if c == GcCode.arraySet then
    let r := rd stack (sp - 3)
    let i := (rd stack (sp - 2)).toNat
    let v := packBits b (rd stack (sp - 1))
    if r == nullRef then .trap st stack trapNullArray else
    match st.obj? r.toNat with
    | none => .trap st stack trapNullArray
    | some o =>
      if i ≥ o.data.count then .trap st stack trapArrayOOB else
      .ok (st.modObj r.toNat fun d => wr d i.toUSize v) stack (sp - 3)
  else if c == GcCode.arrayLen then
    let r := rd stack (sp - 1)
    if r == nullRef then .trap st stack trapNullArray else
    match st.obj? r.toNat with
    | none => .trap st stack trapNullArray
    | some o => .ok st (wr stack (sp - 1) o.data.count.toUInt64) sp
  else if c == GcCode.arrayFill then
    let r := rd stack (sp - 4)
    let i := (rd stack (sp - 3)).toNat
    let v := packBits b (rd stack (sp - 2))
    let n := (rd stack (sp - 1)).toNat
    if r == nullRef then .trap st stack trapNullArray else
    match st.obj? r.toNat with
    | none => .trap st stack trapNullArray
    | some o =>
      if i + n > o.data.count then .trap st stack trapArrayOOB else
      .ok (st.modObj r.toNat fun d => fillSlots d i.toUSize v n) stack (sp - 4)
  else if c == GcCode.arrayCopy then
    let dr := rd stack (sp - 5)
    let di := (rd stack (sp - 4)).toNat
    let sr := rd stack (sp - 3)
    let si := (rd stack (sp - 2)).toNat
    let n := (rd stack (sp - 1)).toNat
    if dr == nullRef || sr == nullRef then .trap st stack trapNullArray else
    match st.obj? dr.toNat, st.obj? sr.toNat with
    | some d, some s =>
      if di + n > d.data.count || si + n > s.data.count then .trap st stack trapArrayOOB else
      -- The source slots are copied out first, so the two arrays may be one.
      let part := s.data.extract (8 * si) (8 * (si + n))
      .ok (st.modObj dr.toNat fun d => part.copySlice 0 d (8 * di) (8 * n)) stack (sp - 5)
    | _, _ => .trap st stack trapNullArray
  else if c == GcCode.arrayInitData then
    let r := rd stack (sp - 4)
    let d := (rd stack (sp - 3)).toNat
    let s := (rd stack (sp - 2)).toNat
    let n := (rd stack (sp - 1)).toNat
    if r == nullRef then .trap st stack trapNullArray else
    match st.obj? r.toNat with
    | none => .trap st stack trapNullArray
    | some o =>
      if d + n > o.data.count then .trap st stack trapArrayOOB else
      let src := st.datas[inst.datas[b]!]!
      if s + n * x > src.size then .trap st stack .memOOB else
      .ok (st.modObj r.toNat fun dd => dataSlots dd src s x d.toUSize n) stack (sp - 4)
  else if c == GcCode.arrayInitElem then
    let r := rd stack (sp - 4)
    let d := (rd stack (sp - 3)).toNat
    let s := (rd stack (sp - 2)).toNat
    let n := (rd stack (sp - 1)).toNat
    if r == nullRef then .trap st stack trapNullArray else
    match st.obj? r.toNat with
    | none => .trap st stack trapNullArray
    | some o =>
      if d + n > o.data.count then .trap st stack trapArrayOOB else
      let seg := st.elems[inst.elems[b]!]!
      if s + n > seg.size then .trap st stack .tableOOB else
      .ok (st.modObj r.toNat fun dd => elemSlots dd seg s d.toUSize n) stack (sp - 4)
  else if c == GcCode.refTest then
    .ok st (wr stack (sp - 1) (if refMatches st inst (rd stack (sp - 1)) (b == 1) a then 1 else 0)) sp
  else if c == GcCode.refCast then
    if refMatches st inst (rd stack (sp - 1)) (b == 1) a then .ok st stack sp else .trap st stack trapCast
  else if c == GcCode.anyConvertExtern || c == GcCode.externConvertAny then
    .ok st (wr stack (sp - 1) (refConvert (rd stack (sp - 1)))) sp
  else if c == GcCode.refI31 then
    .ok st (wr stack (sp - 1) (i31Tag ||| (rd stack (sp - 1) &&& 0x7FFFFFFF))) sp
  else if c == GcCode.i31GetS || c == GcCode.i31GetU then
    let r := rd stack (sp - 1)
    if r == nullRef then .trap st stack trapNullI31 else
    let v := r &&& 0x7FFFFFFF
    let v := if c == GcCode.i31GetS && v &&& 0x40000000 != 0 then v ||| 0x80000000 else v
    .ok st (wr stack (sp - 1) v) sp
  else if c == GcOp.refEq then
    .ok st (wr stack (sp - 2) (if rd stack (sp - 2) == rd stack (sp - 1) then 1 else 0)) (sp - 1)
  else .trap st stack .unreachable

/-- What a cold op gives: go on from these registers, or stop. -/
inductive Cold (M : Type) where
  | go (st : StoreOf M) (stack : Slots) (sp fp pc : USize) (code : Array Op) (inst : ModuleInst) (frames : Array Frame)
  | stop (st : StoreOf M) (m : Machine) (ev : Event)

/-- The ops off the hot path: exceptions, tail calls, typed function references, SIMD. They
are a separate function, reached from the one `default` case of `run`, because as cases
of `run` they made every benchmark slower (sum 363 to 265 million instructions per
second, measured 2026-11-08): the C of the hot cases was the same, the C compiler's
register allocation for the larger function was not. `lim` is borrowed (`@&`), or
`run` would own it and release it on every exit. Each op takes one fuel unit in `run`.
Record: "Cold ops" in docs/designissues/2026-11-07-wasmvm-engine.md. -/
@[noinline] def cold (lim : @& RunLimits) (st : StoreOf M) (stack : Slots) (sp fp pc : USize)
    (code : Array Op) (inst : ModuleInst) (frames : Array Frame) : Op → Cold M
  | .throw x n =>
    let fields := argBits stack (sp - n.toUSize) n
    let exn := st.exc.exns.size
    let st := { st with exc := { st.exc with exns := st.exc.exns.push ⟨inst.tags[x]!, fields⟩ } }
    match raise st exn stack fp pc code inst frames with
    | .caught stack sp fp pc code inst frames => .go st stack sp fp pc code inst frames
    | .uncaught => .stop st ⟨stack, sp, fp, pc, code, inst, frames⟩ (.exception exn)
  | .throwRef =>
    let r := rd stack (sp - 1)
    if r == nullRef then .stop st ⟨stack, sp, fp, pc, code, inst, frames⟩ (.trap .nullExnRef) else
    match raise st r.toNat stack fp pc code inst frames with
    | .caught stack sp fp pc code inst frames => .go st stack sp fp pc code inst frames
    | .uncaught => .stop st ⟨stack, sp, fp, pc, code, inst, frames⟩ (.exception r.toNat)
  | .rethrow slot =>
    let r := rd stack (fp + slot.toUSize)
    if r == nullRef then .stop st ⟨stack, sp, fp, pc, code, inst, frames⟩ (.trap .nullExnRef) else
    match raise st r.toNat stack fp pc code inst frames with
    | .caught stack sp fp pc code inst frames => .go st stack sp fp pc code inst frames
    | .uncaught => .stop st ⟨stack, sp, fp, pc, code, inst, frames⟩ (.exception r.toNat)
  | .returnCall f =>
    match enterTail lim st stack sp fp inst.funcs[f]! with
    | .ok stack sp code inst => .go st stack sp fp 0 code inst frames
    | .host id fa args stack sp =>
      .stop st ⟨stack, sp, fp, pc + 1, code, inst, frames⟩ (.hostCall id fa args)
    | .trap t stack => .stop st ⟨stack, sp, fp, pc, code, inst, frames⟩ (.trap t)
  | .returnCallIndirect ti x =>
    let i := (rd stack (sp - 1)).toNat
    let tab := st.tables[inst.tables[x]!]!
    if i ≥ tab.elems.size then .stop st ⟨stack, sp, fp, pc, code, inst, frames⟩ (.trap .undefinedElement) else
    let r := tab.elems[i]!
    if r == nullRef then .stop st ⟨stack, sp, fp, pc, code, inst, frames⟩ (.trap .uninitializedElement) else
    if (st.funcs[r.toNat]!).typeId != inst.typeIds[ti]! then
      .stop st ⟨stack, sp, fp, pc, code, inst, frames⟩ (.trap .indirectTypeMismatch) else
    match enterTail lim st stack (sp - 1) fp r.toNat with
    | .ok stack sp code inst => .go st stack sp fp 0 code inst frames
    | .host id fa args stack sp =>
      .stop st ⟨stack, sp, fp, pc + 1, code, inst, frames⟩ (.hostCall id fa args)
    | .trap t stack => .stop st ⟨stack, sp - 1, fp, pc, code, inst, frames⟩ (.trap t)
  | .callRef =>
    let r := rd stack (sp - 1)
    if r == nullRef then .stop st ⟨stack, sp, fp, pc, code, inst, frames⟩ (.trap .nullFuncRef) else
    match enterCold lim st stack (sp - 1) fp code inst frames r.toNat (pc + 1) with
    | .ok stack sp fp code inst frames => .go st stack sp fp 0 code inst frames
    | .host id fa args stack sp =>
      .stop st ⟨stack, sp, fp, pc + 1, code, inst, frames⟩ (.hostCall id fa args)
    | .trap t stack => .stop st ⟨stack, sp - 1, fp, pc, code, inst, frames⟩ (.trap t)
  | .returnCallRef =>
    let r := rd stack (sp - 1)
    if r == nullRef then .stop st ⟨stack, sp, fp, pc, code, inst, frames⟩ (.trap .nullFuncRef) else
    match enterTail lim st stack (sp - 1) fp r.toNat with
    | .ok stack sp code inst => .go st stack sp fp 0 code inst frames
    | .host id fa args stack sp =>
      .stop st ⟨stack, sp, fp, pc + 1, code, inst, frames⟩ (.hostCall id fa args)
    | .trap t stack => .stop st ⟨stack, sp - 1, fp, pc, code, inst, frames⟩ (.trap t)
  | .refAsNonNull =>
    if rd stack (sp - 1) == nullRef then .stop st ⟨stack, sp, fp, pc, code, inst, frames⟩ (.trap .nullReference)
    else .go st stack sp fp (pc + 1) code inst frames
  | .brOnNull t =>
    if rd stack (sp - 1) == nullRef then
      let st := hiMoveDown st (sp - 1 - t.keep.toUSize) (fp + t.height.toUSize) t.keep
      let x := brMove stack (sp - 1) fp t
      .go st x.stack x.sp fp t.pc.toUSize code inst frames
    else .go st stack sp fp (pc + 1) code inst frames
  | .brOnNonNull t =>
    if rd stack (sp - 1) != nullRef then
      let st := hiMoveDown st (sp - t.keep.toUSize) (fp + t.height.toUSize) t.keep
      let x := brMove stack sp fp t
      .go st x.stack x.sp fp t.pc.toUSize code inst frames
    else .go st stack (sp - 1) fp (pc + 1) code inst frames
  -- Fixed-width SIMD.
  | .simd c mem off lane =>
    match simdStep st stack sp inst c mem off lane with
    | .ok st stack sp => .go st stack sp fp (pc + 1) code inst frames
    | .trap st stack t => .stop st ⟨stack, sp, fp, pc, code, inst, frames⟩ (.trap t)
  | .simdImm c lo hi =>
    if c == 0x0c then .go (hiWr st sp hi) (wr stack sp lo) (sp + 1) fp (pc + 1) code inst frames
    else
      let r := V128.shuffle ⟨lo, hi⟩ (vAt st stack (sp - 2)) (vAt st stack (sp - 1))
      .go (hiWr st (sp - 2) r.hi) (wr stack (sp - 2) r.lo) (sp - 1) fp (pc + 1) code inst frames
  | .vLocalGet x =>
    let i := fp + x.toUSize
    .go (hiWr st sp (hiRd st i)) (wr stack sp (rd stack i)) (sp + 1) fp (pc + 1) code inst frames
  | .vLocalSet x =>
    let i := fp + x.toUSize
    .go (hiWr st i (hiRd st (sp - 1))) (wr stack i (rd stack (sp - 1))) (sp - 1) fp (pc + 1) code inst frames
  | .vLocalTee x =>
    let i := fp + x.toUSize
    .go (hiWr st i (hiRd st (sp - 1))) (wr stack i (rd stack (sp - 1))) sp fp (pc + 1) code inst frames
  | .vSelect =>
    if rd stack (sp - 1) != 0 then .go st stack (sp - 2) fp (pc + 1) code inst frames
    else
      .go (hiWr st (sp - 3) (hiRd st (sp - 2))) (wr stack (sp - 3) (rd stack (sp - 2))) (sp - 2) fp (pc + 1)
        code inst frames
  | .vGlobalGet x =>
    let a := inst.globals[x]!
    .go (hiWr st sp (st.globalHi a)) (wr stack sp (st.globalBits a)) (sp + 1) fp (pc + 1) code inst frames
  | .vGlobalSet x =>
    let a := inst.globals[x]!
    let lo := rd stack (sp - 1)
    let hi := hiRd st (sp - 1)
    let st := { st with globals := Slots.wr st.globals a.toUSize lo }
    .go (st.setGlobalHi a hi) stack (sp - 1) fp (pc + 1) code inst frames
  | .vBrTable ts d =>
    let i := (rd stack (sp - 1)).toNat
    let t := if h : i < ts.size then ts[i] else d
    let st := hiMoveDown st (sp - 1 - t.keep.toUSize) (fp + t.height.toUSize) t.keep
    let x := brMove stack (sp - 1) fp t
    .go st x.stack x.sp fp t.pc.toUSize code inst frames
  | .hiMove skip n height =>
    .go (hiMoveDown st (sp - skip.toUSize - n.toUSize) (fp + height.toUSize) n) stack sp fp (pc + 1)
      code inst frames
  | .hiZero x n => .go (hiZero st (fp + x.toUSize) n) stack sp fp (pc + 1) code inst frames
  -- Garbage collection.
  | .gc c a b x =>
    if c == GcOp.callIndirectSub || c == GcOp.returnCallIndirectSub then
      -- `call_indirect` through a type that is not final: the function's type may be
      -- a declared subtype of it.
      let i := (rd stack (sp - 1)).toNat
      let tab := st.tables[inst.tables[b]!]!
      if i ≥ tab.elems.size then .stop st ⟨stack, sp, fp, pc, code, inst, frames⟩ (.trap .undefinedElement) else
      let r := tab.elems[i]!
      if r == nullRef then .stop st ⟨stack, sp, fp, pc, code, inst, frames⟩ (.trap .uninitializedElement) else
      if !st.isSubId (st.funcs[r.toNat]!).typeId inst.typeIds[a]! then
        .stop st ⟨stack, sp, fp, pc, code, inst, frames⟩ (.trap .indirectTypeMismatch) else
      if c == GcOp.callIndirectSub then
        match enterCold lim st stack (sp - 1) fp code inst frames r.toNat (pc + 1) with
        | .ok stack sp fp code inst frames => .go st stack sp fp 0 code inst frames
        | .host id fa args stack sp =>
          .stop st ⟨stack, sp, fp, pc + 1, code, inst, frames⟩ (.hostCall id fa args)
        | .trap t stack => .stop st ⟨stack, sp - 1, fp, pc, code, inst, frames⟩ (.trap t)
      else
        match enterTail lim st stack (sp - 1) fp r.toNat with
        | .ok stack sp code inst => .go st stack sp fp 0 code inst frames
        | .host id fa args stack sp =>
          .stop st ⟨stack, sp, fp, pc + 1, code, inst, frames⟩ (.hostCall id fa args)
        | .trap t stack => .stop st ⟨stack, sp - 1, fp, pc, code, inst, frames⟩ (.trap t)
    else
      match gcStep st stack sp inst c a b x with
      | .ok st stack sp => .go st stack sp fp (pc + 1) code inst frames
      | .trap st stack t => .stop st ⟨stack, sp, fp, pc, code, inst, frames⟩ (.trap t)
  | .gcBr t flags ht =>
    if refMatches st inst (rd stack (sp - 1)) (flags / 2 == 1) ht != (flags % 2 == 1) then
      let st := hiMoveDown st (sp - t.keep.toUSize) (fp + t.height.toUSize) t.keep
      let x := brMove stack sp fp t
      .go st x.stack x.sp fp t.pc.toUSize code inst frames
    else .go st stack sp fp (pc + 1) code inst frames
  | _ => .stop st ⟨stack, sp, fp, pc, code, inst, frames⟩ (.trap .unreachable)

/-! ### The loop -/

/-- Stop the loop: the result of `run` (store, registers, fuel left, event). One
function, not inlined, so the exits of `run` share one call instead of each building
the result inline (see "The dispatch loop in C" in the record). -/
@[noinline] def stop (st : StoreOf M) (stack : Slots) (sp fp pc : USize) (code : Array Op)
    (inst : ModuleInst) (frames : Array Frame) (fuel : Nat) (ev : Event) : StoreOf M × Machine × Nat × Event :=
  (st, ⟨stack, sp, fp, pc, code, inst, frames⟩, fuel, ev)

@[specialize] def run (lim : RunLimits) (st : StoreOf M) (stack : Slots) (sp fp pc : USize)
    (code : Array Op) (inst : ModuleInst) (frames : Array Frame) :
    Nat → StoreOf M × Machine × Nat × Event
  | 0 => stop st stack sp fp pc code inst frames 0 .outOfFuel
  | fuel + 1 =>
    if h : pc < code.usize then
    match code.uget pc (pc_ok h) with
    | .unreachable => stop st stack sp fp pc code inst frames fuel (.trap .unreachable)
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
      if frames.isEmpty then stop st stack sp fp pc code inst frames fuel (.done) else
      let f := frames.back!
      run lim st stack sp f.fp f.pc f.code f.inst frames.pop fuel
    | .call f =>
      let fa := inst.funcs[f]!
      match enter lim st stack sp fp code inst frames fa (pc + 1) with
      | .ok stack sp fp code inst frames => run lim st stack sp fp 0 code inst frames fuel
      | .host id fa args stack sp =>
        stop st stack sp fp (pc + 1) code inst frames fuel (.hostCall id fa args)
      | .trap t stack => stop st stack sp fp pc code inst frames fuel (.trap t)
    | .callIndirect ti x =>
      let i := (rd stack (sp - 1)).toNat
      let tab := st.tables[inst.tables[x]!]!
      if i ≥ tab.elems.size then stop st stack sp fp pc code inst frames fuel (.trap .undefinedElement) else
      let r := tab.elems[i]!
      if r == nullRef then stop st stack sp fp pc code inst frames fuel (.trap .uninitializedElement) else
      let fa := r.toNat
      if (st.funcs[fa]!).typeId != inst.typeIds[ti]! then
        stop st stack sp fp pc code inst frames fuel (.trap .indirectTypeMismatch) else
      match enter lim st stack (sp - 1) fp code inst frames fa (pc + 1) with
      | .ok stack sp fp code inst frames => run lim st stack sp fp 0 code inst frames fuel
      | .host id fa args stack sp =>
        stop st stack sp fp (pc + 1) code inst frames fuel (.hostCall id fa args)
      | .trap t stack => stop st stack (sp - 1) fp pc code inst frames fuel (.trap t)
    | .drop =>
      let x := Simple.exec fp .drop stack sp
      run lim st x.stack x.sp fp (pc + 1) code inst frames fuel
    | .select =>
      let c := rd stack (sp - 1)
      let stack := if c != 0 then stack else wr stack (sp - 3) (rd stack (sp - 2))
      run lim st stack (sp - 2) fp (pc + 1) code inst frames fuel
    | .localGet x =>
      let x := Simple.exec fp (.localGet x.toUSize) stack sp
      run lim st x.stack x.sp fp (pc + 1) code inst frames fuel
    | .localSet x =>
      let x := Simple.exec fp (.localSet x.toUSize) stack sp
      run lim st x.stack x.sp fp (pc + 1) code inst frames fuel
    | .localTee x =>
      let x := Simple.exec fp (.localTee x.toUSize) stack sp
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
      else stop st stack sp fp pc code inst frames fuel (.trap .tableOOB)
    | .tableSet x =>
      let v := rd stack (sp - 1)
      let i := (rd stack (sp - 2)).toNat
      let ta := inst.tables[x]!
      if i < (st.tables[ta]!).elems.size then
        let st := { st with tables := st.tables.modify ta fun t => { t with elems := t.elems.set! i v } }
        run lim st stack (sp - 2) fp (pc + 1) code inst frames fuel
      else stop st stack sp fp pc code inst frames fuel (.trap .tableOOB)
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
        stop st stack sp fp pc code inst frames fuel (.trap .tableOOB) else
      let st := { st with tables := st.tables.modify ta fun t => { t with elems := fillArr t.elems i v n } }
      run lim st stack (sp - 3) fp (pc + 1) code inst frames fuel
    | .tableCopy dx sx =>
      let n := (rd stack (sp - 1)).toNat
      let s := (rd stack (sp - 2)).toNat
      let d := (rd stack (sp - 3)).toNat
      let td := inst.tables[dx]!
      let src := (st.tables[inst.tables[sx]!]!).elems
      if s + n > src.size || d + n > (st.tables[td]!).elems.size then
        stop st stack sp fp pc code inst frames fuel (.trap .tableOOB) else
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
        stop st stack sp fp pc code inst frames fuel (.trap .tableOOB) else
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
      else stop st stack sp fp pc code inst frames fuel (.trap .memOOB)
    | .store op mem off =>
      let v := rd stack (sp - 1)
      let ea := (rd stack (sp - 2)).toNat + off
      let ma := inst.mems[mem]!
      if ea + op.width ≤ LinearMemory.size (st.mems[ma]!).data then
        run lim (storeMem st ma ea v op) stack (sp - 2) fp (pc + 1) code inst frames fuel
      else stop st stack sp fp pc code inst frames fuel (.trap .memOOB)
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
        stop st stack sp fp pc code inst frames fuel (.trap .memOOB) else
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
        stop st stack sp fp pc code inst frames fuel (.trap .memOOB) else
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
        stop st stack sp fp pc code inst frames fuel (.trap .memOOB) else
      let st := { st with mems := st.mems.modify ma fun mi => { mi with data := LinearMemory.fill mi.data d v n } }
      run lim st stack (sp - 3) fp (pc + 1) code inst frames fuel
    | .const v =>
      let x := Simple.exec fp (.const v) stack sp
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
        | some t => stop st stack sp fp pc code inst frames fuel (.trap t)
        | none =>
          let x := Simple.exec fp (.bin op) stack sp
          run lim st x.stack x.sp fp (pc + 1) code inst frames fuel
      else
        match (if op.mayTrap then op.trapUn (rd stack (sp - 1)) else none) with
        | some t => stop st stack sp fp pc code inst frames fuel (.trap t)
        | none =>
          let x := Simple.exec fp (.un op) stack sp
          run lim st x.stack x.sp fp (pc + 1) code inst frames fuel
    -- Fused ops: `k` parts take `k` fuel. With less fuel, run the first part only
    -- (the others follow it in the code).
    | .llBin x y op =>
      match fuel with
      | f + 2 =>
        let s := Simple.next fp (.bin op) (Simple.next fp (.localGet y.toUSize)
          (Simple.exec fp (.localGet x.toUSize) stack sp))
        run lim st s.stack s.sp fp (pc + 3) code inst frames f
      | g =>
        let s := Simple.exec fp (.localGet x.toUSize) stack sp
        run lim st s.stack s.sp fp (pc + 1) code inst frames g
    | .lcBin x c op =>
      match fuel with
      | f + 2 =>
        let s := Simple.next fp (.bin op) (Simple.next fp (.const c)
          (Simple.exec fp (.localGet x.toUSize) stack sp))
        run lim st s.stack s.sp fp (pc + 3) code inst frames f
      | g =>
        let s := Simple.exec fp (.localGet x.toUSize) stack sp
        run lim st s.stack s.sp fp (pc + 1) code inst frames g
    | .cBin c op =>
      match fuel with
      | f + 1 =>
        let s := Simple.next fp (.bin op) (Simple.exec fp (.const c) stack sp)
        run lim st s.stack s.sp fp (pc + 2) code inst frames f
      | g =>
        let s := Simple.exec fp (.const c) stack sp
        run lim st s.stack s.sp fp (pc + 1) code inst frames g
    | .lUn x op =>
      match fuel with
      | f + 1 =>
        let s := Simple.next fp (.un op) (Simple.exec fp (.localGet x.toUSize) stack sp)
        run lim st s.stack s.sp fp (pc + 2) code inst frames f
      | g =>
        let s := Simple.exec fp (.localGet x.toUSize) stack sp
        run lim st s.stack s.sp fp (pc + 1) code inst frames g
    | .binSet op z =>
      match fuel with
      | f + 1 =>
        let s := Simple.next fp (.localSet z.toUSize) (Simple.exec fp (.bin op) stack sp)
        run lim st s.stack s.sp fp (pc + 2) code inst frames f
      | g =>
        let s := Simple.exec fp (.bin op) stack sp
        run lim st s.stack s.sp fp (pc + 1) code inst frames g
    | .lcBinSet x c op z =>
      match fuel with
      | f + 3 =>
        let s := Simple.next fp (.localSet z.toUSize) (Simple.next fp (.bin op) (Simple.next fp (.const c)
          (Simple.exec fp (.localGet x.toUSize) stack sp)))
        run lim st s.stack s.sp fp (pc + 4) code inst frames f
      | g =>
        let s := Simple.exec fp (.localGet x.toUSize) stack sp
        run lim st s.stack s.sp fp (pc + 1) code inst frames g
    | .llBinJump x y op t z =>
      match fuel with
      | f + 3 =>
        let s := Simple.next fp (.bin op) (Simple.next fp (.localGet y.toUSize)
          (Simple.exec fp (.localGet x.toUSize) stack sp))
        let c := rd s.stack (s.sp - 1)
        run lim st s.stack (s.sp - 1) fp (jumpTo c z t.toUSize (pc + 4)) code inst frames f
      | g =>
        let s := Simple.exec fp (.localGet x.toUSize) stack sp
        run lim st s.stack s.sp fp (pc + 1) code inst frames g
    | .lcBinJump x v op t z =>
      match fuel with
      | f + 3 =>
        let s := Simple.next fp (.bin op) (Simple.next fp (.const v)
          (Simple.exec fp (.localGet x.toUSize) stack sp))
        let c := rd s.stack (s.sp - 1)
        run lim st s.stack (s.sp - 1) fp (jumpTo c z t.toUSize (pc + 4)) code inst frames f
      | g =>
        let s := Simple.exec fp (.localGet x.toUSize) stack sp
        run lim st s.stack s.sp fp (pc + 1) code inst frames g
    | .binJump op t z =>
      match fuel with
      | f + 1 =>
        let s := Simple.exec fp (.bin op) stack sp
        let c := rd s.stack (s.sp - 1)
        run lim st s.stack (s.sp - 1) fp (jumpTo c z t.toUSize (pc + 2)) code inst frames f
      | g =>
        let s := Simple.exec fp (.bin op) stack sp
        run lim st s.stack s.sp fp (pc + 1) code inst frames g
    -- Everything else (exceptions, tail calls, typed function references): one
    -- `default` case of the C `switch`, which calls `cold`.
    | o =>
      match cold lim st stack sp fp pc code inst frames o with
      | .go st stack sp fp pc code inst frames => run lim st stack sp fp pc code inst frames fuel
      | .stop st m ev => (st, m, fuel, ev)
    else stop st stack sp fp pc code inst frames fuel (.trap (.host "pc out of range"))

/-- Run from a stopped machine. -/
@[inline] def runM (lim : RunLimits) (st : StoreOf M) (m : Machine) (fuel : Nat) :
    StoreOf M × Machine × Nat × Event :=
  run lim st m.stack m.sp m.fp m.pc m.code m.inst m.frames fuel

end
end Run
end L4Factoidal.WasmVM

#print axioms L4Factoidal.WasmVM.Run.simdStep_eq_fast
