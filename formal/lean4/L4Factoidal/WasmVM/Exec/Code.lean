/-
L4Factoidal.WasmVM.Exec.Code: the flat code that the interpreter runs
(https://github.com/danbri/factoidal/issues/1244).

The validator (`WasmVM.Valid`) compiles each function body once into an
`Array Op`. Structured control is gone: a branch names its target pc, how many
values it keeps and the frame-relative operand height to cut back to. Those come
from the static stack heights that validation computes, so the interpreter does no
search for a label and keeps no label stack (the side table of Wizard, folded into
the op as in wasm3).

Heights are relative to the frame base `fp`: slot `fp + i` is local `i`, and the
operand stack of the function starts at `fp + nLocals`.
-/
import L4Factoidal.WasmVM.Syntax
import L4Factoidal.WasmVM.Exec.Bytes
import L4Factoidal.WasmVM.Numerics

namespace L4Factoidal.WasmVM

/-- A branch target: the pc to go to, the number of values to keep and the operand
height (relative to `fp`) at which they go. -/
structure BrTarget where
  pc : Nat
  keep : Nat
  height : Nat
  deriving Repr, Inhabited, BEq

/-- Where a caught exception goes: the handler's pc, and the operand height (relative
to `fp`) at which its values are written. What is written, in order: the exception
reference when `exnBelow` (legacy `catch`: the slot `rethrow` reads), the payload when
`payload`, the exception reference when `exnAbove` (`catch_ref`, `catch_all_ref`). -/
structure CatchTarget where
  /-- Tag index in the module; `none` catches every exception. -/
  tag : Option Nat
  pc : Nat
  height : Nat
  exnBelow : Bool := false
  payload : Bool := true
  exnAbove : Bool := false
  deriving Repr, Inhabited, BEq

/-- One entry of a function's handler table: an exception raised at a pc in
`[start, stop)` is tested against `catches` in order; when none matches, the search
goes on at entry `next` (an enclosing `try`, or a legacy `delegate` target), then in
the caller. Entries are in the order their `try` starts, so for properly nested ranges
the innermost entry holding a pc is the last one that holds it. -/
structure Handler where
  start : Nat
  stop : Nat
  catches : Array CatchTarget
  next : Option Nat
  deriving Repr, Inhabited, BEq

inductive Op where
  | unreachable
  /-- Branch that moves `keep` values down to `height`. -/
  | br (t : BrTarget)
  | brIf (t : BrTarget)
  /-- Branch with no value movement (the values are already in place). -/
  | jump (pc : Nat)
  | jumpIf (pc : Nat)
  /-- `if`: jump when the condition is zero. -/
  | jumpUnless (pc : Nat)
  | brTable (ts : Array BrTarget) (d : BrTarget)
  | return_ (keep : Nat)
  | call (f : Nat)
  | callIndirect (type table : Nat)
  | drop | select
  | localGet (x : Nat) | localSet (x : Nat) | localTee (x : Nat)
  | globalGet (x : Nat) | globalSet (x : Nat)
  | tableGet (x : Nat) | tableSet (x : Nat) | tableSize (x : Nat) | tableGrow (x : Nat)
  | tableFill (x : Nat) | tableCopy (dst src : Nat) | tableInit (table elem : Nat)
  | elemDrop (x : Nat)
  | load (op : LoadOp) (mem offset : Nat)
  | store (op : StoreOp) (mem offset : Nat)
  | memorySize (mem : Nat) | memoryGrow (mem : Nat) | memoryInit (data mem : Nat)
  | dataDrop (x : Nat) | memoryCopy (dst src : Nat) | memoryFill (mem : Nat)
  | const (v : UInt64)
  | refIsNull | refFunc (f : Nat)
  | num (op : NumOp)
  -- Fused ops, made by `fuse`. Each stands for its parts (`Op.parts`), which stay in
  -- the code after it, so a branch into the middle still finds them. `run` executes a
  -- fused op as its parts in sequence (`Proofs/Fuse.lean`). Every `op` here is a binary
  -- (`lUn`: unary) numeric op that cannot trap.
  | llBin (x y : Nat) (op : NumOp)
  | lcBin (x : Nat) (c : UInt64) (op : NumOp)
  | cBin (c : UInt64) (op : NumOp)
  | lUn (x : Nat) (op : NumOp)
  | binSet (op : NumOp) (z : Nat)
  | lcBinSet (x : Nat) (c : UInt64) (op : NumOp) (z : Nat)
  /-- `local.get x; local.get y; op; jumpIf t` (`jumpUnless t` when `onZero`). -/
  | llBinJump (x y : Nat) (op : NumOp) (t : Nat) (onZero : Bool)
  | lcBinJump (x : Nat) (c : UInt64) (op : NumOp) (t : Nat) (onZero : Bool)
  | binJump (op : NumOp) (t : Nat) (onZero : Bool)
  -- Ops off the hot path, last so that the constructor numbers of the ops above (the
  -- `switch` cases of `run`) are those they had before these were added.
  /-- Throw a new exception of tag `tag` (module index) with `n` payload values. -/
  | throw (tag : Nat) (n : Nat)
  | throwRef
  /-- Legacy `rethrow`: throw again the exception held at slot `fp + slot`. -/
  | rethrow (slot : Nat)
  /-- A tail call. The validator puts `return_ k` after it, which runs after a host
  callee returns. -/
  | returnCall (f : Nat)
  | returnCallIndirect (type table : Nat)
  | callRef
  | returnCallRef
  | refAsNonNull
  /-- Branch to `t` when the reference on top is null (popping it). -/
  | brOnNull (t : BrTarget)
  /-- Branch to `t` with the reference when it is not null; else pop it. -/
  | brOnNonNull (t : BrTarget)
  /-- The function's handler table. Data, not an instruction: the validator puts it
  last, after the final `return_`, only in functions with a `try`. -/
  | handlers (hs : Array Handler)
  -- Fixed-width SIMD (record, "SIMD"). All of these run in `cold`. A v128 value has
  -- one slot index: its low half is in the operand stack, its high half in the slot of
  -- the same index of the hi stack (`ExcStore.hi`). The ops of the hot loop move low
  -- halves only, so where the validator knows that a moved value is a v128 it emits
  -- one of the ops below.
  /-- A SIMD instruction with no 16-byte immediate: opcode number, then memory index,
  offset and lane index (zero when the opcode has none). -/
  | simd (code mem offset lane : Nat)
  /-- `v128.const` (the value) and `i8x16.shuffle` (the 16 lane indices). -/
  | simdImm (code : Nat) (lo hi : UInt64)
  | vLocalGet (x : Nat) | vLocalSet (x : Nat) | vLocalTee (x : Nat)
  | vSelect
  | vGlobalGet (x : Nat) | vGlobalSet (x : Nat)
  /-- `brTable` that moves both halves of the kept values. -/
  | vBrTable (ts : Array BrTarget) (d : BrTarget)
  /-- Move the high halves of the `n` slots below the top `skip` slots down to
  `fp + height`. The validator puts it before a `br`, `return_` or tail call that
  moves v128 values; that op then moves the low halves. -/
  | hiMove (skip n height : Nat)
  /-- Zero the high halves of locals `x` to `x + n - 1` (function entry, when a
  declared local is a v128). -/
  | hiZero (x n : Nat)
  -- Garbage collection (record, "GC"). Both run in `cold`.
  /-- A garbage-collection op: `code` is the instruction's number after the 0xFB prefix
  (`GcCode`), or one of `GcOp`; `a`, `b`, `c` are what `Run.gcStep` says for the code. -/
  | gc (code a b c : Nat)
  /-- `br_on_cast` (`flags` bit 0 clear) and `br_on_cast_fail` (bit 0 set): branch to
  `t` with the reference on top when it matches (does not match) the heap type `ht`
  (`heapCode`; null matches when bit 1 of `flags` is set). The reference stays. -/
  | gcBr (t : BrTarget) (flags ht : Nat)
  deriving Repr, Inhabited

/-! Codes of `Op.gc` that are not instruction numbers. -/
namespace GcOp
def refEq : Nat := 31
/-- `call_indirect` and `return_call_indirect` through a type that is not final: the
function's type may be a declared subtype (`a`: type index, `b`: table index). -/
def callIndirectSub : Nat := 100
def returnCallIndirectSub : Nat := 101
end GcOp

/-- A heap type as a number, for `Op.gc` and `Op.gcBr`. -/
def heapCode : HeapType → Nat
  | .func => 0 | .extern => 1 | .any => 2 | .eq => 3 | .i31 => 4 | .struct => 5 | .array => 6
  | .none => 7 | .nofunc => 8 | .noextern => 9 | .exn => 10 | .noexn => 11
  | .idx i => 12 + i

/-- How a storage type is kept in an object's 64-bit slot: 1 for i8 and 2 for i16
(the value is cut to 8 or 16 bits), 0 for a value type (the slot bits). -/
def packCode : StorageType → Nat
  | .i8 => 1 | .i16 => 2 | .val _ => 0

/-- The conditional jump at the end of a fused op. -/
def Op.condJump (t : Nat) : Bool → Op
  | false => .jumpIf t
  | true => .jumpUnless t

/-- The ops a fused op stands for; empty for every other op. -/
def Op.parts : Op → List Op
  | .llBin x y op => [.localGet x, .localGet y, .num op]
  | .lcBin x c op => [.localGet x, .const c, .num op]
  | .cBin c op => [.const c, .num op]
  | .lUn x op => [.localGet x, .num op]
  | .binSet op z => [.num op, .localSet z]
  | .lcBinSet x c op z => [.localGet x, .const c, .num op, .localSet z]
  | .llBinJump x y op t z => [.localGet x, .localGet y, .num op, Op.condJump t z]
  | .lcBinJump x c op t z => [.localGet x, .const c, .num op, Op.condJump t z]
  | .binJump op t z => [.num op, Op.condJump t z]
  | _ => []

/-- A numeric op that `fuse` may put in a fused op as its binary op. -/
def NumOp.pureBin (op : NumOp) : Bool := op.isBinary && !op.mayTrap
def NumOp.pureUn (op : NumOp) : Bool := !op.isBinary && !op.mayTrap

/-- The conditional jump `o` is, if any. -/
def jumpAt : Option Op → Option (Nat × Bool)
  | some (.jumpIf t) => some (t, false)
  | some (.jumpUnless t) => some (t, true)
  | _ => none

/-- The fused op that starts at `i`, the longest that matches. -/
def fuseAt (c : Array Op) (i : Nat) : Option Op :=
  match c[i]?, c[i+1]?, c[i+2]? with
  | some (.localGet x), some (.localGet y), some (.num op) =>
    if op.pureBin then
      match jumpAt c[i+3]? with
      | some (t, z) => some (.llBinJump x y op t z)
      | none => some (.llBin x y op)
    else none
  | some (.localGet x), some (.const v), some (.num op) =>
    if op.pureBin then
      match jumpAt c[i+3]?, c[i+3]? with
      | some (t, z), _ => some (.lcBinJump x v op t z)
      | none, some (.localSet w) => some (.lcBinSet x v op w)
      | none, _ => some (.lcBin x v op)
    else none
  | some (.localGet x), some (.num op), _ => if op.pureUn then some (.lUn x op) else none
  | some (.const v), some (.num op), _ => if op.pureBin then some (.cBin v op) else none
  | some (.num op), some (.localSet z), _ => if op.pureBin then some (.binSet op z) else none
  | some (.num op), o, _ =>
    if op.pureBin then
      match jumpAt o with
      | some (t, z) => some (.binJump op t z)
      | none => none
    else none
  | _, _, _ => none

/-- Put fused ops into compiled code. The length and every op that is not the first
of a fused group stay as they were. -/
def fuse (c : Array Op) : Array Op := go 0 c
where
  go (i : Nat) (out : Array Op) : Array Op :=
    if i < c.size then
      match fuseAt c i with
      | some f => go (i + max 1 f.parts.length) (out.set! i f)
      | none => go (i + 1) out
    else out
  termination_by c.size - i

/-- 64-bit slots, 8 little-endian bytes each, in a `ByteArray`: the operand stack and
the globals. Slot `i` is bytes `8i .. 8i+8`.

Not a `FloatArray` read through `Float.ofBits`/`Float.toBits`, although that measured
faster than the first byte form (17 against 25 ns in `Bench/Repr.lean`): Lean 4.33
models `Float` with all NaNs equal, and the compiled `Float.ofBits` makes every NaN
bit pattern the canonical NaN. An i64 such as -1 (all ones) is such a pattern, so it
did not survive a round trip. Found 2026-11-07 by the spec test `fac` (`fac-opt` gave
0x7f38000000000000).

Access is by a `USize` slot index with ONE check, `i < s.usize / 8`; the byte offsets
are proved in range from it (`slot_ok`, then `Bytes.byte_ok`). Measured in
`Bench/Repr.lean`: 3.3 ns per iteration against 25 ns for eight checked byte accesses
(variant X against C). -/
abbrev Slots := ByteArray

namespace Slots

theorem slot_ok {s : Slots} {i : USize} (h : i < s.usize / 8) : (i * 8).toNat + 8 ≤ s.usize.toNat := by
  rw [USize.lt_iff_toNat_lt, USize.toNat_div] at h
  have h8 : (8 : USize).toNat = 8 := by simp
  rw [h8] at h
  have h2 := USize.toNat_lt_size s.usize
  have hs : USize.size = 2 ^ System.Platform.numBits := rfl
  rw [USize.toNat_mul, h8, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Read slot `i` (0 when out of range; validation keeps every access in range). -/
@[inline] def rd (s : Slots) (i : USize) : UInt64 :=
  if h : i < s.usize / 8 then Bytes.ld64 s (i * 8) (slot_ok h) else 0

/-- Write slot `i` (no change when out of range). -/
@[inline] def wr (s : Slots) (i : USize) (v : UInt64) : Slots :=
  if h : i < s.usize / 8 then Bytes.st64 s (i * 8) v (slot_ok h) else s

/-- Number of slots. -/
@[inline] def count (s : Slots) : Nat := s.size / 8

/-- Append `k` zero slots. -/
def grow (s : Slots) : Nat → Slots
  | 0 => s
  | k + 1 => grow (s.push 0 |>.push 0 |>.push 0 |>.push 0 |>.push 0 |>.push 0 |>.push 0 |>.push 0) k

def push (s : Slots) (v : UInt64) : Slots := wr (grow s 1) s.count.toUSize v

/-- Write slot `i`, growing the array when `i` is past its end (to twice its size at
least, so repeated writes at the top cost amortised constant time). -/
def wrGrow (s : Slots) (i : USize) (v : UInt64) : Slots :=
  let n := i.toNat
  let s := if n < s.count then s else grow s (max (n + 1) (2 * s.count) - s.count)
  wr s i v

def zeros (n : Nat) : Slots := grow (ByteArray.emptyWithCapacity (8 * n)) n

end Slots

/-- The bits of a null reference. -/
def nullRef : UInt64 := 0xFFFFFFFFFFFFFFFF

/-! ### Reference bits (record, "GC")

A reference is one slot. All ones is null in every hierarchy. In the `any` hierarchy:
bit 63 set is an i31 value (bits 0 to 30), bit 62 set is a host value (an external
reference made internal by `any.convert_extern`), and with both clear the slot is the
address of a struct or an array in `GcStore.objs`. In the `extern` hierarchy: a slot
with bits 62 and 63 clear is the embedder's number, and the other forms are values of
the `any` hierarchy made external. A function reference is a function address and an
exception reference an exception address; validation keeps the hierarchies apart. -/

def i31Tag : UInt64 := 0x8000000000000000
def hostTag : UInt64 := 0x4000000000000000

/-- `any.convert_extern` and `extern.convert_any`: null and i31 values stay; an object
address and a host number change places (bit 62 flips). The function is its own
inverse. -/
def refConvert (r : UInt64) : UInt64 :=
  if r == nullRef || r &&& i31Tag != 0 then r else r ^^^ hostTag

/-- Whether a non-null slot of the `any` hierarchy is an object address. -/
def refIsObj (r : UInt64) : Bool := r &&& 0xC000000000000000 == 0

/-- The zero value of a type, as slot bits (null for a reference type). -/
def ValType.zeroBits : ValType → UInt64
  | .ref _ => nullRef
  | _ => 0

/-- A compiled function body. -/
structure CompiledFunc where
  /-- Index of its type in the module's type section. -/
  type : Nat
  nParams : Nat
  /-- Initial bits of the declared locals (after the parameters). -/
  localInit : Array UInt64
  /-- Most slots the function uses above `fp`: locals plus operand height. -/
  maxHeight : Nat
  code : Array Op
  deriving Inhabited

def CompiledFunc.nLocals (f : CompiledFunc) : Nat := f.nParams + f.localInit.size

/-! ### Fresh copies of compiled code

A value that a `Task` returns is marked multi-threaded, with everything it reaches. The
reference count of a multi-threaded object is changed with atomic operations, in
`lean_inc_ref_cold`/`lean_dec_ref_cold`. `run` changes the count of the op it reads at
every instruction (`lean_array_uget`, then a decrement after the case reads the
fields), so code compiled in parallel (`validateParallel`) ran every op through these
calls: the VP8 decoder ran 137 million instructions a second with such code and 183
with serially compiled code (measured 2026-11-08). `compileAll` copies the code that
the tasks give: each op is rebuilt, which allocates a new object (the old one is shared,
so it is not reused), and the copy is single-threaded. Each `fresh` is the identity
(`Op.fresh_id`, `CompiledFunc.fresh_eq`). -/

/-- Zero, behind a call the compiler does not look through. `fresh` adds it to every
`Nat` field: rebuilding a constructor from its own fields is compiled to the identity
(the object is returned, still multi-threaded), and adding an unknown number is not. -/
@[noinline] def freshZero : Nat := 0

/-- The op unchanged when `k` is not 1 (`k` is `freshZero`): keeps `Op.num` from being
compiled to the identity. -/
@[inline] def keepNumOp (k : Nat) (op : NumOp) : NumOp := if k = 1 then .i32_eqz else op

def BrTarget.freshWith (k : Nat) (t : BrTarget) : BrTarget :=
  { pc := t.pc + k, keep := t.keep + k, height := t.height + k }

def CatchTarget.freshWith (k : Nat) (c : CatchTarget) : CatchTarget :=
  { tag := c.tag.map (· + k), pc := c.pc + k, height := c.height + k, exnBelow := c.exnBelow,
    payload := c.payload, exnAbove := c.exnAbove }

def Handler.freshWith (k : Nat) (h : Handler) : Handler :=
  { start := h.start + k, stop := h.stop + k, catches := h.catches.map (CatchTarget.freshWith k),
    next := h.next.map (· + k) }

def Op.freshWith (k : Nat) : Op → Op
  | .unreachable => .unreachable
  | .br t => .br (t.freshWith k)
  | .brIf t => .brIf (t.freshWith k)
  | .jump pc => .jump (pc + k)
  | .jumpIf pc => .jumpIf (pc + k)
  | .jumpUnless pc => .jumpUnless (pc + k)
  | .brTable ts d => .brTable (ts.map (BrTarget.freshWith k)) (d.freshWith k)
  | .return_ keep => .return_ (keep + k)
  | .call f => .call (f + k)
  | .callIndirect type table => .callIndirect (type + k) (table + k)
  | .drop => .drop
  | .select => .select
  | .localGet x => .localGet (x + k)
  | .localSet x => .localSet (x + k)
  | .localTee x => .localTee (x + k)
  | .globalGet x => .globalGet (x + k)
  | .globalSet x => .globalSet (x + k)
  | .tableGet x => .tableGet (x + k)
  | .tableSet x => .tableSet (x + k)
  | .tableSize x => .tableSize (x + k)
  | .tableGrow x => .tableGrow (x + k)
  | .tableFill x => .tableFill (x + k)
  | .tableCopy dst src => .tableCopy (dst + k) (src + k)
  | .tableInit table elem => .tableInit (table + k) (elem + k)
  | .elemDrop x => .elemDrop (x + k)
  | .load op mem offset => .load op (mem + k) (offset + k)
  | .store op mem offset => .store op (mem + k) (offset + k)
  | .memorySize mem => .memorySize (mem + k)
  | .memoryGrow mem => .memoryGrow (mem + k)
  | .memoryInit data mem => .memoryInit (data + k) (mem + k)
  | .dataDrop x => .dataDrop (x + k)
  | .memoryCopy dst src => .memoryCopy (dst + k) (src + k)
  | .memoryFill mem => .memoryFill (mem + k)
  | .const v => .const (v + k.toUInt64)
  | .refIsNull => .refIsNull
  | .refFunc f => .refFunc (f + k)
  | .num op => .num (keepNumOp k op)
  | .llBin x y op => .llBin (x + k) (y + k) (keepNumOp k op)
  | .lcBin x c op => .lcBin (x + k) (c + k.toUInt64) (keepNumOp k op)
  | .cBin c op => .cBin (c + k.toUInt64) (keepNumOp k op)
  | .lUn x op => .lUn (x + k) (keepNumOp k op)
  | .binSet op z => .binSet (keepNumOp k op) (z + k)
  | .lcBinSet x c op z => .lcBinSet (x + k) (c + k.toUInt64) (keepNumOp k op) (z + k)
  | .llBinJump x y op t onZero => .llBinJump (x + k) (y + k) (keepNumOp k op) (t + k) onZero
  | .lcBinJump x c op t onZero => .lcBinJump (x + k) (c + k.toUInt64) (keepNumOp k op) (t + k) onZero
  | .binJump op t onZero => .binJump (keepNumOp k op) (t + k) onZero
  | .throw tag n => .throw (tag + k) (n + k)
  | .throwRef => .throwRef
  | .rethrow slot => .rethrow (slot + k)
  | .returnCall f => .returnCall (f + k)
  | .returnCallIndirect type table => .returnCallIndirect (type + k) (table + k)
  | .callRef => .callRef
  | .returnCallRef => .returnCallRef
  | .refAsNonNull => .refAsNonNull
  | .brOnNull t => .brOnNull (t.freshWith k)
  | .brOnNonNull t => .brOnNonNull (t.freshWith k)
  | .handlers hs => .handlers (hs.map (Handler.freshWith k))
  | .simd code mem offset lane => .simd (code + k) (mem + k) (offset + k) (lane + k)
  | .simdImm code lo hi => .simdImm (code + k) (lo + k.toUInt64) (hi + k.toUInt64)
  | .vLocalGet x => .vLocalGet (x + k)
  | .vLocalSet x => .vLocalSet (x + k)
  | .vLocalTee x => .vLocalTee (x + k)
  | .vSelect => .vSelect
  | .vGlobalGet x => .vGlobalGet (x + k)
  | .vGlobalSet x => .vGlobalSet (x + k)
  | .vBrTable ts d => .vBrTable (ts.map (BrTarget.freshWith k)) (d.freshWith k)
  | .hiMove skip n height => .hiMove (skip + k) (n + k) (height + k)
  | .hiZero x n => .hiZero (x + k) (n + k)
  | .gc code a b c => .gc (code + k) (a + k) (b + k) (c + k)
  | .gcBr t flags ht => .gcBr (t.freshWith k) (flags + k) (ht + k)

/-- A new copy of an op (see above). -/
def Op.fresh (o : Op) : Op := o.freshWith freshZero

/-- A new copy of an array of slot bits. -/
def freshBits (a : Array UInt64) : Array UInt64 := a.foldl (·.push ·) (Array.mkEmpty a.size)

/-- A new, single-threaded copy of a compiled function (see above). -/
def CompiledFunc.fresh (f : CompiledFunc) : CompiledFunc :=
  { type := f.type + freshZero, nParams := f.nParams + freshZero, localInit := freshBits f.localInit,
    maxHeight := f.maxHeight + freshZero, code := f.code.map Op.fresh }

theorem BrTarget.freshWith_zero : BrTarget.freshWith 0 = id := funext fun _ => rfl
theorem CatchTarget.freshWith_zero : CatchTarget.freshWith 0 = id := funext fun c => by
  cases c with | mk tag => cases tag <;> rfl
theorem Handler.freshWith_zero : Handler.freshWith 0 = id := funext fun h => by
  cases h with | mk start stop catches next =>
  cases next <;> simp [Handler.freshWith, CatchTarget.freshWith_zero]

theorem Op.fresh_id : Op.fresh = id := funext fun o => by
  cases o <;> simp [Op.fresh, freshZero, Op.freshWith, BrTarget.freshWith_zero, Handler.freshWith_zero, keepNumOp]

theorem freshBits_eq (a : Array UInt64) : freshBits a = a := by
  unfold freshBits
  rw [← Array.foldl_toList]
  suffices ∀ (l : List UInt64) (acc : Array UInt64), l.foldl (·.push ·) acc = acc ++ l.toArray by
    rw [this]; simp
  intro l; induction l with
  | nil => intro acc; simp
  | cons x xs ih => intro acc; simp [ih]

theorem CompiledFunc.fresh_eq (f : CompiledFunc) : f.fresh = f := by
  cases f; simp [CompiledFunc.fresh, freshBits_eq, Op.fresh_id, freshZero]


/-- The handler table of compiled code (empty when the function has no `try`). -/
def handlersOf (code : Array Op) : Array Handler :=
  match code.back? with
  | some (.handlers hs) => hs
  | _ => #[]

end L4Factoidal.WasmVM
