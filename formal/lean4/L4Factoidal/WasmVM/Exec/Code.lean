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
  deriving Repr, Inhabited

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

def zeros (n : Nat) : Slots := grow (ByteArray.emptyWithCapacity (8 * n)) n

end Slots

/-- The bits of a null reference. -/
def nullRef : UInt64 := 0xFFFFFFFFFFFFFFFF

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

/-- The handler table of compiled code (empty when the function has no `try`). -/
def handlersOf (code : Array Op) : Array Handler :=
  match code.back? with
  | some (.handlers hs) => hs
  | _ => #[]

end L4Factoidal.WasmVM
