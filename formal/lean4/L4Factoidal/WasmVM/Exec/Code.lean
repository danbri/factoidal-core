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

namespace L4Factoidal.WasmVM

/-- A branch target: the pc to go to, the number of values to keep and the operand
height (relative to `fp`) at which they go. -/
structure BrTarget where
  pc : Nat
  keep : Nat
  height : Nat
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
  deriving Repr, Inhabited

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

end L4Factoidal.WasmVM
