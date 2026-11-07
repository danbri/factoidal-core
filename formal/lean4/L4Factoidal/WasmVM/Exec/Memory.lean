/-
L4Factoidal.WasmVM.Exec.Memory: the linear-memory interface and backend A
(https://github.com/danbri/factoidal/issues/1244, https://github.com/danbri/factoidal/issues/1289
section 1; record: docs/designissues/2026-11-07-wasmvm-engine.md, "Linear memory").

The engine (`Exec/Run.lean`, `Exec/Instantiate.lean`, `Api.lean`) reaches a memory only
through `LinearMemory`. It never assumes that a memory is a Lean `ByteArray`.

- The class is an instance argument of the engine functions, which are
  `@[specialize]`: compiled code has one copy of the loop per backend, with the
  backend's functions inlined. There is no call through a table per access
  (checked in the emitted C: see the record).
- Loads and stores take a proof that the access is in range (`ea + w ≤ size m`); the
  engine makes the one check. So a backend needs no check of its own.
- `create` gets the most bytes the memory may ever have (`max`), so a backend can
  reserve that address range and commit pages at `grow`.
- Backend A, `ByteMem`, is a `ByteArray`. It is also the reference model: the
  differential test of a second backend runs the same program on both
  (`WasmVM/Tests/Memory.lean`).

Ownership: a memory value is held by exactly one `MemInst` in one store, and the loop
holds that store with reference count 1, so stores update in place. A host function
gets the store, not the memory, and reads and writes through `Store.readMem` and
`Store.writeMem`; it gives the store back through `resume`. A caller that keeps an
old store and runs on a new one pays one copy of each memory it then writes. The test
`Tests/Memory.lean` fails when a store copies the memory.
-/
import L4Factoidal.WasmVM.Exec.Bytes

namespace L4Factoidal.WasmVM

class LinearMemory (M : Type) where
  /-- An empty memory (the `Inhabited` value). -/
  empty : M
  /-- Size in bytes. -/
  size : M → Nat
  /-- `n` zero bytes; the memory never grows past `max` bytes. -/
  create : (n : Nat) → (max : Nat) → M
  /-- Add `n` zero bytes at the end. The caller checks the limits. -/
  grow : M → Nat → M
  load8 : (m : M) → (ea : Nat) → ea + 1 ≤ size m → UInt64
  load16 : (m : M) → (ea : Nat) → ea + 2 ≤ size m → UInt64
  load32 : (m : M) → (ea : Nat) → ea + 4 ≤ size m → UInt64
  load64 : (m : M) → (ea : Nat) → ea + 8 ≤ size m → UInt64
  /-- Store the low byte(s) of `v`, little-endian. -/
  store8 : (m : M) → (ea : Nat) → UInt64 → ea + 1 ≤ size m → M
  store16 : (m : M) → (ea : Nat) → UInt64 → ea + 2 ≤ size m → M
  store32 : (m : M) → (ea : Nat) → UInt64 → ea + 4 ≤ size m → M
  store64 : (m : M) → (ea : Nat) → UInt64 → ea + 8 ≤ size m → M
  /-- `memory.copy` inside one memory, correct for overlapping ranges. The caller
  checks both ranges. -/
  copyWithin : M → (src dst n : Nat) → M
  /-- Copy `n` bytes from `src` at `s` into `dst` at `d`. The caller checks. -/
  copyInto : (src : M) → (s : Nat) → (dst : M) → (d n : Nat) → M
  /-- `memory.fill`. The caller checks. -/
  fill : M → (d : Nat) → UInt8 → (n : Nat) → M
  /-- Write `bytes[s .. s+n)` at `d` (data segments, `memory.init`, host writes).
  The caller checks. -/
  writeBytes : M → (d : Nat) → (bytes : ByteArray) → (s n : Nat) → M
  /-- Read `n` bytes at `off` (host reads). The caller checks. -/
  readBytes : M → (off n : Nat) → ByteArray

instance (M : Type) [LinearMemory M] : Inhabited M := ⟨LinearMemory.empty⟩

/-! ### Backend A: a `ByteArray` -/

/-- Backend A: the memory is a `ByteArray`. -/
structure ByteMem where
  data : ByteArray

namespace ByteMem
open Bytes

def fillBytes (d : ByteArray) (ea : Nat) (v : UInt8) : Nat → ByteArray
  | 0 => d
  | k + 1 => fillBytes (d.set! ea v) (ea + 1) v k

def copyFwd (d : ByteArray) (src dst : Nat) : Nat → ByteArray
  | 0 => d
  | k + 1 => copyFwd (d.set! dst (d.get! src)) (src + 1) (dst + 1) k
def copyBwd (d : ByteArray) (src dst : Nat) : Nat → ByteArray
  | 0 => d
  | k + 1 => copyBwd (d.set! (dst + k) (d.get! (src + k))) src dst k

def zeros (n : Nat) : ByteArray := go n (ByteArray.emptyWithCapacity n)
where
  go : Nat → ByteArray → ByteArray
    | 0, b => b
    | k + 1, b => go k (b.push 0)

/-- Size is `usize` (equal to `size` for every array that fits in memory), so a check
against it gives the `USize` offsets their proof. -/
@[inline] def size (m : ByteMem) : Nat := m.data.usize.toNat

instance : LinearMemory ByteMem where
  empty := ⟨ByteArray.empty⟩
  size := size
  create n _ := ⟨zeros n⟩
  grow m n := ⟨m.data ++ zeros n⟩
  load8 m ea h := ld8 m.data ea.toUSize (nat_ok h)
  load16 m ea h := ld16 m.data ea.toUSize (nat_ok h)
  load32 m ea h := ld32 m.data ea.toUSize (nat_ok h)
  load64 m ea h := ld64 m.data ea.toUSize (nat_ok h)
  store8 m ea v h := ⟨st8 m.data ea.toUSize v (nat_ok h)⟩
  store16 m ea v h := ⟨st16 m.data ea.toUSize v (nat_ok h)⟩
  store32 m ea v h := ⟨st32 m.data ea.toUSize v (nat_ok h)⟩
  store64 m ea v h := ⟨st64 m.data ea.toUSize v (nat_ok h)⟩
  copyWithin m s d n := ⟨if d ≤ s then copyFwd m.data s d n else copyBwd m.data s d n⟩
  copyInto src s dst d n := ⟨src.data.copySlice s dst.data d n⟩
  fill m d v n := ⟨fillBytes m.data d v n⟩
  writeBytes m d b s n := ⟨b.copySlice s m.data d n⟩
  readBytes m off n := m.data.extract off (off + n)

end ByteMem
end L4Factoidal.WasmVM
