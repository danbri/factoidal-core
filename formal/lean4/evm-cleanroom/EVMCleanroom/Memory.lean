import EVMCleanroom.MemoryGas

/-!
# Byte-addressed, sparse EVM memory

Functional byte store with an explicit high-water mark in 32-byte words.
Unallocated and unwritten bytes are zero. This representation intentionally
does not allocate an offset-sized host array on an EVM memory access: even
adversarially large offsets remain representable until gas checking rejects
them. This is a semantic model, not a high-performance byte-array backend.

EELS Prague: forks/prague/vm/instructions/memory.py and vm/gas.py.
-/

namespace EVMCleanroom

/-- A bounded byte source. The backing function is consulted only within the view. -/
structure ByteView where
  size : Nat := 0
  raw : Nat → UInt8 := fun _ => 0

def ByteView.readByte (view : ByteView) (offset : Nat) : UInt8 :=
  if offset < view.size then view.raw offset else 0

def ByteView.ofArray (bytes : Array UInt8) : ByteView :=
  { size := bytes.size, raw := fun offset => bytes.getD offset 0 }

structure Memory where
  words : Nat := 0
  raw : Nat → UInt8 := fun _ => 0

def Memory.empty : Memory := {}

/-- Bytes outside the paid-for high-water mark behave as zero. -/
def Memory.readByte (m : Memory) (address : Nat) : UInt8 :=
  if address < 32 * m.words then m.raw address else 0

/-- A read-only window on an immutable memory snapshot. -/
def ByteView.ofMemory (m : Memory) (offset length : Nat) : ByteView :=
  { size := length, raw := fun i => m.readByte (offset + i) }

/-- Expansion increases the high-water mark but materializes no bytes. -/
def Memory.expand (m : Memory) (targetWords : Nat) : Memory :=
  { m with words := max m.words targetWords }

/-- Replace one stored byte; called only after memory expansion. -/
def Memory.writeByte (m : Memory) (address : Nat) (value : UInt8) : Memory :=
  { m with raw := fun i => if i == address then value else m.raw i }

/-- Overlay a destination range on already expanded memory. The view is
    immutable and may share memory with the destination's earlier snapshot.
    The overlay stores the range and source without enumerating its bytes. -/
def Memory.copyFrom (m : Memory) (source : ByteView)
    (sourceOffset destOffset length : Nat) : Memory :=
  if length = 0 then m
  else
    let destEnd := destOffset + length
    { m with raw := fun address =>
        if destOffset ≤ address ∧ address < destEnd then
          source.readByte (sourceOffset + (address - destOffset))
        else m.raw address }

/-- Kind: boundary.
    Says: an empty copy leaves the complete memory value unchanged.
    Does not say: an opcode with zero length bypasses its other checks. -/
theorem Memory.copyFrom_zero (m : Memory) (source : ByteView) (sourceOffset destOffset : Nat) :
    m.copyFrom source sourceOffset destOffset 0 = m := rfl

/-- Kind: invariant.
    Says: a copy overlay retains the allocated word count.
    Does not say: the instruction that requested the copy cannot expand memory. -/
theorem Memory.copyFrom_preserves_words (m : Memory) (source : ByteView)
    (sourceOffset destOffset length : Nat) :
    (m.copyFrom source sourceOffset destOffset length).words = m.words := by
  unfold Memory.copyFrom
  split <;> rfl

/-- Kind: correspondence.
    Says: each allocated byte in the destination range reads its corresponding source byte.
    Does not say: creating the overlay expands memory. -/
theorem Memory.readByte_copyFrom_inside (m : Memory) (source : ByteView)
    (sourceOffset destOffset length address : Nat) (hPaid : address < 32 * m.words)
    (hStart : destOffset ≤ address) (hEnd : address < destOffset + length) :
    (m.copyFrom source sourceOffset destOffset length).readByte address =
      source.readByte (sourceOffset + (address - destOffset)) := by
  have hNonempty : length ≠ 0 := by omega
  simp [Memory.copyFrom, Memory.readByte, hNonempty, hPaid, hStart, hEnd]

/-- Kind: non-interference.
    Says: each byte outside the destination range keeps its previous value.
    Does not say: a later expansion preserves the memory high-water mark. -/
theorem Memory.readByte_copyFrom_outside (m : Memory) (source : ByteView)
    (sourceOffset destOffset length address : Nat)
    (hOutside : address < destOffset ∨ destOffset + length ≤ address) :
    (m.copyFrom source sourceOffset destOffset length).readByte address = m.readByte address := by
  have hOutside' : ¬ (destOffset ≤ address ∧ address < destOffset + length) := by omega
  by_cases hEmpty : length = 0 <;> simp [Memory.copyFrom, Memory.readByte, hEmpty, hOutside']

#print axioms Memory.copyFrom_zero
#print axioms Memory.copyFrom_preserves_words
#print axioms Memory.readByte_copyFrom_inside
#print axioms Memory.readByte_copyFrom_outside

/-- Big-endian 32-byte EVM memory read, 256-bit value as a Nat. -/
def Memory.readWord (m : Memory) (start : Nat) : Nat :=
  (List.range 32).foldl
    (fun acc i => acc * 256 + (m.readByte (start + i)).toNat) 0

/-- Big-endian 32-byte EVM memory write; low 256 bits of the value. -/
def Memory.writeWord (m : Memory) (start value : Nat) : Memory :=
  (List.range 32).foldl
    (fun acc i =>
      let byte := UInt8.ofNat ((value / (256 ^ (31 - i))) % 256)
      acc.writeByte (start + i) byte) m

/-- Expansion cannot reduce the allocated word count. -/
theorem Memory.expand_monotone (m : Memory) (targetWords : Nat) :
    m.words ≤ (m.expand targetWords).words := by
  simp [Memory.expand, Nat.le_max_left]

/-- Writing a byte does not charge memory or alter the allocation size. -/
theorem Memory.writeByte_preserves_words (m : Memory) (address : Nat) (value : UInt8) :
    (m.writeByte address value).words = m.words := rfl

/-- A byte write is visible address its address if that address is allocated. -/
theorem Memory.readByte_after_write (m : Memory) (address : Nat) (value : UInt8)
    (h : address < 32 * m.words) :
    (m.writeByte address value).readByte address = value := by
  simp [Memory.readByte, Memory.writeByte, h]

/-- Expansion of empty memory produces zero-filled bytes. -/
theorem Memory.empty_expand_zero (targetWords address : Nat) :
    ((Memory.empty).expand targetWords).readByte address = 0 := by
  simp [Memory.readByte, Memory.empty, Memory.expand]

#print axioms Memory.expand_monotone
#print axioms Memory.writeByte_preserves_words
#print axioms Memory.readByte_after_write
#print axioms Memory.empty_expand_zero

/-- Writing to one byte cannot affect a different byte, even if memory
    is sparse and the target lies outside the current allocation. -/
theorem Memory.readByte_write_other (m : Memory) (written queried : Nat)
    (value : UInt8) (h : queried ≠ written) :
    (m.writeByte written value).readByte queried = m.readByte queried := by
  simp [Memory.readByte, Memory.writeByte, h]

/-- Materializing 32 bytes cannot itself increase the paid-for allocation.
    All such expansion is accounted for separately in the opcode gas plan. -/
private theorem foldWordBytes_preserves_words (positions : List Nat)
    (m : Memory) (start value : Nat) :
    (positions.foldl
      (fun acc i => acc.writeByte (start + i)
        (UInt8.ofNat ((value / (256 ^ (31 - i))) % 256))) m).words = m.words := by
  induction positions generalizing m with
  | nil => rfl
  | cons i rest ih =>
    change (rest.foldl
      (fun acc j => acc.writeByte (start + j)
        (UInt8.ofNat ((value / (256 ^ (31 - j))) % 256)))
      (m.writeByte (start + i)
        (UInt8.ofNat ((value / (256 ^ (31 - i))) % 256)))).words = m.words
    exact (ih (m := m.writeByte (start + i)
      (UInt8.ofNat ((value / (256 ^ (31 - i))) % 256)))).trans
      (Memory.writeByte_preserves_words m (start + i)
        (UInt8.ofNat ((value / (256 ^ (31 - i))) % 256)))

theorem Memory.writeWord_preserves_words (m : Memory) (start value : Nat) :
    (m.writeWord start value).words = m.words := by
  exact foldWordBytes_preserves_words (List.range 32) m start value

#print axioms Memory.readByte_write_other
#print axioms Memory.writeWord_preserves_words

end EVMCleanroom
