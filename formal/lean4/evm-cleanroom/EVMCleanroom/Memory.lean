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

structure Memory where
  words : Nat := 0
  raw : Nat → UInt8 := fun _ => 0

def Memory.empty : Memory := {}

/-- Bytes outside the paid-for high-water mark behave as zero. -/
def Memory.readByte (m : Memory) (address : Nat) : UInt8 :=
  if address < 32 * m.words then m.raw address else 0

/-- Expansion increases the high-water mark but materializes no bytes. -/
def Memory.expand (m : Memory) (targetWords : Nat) : Memory :=
  { m with words := max m.words targetWords }

/-- Replace one stored byte; called only after memory expansion. -/
def Memory.writeByte (m : Memory) (address : Nat) (value : UInt8) : Memory :=
  { m with raw := fun i => if i == address then value else m.raw i }

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
theorem Memory.writeWord_preserves_words (m : Memory) (start value : Nat) :
    (m.writeWord start value).words = m.words := by
  simp [Memory.writeWord, Memory.writeByte]

#print axioms Memory.readByte_write_other
#print axioms Memory.writeWord_preserves_words

end EVMCleanroom
