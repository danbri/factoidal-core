import EVMCleanroom.Core

/-!
# Declarative instruction boundaries and JUMPDEST soundness

These are theorems for *arbitrary bytecode arrays*, including malformed code
and PUSH1..PUSH32 immediate payloads, not merely individual examples.

The declarative relation defines candidate instruction boundaries by
starting at byte zero and advancing by the width of the current opcode.
A decoder claiming a valid JUMPDEST must provide an inhabitant of this
relation and an opcode equal to 0x5b at the target.

This is a soundness theorem for the local decoder. Completeness and
refinement against EELS are separate obligations.
-/

namespace EVMCleanroom

/-- A parsed instruction boundary: zero, or the next byte after an entire
    instruction at another boundary. In particular PUSH immediates are not
    independently executable instructions. -/
inductive InstructionStart (code : Array UInt8) : Nat → Prop where
  | atZero : InstructionStart code 0
  | next {pc : Nat} (h : InstructionStart code pc) (inCode : pc < code.size) :
      InstructionStart code (pc + opcodeWidth code pc)

/-- Every opcode consumes between one and 33 bytes in the legacy EVM
    instruction encoding. -/
theorem opcodeWidth_bounds (code : Array UInt8) (pc : Nat) :
    1 ≤ opcodeWidth code pc ∧ opcodeWidth code pc ≤ 33 := by
  constructor
  · dsimp [opcodeWidth]
    split
    · omega
    · omega
  · dsimp [opcodeWidth]
    split
    · omega
    · omega

/-- Following an opcode boundary strictly advances the byte position. -/
theorem next_opcode_advances (code : Array UInt8) (pc : Nat) :
    pc < pc + opcodeWidth code pc := by
  have hb := (opcodeWidth_bounds code pc).1
  omega

/-- The scanner cannot claim that an arbitrary data byte is an executable
    JUMPDEST. Each successful scan yields a valid parse-boundary witness
    and the JUMPDEST opcode at that exact byte. -/
theorem scanJumpdest_sound (code : Array UInt8) (target fuel : Nat) :
    ∀ (pc : Nat), InstructionStart code pc →
      scanJumpdest code target pc fuel = true →
      InstructionStart code target ∧ (code.getD target 0).toNat = 0x5b := by
  induction fuel with
  | zero =>
    intro pc _ h
    simp [scanJumpdest] at h
  | succ remaining ih =>
    intro pc hstart hscan
    by_cases hsize : pc ≥ code.size
    · simp [scanJumpdest, hsize] at hscan
    · by_cases htarget : pc = target
      · subst target
        have hop : ((code.getD pc 0).toNat == 0x5b) = true := by
          simpa [scanJumpdest, hsize] using hscan
        have hvalue : (code.getD pc 0).toNat = 0x5b := by
          simpa using hop
        exact ⟨hstart, hvalue⟩
      · have hrec : scanJumpdest code target (pc + opcodeWidth code pc)
            remaining = true := by
          simpa [scanJumpdest, hsize, htarget] using hscan
        have hnext : InstructionStart code (pc + opcodeWidth code pc) :=
          InstructionStart.next hstart (Nat.lt_of_not_ge hsize)
        exact ih (pc + opcodeWidth code pc) hnext hrec

/-- Universal JUMPDEST soundness for the local executable scanner.
    This quantifies over *every* bytecode array and candidate jump target. -/
theorem validJumpdest_sound (code : Array UInt8) (target : Nat)
    (h : validJumpdest code target = true) :
    InstructionStart code target ∧ (code.getD target 0).toNat = 0x5b := by
  exact scanJumpdest_sound code target (code.size + 1) 0
    InstructionStart.atZero (by simpa [validJumpdest] using h)

#print axioms opcodeWidth_bounds
#print axioms next_opcode_advances
#print axioms scanJumpdest_sound
#print axioms validJumpdest_sound

end EVMCleanroom
