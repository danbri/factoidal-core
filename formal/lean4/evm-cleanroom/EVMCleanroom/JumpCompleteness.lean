import EVMCleanroom.JumpProofs

/-!
# Completeness of the EVM JUMPDEST scanner

The soundness theorem in JumpProofs establishes that every accepted
JUMPDEST is an instruction boundary. This module proves the converse
for every in-bounds JUMPDEST in the declarative boundary relation.
The proof follows the actual variable-width PUSH1..PUSH32 encoding.

The scanner and declarative relation still use the same local
opcodeWidth; EELS refinement remains a separate proof obligation.
-/

namespace EVMCleanroom

/-- Forward instruction path, carrying the number of complete opcodes
    crossed. It is independent of the implementation's scan fuel. -/
inductive ForwardPath (code : Array UInt8) : Nat → Nat → Nat → Prop where
  | refl (pc : Nat) : ForwardPath code pc pc 0
  | step {pc target count : Nat}
      (hin : pc < code.size)
      (rest : ForwardPath code (pc + opcodeWidth code pc) target count) :
      ForwardPath code pc target (count + 1)

/-- Append one complete instruction to the end of a path. -/
theorem ForwardPath.extend {code : Array UInt8} {start pc count : Nat}
    (h : ForwardPath code start pc count)
    (hin : pc < code.size) :
    ForwardPath code start (pc + opcodeWidth code pc) (count + 1) := by
  induction h with
  | refl _ =>
    exact ForwardPath.step hin (ForwardPath.refl _)
  | step hprev rest ih =>
    exact ForwardPath.step hprev (ih hin)

/-- Every declarative boundary is reachable from byte zero by a finite
    number of complete instruction-width transitions. -/
theorem InstructionStart.hasPath {code : Array UInt8} {target : Nat}
    (h : InstructionStart code target) :
    ∃ count, ForwardPath code 0 target count := by
  induction h with
  | atZero =>
    exact ⟨0, ForwardPath.refl 0⟩
  | next hprev hin ih =>
    obtain ⟨count, hpath⟩ := ih
    exact ⟨count + 1, hpath.extend hin⟩

/-- The opcode count is bounded by distance in bytes. This is what makes
    a scanner fuel bound of code.size+1 sufficient even for variable-width
    PUSH immediates. -/
theorem ForwardPath.count_le_distance {code : Array UInt8}
    {start target count : Nat}
    (h : ForwardPath code start target count) :
    start + count ≤ target := by
  induction h with
  | refl _ =>
    omega
  | @step pc target n hin rest ih =>
    have hwidth := (opcodeWidth_bounds code pc).1
    omega

/-- Every in-range JUMPDEST at the end of a forward instruction path is
    accepted by the scanner with any fuel greater than the opcode count. -/
theorem ForwardPath.scan_accepts {code : Array UInt8}
    {start target count fuel : Nat}
    (h : ForwardPath code start target count)
    (htarget : target < code.size)
    (hopcode : (code.getD target 0).toNat = 0x5b)
    (hfuel : count < fuel) :
    scanJumpdest code target start fuel = true := by
  induction h generalizing fuel with
  | refl pc =>
    cases fuel with
    | zero => omega
    | succ remaining =>
      simp [scanJumpdest, Nat.not_le_of_gt htarget]
      simpa only [Array.getD_eq_getD_getElem?] using hopcode
  | @step pc target count hin rest ih =>
    cases fuel with
    | zero => omega
    | succ remaining =>
      have hprogress : pc ≠ target := by
        have hb := ForwardPath.count_le_distance rest
        have hw := (opcodeWidth_bounds code pc).1
        omega
      have hnext : scanJumpdest code target (pc + opcodeWidth code pc)
          remaining = true := ih htarget hopcode (by omega)
      simpa [scanJumpdest, Nat.not_le_of_gt hin, hprogress] using hnext

/-- Completeness: any declared in-bounds JUMPDEST instruction boundary is
    recognised by the executable scanner. This is true for all finite
    bytecode arrays, including malformed/truncated PUSH immediates. -/
theorem validJumpdest_complete (code : Array UInt8) (target : Nat)
    (hstart : InstructionStart code target)
    (hin : target < code.size)
    (hopcode : (code.getD target 0).toNat = 0x5b) :
    validJumpdest code target = true := by
  obtain ⟨count, hpath⟩ := InstructionStart.hasPath hstart
  have hsteps := ForwardPath.count_le_distance hpath
  have hfuel : count < code.size + 1 := by omega
  exact ForwardPath.scan_accepts hpath hin hopcode hfuel

#print axioms ForwardPath.extend
#print axioms InstructionStart.hasPath
#print axioms ForwardPath.count_le_distance
#print axioms ForwardPath.scan_accepts
#print axioms validJumpdest_complete

end EVMCleanroom
