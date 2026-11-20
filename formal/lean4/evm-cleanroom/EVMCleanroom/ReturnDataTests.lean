import EVMCleanroom.OpcodeCall

/-! Scoped EIP-211 byte copying, gas and actual CALL-return-data tests. -/

namespace EVMCleanroom.ReturnDataTests

private def buffer : Array UInt8 := #[0x2a]
private def input (offset length dest : Nat) (gas : Nat := 100) : State :=
  { code := #[0x3e], gas := gas,
    stack := { items := [word dest, word offset, word length],
      bounded := by decide } }

private def copiedByte (r : Except Error State) (addr : Nat) : Option Nat :=
  match r with
  | .ok s => some (s.memory.readByte addr).toNat
  | .error _ => none

private def remaining (r : Except Error State) : Option Nat :=
  match r with
  | .ok s => some s.gas
  | .error _ => none

private def allocated (r : Except Error State) : Option Nat :=
  match r with
  | .ok s => some s.memory.words
  | .error _ => none

private def outOfBounds (r : Except Error State) : Bool :=
  match r with
  | .error .returnDataOutOfBounds => true
  | _ => false

#guard copiedByte (ReturnData.copy (input 0 1 31) buffer) 31 == some 42
#guard remaining (ReturnData.copy (input 0 1 31) buffer) == some 91
#guard allocated (ReturnData.copy (input 0 1 31) buffer) == some 1
#guard outOfBounds (ReturnData.copy (input 1 1 0) buffer)
#guard outOfBounds (ReturnData.copy (input 2 0 0) buffer)
#guard remaining (ReturnData.copy (input 1 0 1000000) buffer) == some 97
#guard allocated (ReturnData.copy (input 1 0 1000000) buffer) == some 0
#guard remaining (ReturnData.copy (input 0 1 31 8) buffer) == none

end EVMCleanroom.ReturnDataTests
