import EVMCleanroom.Core
/-! Executable smoke and edge tests. Each #guard is checked by Lean. -/

namespace EVMCleanroom

private def initial (code : Array UInt8) (gas : Nat := 100)
    (profile : Profile := .shanghaiPlus) : State :=
  { code := code, gas := gas, profile := profile }

private def isError (result : Except Error State) (expected : Error) : Bool :=
  match result with
  | .error actual => decide (actual = expected)
  | .ok _ => false

private def resultWord (result : Except Error State) : Option Nat :=
  match result with
  | .ok s => s.stack.items.head?.map Word.val
  | .error _ => none

-- PUSH1 2; PUSH1 3; ADD; STOP.
#guard resultWord (run 10 (initial #[0x60, 0x02, 0x60, 0x03, 0x01, 0x00])) == some 5
-- Noncommutative operand order: 7 - 2 = 5.
#guard resultWord (run 10 (initial #[0x60, 0x02, 0x60, 0x07, 0x03, 0x00])) == some 5
-- PUSH0 is available post-Shanghai, but not pre-Shanghai.
#guard resultWord (run 5 (initial #[0x5f, 0x00])) == some 0
#guard isError (step (initial #[0x5f] 10 .preShanghai)) (.invalidOpcode 0x5f)
-- PUSH2 beyond end of code zero-fills its missing immediate byte.
#guard resultWord (run 3 (initial #[0x61, 0xff])) == some 65280
-- JUMPDEST embedded in a PUSH immediate cannot be jumped to.
#guard validJumpdest #[0x60, 0x5b, 0x5b] 1 == false
#guard validJumpdest #[0x60, 0x5b, 0x5b] 2 == true
-- Stack underflow and insufficient gas reject execution.
#guard isError (step (initial #[0x01])) .stackUnderflow
#guard isError (step (initial #[0x60, 0x01] 2)) .outOfGas
-- PC and GAS push the current program counter and post-charge gas.
#guard resultWord (run 3 (initial #[0x58, 0x00])) == some 0
#guard resultWord (run 3 (initial #[0x5a, 0x00])) == some 98
-- DUP1 retains the original element and pushes a copy.
#guard resultWord (run 5 (initial #[0x60, 0x09, 0x80, 0x00])) == some 9
-- A previously halted machine is not stepped again.
#guard isError (step { (initial #[0x00]) with halted := true }) .alreadyHalted

-- The following arithmetic boundary cases are adapted from the official
-- Ethereum execution-spec-tests VM arithmetic addFiller.yml, which expects
-- (2^256-1)+(2^256-1) = 2^256-2 and (2^256-1)+4 = 3 in storage.
-- Here we check the EVM stack computation, not the fixture's full state test.
-- https://github.com/ethereum/execution-spec-tests/blob/main/tests/static/state_tests/VMTests/vmArithmeticTest/addFiller.yml
private def pushMax : Array UInt8 :=
  #[0x7f] ++ (List.replicate 32 (0xff : UInt8)).toArray

#guard resultWord (run 8 (initial (pushMax ++ pushMax ++ #[0x01, 0x00]) 100)) ==
  some (modulus - 2)
#guard resultWord (run 8 (initial (pushMax ++ #[0x60, 0x04, 0x01, 0x00]) 100)) ==
  some 3

-- A JUMP to 0x5b *inside* a PUSH immediate must be rejected.
#guard isError (run 6 (initial #[0x60, 0x5b, 0x60, 0x01, 0x56]))
  (.invalidJump 1)

private def resultGas (result : Except Error State) : Option Nat :=
  match result with
  | .ok s => some s.gas
  | .error _ => none

-- PUSH32 + PUSH32 + ADD + STOP consumes 3 + 3 + 3 + 0 gas.
#guard resultGas (run 8 (initial (pushMax ++ pushMax ++ #[0x01, 0x00]) 100)) ==
  some 91

-- Valid JUMP to JUMPDEST and STOP consume 3 + 8 + 1 + 0 gas.
#guard resultGas (run 8 (initial #[0x60, 0x05, 0x56, 0x00, 0x00, 0x5b, 0x00] 100)) ==
  some 88

-- A bounded driver must accept a STOP using exactly its last fuel unit.
-- Previously, run 1 STOP incorrectly returned stepLimit.
private def successfulAndHalted (r : Except Error State) : Bool :=
  match r with
  | .ok s => s.halted
  | .error _ => false

#guard successfulAndHalted (run 1 (initial #[0x00]))
#guard successfulAndHalted (run 2 (initial #[0x5f, 0x00]))
#guard isError (run 1 (initial #[0x5f, 0x00])) .stepLimit
#guard resultGas (run 2 (initial #[0x5f, 0x00])) == some 98

-- MSTORE followed by MLOAD: 2 survives an actual 32-byte memory round-trip.
-- Gas = PUSH1 (3) + PUSH1 (3) + MSTORE (3+3 expansion)
--     + PUSH1 (3) + MLOAD (3) + STOP (0) = 18.
private def memoryRoundTrip : Except Error State :=
  run 8 (initial #[0x60, 0x02, 0x60, 0x00, 0x52,
                   0x60, 0x00, 0x51, 0x00])

private def resultMemoryWords (result : Except Error State) : Option Nat :=
  match result with
  | .ok s => some s.memory.words
  | .error _ => none

private def resultByte (result : Except Error State) (address : Nat) : Option Nat :=
  match result with
  | .ok s => some ((s.memory.readByte address).toNat)
  | .error _ => none

#guard resultWord memoryRoundTrip == some 2
#guard resultMemoryWords memoryRoundTrip == some 1
#guard resultByte memoryRoundTrip 31 == some 2
#guard resultByte memoryRoundTrip 30 == some 0
#guard resultGas memoryRoundTrip == some 82

-- Big-endian MSTORE: the low two bytes of 0x0102 are at offsets 30 and 31.
private def bigEndianStore : Except Error State :=
  run 5 (initial #[0x61, 0x01, 0x02, 0x60, 0x00, 0x52, 0x00])
#guard resultByte bigEndianStore 30 == some 1
#guard resultByte bigEndianStore 31 == some 2
#guard resultByte bigEndianStore 0 == some 0

-- MSTORE8 keeps only the low byte (0x012c → 0x2c), at the last byte of a word.
private def oneByteStore : Except Error State :=
  run 8 (initial #[0x61, 0x01, 0x2c, 0x60, 0x1f, 0x53,
                   0x60, 0x00, 0x51, 0x00])
#guard resultWord oneByteStore == some 44
#guard resultByte oneByteStore 31 == some 44
#guard resultMemoryWords oneByteStore == some 1
#guard resultGas oneByteStore == some 82

-- Accessing byte 32 expands memory to *64* bytes; MSIZE reports bytes.
#guard resultWord (run 6 (initial #[0x60, 0x01, 0x60, 0x20, 0x53,
                                   0x59, 0x00])) == some 64
#guard resultMemoryWords (run 6 (initial #[0x60, 0x01, 0x60, 0x20,
                                          0x53, 0x59, 0x00])) == some 2
#guard resultGas (run 6 (initial #[0x60, 0x01, 0x60, 0x20,
                                  0x53, 0x59, 0x00])) == some 83
#guard resultWord (run 2 (initial #[0x59, 0x00])) == some 0

-- An initially zero-filled MLOAD starting at byte 31 touches two words.
#guard resultWord (run 4 (initial #[0x60, 0x1f, 0x51, 0x00])) == some 0
#guard resultMemoryWords (run 4 (initial #[0x60, 0x1f, 0x51, 0x00])) == some 2
#guard resultGas (run 4 (initial #[0x60, 0x1f, 0x51, 0x00])) == some 88

-- The interpreter refuses insufficient gas even when the memory update
-- has already been *planned*; functional memory is committed only on success.
#guard isError (run 5 (initial #[0x60, 0x01, 0x60, 0x00, 0x52] 8)) .outOfGas
#guard isError (run 5 (initial (pushMax ++ #[0x51, 0x00]) 100)) .outOfGas

end EVMCleanroom
