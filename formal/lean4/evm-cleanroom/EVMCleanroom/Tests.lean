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

end EVMCleanroom
