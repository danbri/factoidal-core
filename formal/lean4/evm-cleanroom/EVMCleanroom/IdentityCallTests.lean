import EVMCleanroom.CallOpcode

/-!
# Identity precompile at both public world-aware CALL entry points

These executable guards start from the same decoded caller and compare the
public `callStep` adapter with the normal opcode dispatcher. The target
account deliberately contains INVALID: address 0x04 must execute identity
instead of that account code. The fixtures check exact bytes, gas and the
failure bit. They are regression tests, not universal refinement proofs.
-/

namespace EVMCleanroom.IdentityCallTests

open World CallOpcode

private def testWorld : TxWorld :=
  beginTransaction fun address =>
    if address == 0xc1 then { code := #[0xf1, 0x00], balance := 100 }
    else if address == 4 then { code := #[0xfe], balance := 1 }
    else {}

private def inputMemory : Memory :=
  (Memory.empty.expand 2).copyFrom (ByteView.ofArray #[0x00, 0x11, 0x80, 0xff]) 0 0 4

private def caller (requested size : Nat := 4) (value : Nat := 0) : State :=
  { frameInput testWorld 0xc1 100000 with
    memory := inputMemory
    stack := ⟨[word requested, word 4, word value, word 0, word size, word 32, word 4], by simp⟩ }

private def observeState (world : TxWorld) (state : State) :
    Nat × Nat × List Nat × List Nat × Nat × Nat :=
  (state.gas, state.returnData.size, state.stack.items.map (·.val),
    (List.range 4).map (fun i => (state.memory.readByte (32 + i)).toNat),
    (world.accounts 0xc1).balance, (world.accounts 4).balance)

private def single (requested : Nat) (size : Nat := 4) (value : Nat := 0) :=
  match callStep 20 testWorld 0xc1 (caller requested size value) with
  | .committed world state => some (observeState world state)
  | _ => none

private def dispatched (requested : Nat) (size : Nat := 4) (value : Nat := 0) :=
  match execute 20 testWorld 0xc1 (caller requested size value) with
  | .stopped world state => some (observeState world state)
  | _ => none

-- Both APIs charge identity's eighteen gas and preserve the leading zero.
#guard single 20 == some (99882, 4, [1], [0, 17, 128, 255], 100, 1)
#guard dispatched 20 == single 20
#guard single 18 == single 20
#guard dispatched 18 == single 18

-- Child gas below eighteen produces zero without running target INVALID.
#guard single 17 == some (99883, 0, [0], [0, 0, 0, 0], 100, 1)
#guard dispatched 17 == single 17
#guard single 0 == some (99900, 0, [0], [0, 0, 0, 0], 100, 1)
#guard dispatched 0 == single 0

-- Empty input costs fifteen gas; it does not overwrite the output window.
#guard single 15 0 == some (99885, 0, [1], [0, 0, 0, 0], 100, 1)
#guard dispatched 15 0 == single 15 0
#guard single 14 0 == some (99886, 0, [0], [0, 0, 0, 0], 100, 1)
#guard dispatched 14 0 == single 14 0

-- The stipend permits identity even with zero explicitly requested gas.
#guard single 0 4 1 == some (93182, 4, [1], [0, 17, 128, 255], 99, 2)
#guard dispatched 0 4 1 == single 0 4 1

private def oversizedCaller : State :=
  { frameInput testWorld 0xc1 1000000000 with
    stack := ⟨[word 10000000, word 4, word 0, word 0,
      word (maxIdentityCallBytes + 1), word 0, word 0], by decide⟩ }

-- The local input limit remains indeterminate, not an EVM failure bit.
#guard (match callStep 20 testWorld 0xc1 oversizedCaller with
  | .indeterminate .resourceLimit => true
  | _ => false)
#guard (match execute 20 testWorld 0xc1 oversizedCaller with
  | .indeterminate .resourceLimit => true
  | _ => false)

end EVMCleanroom.IdentityCallTests
