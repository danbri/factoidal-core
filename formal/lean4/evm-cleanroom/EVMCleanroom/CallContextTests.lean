import EVMCleanroom.CallOpcode

/-!
# Executable CALL context guards

These guards exercise the EXACT Core.step / World.frameInput code paths used
by the full EVM CALL interpreter; they are not duplicated pure calculations.
They verify fork-aware prices and distinguish CALLVALUE (incoming wei) from
SELFBALANCE (current account balance) and ADDRESS (current target).
-/

namespace EVMCleanroom.CallContextTests

private def observe (op : UInt8) (value balance address : Nat) : Option (Nat × Nat) :=
  let input : EVMCleanroom.State := {
    code := #[op, 0x00], gas := 100,
    callValue := value, selfBalance := balance,
    currentAddress := address
  }
  match EVMCleanroom.run 4 input with
  | .ok after =>
    after.stack.items.head?.map (fun w => (w.val, after.gas))
  | .error _ => none

#guard observe 0x34 2 7 0xc3 == some (2, 98)  -- CALLVALUE 2 gas
#guard observe 0x34 0 7 0xc3 == some (0, 98)
#guard observe 0x47 2 7 0xc3 == some (7, 95)  -- SELFBALANCE 5 gas
#guard observe 0x30 2 7 0xc3 == some (0xc3, 98) -- ADDRESS 2 gas

private def accountAt (addr : Nat) : World.Account :=
  if addr == 0xc3 then { balance := 7, code := #[0x34, 0x00] }
  else {}

private def projected : State :=
  World.frameInput (World.beginTransaction accountAt) 0xc3 100

#guard projected.currentAddress == 0xc3
#guard projected.callValue == 0
#guard projected.selfBalance == 7


-- Explicit top-level context, distinct from the executable account's address.
private def observeParticipants (op : UInt8) (origin caller : Nat) (gas : Nat := 100) :
    Option (Nat × Nat) :=
  let input : State := { code := #[op, 0x00], gas := gas,
    txOrigin := origin, callerAddress := caller }
  match EVMCleanroom.run 4 input with
  | .ok out => out.stack.items.head?.map (fun w => (w.val, out.gas))
  | .error _ => none

#guard observeParticipants 0x32 0x77 0xc2 == some (0x77, 98)
#guard observeParticipants 0x33 0x77 0xc2 == some (0xc2, 98)
#guard observeParticipants 0x32 0x77 0xc2 1 == none
#guard observeParticipants 0x33 0x77 0xc2 1 == none

-- Real parent CALL, real child SSTORE, actual nested interpreter path.
private def nestedParticipantSlot (opcode : UInt8) : Option Nat :=
  let parentCode : Array UInt8 :=
    #[0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x60, 0xc3, 0x61, 0x75, 0x30, 0xf1, 0x00]
  let childCode : Array UInt8 := #[opcode, 0x60, 0x00, 0x55, 0x00]
  let accounts : Nat → World.Account := fun address =>
    if address == 0xc1 then { balance := 100000, code := parentCode }
    else if address == 0xc3 then { code := childCode }
    else {}
  let w := World.beginTransaction accounts
  let parent := World.frameInput w 0xc1 100000 false .shanghaiPlus 0x77 0x42
  match CallOpcode.execute 40 w 0xc1 parent with
  | .stopped outputWorld _ => some ((outputWorld.accounts 0xc3).storage 0)
  | _ => none

#guard nestedParticipantSlot 0x33 == some 0xc1
#guard nestedParticipantSlot 0x32 == some 0x77

end EVMCleanroom.CallContextTests
