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

end EVMCleanroom.CallContextTests
