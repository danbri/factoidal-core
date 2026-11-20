import EVMCleanroom.World

/-!
Two distinct account addresses with independently existing storage. Tests
exercise whole-world isolation and the transaction-original-value snapshot,
not an actual EVM CALL instruction or authenticated Merkle state root.
-/

namespace EVMCleanroom.WorldTests
open EVMCleanroom.World

private def accountA : Account :=
  { balance := 100, nonce := 1
    code := #[0x60,0x01,0x60,0x00,0x55,0x00] }

private def accountB : Account :=
  { balance := 200, nonce := 3
    code := #[0x60,0x00,0x60,0x00,0x55,
              0x60,0x00,0x60,0x00,0xfd]
    storage := fun k => if k == 0 then 7 else 0 }

private def initialAccounts (addr : Nat) : Account :=
  if addr == 1 then accountA
  else if addr == 2 then accountB
  else {}

private def initial : TxWorld := beginTransaction initialAccounts

private def afterA : Option TxWorld :=
  match runAt 12 initial 1 50000 with
  | .stopped w _ => some w
  | _ => none

private def afterB : Option TxWorld :=
  match afterA with
  | some w =>
    match runAt 12 w 2 50000 with
    | .reverted final _ _ _ => some final
    | _ => none
  | none => none

private def storageAt (ow : Option TxWorld) (address slot : Nat) : Option Nat :=
  ow.map (fun w => (w.accounts address).storage slot)

private def originalAt (ow : Option TxWorld) (address slot : Nat) : Option Nat :=
  ow.map (fun w => w.original address slot)

private def balanceAt (ow : Option TxWorld) (address : Nat) : Option Nat :=
  ow.map (fun w => (w.accounts address).balance)

private def nonceAt (ow : Option TxWorld) (address : Nat) : Option Nat :=
  ow.map (fun w => (w.accounts address).nonce)

-- Account A writes slot zero; account B's original and current remain 7.
#guard storageAt afterA 1 0 == some 1
#guard storageAt afterA 2 0 == some 7
#guard originalAt afterA 1 0 == some 0
#guard originalAt afterA 2 0 == some 7

-- Executing B's frame clears its slot and then REVERTs, preserving the
-- already-committed write to A. No account balances or nonces change.
#guard storageAt afterB 1 0 == some 1
#guard storageAt afterB 2 0 == some 7
#guard originalAt afterB 1 0 == some 0
#guard originalAt afterB 2 0 == some 7
#guard balanceAt afterB 1 == some 100
#guard balanceAt afterB 2 == some 200
#guard nonceAt afterB 1 == some 1
#guard nonceAt afterB 2 == some 3

-- Reverting at a new account cannot erase unrelated warm access state.
private def firstFrameWarm : Bool :=
  match afterA with
  | some w => w.warmSlots 1 0 && !(w.warmSlots 2 0)
  | none => false

private def revertedFrameWarm : Bool :=
  match afterB with
  | some w => w.warmSlots 1 0 && !(w.warmSlots 2 0)
  | none => false

#guard firstFrameWarm
#guard revertedFrameWarm

end EVMCleanroom.WorldTests
