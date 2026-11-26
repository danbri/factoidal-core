import EVMCleanroom.Value

namespace EVMCleanroom.WorldValueTests
open EVMCleanroom.World

private def accounts (a : Nat) : Account :=
  if a == 1 then { balance := 100, nonce := 3, storage := fun k => if k == 0 then 8 else 0 }
  else if a == 2 then { balance := 200, nonce := 4 }
  else {}

private def initial : TxWorld := beginTransaction accounts

private def paid : Except TransferError TxWorld := pay initial 1 2 30

private def valueAt (result : Except TransferError TxWorld) (addr : Nat) : Option Nat :=
  match result with
  | .ok w => some (w.accounts addr).balance
  | .error _ => none

private def originalAt (result : Except TransferError TxWorld)
    (addr key : Nat) : Option Nat :=
  match result with
  | .ok w => some (w.original addr key)
  | .error _ => none

private def isTransferError (result : Except TransferError TxWorld)
    (expected : TransferError) : Bool :=
  match result with
  | .error actual => decide (actual = expected)
  | .ok _ => false

#guard valueAt paid 1 == some 70
#guard valueAt paid 2 == some 230
#guard valueAt paid 3 == some 0
#guard originalAt paid 1 0 == some 8
#guard valueAt (pay initial 1 1 30) 1 == some 100

#guard isTransferError (pay initial 1 2 101) .insufficientBalance
#guard isTransferError (pay initial (2 ^ 160) 2 0) .invalidAddress
#guard isTransferError (pay initial 1 2 (modulus - 200)) .insufficientBalance

private def invalidHugeAccounts (a : Nat) : Account :=
  if a == 1 then { balance := modulus }
  else if a == 2 then { balance := 1 }
  else {}
#guard isTransferError
  (pay (beginTransaction invalidHugeAccounts) 1 2 1) .invalidBalance

private def nearMaxAccounts (a : Nat) : Account :=
  if a == 1 then { balance := 100 }
  else if a == 2 then { balance := modulus - 2 }
  else {}
#guard isTransferError
  (pay (beginTransaction nearMaxAccounts) 1 2 3) .recipientOverflow

end EVMCleanroom.WorldValueTests
