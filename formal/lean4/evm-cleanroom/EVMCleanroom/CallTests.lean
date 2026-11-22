import EVMCleanroom.Call

/-!
Tests for the explicit zero-value child-call *API*, not bytecode opcode CALL.
The data verifies original-storage snapshots, warm address scopes, storage
rollback and parent gas accounting on actual executed child EVM frames.
-/

namespace EVMCleanroom.WorldCallTests
open EVMCleanroom.World
open EVMCleanroom.WorldCall

-- Use ordinary contract accounts outside the precompile range.
private def accounts (address : Nat) : Account :=
  if address == 0xc3 then
    { code := #[0x60,0x01,0x60,0x00,0x55,0x00] }
  else if address == 0xc4 then
    { code := #[0x60,0x01,0x60,0x00,0x55,0x60,0x00,0x60,0x00,0xfd] }
  else if address == 0xc5 then
    { code := #[0x60,0x01,0x60,0x00,0x55,0xfe] }
  else {}

private def initial : TxWorld := beginTransaction accounts

private def successful := callZeroValue 20 initial 0xc3 50000 30000
private def reverting := callZeroValue 20 initial 0xc4 50000 30000
private def exceptional := callZeroValue 20 initial 0xc5 50000 30000

private def gasRemaining (o : WorldCall.Outcome) : Option Nat :=
  match o with
  | .childSuccess _ gas => some gas
  | .childReverted _ gas => some gas
  | .childExceptional _ gas _ => some gas
  | _ => none

private def committedSlot (o : WorldCall.Outcome) (address key : Nat) : Option Nat :=
  match o with
  | .childSuccess w _ => some ((w.accounts address).storage key)
  | .childReverted w _ => some ((w.accounts address).storage key)
  | .childExceptional w _ _ => some ((w.accounts address).storage key)
  | _ => none

private def warmAddr (o : WorldCall.Outcome) (address : Nat) : Bool :=
  match o with
  | .childSuccess w _ => w.warmAddresses address
  | .childReverted w _ => w.warmAddresses address
  | .childExceptional w _ _ => w.warmAddresses address
  | _ => false

private def warmSlot (o : WorldCall.Outcome) (address key : Nat) : Bool :=
  match o with
  | .childSuccess w _ => w.warmSlots address key
  | .childReverted w _ => w.warmSlots address key
  | .childExceptional w _ _ => w.warmSlots address key
  | _ => false

private def refunded (o : WorldCall.Outcome) : Option Int :=
  match o with
  | .childSuccess w _ => some w.refund
  | .childReverted w _ => some w.refund
  | .childExceptional w _ _ => some w.refund
  | _ => none

private def isChildException (o : WorldCall.Outcome) : Bool :=
  match o with
  | .childExceptional _ _ (.invalidOpcode _) => true
  | _ => false

private def isCallerOOG (o : WorldCall.Outcome) : Bool :=
  match o with
  | .callerOutOfGas => true
  | _ => false

-- Cold target incurs 2,600; of 47,400 remaining, requested 30,000
-- goes to child; child burns 22,106; parent ends with 25,294.
#guard gasRemaining successful == some 25294
#guard committedSlot successful 0xc3 0 == some 1
#guard warmAddr successful 0xc3
#guard warmSlot successful 0xc3 0
#guard refunded successful == some 0

-- A child's REVERT costs execution gas but rolls back persistent state
-- and child slot warmth; target address warmth remains a parent-side effect.
#guard gasRemaining reverting == some 25288
#guard committedSlot reverting 0xc4 0 == some 0
#guard warmAddr reverting 0xc4
#guard !(warmSlot reverting 0xc4 0)
#guard refunded reverting == some 0

-- An exceptionally failing child consumes all forwarded gas and rolls
-- back its SSTORE. It does NOT make the parent exceptionally halt.
#guard isChildException exceptional
#guard gasRemaining exceptional == some 17400
#guard committedSlot exceptional 0xc5 0 == some 0
#guard warmAddr exceptional 0xc5
#guard !(warmSlot exceptional 0xc5 0)

-- Fewer than 2,600 gas cannot touch a cold target.
#guard isCallerOOG (callZeroValue 20 initial 0xc3 2599 10)

-- Once warm, target is billed at 100 rather than 2,600; a repeated
-- same-value SSTORE costs 100, plus two PUSH1s (6).
private def secondCall : Option WorldCall.Outcome :=
  match successful with
  | .childSuccess w _ => some (callZeroValue 20 w 0xc3 50000 30000)
  | _ => none
#guard secondCall.map gasRemaining == some (some 49794)

end EVMCleanroom.WorldCallTests
