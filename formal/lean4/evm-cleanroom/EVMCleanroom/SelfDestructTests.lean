import EVMCleanroom.CallTransaction

/-! Executable regression guards for SELFDESTRUCT (EIP-6780) through the
    actual world-aware dispatcher, and for the transaction-end deletion
    through `CallTransaction.settleFrame`. A `#guard` is a test, not a proof. -/

namespace EVMCleanroom.SelfDestructTests

open World CallOpcode

/-- PUSH1 target SELFDESTRUCT. -/
private def destructCode (target : UInt8) : Array UInt8 := #[0x60, target, 0xff]

/-- CALL 0xc3 with no value and empty windows, then the supplied ending. -/
private def callChild (ending : Array UInt8) : Array UInt8 :=
  #[0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x60, 0xc3, 0x61, 0xff, 0xff, 0xf1] ++ ending

/-- 0xc1 is the entry contract, 0xc3 a second contract, 0xc4 a funded
    account without code; 0xc5 is absent. The entry and its caller are warm,
    as a transaction's destination and sender are. -/
private def fixture (entryCode childCode : Array UInt8) (createdEntry createdChild : Bool)
    (entryBalance : Nat := 1000) : TxWorld :=
  let entry : Account :=
    { balance := entryBalance, nonce := 1, code := entryCode, storage := fun k => if k = 1 then 5 else 0 }
  let child : Account :=
    { balance := 50, nonce := 1, code := childCode, storage := fun k => if k = 0 then 3 else 0 }
  { beginTransaction (fun a =>
      if a == 0xc1 then entry else if a == 0xc3 then child else if a == 0xc4 then { balance := 5 } else {}) with
    warmAddresses := fun a => a == 0xc1 || a == 0xc2
    created := fun a => (a == 0xc1 && createdEntry) || (a == 0xc3 && createdChild) }

private def runEntry (w : TxWorld) (gas : Nat := 100000) (profile : Profile := .cancunPlus)
    (readOnly : Bool := false) : CallOpcode.Outcome :=
  let s := frameInput w 0xc1 gas readOnly profile 0xc2 0xc2
  settle w s (executeAtDepth 64 w 0xc1 0 s)

private def absent (a : Account) : Bool :=
  a.balance == 0 && a.nonce == 0 && a.code.isEmpty && a.storage 0 == 0 && a.storage 1 == 0

-- A pre-existing account: 3 + 5000 + 2600 gas, the balance moves, the code,
-- nonce and storage stay, nothing is registered, the beneficiary is warm.
#guard match runEntry (fixture (destructCode 0xc4) #[] false false) with
  | .stopped w s => s.gas == 100000 - 3 - 7600 && s.halted && s.stack.items.isEmpty &&
      (w.accounts 0xc1).balance == 0 && (w.accounts 0xc4).balance == 1005 &&
      (w.accounts 0xc1).code.size == 3 && (w.accounts 0xc1).nonce == 1 &&
      (w.accounts 0xc1).storage 1 == 5 && w.toDelete.isEmpty && w.warmAddresses 0xc4 &&
      !absent ((SelfDestruct.destroyRegistered w).accounts 0xc1)
  | _ => false

-- An absent beneficiary with value: the 25000 new-account surcharge.
#guard match runEntry (fixture (destructCode 0xc5) #[] false false) with
  | .stopped w s => s.gas == 100000 - 3 - 32600 && (w.accounts 0xc5).balance == 1000
  | _ => false

-- No surcharge when no value moves.
#guard match runEntry (fixture (destructCode 0xc5) #[] false false 0) with
  | .stopped _ s => s.gas == 100000 - 3 - 7600
  | _ => false

-- Self-beneficiary, not created: only the warm 5000 charge, nothing changes.
#guard match runEntry (fixture (destructCode 0xc1) #[] false false) with
  | .stopped w s => s.gas == 100000 - 3 - 5000 && (w.accounts 0xc1).balance == 1000 && w.toDelete.isEmpty
  | _ => false

-- Created in this transaction: registered, balance zero, code still present
-- until the transaction end, then absent.
#guard match runEntry (fixture (destructCode 0xc4) #[] true false) with
  | .stopped w _ => w.toDelete == [0xc1] && (w.accounts 0xc1).balance == 0 &&
      (w.accounts 0xc4).balance == 1005 && (w.accounts 0xc1).code.size == 3 &&
      absent ((SelfDestruct.destroyRegistered w).accounts 0xc1) &&
      ((SelfDestruct.destroyRegistered w).accounts 0xc4).balance == 1005 &&
      (SelfDestruct.destroyRegistered w).toDelete.isEmpty
  | _ => false

-- Created with a self-beneficiary: the balance is burnt.
#guard match runEntry (fixture (destructCode 0xc1) #[] true false) with
  | .stopped w _ => w.toDelete == [0xc1] && (w.accounts 0xc1).balance == 0
  | _ => false

-- Exact gas succeeds with nothing left; one less is out of gas and restores the world.
#guard match runEntry (fixture (destructCode 0xc5) #[] true false) (gas := 32603) with
  | .stopped w s => s.gas == 0 && w.toDelete == [0xc1]
  | _ => false
#guard match runEntry (fixture (destructCode 0xc5) #[] true false) (gas := 32602) with
  | .exceptional w _ .outOfGas => w.toDelete.isEmpty && (w.accounts 0xc1).balance == 1000 &&
      !w.warmAddresses 0xc5
  | _ => false

-- Static frame: write protection after the charge; out of gas if the charge fails first.
#guard match runEntry (fixture (destructCode 0xc4) #[] true false) (readOnly := true) with
  | .exceptional w _ .writeProtection => w.toDelete.isEmpty && (w.accounts 0xc1).balance == 1000
  | _ => false
#guard match runEntry (fixture (destructCode 0xc4) #[] true false) (gas := 7602) (readOnly := true) with
  | .exceptional _ _ .outOfGas => true
  | _ => false

-- Fork admission: shanghaiPlus spans the Cancun boundary and refuses; Osaka executes.
#guard match runEntry (fixture (destructCode 0xc4) #[] false false) (profile := .shanghaiPlus) with
  | .indeterminate .unsupportedFork => true
  | _ => false
#guard match runEntry (fixture (destructCode 0xc4) #[] true false) (profile := .osaka) with
  | .stopped w s => s.gas == 100000 - 3 - 7600 && w.toDelete == [0xc1]
  | _ => false

-- Stack underflow is an exceptional halt.
#guard match runEntry (fixture #[0xff] #[] false false) with
  | .exceptional _ _ .stackUnderflow => true
  | _ => false

-- A created child destroys itself; the caller sees success and continues.
#guard match runEntry (fixture (callChild #[0x00]) (destructCode 0xc4) false true) with
  | .stopped w s => s.stack.items.map (·.val) == [1] && w.toDelete == [0xc3] &&
      (w.accounts 0xc3).balance == 0 && (w.accounts 0xc4).balance == 55 &&
      (w.accounts 0xc3).code.size == 3 && s.returnData.size == 0 &&
      absent ((SelfDestruct.destroyRegistered w).accounts 0xc3) &&
      !absent ((SelfDestruct.destroyRegistered w).accounts 0xc1)
  | _ => false

-- The caller reverts or fails after the child's SELFDESTRUCT: nothing is
-- registered and the child's balance is back.
#guard match runEntry (fixture (callChild #[0x5f, 0x5f, 0xfd]) (destructCode 0xc4) false true) with
  | .reverted w _ => w.toDelete.isEmpty && (w.accounts 0xc3).balance == 50 && (w.accounts 0xc4).balance == 5
  | _ => false
#guard match runEntry (fixture (callChild #[0xfe]) (destructCode 0xc4) false true) with
  | .exceptional w _ _ => w.toDelete.isEmpty && (w.accounts 0xc3).balance == 50
  | _ => false

-- Two SELFDESTRUCTs of the same created account register it once.
#guard match runEntry (fixture (callChild (callChild #[0x00])) (destructCode 0xc4) false true) with
  | .stopped w s => s.stack.items.map (·.val) == [1, 1] && w.toDelete == [0xc3]
  | _ => false

-- Witness mode: an uncovered beneficiary is a refusal naming it.
#guard
  let w := { fixture (destructCode 0xc4) #[] false false with
    witnessed := some { account := fun a => a == 0xc1, slot := fun _ _ => false } }
  match runEntry w with
  | .indeterminate (.incompleteState 0xc4 none) => true
  | _ => false

/-! Transaction end through the settlement function of `CallTransaction`. -/

private def tx : CallTransaction.Envelope :=
  { kind := 2, signedChainId := some 1, sender := 0xa1, to := 0xc1, nonce := 0, value := 0,
    gasLimit := 100000, gasPriceCap := 10, priorityFeeCap := 2, data := #[], accessList := [] }

private def block (coinbase : Nat) : CallTransaction.BlockContext :=
  { chainId := 1, coinbase, number := 1, timestamp := 1, gasLimit := 30000000, gasUsedBefore := 0,
    baseFee := 7, prevRandao := 0, blobBaseFee := 1 }

private def budget : CallTransaction.Budget := ⟨21000, 100000, 9, 7⟩

private def settleEntry (w : TxWorld) (coinbase : Nat) : CallTransaction.Outcome :=
  let s := frameInput w 0xc1 budget.frameGas false .cancunPlus 0xa1 0xa1
  CallTransaction.settleFrame tx (block coinbase) budget w s (CallOpcode.execute 64 w 0xc1 s)

-- A created contract is deleted at the transaction end; the sender refund
-- and the tip are credited; the beneficiary keeps the moved balance.
#guard match settleEntry (fixture (destructCode 0xc4) #[] true false) 0xee with
  | .executed r => r.receiptStatus && absent (r.world.accounts 0xc1) && r.world.toDelete.isEmpty &&
      (r.world.accounts 0xc4).balance == 1005 && r.charge.used == 21000 + 3 + 7600 &&
      (r.world.accounts 0xee).balance == r.charge.tip && r.charge.tip == 28603 * 2 &&
      (r.world.accounts 0xa1).balance == r.charge.returnedWei
  | _ => false

-- EELS order: deletion follows the fee credits, so a destroyed fee recipient loses its tip.
#guard match settleEntry (fixture (destructCode 0xc4) #[] true false) 0xc1 with
  | .executed r => r.receiptStatus && absent (r.world.accounts 0xc1) && r.charge.tip != 0
  | _ => false

-- A pre-existing contract is not deleted: it keeps code, nonce and storage.
#guard match settleEntry (fixture (destructCode 0xc4) #[] false false) 0xee with
  | .executed r => r.receiptStatus && (r.world.accounts 0xc1).code.size == 3 &&
      (r.world.accounts 0xc1).nonce == 1 && (r.world.accounts 0xc1).storage 1 == 5 &&
      (r.world.accounts 0xc1).balance == 0 && (r.world.accounts 0xc4).balance == 1005
  | _ => false

-- A failed transaction frame deletes nothing, even for a created child that ran SELFDESTRUCT.
#guard match settleEntry (fixture (callChild #[0xfe]) (destructCode 0xc4) false true) 0xee with
  | .executed r => !r.receiptStatus && (r.world.accounts 0xc3).code.size == 3 &&
      (r.world.accounts 0xc3).balance == 50
  | _ => false

end EVMCleanroom.SelfDestructTests
