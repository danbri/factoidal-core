import EVMCleanroom.CreateTransactionProofs

/-!
Executable checks of contract-creation transactions through the public
`CallTransaction.run` entry. These are tests of particular inputs, not proofs.
-/

namespace EVMCleanroom.CreateTransactionTests

open World CallTransaction

private def acceptance : Keccak.Acceptance := Keccak.dangerouslyAcceptUnverified

private def sender : Nat := 0x1000

/-- The address created by `sender` at nonce 0. -/
private def new : Nat := Create.createAddress acceptance sender 0

private def absent (address : Nat) : WitnessAccount :=
  { address, present := false, balance := 0, nonce := 0, code := #[], storage := [] }

private def block : BlockContext :=
  { chainId := 1, coinbase := 0xc4, number := 1, timestamp := 1, gasLimit := 30000000
    gasUsedBefore := 0, baseFee := 2, prevRandao := 0, blobBaseFee := 1 }

private def request (data : Array UInt8) (gas : Nat := 200000) (value : Nat := 0)
    (target : Option WitnessAccount := some (absent new)) (kind : Nat := 2) : Request :=
  { fork := .cancun, fuel := 1000
    tx := Envelope.creation (some acceptance) {
      kind, signedChainId := some 1, sender, to := 0, nonce := 0, value
      gasLimit := gas, gasPriceCap := 3, priorityFeeCap := if kind == 2 then 1 else 0, data, accessList := [] }
    block
    witnesses := [{ address := sender, present := true, balance := 10000000, nonce := 0, code := #[], storage := [] },
      absent 0xc4] ++ target.toList
    keccakAcceptance := some acceptance }

private def executed (p : Request) (test : Result → Bool) : Bool :=
  match CallTransaction.run p with
  | .executed result => test result
  | _ => false

private def rejected (p : Request) (reason : String) : Bool :=
  match CallTransaction.run p with
  | .rejected why => why == reason
  | _ => false

private def runtime : Array UInt8 := #[0x60, 0x2a, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]

/-- CODECOPY the 8 runtime bytes that follow these 10 and return them. -/
private def deploy : Array UInt8 := #[0x60, 8, 0x60, 10, 0x5f, 0x39, 0x60, 8, 0x5f, 0xf3] ++ runtime

-- The envelope constructor fills in the derived address and nothing else.
#guard (request deploy).tx.create && (request deploy).tx.to == new && new < addressBound
#guard (Envelope.creation none (request deploy).tx).to == 0

-- Successful deployment: code stored, both nonces 1, the address reported.
#guard executed (request deploy) fun r =>
  r.receiptStatus && createdAddress (request deploy).tx r == some new &&
  (r.world.accounts new).code == runtime && (r.world.accounts new).nonce == 1 &&
  (r.world.accounts sender).nonce == 1 && r.world.created new &&
  -- 21000 + 32000 + 2 (one initcode word) + calldata, then execution and 1600 deposit gas.
  r.charge.used > 53002 + 1600 && r.charge.used < 60000

-- Empty initcode at exactly the intrinsic gas: 21000 + 32000, empty code, nonce 1.
#guard executed (request #[] 53000) fun r =>
  r.receiptStatus && r.charge.used == 53000 && r.charge.returnedWei == 0 &&
  (r.world.accounts new).code.isEmpty && (r.world.accounts new).nonce == 1 &&
  createdAddress (request #[] 53000).tx r == some new
#guard rejected (request #[] 52999) "below-intrinsic-gas"
-- One byte of initcode is one word: 2 more gas, plus 4 for the zero byte.
#guard executed (request #[0] 53006) fun r => r.receiptStatus && r.charge.used == 53006
#guard rejected (request #[0] 53005) "below-intrinsic-gas"

-- EIP-3860 admission: 49152 bytes pass, 49153 are an invalid transaction.
#guard executed (request (Array.replicate 49152 0) 400000) fun r =>
  r.receiptStatus && r.charge.used == 53000 + 4 * 49152 + 2 * 1536
#guard rejected (request (Array.replicate 49153 0) 400000) "initcode-too-large"

-- Types 0 and 1 may create; type 3 is not run by the ordinary entry.
#guard executed (request deploy (kind := 0)) fun r => r.receiptStatus
#guard executed (request deploy (kind := 1)) fun r => r.receiptStatus
#guard match CallTransaction.run (request deploy (kind := 3)) with
  | .indeterminate (.unsupported "unsupported-transaction-type") => true
  | _ => false

-- Value endowment: kept on success, returned on REVERT and on an exceptional halt.
#guard executed (request deploy (value := 5)) fun r => (r.world.accounts new).balance == 5
#guard executed (request #[0x5f, 0x5f, 0xfd] (value := 5)) fun r =>
  !r.receiptStatus && (r.world.accounts new).balance == 0 && (r.world.accounts new).nonce == 0 &&
  (r.world.accounts sender).nonce == 1 && !r.world.created new &&
  createdAddress (request #[0x5f, 0x5f, 0xfd] (value := 5)).tx r == none
#guard executed (request #[0xfe] (value := 5)) fun r =>
  !r.receiptStatus && (r.world.accounts new).balance == 0 && r.charge.used == 200000
#guard rejected (request deploy (value := 10000000)) "insufficient-upfront-balance"

-- Collision: status zero, all gas, sender nonce incremented, target untouched.
private def occupied : WitnessAccount :=
  { address := new, present := true, balance := 3, nonce := 1, code := #[], storage := [] }
#guard executed (request deploy (value := 5) (target := some occupied)) fun r =>
  !r.receiptStatus && r.charge.used == 200000 && r.charge.returnedWei == 0 &&
  (match r.frame with | .exceptional .addressCollision => true | _ => false) &&
  (r.world.accounts sender).nonce == 1 && (r.world.accounts new).nonce == 1 &&
  (r.world.accounts new).balance == 3 && (r.world.accounts new).code.isEmpty
-- EIP-7610: a listed nonzero slot is storage, and collides.
#guard executed (request deploy (target := some { occupied with nonce := 0, storage := [{ key := 3, value := 4 }] }))
  fun r => !r.receiptStatus && r.charge.used == 200000
-- A balance alone does not collide.
#guard executed (request deploy (target := some { occupied with nonce := 0 })) fun r =>
  r.receiptStatus && (r.world.accounts new).balance == 3 && (r.world.accounts new).code == runtime

-- Deposit rules: 0xEF first byte.
#guard executed (request #[0x60, 0xef, 0x5f, 0x53, 0x60, 1, 0x5f, 0xf3]) fun r =>
  !r.receiptStatus && r.charge.used == 200000 && (r.world.accounts new).nonce == 0 &&
  (match r.frame with | .exceptional .invalidContractPrefix => true | _ => false)

-- Witness mode: the new address must be covered.
#guard match CallTransaction.run (request deploy (target := none)) with
  | .indeterminate (.frame (.incompleteState address none)) => address == new
  | _ => false
-- No Keccak opt-in: no address, so no answer.
#guard match CallTransaction.run { request deploy with keccakAcceptance := none } with
  | .indeterminate (.frame .unsupportedFork) => true
  | _ => false
-- A target other than the derived address is refused, never used.
#guard match CallTransaction.run { request deploy with tx := { (request deploy).tx with to := new + 1 } } with
  | .indeterminate (.unsupported "creation-target-mismatch") => true
  | _ => false
-- The same envelope read as a call to the derived address deploys nothing.
#guard executed { request deploy with tx := { (request deploy).tx with create := false } } fun r =>
  r.receiptStatus && (r.world.accounts new).code.isEmpty && (r.world.accounts new).nonce == 0

end EVMCleanroom.CreateTransactionTests
