import EVMCleanroom.TransactionListProofs

/-!
# Ordered transaction-list executable guards

These tests use synthetic checked Cancun headers and the real public list
runner. They are distinct from the kernel-checked theorem claims and from the
independent signed EthereumJS/Geth block comparisons.
-/

namespace EVMCleanroom.TransactionListTests

open TransactionList

private def acceptance : Keccak.Acceptance := Keccak.dangerouslyAcceptUnverified

private def fixedBytes (value width : Nat) : Array UInt8 :=
  ((List.range width).reverse.map (fun index => UInt8.ofNat (value / 256 ^ index % 256))).toArray

private def natBytes (value : Nat) : Array UInt8 :=
  ((fixedBytes value 32).toList.dropWhile (· == 0)).toArray

private def header (number timestamp gasUsed blobGas : Nat) : HeaderRLP.Fields :=
  #[fixedBytes 0 32, fixedBytes 0 32, fixedBytes 0xc4 20,
    fixedBytes 0 32, fixedBytes 0 32, fixedBytes 0 32, fixedBytes 0 256,
    #[], natBytes number, natBytes 30000000, natBytes gasUsed, natBytes timestamp,
    #[], fixedBytes 9 32, fixedBytes 0 8, natBytes 2, fixedBytes 0 32,
    natBytes blobGas, #[], fixedBytes 0 32]

private def parentHeader : HeaderRLP.Fields :=
  header 19500000 1710338235 15000000 (3 * HeaderRLP.gasPerBlob)

private def parentDigest : Nat :=
  match HeaderRLP.hash acceptance parentHeader with
  | .ok (_, digest) => digest
  | .error _ => 0

private def childHeader (gasUsed blobGas : Nat) : HeaderRLP.Fields :=
  (header 19500001 1710338236 gasUsed blobGas).set! 0 (fixedBytes parentDigest 32)

private def entry (nonce : Nat) (to : Nat := 0xc1) (gas : Nat := 100000)
    (data : Array UInt8 := #[]) (fuel : Nat := 100) : Entry :=
  { tx := {
      kind := 2, signedChainId := some 1, sender := 0x1000, to, nonce, value := 0
      gasLimit := gas, gasPriceCap := 3, priorityFeeCap := 1, data, accessList := [] }
    fuel }

private def asBlob (item : Entry) (tag : Nat) : Entry :=
  { item with
    tx := { item.tx with kind := 3 }
    blob := some { hashes := #[fixedBytes (2 ^ 248 + tag) 32], maxFeePerBlobGas := 2 } }

private def witnesses (code : Array UInt8 := #[0]) (childCode : Array UInt8 := #[0]) :
    List CallTransaction.WitnessAccount :=
  [ { address := 0x1000, present := true, balance := 1000000000000, nonce := 0, code := #[], storage := [] },
    { address := 0xc1, present := true, balance := 1000, nonce := 1, code,
      storage := [{ key := 0, value := 7 }, { key := 1, value := 0 }] },
    { address := 0xc2, present := true, balance := 100, nonce := 1, code := childCode,
      storage := [{ key := 0, value := 7 }, { key := 1, value := 0 }] },
    { address := 0xc4, present := false, balance := 0, nonce := 0, code := #[], storage := [] },
    { address := 0xc5, present := false, balance := 0, nonce := 0, code := #[], storage := [] },
    { address := 4, present := false, balance := 0, nonce := 0, code := #[], storage := [] } ]

private def input (items : List Entry) (gasUsed : Nat) (blobGas : Nat := 0)
    (code : Array UInt8 := #[0]) (childCode : Array UInt8 := #[0]) : Input :=
  { parent := parentHeader, child := childHeader gasUsed blobGas
    initialWitnesses := witnesses code childCode, transactions := items }

private def accepted (p : Input) (test : Result → Bool) : Bool :=
  match TransactionList.run acceptance p with
  | .accepted result => test result
  | _ => false

private def viewBytes (view : ByteView) : Array UInt8 :=
  ((List.range view.size).map view.readByte).toArray

private def accountIs (result : Result) (address : Nat)
    (test : CallTransaction.WitnessAccount → Bool) : Bool :=
  (result.finalWitnesses.find? (fun w => w.address == address)).any test

#guard match HeaderRLP.checkedFeePair acceptance parentHeader (childHeader 21000 0) with
  | .ok fees => fees == (2, 1)
  | .error _ => false

#guard accepted (input [] 0) (fun r =>
  r.receipts.isEmpty && r.gasUsed == 0 && r.blobGasUsed == 0 &&
  r.finalWitnesses.length == 6 && r.observationBytes == 0)

#guard accepted (input [entry 0, entry 1] 42000) (fun r =>
  r.receipts.map (·.cumulativeGasUsed) == [21000, 42000] &&
  r.receipts.map (fun receipt => receipt.charge.used) == [21000, 21000] &&
  r.receipts.all (·.receiptStatus) &&
  accountIs r 0x1000 (fun w => w.nonce == 2 && w.balance == 999999874000))

#guard accepted (input ((List.range 256).map (fun nonce => entry nonce (fuel := 1))) (256 * 21000))
  (fun r => r.receipts.length == 256 && r.gasUsed == 5376000 &&
    accountIs r 0x1000 (fun w => w.nonce == 256))

#guard accepted (input [entry 0 (fuel := maxReservedFuel)] 21000) (fun r => r.receipts.length == 1)

#guard match TransactionList.run acceptance (input [entry 0, entry 0] 42000) with
  | .rejected (some 1) "invalid-sender-nonce" => true
  | _ => false

#guard match TransactionList.run acceptance (input [entry 0, entry 1 (fuel := 0)] 42000) with
  | .indeterminate (some 1) (.frame .stepLimit) => true
  | _ => false

#guard match TransactionList.run acceptance (input [entry 0 1] 21000) with
  | .indeterminate (some 0) (.frame (.incompleteState 1 none)) => true
  | _ => false

#guard let p := input [entry 0] 23102 (code := #[0x5f, 0x54, 0])
  let ws := p.initialWitnesses.map (fun w => if w.address == 0xc1 then { w with storage := [] } else w)
  match TransactionList.run acceptance { p with initialWitnesses := ws } with
  | .indeterminate (some 0) (.frame (.incompleteState 0xc1 (some 0))) => true
  | _ => false

-- A reverted receipt is retained, and the following ordinary transaction runs.
#guard let first := entry 0 0xc2
  let first := { first with tx := { first.tx with value := 7 } }
  accepted (input [first, entry 1] 42004 (childCode := #[0x5f, 0x5f, 0xfd])) (fun r =>
    r.receipts.map (·.receiptStatus) == [false, true] &&
    r.receipts.map (·.cumulativeGasUsed) == [21004, 42004] &&
    accountIs r 0xc2 (fun w => w.balance == 100) &&
    accountIs r 0x1000 (fun w => w.nonce == 2))

#guard accepted (input [entry 0 0xc2 30000, entry 1] 51000 (childCode := #[0xfe])) (fun r =>
  r.receipts.map (·.receiptStatus) == [false, true] &&
  r.receipts.map (fun receipt => receipt.charge.used) == [30000, 21000])

-- The same account is cold again next transaction; a new access list can warm it.
#guard let third := entry 2
  let third := { third with tx := { third.tx with accessList := [{ address := 0xc1, storageKeys := [0] }] } }
  accepted (input [entry 0, entry 1, third] 71612 (code := #[0x5f, 0x54, 0x50, 0])) (fun r =>
    r.receipts.map (fun receipt => receipt.charge.used) == [23104, 23104, 25404])

#guard accepted (input [entry 0, entry 1] 47236
    (code := #[0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x60, 0xc2, 0x61, 0x4e, 0x20, 0xf1, 0x50, 0]))
  (fun r => r.receipts.map (fun receipt => receipt.charge.used) == [23618, 23618])

-- Repeated clear/set/clear distinguishes fresh original storage and refund state.
#guard accepted (input [entry 0, entry 1 (data := #[9]), entry 2] 85537
    (code := #[0x5f, 0x35, 0x5f, 0x55, 0])) (fun r =>
  r.receipts.map (fun receipt => receipt.charge.used) == [21207, 43123, 21207] &&
  r.receipts.map (fun receipt => receipt.charge.refund) == [4800, 0, 4800] &&
  accountIs r 0xc1 (fun w => w.storage.any (fun slot => slot.key == 0 && slot.value == 0)))

#guard accepted (input [entry 0, entry 1 0xc2] 42379 (code := #[0x5f, 0x5f, 0xa0, 0])) (fun r =>
  r.receipts.map (fun receipt => receipt.logs.length) == [1, 0] && r.observationBytes == 20)

private def hashCode : Array UInt8 := #[0x5f, 0x49, 0x5f, 0x52, 0x60, 32, 0x5f, 0xf3]

#guard accepted (input [asBlob (entry 0) 0x11, entry 1, asBlob (entry 2) 0x22]
    63054 (2 * HeaderRLP.gasPerBlob) hashCode) (fun r =>
  r.receipts.map (·.kind) == [3, 2, 3] &&
  r.receipts.map (fun receipt => viewBytes receipt.output) ==
    [fixedBytes (2 ^ 248 + 0x11) 32, fixedBytes 0 32, fixedBytes (2 ^ 248 + 0x22) 32] &&
  r.receipts.map (·.blobGasUsed) == [131072, 0, 131072] &&
  r.observationBytes == 96 && accountIs r 0x1000 (fun w => w.nonce == 3))

#guard accepted (input [asBlob (entry 0 0xc2 30000) 0x11, entry 1]
    51000 HeaderRLP.gasPerBlob (childCode := #[0xfe])) (fun r =>
  r.receipts.map (·.receiptStatus) == [false, true] &&
  r.receipts.map (·.blobGasUsed) == [131072, 0] && r.blobGasUsed == 131072)

#guard match TransactionList.run acceptance (input [asBlob (entry 0) 0x11] 21000) with
  | .rejected (some 0) "declared-gas-total-exceeded" => true
  | _ => false

#guard match TransactionList.run acceptance
    (input ((List.range 7).map (fun nonce => asBlob (entry nonce) (nonce + 1)))
      (7 * 21000) (6 * HeaderRLP.gasPerBlob)) with
  | .rejected (some 6) "declared-gas-total-exceeded" => true
  | _ => false

#guard let funded := entry 0 0xc5
  let funded := { funded with tx := { funded.tx with value := 500000 } }
  let spending := entry 0
  let spending := { spending with tx := { spending.tx with sender := 0xc5, value := 1 } }
  accepted (input [funded, spending] 42000) (fun r =>
    accountIs r 0xc5 (fun w => w.present && w.nonce == 1 && w.balance == 436999) &&
    accountIs r 0xc1 (fun w => w.balance == 1001))

#guard let p := input [entry 0, entry 1] 42000
  accepted { p with child := p.child.set! 2 (fixedBytes 0x1000 20) } (fun r =>
    accountIs r 0x1000 (fun w => w.nonce == 2 && w.balance == 999999916000))

#guard accepted (input [entry 0 4 21015 (fuel := 0), entry 1 4 21015 (fuel := 0)] 42030) (fun r =>
  r.receipts.all (·.receiptStatus) && r.receipts.map (fun receipt => receipt.output.size) == [0, 0])

#guard match TransactionList.run acceptance (input [] 1) with
  | .rejected none "execution-gas-total-mismatch" => true
  | _ => false

#guard match TransactionList.run acceptance (input [] 0 HeaderRLP.gasPerBlob) with
  | .rejected none "blob-gas-total-mismatch" => true
  | _ => false

#guard match TransactionList.run acceptance (input [entry 0] 21001) with
  | .rejected none "execution-gas-total-mismatch" => true
  | _ => false

#guard let p := input [] 0
  match TransactionList.run acceptance { p with child := p.child.set! 11 (natBytes (HeaderRLP.cancunTime - 1)) } with
  | .indeterminate none (.unsupported "outside-cancun-transaction-rules") => true
  | _ => false

#guard let p := input [] 0
  match TransactionList.run acceptance { p with child := p.child.set! 11 (natBytes HeaderRLP.pragueTime) } with
  | .indeterminate none (.unsupported "outside-cancun-transaction-rules") => true
  | _ => false

#guard let p := input [] 0
  match TransactionList.run acceptance { p with child := p.child.set! 0 (fixedBytes 1 32) } with
  | .indeterminate none (.unsupported "header-pair-refused") => true
  | _ => false

#guard let p := input [] 0
  match TransactionList.run acceptance { p with initialWitnesses := p.initialWitnesses ++ p.initialWitnesses } with
  | .indeterminate none .invalidWitness => true
  | _ => false

#guard match TransactionList.run acceptance (input ((List.range 257).map (fun nonce => entry nonce (fuel := 1))) 0) with
  | .indeterminate none (.frame .resourceLimit) => true
  | _ => false

#guard match TransactionList.run acceptance (input [entry 0 (fuel := 600000), entry 1 (fuel := 600000)] 42000) with
  | .indeterminate none (.frame .resourceLimit) => true
  | _ => false

#guard let shared := Array.replicate (maxInputBytes / 2) (0 : UInt8)
  let p := input [entry 0 (data := shared), entry 1 (data := shared)] 0 (code := #[]) (childCode := #[])
  match preflight p with | .ok () => true | .error _ => false

#guard let shared := Array.replicate (maxInputBytes / 2) (0 : UInt8)
  let p := input [entry 0 (data := shared), entry 1 (data := shared), entry 2 (data := #[0])]
    0 (code := #[]) (childCode := #[])
  match TransactionList.run acceptance p with
  | .indeterminate none (.frame .resourceLimit) => true
  | _ => false

-- Virtual byte views exercise the retention gate without allocating their bytes.
private def transition (size : Nat) : Transition :=
  { result := {
      world := World.beginTransaction (fun _ => {})
      frame := .returned
      receiptStatus := true
      output := { size }
      charge := {
        beforeRefund := 0, refund := 0, used := 0
        returnedWei := 0, tip := 0, burned := 0 }
      cumulativeGasUsed := 0, effectiveGasPrice := 0, logs := [] }
    blobGasUsed := 0, blobFeeBurn := 0 }

#guard match advance { witnesses := [] } (entry 0) (transition maxObservationBytes) with
  | .ok next => next.receiptsRev.length == 1 && next.observationBytes == maxObservationBytes
  | .error _ => false

#guard match advance { witnesses := [] } (entry 0) (transition (maxObservationBytes + 1)) with
  | .error (.indeterminate (.frame .resourceLimit)) => true
  | _ => false

#guard match advance { witnesses := [], observationBytes := maxObservationBytes - 1 }
    (entry 0) (transition 2) with
  | .error (.indeterminate (.frame .resourceLimit)) => true
  | _ => false

/-- Three creations by one sender in one list: the sender nonce and therefore
    the derived address advance inside Lean; only the three absences are
    supplied up front. Empty initcode costs exactly 53000 gas each. -/
private def creationEntry (nonce : Nat) : Entry :=
  { (entry nonce) with tx := CallTransaction.Envelope.creation (some acceptance) (entry nonce).tx }

private def creationAddresses : List Nat :=
  [0, 1, 2].map (Create.createAddress acceptance 0x1000)

private def creationInput : Input :=
  let p := input ([0, 1, 2].map creationEntry) (3 * 53000)
  { p with initialWitnesses := p.initialWitnesses ++ creationAddresses.map fun address =>
      { address, present := false, balance := 0, nonce := 0, code := #[], storage := [] } }

#guard creationAddresses.Nodup
#guard accepted creationInput (fun r =>
  r.receipts.map (·.createdAddress) == creationAddresses.map some &&
  r.receipts.all (·.receiptStatus) && r.gasUsed == 3 * 53000 &&
  accountIs r 0x1000 (fun w => w.nonce == 3) &&
  creationAddresses.all (fun address => accountIs r address (fun w => w.present && w.nonce == 1)))
-- A call receipt in a list reports no created address.
#guard accepted (input [entry 0] 21000 (code := #[])) (fun r => r.receipts.all (·.createdAddress.isNone))

end EVMCleanroom.TransactionListTests
