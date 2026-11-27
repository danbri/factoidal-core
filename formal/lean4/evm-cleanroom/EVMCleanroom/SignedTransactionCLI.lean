import EVMCleanroom.SignedTransaction
import EVMCleanroom.TransactionCodec
import EVMCleanroom.WitnessJSON

/-! Separate experimental raw-signed list transport. No supplied sender or
decoded envelope is accepted. Both unverified crypto opt-ins are required. -/
namespace EVMCleanroom.SignedTransactionCLI
open Lean (Json toJson)
open EVMCleanroom.TransactionCodec
open EVMCleanroom.CLI (errorCode exactViewHex hexBytes)

private def fieldsOnly (value : Json) (allowed : List String) : Except String Unit := do
  let object ← value.getObj?
  for (name, _) in object.toList do
    if !allowed.contains name then throw ("unexpected field: " ++ name)

private def receiptJSON (receipt : TransactionList.Receipt) : Json :=
  let (frameStatus, frameError) := match receipt.frame with
    | .stopped => ("stopped", [])
    | .returned => ("returned", [])
    | .reverted => ("reverted", [])
    | .exceptional error => ("exceptional", [("frameError", Json.str (errorCode error))])
  Json.mkObj ([
    ("type", toJson receipt.kind),
    ("receiptStatus", toJson (if receipt.receiptStatus then (1 : Nat) else 0)),
    ("frameStatus", .str frameStatus),
    ("gasUsedBeforeRefund", decimal receipt.charge.beforeRefund),
    ("refundGas", decimal receipt.charge.refund),
    ("gasUsed", decimal receipt.charge.used),
    ("cumulativeGasUsed", decimal receipt.cumulativeGasUsed),
    ("effectiveGasPrice", decimal receipt.effectiveGasPrice),
    ("gasWeiReturned", decimal receipt.charge.returnedWei),
    ("beneficiaryTip", decimal receipt.charge.tip),
    ("baseFeeBurn", decimal receipt.charge.burned),
    ("returnBytesHex", .str (exactViewHex receipt.output)),
    ("logs", .arr (receipt.logs.map transactionLogJSON).toArray),
    ("blobGasUsed", decimal receipt.blobGasUsed),
    ("blobFeeBurn", decimal receipt.blobFeeBurn)
  ] ++ frameError ++ (receipt.createdAddress.map fun new => [("createdAddress", decimal new)]).getD [])

private def report (status : String) (fields : List (String × Json)) (optIn : Bool := true)
    (schemaVersion : Nat := 1) : Json :=
  Json.mkObj ([("schemaVersion", toJson schemaVersion), ("status", .str status),
    ("keccakOptIn", .bool optIn), ("secpOptIn", .bool optIn)] ++ fields)

private def response (outcome : TransactionList.Outcome) (schemaVersion : Nat := 1) : Json :=
  match outcome with
  | .accepted result =>
    report "executed" [
      ("gasUsed", decimal result.gasUsed),
      ("blobGasUsed", decimal result.blobGasUsed),
      ("receipts", .arr (result.receipts.map receiptJSON).toArray),
      ("accounts", .arr (result.finalWitnesses.map witnessAccountJSON).toArray)] true schemaVersion
  | .rejected index reason =>
    report "rejected" [("index", (index.map toJson).getD .null), ("reason", .str reason)] true schemaVersion
  | .indeterminate index reason =>
    let fields := match reason with
      | .frame error => transactionErrorFields error
      | .invalidWitness => [("reason", .str "invalidWitness")]
      | .unsupported message => [("reason", .str message)]
    report "indeterminate" ([("index", (index.map toJson).getD .null)] ++ fields) true schemaVersion

private def readBoundedInput (path : String) : IO (Except String String) := do
  try
    let file ← IO.FS.Handle.mk path .read
    let bytes ← file.read (USize.ofNat (TransactionList.maxInputBytes + 1))
    if bytes.size > TransactionList.maxInputBytes || !(← file.read 1).isEmpty then
      pure (.error "transaction-list input exceeds the byte limit")
    else
      match String.fromUTF8? bytes with
      | some text => pure (.ok text)
      | none => pure (.error "transaction-list input must be UTF-8")
  catch error => pure (.error error.toString)

private def parseProof (value : Json) : Except String (Array (Array UInt8)) := do
  let nodes ← value.getArr?
  if nodes.size > WitnessAdmission.maxWitnessNodes then throw "too many proof nodes"
  nodes.mapM fun node => do
    EVMCleanroom.CLI.parseBytecode (← node.getStr?)

private def parseStorageInput (value : Json) : Except String WitnessAdmission.StorageInput := do
  fieldsOnly value ["key", "proof"]
  return {
    key := ← decimalField value "key"
    proof := ← parseProof (← value.getObjVal? "proof") }

private def parseAccountInput (value : Json) : Except String WitnessAdmission.AccountInput := do
  fieldsOnly value ["address", "codeHex", "accountProof", "storage"]
  return {
    address := ← decimalField value "address"
    code := ← hexField value "codeHex"
    accountProof := ← parseProof (← value.getObjVal? "accountProof")
    storage := ← (← arrayField value "storage" CallTransaction.maxKeysPerAccount).mapM parseStorageInput }


private def parseRaw (value : Json) : Except String SignedTransaction.RawEntry := do
  fieldsOnly value ["rawHex", "fuel"]
  return { raw := ← hexField value "rawHex", fuel := ← decimalField value "fuel" }

private def parseInput (value : Json) :
    Except String (HeaderRLP.Fields × HeaderRLP.Fields × List WitnessAdmission.AccountInput × List SignedTransaction.RawEntry) := do
  fieldsOnly value ["schemaVersion", "parentHeader", "childHeader", "accounts", "transactions"]
  if (← (← value.getObjVal? "schemaVersion").getNat?) != 3 then
    throw "expected raw signed list schema version 3"
  return (← parseHeader (← value.getObjVal? "parentHeader"),
    ← parseHeader (← value.getObjVal? "childHeader"),
    ← (← arrayField value "accounts" CallTransaction.maxAccounts).mapM parseAccountInput,
    ← (← arrayField value "transactions" TransactionList.maxTransactions).mapM parseRaw)

private def signedMain (a : Keccak.Acceptance) (c : SecpRecovery.Acceptance) (path : String) : IO UInt32 := do
  let input ← readBoundedInput path
  match input >>= WitnessJSON.parse >>= parseInput with
  | .error why =>
    IO.println (report "inputError" [("reason", .str why)] true 3).compress
    return 2
  | .ok (parent, child, accounts, entries) =>
    let result := response (SignedTransaction.run a c parent child accounts entries) 3
    let encoded := result.compress
    if encoded.utf8ByteSize > TransactionList.maxSerializedBytes then
      IO.println (response (.indeterminate none (.frame .resourceLimit)) 3).compress
    else IO.println encoded
    return 0

private def errorJSON (e : SignedTransaction.Failure) : Json :=
  match e with
  | .malformed why => Json.mkObj [("status", .str "malformed"), ("reason", .str why)]
  | .unsupported why => Json.mkObj [("status", .str "unsupported"), ("reason", .str why)]
  | .invalidSignature => Json.mkObj [("status", .str "invalid-signature")]
  | .resourceLimit => Json.mkObj [("status", .str "resource-limit")]
  | .arithmeticRefusal => Json.mkObj [("status", .str "arithmetic-refusal")]

private def inspectRaw (a : Keccak.Acceptance) (c : SecpRecovery.Acceptance) (raw : Array UInt8) : Json :=
  match SignedTransaction.decode raw with
  | .error error => errorJSON error
  | .ok d =>
    match SignedTransaction.recover a c d with
    | .error error => errorJSON error
    | .ok sender =>
      Json.mkObj [
        ("status", .str "recovered"), ("sender", decimal sender),
        ("kind", toJson d.kind), ("chainId", (d.chain.map decimal).getD .null),
        ("to", (d.to.map decimal).getD .null), ("signingHex", .str (hexBytes d.signing)),
        ("nonce", decimal d.nonce), ("gasLimit", decimal d.gasLimit),
        ("gasPriceCap", decimal d.gasPriceCap), ("priorityFeeCap", decimal d.priorityFeeCap),
        ("value", decimal d.value), ("dataHex", .str (hexBytes d.data)),
        ("accessList", .arr (d.accessList.map (fun entry => Json.mkObj [
          ("address", decimal entry.address), ("storageKeys", .arr (entry.storageKeys.map decimal).toArray)])).toArray),
        ("blobVersionedHashes", (d.blob.map (fun b => Json.arr (b.hashes.map fun h => Json.str (hexBytes h)))).getD .null),
        ("maxFeePerBlobGas", (d.blob.map (fun b => decimal b.maxFeePerBlobGas)).getD .null)]

private def parseBatch (value : Json) : Except String (Array (Array UInt8)) := do
  let rows ← value.getArr?
  if rows.size > 1024 then throw "too many raw entries"
  rows.mapM fun row => do
    EVMCleanroom.CLI.parseBytecode (← row.getStr?)

private def inspectMain (a : Keccak.Acceptance) (c : SecpRecovery.Acceptance) (path : String) : IO UInt32 := do
  let input ← readBoundedInput path
  match input >>= WitnessJSON.parse >>= parseBatch with
  | .error why =>
    IO.println (report "inputError" [("reason", .str why)] true 3).compress
    return 2
  | .ok rows =>
    let result := report "inspected" [("rows", .arr (rows.map (inspectRaw a c)))] true 3
    let encoded := result.compress
    if encoded.utf8ByteSize > TransactionList.maxSerializedBytes then
      IO.println (report "indeterminate" [("reason", .str "resource-limit")] true 3).compress
    else IO.println encoded
    return 0

def cliMain (args : List String) : IO UInt32 := do
  match args with
  | ["--dangerously-enable-unverified-keccak", "--dangerously-enable-unverified-secp256k1", mode, path] =>
    let a := Keccak.dangerouslyAcceptUnverified
    let c := SecpRecovery.dangerouslyAcceptUnverified
    if mode == "--raw-signed-list" then signedMain a c path
    else if mode == "--inspect-raw-signed" then inspectMain a c path
    else
      IO.println (report "inputError" [("reason", .str "unknown mode")] true 3).compress
      return 2
  | _ =>
    IO.println (report "inputError" [("reason", .str "both experimental crypto flags required")] false 3).compress
    return 2

end EVMCleanroom.SignedTransactionCLI

def main (args : List String) : IO UInt32 :=
  EVMCleanroom.SignedTransactionCLI.cliMain args
