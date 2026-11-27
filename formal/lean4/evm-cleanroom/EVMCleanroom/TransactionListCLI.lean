import EVMCleanroom.TransactionCodec
import EVMCleanroom.TransactionList
import EVMCleanroom.WitnessAdmissionProofs
import EVMCleanroom.WitnessJSON

/-!
Bounded JSON transport for ordered decoded transactions and state witnesses.
The legacy mode consumes decoded account values. The authenticated mode derives
its initial values from account and storage proofs under the parent state root;
the separate state-witness mode exposes that admission without execution.
Prefix state and counters are computed by TransactionList. Transaction signatures
and canonical-chain membership are not authenticated here.
-/
namespace EVMCleanroom.TransactionListCLI

open Lean (Json toJson)
open EVMCleanroom.TransactionCodec
open EVMCleanroom.CLI (errorCode exactViewHex)

/-- Reject extra top-level or entry fields so supplied intermediate states and
    counters cannot be mistaken for inputs that the runner authenticates. -/
private def fieldsOnly (value : Json) (allowed : List String) : Except String Unit := do
  let object ← value.getObj?
  for (name, _) in object.toList do
    if !allowed.contains name then throw ("unexpected field: " ++ name)

private def parseEntry (value : Json) : Except String TransactionList.Entry := do
  fieldsOnly value ["fuel", "transaction", "blobVersionedHashes", "maxFeePerBlobGas"]
  let blob : Option TransactionList.BlobFields ← match (value.getObjVal? "blobVersionedHashes").toOption,
      (value.getObjVal? "maxFeePerBlobGas").toOption with
    | none, none => pure none
    | some hashes, some cap => do
      let decodedHashes ← parseBlobHashes hashes
      let maxFee ← decimalJSON cap
      pure (some { hashes := decodedHashes, maxFeePerBlobGas := maxFee })
    | _, _ => throw "blobVersionedHashes and maxFeePerBlobGas must be supplied together"
  return {
    tx := ← parseTransactionEnvelope (← value.getObjVal? "transaction")
      (some Keccak.dangerouslyAcceptUnverified)
    fuel := ← decimalField value "fuel"
    blob }

private def parseInput (value : Json) : Except String TransactionList.Input := do
  fieldsOnly value ["schemaVersion", "parentHeader", "childHeader", "accounts", "transactions"]
  if (← (← value.getObjVal? "schemaVersion").getNat?) != 1 then
    throw "expected transaction-list schema version 1"
  return {
    parent := ← parseHeader (← value.getObjVal? "parentHeader")
    child := ← parseHeader (← value.getObjVal? "childHeader")
    initialWitnesses := ← (← arrayField value "accounts" CallTransaction.maxAccounts).mapM parseWitnessAccount
    transactions := ← (← arrayField value "transactions" TransactionList.maxTransactions).mapM parseEntry }

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
    ("keccakOptIn", .bool optIn)] ++ fields)

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

private def transactionListMain (path : String) : IO UInt32 := do
  let input ← readBoundedInput path
  match input >>= parseJSON >>= parseInput with
  | .error why =>
    IO.println (report "inputError" [("reason", .str why)]).compress
    return 2
  | .ok request =>
    let result := response (TransactionList.run Keccak.dangerouslyAcceptUnverified request)
    let encoded := result.compress
    if encoded.utf8ByteSize > TransactionList.maxSerializedBytes then
      IO.println (response (.indeterminate none (.frame .resourceLimit))).compress
    else
      IO.println encoded
    return 0

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

private def parseAuthenticatedInput (value : Json) :
    Except String (TransactionList.Input × List WitnessAdmission.AccountInput) := do
  fieldsOnly value ["schemaVersion", "parentHeader", "childHeader", "accounts", "transactions"]
  if (← (← value.getObjVal? "schemaVersion").getNat?) != 2 then
    throw "expected authenticated transaction-list schema version 2"
  let accounts ← (← arrayField value "accounts" CallTransaction.maxAccounts).mapM parseAccountInput
  let input : TransactionList.Input := {
    parent := ← parseHeader (← value.getObjVal? "parentHeader")
    child := ← parseHeader (← value.getObjVal? "childHeader")
    initialWitnesses := []
    transactions := ← (← arrayField value "transactions" TransactionList.maxTransactions).mapM parseEntry }
  return (input, accounts)

private def parseStateWitness (value : Json) :
    Except String (Array UInt8 × List WitnessAdmission.AccountInput) := do
  fieldsOnly value ["schemaVersion", "stateRoot", "accounts"]
  if (← (← value.getObjVal? "schemaVersion").getNat?) != 1 then
    throw "expected state-witness schema version 1"
  return (← hexField value "stateRoot",
    ← (← arrayField value "accounts" CallTransaction.maxAccounts).mapM parseAccountInput)

private def witnessResponse (outcome : Except WitnessAdmission.Error (List CallTransaction.WitnessAccount)) :
    Json :=
  match outcome with
  | .error error => report "refused" [
      ("classification", .str error.category), ("reason", .str error.reason)]
  | .ok witnesses => report "authenticated" [
      ("accounts", .arr (witnesses.map witnessAccountJSON).toArray)]

private def stateWitnessMain (path : String) : IO UInt32 := do
  let input ← readBoundedInput path
  match input >>= WitnessJSON.parse >>= parseStateWitness with
  | .error why =>
    IO.println (report "inputError" [("reason", .str why)]).compress
    return 2
  | .ok (root, accounts) =>
    let result := witnessResponse (WitnessAdmission.admit Keccak.dangerouslyAcceptUnverified root accounts)
    let encoded := result.compress
    if encoded.utf8ByteSize > TransactionList.maxSerializedBytes then
      IO.println (witnessResponse (.error .resourceLimit)).compress
    else IO.println encoded
    return 0

private def authenticatedListMain (path : String) : IO UInt32 := do
  let input ← readBoundedInput path
  match input >>= WitnessJSON.parse >>= parseAuthenticatedInput with
  | .error why =>
    IO.println (report "inputError" [("reason", .str why)] true 2).compress
    return 2
  | .ok (request, accounts) =>
    let result := response
      (WitnessAdmission.runAuthenticated Keccak.dangerouslyAcceptUnverified request accounts) 2
    let encoded := result.compress
    if encoded.utf8ByteSize > TransactionList.maxSerializedBytes then
      IO.println (response (.indeterminate none (.frame .resourceLimit)) 2).compress
    else IO.println encoded
    return 0

def cliMain (args : List String) : IO UInt32 := do
  match args with
  | ["--dangerously-enable-unverified-keccak", "--transaction-list", path] =>
    transactionListMain path
  | ["--dangerously-enable-unverified-keccak", "--authenticated-transaction-list", path] =>
    authenticatedListMain path
  | ["--dangerously-enable-unverified-keccak", "--state-witness", path] =>
    stateWitnessMain path
  | _ =>
    let optIn := args.contains "--dangerously-enable-unverified-keccak"
    IO.println (report "inputError"
      [("reason", .str "usage: evm-transaction-list --dangerously-enable-unverified-keccak --transaction-list|--authenticated-transaction-list|--state-witness FILE")]
      optIn).compress
    return 2

end EVMCleanroom.TransactionListCLI

def main (args : List String) : IO UInt32 :=
  EVMCleanroom.TransactionListCLI.cliMain args
