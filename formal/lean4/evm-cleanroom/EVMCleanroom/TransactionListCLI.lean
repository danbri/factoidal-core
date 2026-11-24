import EVMCleanroom.TransactionCodec
import EVMCleanroom.TransactionList

/-!
Bounded JSON transport for an ordered decoded transaction list. Only the initial
witness and common header pair enter the runner; prefix state and counters are
computed by TransactionList. No signed-byte authentication is performed here.
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
  ] ++ frameError)

private def report (status : String) (fields : List (String × Json)) (optIn : Bool := true) : Json :=
  Json.mkObj ([("schemaVersion", toJson (1 : Nat)), ("status", .str status),
    ("keccakOptIn", .bool optIn)] ++ fields)

private def response (outcome : TransactionList.Outcome) : Json :=
  match outcome with
  | .accepted result =>
    report "executed" [
      ("gasUsed", decimal result.gasUsed),
      ("blobGasUsed", decimal result.blobGasUsed),
      ("receipts", .arr (result.receipts.map receiptJSON).toArray),
      ("accounts", .arr (result.finalWitnesses.map witnessAccountJSON).toArray)]
  | .rejected index reason =>
    report "rejected" [("index", (index.map toJson).getD .null), ("reason", .str reason)]
  | .indeterminate index reason =>
    let fields := match reason with
      | .frame error => transactionErrorFields error
      | .invalidWitness => [("reason", .str "invalidWitness")]
      | .unsupported message => [("reason", .str message)]
    report "indeterminate" ([("index", (index.map toJson).getD .null)] ++ fields)

private def transactionListMain (path : String) : IO UInt32 := do
  let input ← try
      let file ← IO.FS.Handle.mk path .read
      let bytes ← file.read (USize.ofNat (TransactionList.maxInputBytes + 1))
      if bytes.size > TransactionList.maxInputBytes || !(← file.read 1).isEmpty then
        pure (.error "transaction-list input exceeds the byte limit")
      else
        match String.fromUTF8? bytes with
        | some text => pure (.ok text)
        | none => pure (.error "transaction-list input must be UTF-8")
    catch error => pure (.error error.toString)
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

def cliMain (args : List String) : IO UInt32 := do
  match args with
  | ["--dangerously-enable-unverified-keccak", "--transaction-list", path] =>
    transactionListMain path
  | _ =>
    let optIn := args.contains "--dangerously-enable-unverified-keccak"
    IO.println (report "inputError"
      [("reason", .str "usage: evm-transaction-list --dangerously-enable-unverified-keccak --transaction-list FILE")]
      optIn).compress
    return 2

end EVMCleanroom.TransactionListCLI

def main (args : List String) : IO UInt32 :=
  EVMCleanroom.TransactionListCLI.cliMain args
