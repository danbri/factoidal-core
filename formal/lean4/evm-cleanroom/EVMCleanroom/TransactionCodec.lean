import EVMCleanroom.CLIEncoding
import EVMCleanroom.CallTransaction
import EVMCleanroom.TransactionTransport
import Lean.Data.Json

/-!
Shared JSON byte transport for decoded transaction entry points. This module
has no main function and is imported only by native JSON frontends. Admission,
execution and settlement remain in the protocol modules.
-/
namespace EVMCleanroom.TransactionCodec

open Lean (Json toJson)
open EVMCleanroom.CLI (errorCode exactViewHex hexBytes parseBytecode)

/-- Bound lexical nesting and numeric work before the standard JSON parser. -/
def parseJSON (text : String) : Except String Json :=
  TransactionTransport.parseWith Json.parse text

def decimal (value : Nat) : Json := .str (toString value)

def transactionLogJSON (entry : LogEntry) : Json :=
  Json.mkObj [
    ("address", decimal entry.address),
    ("topics", .arr (entry.topics.map (fun topic => decimal topic.val)).toArray),
    ("dataHex", .str (exactViewHex entry.data)) ]

def decimalJSON (value : Json) : Except String Nat := do
  let digits ← value.getStr?
  if digits.utf8ByteSize > 78 then throw "decimal field exceeds EVM word width"
  match digits.toNat? with
  | none => throw "expected an unsigned decimal string"
  | some n => return n

def decimalField (value : Json) (name : String) : Except String Nat :=
  (value.getObjVal? name).bind decimalJSON

def hexField (value : Json) (name : String) : Except String (Array UInt8) := do
  parseBytecode (← (← value.getObjVal? name).getStr?)

def arrayField (value : Json) (name : String) (limit : Nat) : Except String (List Json) := do
  let data ← (← value.getObjVal? name).getArr?
  if data.size > limit then throw ("too many entries in " ++ name)
  return data.toList

def parseTransactionAccess (value : Json) : Except String CallTransaction.Access := do
  return {
    address := ← decimalField value "address"
    storageKeys := ← (← arrayField value "storageKeys" CallTransaction.maxKeysPerAccount).mapM decimalJSON }

def parseTransactionEnvelope (value : Json) : Except String CallTransaction.Envelope := do
  let chain ← value.getObjVal? "chainId"
  let signedChainId ← match chain with
    | .null => pure none
    | _ => some <$> decimalJSON chain
  return {
    kind := ← (← value.getObjVal? "type").getNat?
    signedChainId
    sender := ← decimalField value "sender"
    to := ← decimalField value "to"
    nonce := ← decimalField value "nonce"
    value := ← decimalField value "value"
    gasLimit := ← decimalField value "gasLimit"
    gasPriceCap := ← decimalField value "gasPriceCap"
    priorityFeeCap := ← decimalField value "priorityFeeCap"
    data := ← hexField value "dataHex"
    accessList := ← (← arrayField value "accessList" CallTransaction.maxAccessEntries).mapM parseTransactionAccess }

def parseTransactionBlock (value : Json) : Except String CallTransaction.BlockContext := do
  return {
    chainId := ← decimalField value "chainId"
    coinbase := ← decimalField value "coinbase"
    number := ← decimalField value "number"
    timestamp := ← decimalField value "timestamp"
    gasLimit := ← decimalField value "gasLimit"
    gasUsedBefore := ← decimalField value "gasUsedBefore"
    baseFee := ← decimalField value "baseFee"
    prevRandao := ← decimalField value "prevRandao"
    blobBaseFee := ← decimalField value "blobBaseFee" }

def parseWitnessSlot (value : Json) : Except String CallTransaction.Slot := do
  return { key := ← decimalField value "key", value := ← decimalField value "value" }

def parseWitnessAccount (value : Json) : Except String CallTransaction.WitnessAccount := do
  return {
    address := ← decimalField value "address"
    present := ← (← value.getObjVal? "exists").getBool?
    balance := ← decimalField value "balance"
    nonce := ← decimalField value "nonce"
    code := ← hexField value "codeHex"
    storage := ← (← arrayField value "storage" CallTransaction.maxKeysPerAccount).mapM parseWitnessSlot }

def parseCallTransaction (value : Json) (acceptance : Option Keccak.Acceptance) :
    Except String CallTransaction.Request := do
  if (← (← value.getObjVal? "schemaVersion").getNat?) != 1 then
    throw "expected transaction schema version 1"
  let fork : CallTransaction.Fork ← match ← (← value.getObjVal? "fork").getStr? with
    | "shanghai" => pure .shanghai
    | "cancun" => pure .cancun
    | _ => throw "expected shanghai or cancun"
  return {
    fork
    fuel := ← decimalField value "fuel"
    tx := ← parseTransactionEnvelope (← value.getObjVal? "transaction")
    block := ← parseTransactionBlock (← value.getObjVal? "block")
    witnesses := ← (← arrayField value "accounts" CallTransaction.maxAccounts).mapM parseWitnessAccount
    keccakAcceptance := acceptance }

def transactionAccountJSON (world : World.TxWorld) (witness : CallTransaction.WitnessAccount) : Json :=
  let account := world.accounts witness.address
  Json.mkObj [
    ("address", decimal witness.address),
    ("exists", .bool (CallValue.accountAlive account)),
    ("balance", decimal account.balance),
    ("nonce", decimal account.nonce),
    ("codeHex", .str (hexBytes account.code)),
    ("storage", .arr (witness.storage.map (fun slot =>
      Json.mkObj [("key", decimal slot.key), ("value", decimal (account.storage slot.key))])).toArray) ]

/-- Encode the final covered values already refreshed by the transaction-list
    runner. The transport does not derive or supply intermediate states. -/
def witnessAccountJSON (witness : CallTransaction.WitnessAccount) : Json :=
  Json.mkObj [
    ("address", decimal witness.address),
    ("exists", .bool witness.present),
    ("balance", decimal witness.balance),
    ("nonce", decimal witness.nonce),
    ("codeHex", .str (hexBytes witness.code)),
    ("storage", .arr (witness.storage.map (fun slot =>
      Json.mkObj [("key", decimal slot.key), ("value", decimal slot.value)])).toArray) ]

def transactionErrorFields (error : Error) : List (String × Json) :=
  let reason := ("reason", Json.str (errorCode error))
  match error with
  | .incompleteState address slot =>
    [reason, ("address", decimal address), ("slot", (slot.map decimal).getD .null)]
  | _ => [reason]

def transactionResponse (request : CallTransaction.Request) (outcome : CallTransaction.Outcome) : Json :=
  let report := fun status fields =>
    Json.mkObj ([("schemaVersion", toJson (1 : Nat)), ("status", .str status),
      ("keccakOptIn", .bool request.keccakAcceptance.isSome)] ++ fields)
  match outcome with
  | .rejected reason => report "rejected" [("reason", .str reason)]
  | .indeterminate (.frame error) => report "indeterminate" (transactionErrorFields error)
  | .indeterminate .invalidWitness => report "indeterminate" [("reason", .str "invalidWitness")]
  | .indeterminate (.unsupported reason) => report "indeterminate" [("reason", .str reason)]
  | .executed result =>
    let bytes := result.logs.foldl (fun n entry => n + entry.data.size + 32 * entry.topics.length + 20)
      result.output.size
    if bytes > CallTransaction.maxDataBytes then
      report "indeterminate" (transactionErrorFields .resourceLimit)
    else
      let (frameStatus, frameError) := match result.frame with
        | .stopped => ("stopped", [])
        | .returned => ("returned", [])
        | .reverted => ("reverted", [])
        | .exceptional error => ("exceptional", [("frameError", Json.str (errorCode error))])
      report "executed" ([
        ("receiptStatus", toJson (if result.receiptStatus then (1 : Nat) else 0)),
        ("frameStatus", .str frameStatus),
        ("gasUsedBeforeRefund", decimal result.charge.beforeRefund),
        ("refundGas", decimal result.charge.refund),
        ("gasUsed", decimal result.charge.used),
        ("cumulativeGasUsed", decimal result.cumulativeGasUsed),
        ("effectiveGasPrice", decimal result.effectiveGasPrice),
        ("gasWeiReturned", decimal result.charge.returnedWei),
        ("beneficiaryTip", decimal result.charge.tip),
        ("baseFeeBurn", decimal result.charge.burned),
        ("returnBytesHex", .str (exactViewHex result.output)),
        ("logs", .arr (result.logs.map transactionLogJSON).toArray),
        ("accounts", .arr (request.witnesses.map (transactionAccountJSON result.world)).toArray)
      ] ++ frameError)

def parseHeader (v : Json) : Except String (Array (Array UInt8)) := do
  let a ← v.getArr?
  if a.size > 24 then throw "header-field-count"
  a.mapM fun x => do
    let h ← x.getStr?
    if h.length > 514 then throw "header-field-width"
    parseBytecode h

def parseBlobHashes (v : Json) : Except String (Array (Array UInt8)) := do
  let hashes ← v.getArr?
  if hashes.size > 128 then throw "hash-inventory-limit"
  hashes.mapM fun x => do
    let h ← x.getStr?
    if h.length > 514 then throw "hash-width-limit"
    parseBytecode h

end EVMCleanroom.TransactionCodec
