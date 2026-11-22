import EVMCleanroom.CLIEncoding
import EVMCleanroom.CallTransaction
import Lean.Data.Json

/-!
Machine-readable entry point for call transactions with a decoded envelope
and state witness already authenticated by a host. Its JSON codec stays in
this executable so standalone bytecode runs use Lean's lightweight startup.
-/

namespace EVMCleanroom.CLITransaction

open Lean (Json toJson)
open EVMCleanroom.CLI (errorCode exactViewHex hexBytes parseBytecode)

private def decimal (value : Nat) : Json := .str (toString value)

private def transactionLogJSON (entry : LogEntry) : Json :=
  Json.mkObj [
    ("address", decimal entry.address),
    ("topics", .arr (entry.topics.map (fun topic => decimal topic.val)).toArray),
    ("dataHex", .str (exactViewHex entry.data)) ]

private def decimalJSON (value : Json) : Except String Nat := do
  let digits ← value.getStr?
  if digits.utf8ByteSize > 78 then throw "decimal field exceeds EVM word width"
  match digits.toNat? with
  | none => throw "expected an unsigned decimal string"
  | some n => return n

private def decimalField (value : Json) (name : String) : Except String Nat :=
  (value.getObjVal? name).bind decimalJSON

private def hexField (value : Json) (name : String) : Except String (Array UInt8) := do
  parseBytecode (← (← value.getObjVal? name).getStr?)

private def arrayField (value : Json) (name : String) (limit : Nat) : Except String (List Json) := do
  let data ← (← value.getObjVal? name).getArr?
  if data.size > limit then throw ("too many entries in " ++ name)
  return data.toList

private def parseTransactionAccess (value : Json) : Except String CallTransaction.Access := do
  return {
    address := ← decimalField value "address"
    storageKeys := ← (← arrayField value "storageKeys" CallTransaction.maxKeysPerAccount).mapM decimalJSON }

private def parseTransactionEnvelope (value : Json) : Except String CallTransaction.Envelope := do
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

private def parseTransactionBlock (value : Json) : Except String CallTransaction.BlockContext := do
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

private def parseWitnessSlot (value : Json) : Except String CallTransaction.Slot := do
  return { key := ← decimalField value "key", value := ← decimalField value "value" }

private def parseWitnessAccount (value : Json) : Except String CallTransaction.WitnessAccount := do
  return {
    address := ← decimalField value "address"
    present := ← (← value.getObjVal? "exists").getBool?
    balance := ← decimalField value "balance"
    nonce := ← decimalField value "nonce"
    code := ← hexField value "codeHex"
    storage := ← (← arrayField value "storage" CallTransaction.maxKeysPerAccount).mapM parseWitnessSlot }

private def parseCallTransaction (value : Json) (acceptance : Option Keccak.Acceptance) :
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

private def transactionAccountJSON (world : World.TxWorld) (witness : CallTransaction.WitnessAccount) : Json :=
  let account := world.accounts witness.address
  Json.mkObj [
    ("address", decimal witness.address),
    ("exists", .bool (CallValue.accountAlive account)),
    ("balance", decimal account.balance),
    ("nonce", decimal account.nonce),
    ("codeHex", .str (hexBytes account.code)),
    ("storage", .arr (witness.storage.map (fun slot =>
      Json.mkObj [("key", decimal slot.key), ("value", decimal (account.storage slot.key))])).toArray) ]

private def transactionErrorFields (error : Error) : List (String × Json) :=
  let reason := ("reason", Json.str (errorCode error))
  match error with
  | .incompleteState address slot =>
    [reason, ("address", decimal address), ("slot", (slot.map decimal).getD .null)]
  | _ => [reason]

private def transactionResponse (request : CallTransaction.Request) (outcome : CallTransaction.Outcome) : Json :=
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

private def callTransactionMain (path : String) (acceptance : Option Keccak.Acceptance := none) : IO UInt32 := do
  let inputError := fun message => Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("status", .str "inputError"),
    ("reason", .str message), ("keccakOptIn", .bool acceptance.isSome)]
  let input ← try
      let file ← IO.FS.Handle.mk path .read
      let cap := USize.ofNat (CallTransaction.maxDataBytes + 1)
      let bytes ← file.read cap
      if bytes.size > CallTransaction.maxDataBytes || !(← file.read 1).isEmpty then
        pure (.error "transaction input exceeds the observation limit")
      else
        match String.fromUTF8? bytes with
        | some text => pure (.ok text)
        | none => pure (.error "transaction input must be UTF-8")
    catch error => pure (.error error.toString)
  match input >>= Json.parse >>= (parseCallTransaction · acceptance) with
  | .ok request =>
    IO.println (transactionResponse request (CallTransaction.run request)).compress
    return 0
  | .error why =>
    IO.println (inputError why).compress
    return 2

def cliMain (args : List String) : IO UInt32 := do
  let (args, acceptance) := match args with
    | "--dangerously-enable-unverified-keccak" :: rest =>
      (rest, some Keccak.dangerouslyAcceptUnverified)
    | _ => (args, none)
  let args := match args with
    | "--observe-logs" :: rest => rest
    | _ => args
  match args with
  | ["--call-transaction", path] => callTransactionMain path acceptance
  | _ =>
    IO.println (Json.mkObj [("schemaVersion", toJson (1 : Nat)), ("status", .str "inputError"),
      ("reason", .str "usage: evm-call-transaction --call-transaction FILE"),
      ("keccakOptIn", .bool acceptance.isSome)]).compress
    return 2

end EVMCleanroom.CLITransaction

def main (args : List String) : IO UInt32 :=
  EVMCleanroom.CLITransaction.cliMain args
