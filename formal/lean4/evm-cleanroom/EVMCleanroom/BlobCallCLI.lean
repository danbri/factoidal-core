import EVMCleanroom.CLIEncoding
import EVMCleanroom.BlobCall
import Lean.Data.Json

/-! JSON byte transport for the decoded blob-call runner. The ordinary
transaction JSON codec is from the repository-owned CLITransaction module;
protocol decisions remain in BlobCall and CallTransaction. -/

namespace EVMCleanroom.BlobCallCLI

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

private def parseHeader (v : Json) : Except String HeaderRLP.Fields := do
  let a ← v.getArr?
  if a.size > 24 then throw "header-field-count"
  a.mapM fun x => do
    let h ← x.getStr?
    if h.length > 514 then throw "header-field-width"
    parseBytecode h

private def parseBlobCall (v : Json) (a : Keccak.Acceptance) : Except String BlobCall.Input := do
  let req ← parseCallTransaction v (some a)
  let hashes ← (← v.getObjVal? "blobVersionedHashes").getArr?
  if hashes.size > 128 then throw "hash-inventory-limit"
  let hashes ← hashes.mapM fun x => do
    let h ← x.getStr?
    if h.length > 514 then throw "hash-width-limit"
    parseBytecode h
  return { request := req
    parent := ← parseHeader (← v.getObjVal? "parentHeader")
    child := ← parseHeader (← v.getObjVal? "childHeader")
    hashes := hashes
    blobCap := ← decimalField v "maxFeePerBlobGas"
    priorBlobGas := ← decimalField v "priorBlobGas" }

private def report (out : BlobCall.Outcome) : Json :=
  match out with
  | .refused (.rejected reason) =>
    Json.mkObj [("status", .str "rejected"), ("reason", .str reason)]
  | .refused (.indeterminate reason) =>
    Json.mkObj [("status", .str "indeterminate"), ("reason", .str reason)]
  | .transaction p result =>
    match result with
    | .executed _ =>
      Json.mkObj [("status", .str "executed"), ("blobGasUsed", decimal p.blobGas),
        ("blobFeeBurn", decimal p.burn), ("result", transactionResponse p.request result)]
    | _ => transactionResponse p.request result

def cliMain (args : List String) : IO UInt32 := do
  match args with
  | ["--dangerously-enable-unverified-keccak", "--batch", path] =>
    let file ← IO.FS.Handle.mk path .read
    let cap := USize.ofNat (CallTransaction.maxDataBytes + 1)
    let bytes ← file.read cap
    if bytes.size > CallTransaction.maxDataBytes || !(← file.read 1).isEmpty then
      return 2
    match String.fromUTF8? bytes with
    | none => return 2
    | some input =>
      let mut count := 0
      let mut bad := false
      for line in input.splitOn "\n" do
        if !line.isEmpty then
          count := count + 1
          if count > 4096 then return 2
          let a := Keccak.dangerouslyAcceptUnverified
          match Json.parse line >>= (parseBlobCall · a) with
          | .error reason =>
            IO.println (Json.mkObj [("status", .str "inputError"), ("reason", .str reason)]).compress
            bad := true
          | .ok p => IO.println (report (BlobCall.run a p)).compress
      return if bad || count == 0 then 2 else 0
  | _ => return 2

end EVMCleanroom.BlobCallCLI

def main (args : List String) : IO UInt32 :=
  EVMCleanroom.BlobCallCLI.cliMain args
