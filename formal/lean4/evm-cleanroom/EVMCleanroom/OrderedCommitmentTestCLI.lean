import EVMCleanroom.OrderedCommitments
import EVMCleanroom.TransactionCodec
import EVMCleanroom.WitnessJSON

/-! Test-only native entry for the restricted commitment checker. Input is
    bounded; no host-computed verdict enters the Lean transition. -/
namespace EVMCleanroom.OrderedCommitmentTestCLI
open Lean (Json toJson)
open EVMCleanroom.TransactionCodec
open EVMCleanroom.CLI (hexBytes)

private def proofNodes (value : Json) : Except String (Array (Array UInt8)) := do
  let nodes ← value.getArr?
  if nodes.size > WitnessAdmission.maxWitnessNodes then throw "too many proof nodes"
  nodes.mapM fun node => EVMCleanroom.CLI.parseBytecode (← node.getStr?)

private def slot (value : Json) : Except String WitnessAdmission.StorageInput := do
  return { key := ← decimalField value "key",
    proof := ← proofNodes (← value.getObjVal? "proof") }

private def account (value : Json) : Except String WitnessAdmission.AccountInput := do
  return { address := ← decimalField value "address", code := ← hexField value "codeHex",
    accountProof := ← proofNodes (← value.getObjVal? "accountProof"),
    storage := ← (← arrayField value "storage" CallTransaction.maxKeysPerAccount).mapM slot }

private def rawEntry (value : Json) : Except String SignedTransaction.RawEntry := do
  return { raw := ← hexField value "rawHex", fuel := ← decimalField value "fuel" }

private def parseRequest (value : Json) :
    Except String (HeaderRLP.Fields × HeaderRLP.Fields × List WitnessAdmission.AccountInput × List SignedTransaction.RawEntry) := do
  if (← (← value.getObjVal? "schemaVersion").getNat?) != 3 then throw "schema"
  return (← parseHeader (← value.getObjVal? "parentHeader"),
    ← parseHeader (← value.getObjVal? "childHeader"),
    ← (← arrayField value "accounts" CallTransaction.maxAccounts).mapM account,
    ← (← arrayField value "transactions" TransactionList.maxTransactions).mapM rawEntry)

private def failJSON (e : OrderedCommitments.Error) : Json :=
  Json.mkObj [("status", .str "commitment-refused"), ("reason", .str (reprStr e))]

private def checked (a : Keccak.Acceptance) (c : SecpRecovery.Acceptance) (value : Json) :
    Except String Json := do
  let (parent, child, accounts, entries) ← parseRequest value
  match OrderedCommitments.run a c parent child accounts entries with
  | .error (.prior (.rejected index why)) =>
    return Json.mkObj [("status", .str "rejected"), ("index", (index.map toJson).getD .null),
      ("reason", .str why)]
  | .error (.prior (.indeterminate index why)) =>
    let fields := match why with
      | .frame error => transactionErrorFields error
      | .invalidWitness => [("reason", Json.str "invalidWitness")]
      | .unsupported message => [("reason", Json.str message)]
    return Json.mkObj ([("status", .str "indeterminate"), ("index", (index.map toJson).getD .null)] ++ fields)
  | .error (.prior (.accepted _)) => throw "unexpected accepted prior refusal"
  | .error (.commitment e) => return failJSON e
  | .ok out => return Json.mkObj [("status", .str "commitment-checked"),
      ("transactionRoot", .str (hexBytes out.roots.transactions)),
      ("receiptsRoot", .str (hexBytes out.roots.receipts)),
      ("receipts", toJson out.execution.receipts.length)]

private def rootOnly (a : Keccak.Acceptance) (value : Json) : Except String Json := do
  let rows ← value.getArr?
  if rows.size > TransactionList.maxTransactions then return failJSON .resourceLimit
  let raw ← rows.mapM fun row => EVMCleanroom.CLI.parseBytecode (← row.getStr?)
  match OrderedCommitments.root a raw.toList with
  | .ok root => return Json.mkObj [("status", .str "root"), ("root", .str (hexBytes root))]
  | .error e => return failJSON e

def cliMain (args : List String) : IO UInt32 := do
  match args with
  | ["--dangerously-enable-unverified-keccak", "--dangerously-enable-unverified-secp256k1", mode, path] =>
    let file ← IO.FS.Handle.mk path .read
    let raw ← file.read (USize.ofNat (TransactionList.maxInputBytes + 1))
    if raw.size > TransactionList.maxInputBytes || !(← file.read 1).isEmpty then return 2
    let some input := String.fromUTF8? raw | return 2
    let a := Keccak.dangerouslyAcceptUnverified
    let c := SecpRecovery.dangerouslyAcceptUnverified
    let result := WitnessJSON.parse input >>= fun value =>
      if mode == "--checked" then checked a c value
      else if mode == "--root" then rootOnly a value else .error "unknown test mode"
    match result with
    | .ok out => IO.println out.compress; return 0
    | .error why => IO.eprintln why; return 2
  | _ => return 2
end EVMCleanroom.OrderedCommitmentTestCLI

def main (args : List String) : IO UInt32 :=
  EVMCleanroom.OrderedCommitmentTestCLI.cliMain args
