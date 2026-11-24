import EVMCleanroom.TransactionCodec
import EVMCleanroom.BlobCall

/-! JSON byte transport for the decoded blob-call runner. The ordinary
transaction codec is shared without importing another executable's main;
protocol decisions remain in BlobCall and CallTransaction. -/

namespace EVMCleanroom.BlobCallCLI

open Lean (Json toJson)
open EVMCleanroom.TransactionCodec

private def parseBlobCall (v : Json) (a : Keccak.Acceptance) : Except String BlobCall.Input := do
  let req ← parseCallTransaction v (some a)
  let hashes ← parseBlobHashes (← v.getObjVal? "blobVersionedHashes")
  return {
    request := req
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
    let inner := transactionResponse p.request result
    match inner.getObjVal? "status" with
    | .ok (.str "executed") =>
      Json.mkObj [("status", .str "executed"), ("blobGasUsed", decimal p.blobGas),
        ("blobFeeBurn", decimal p.burn), ("result", inner)]
    | _ => inner

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
          match parseJSON line >>= (parseBlobCall · a) with
          | .error reason =>
            IO.println (Json.mkObj [("status", .str "inputError"), ("reason", .str reason)]).compress
            bad := true
          | .ok p => IO.println (report (BlobCall.run a p)).compress
      return if bad || count == 0 then 2 else 0
  | _ => return 2

end EVMCleanroom.BlobCallCLI

def main (args : List String) : IO UInt32 :=
  EVMCleanroom.BlobCallCLI.cliMain args
